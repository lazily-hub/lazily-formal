/-
! Command / RPC message plane — formal model.

The formal counterpart of `lazily-spec/protocol.md` § "Command / RPC Message
Plane". It models the pure `CommandProjection` reducer that folds command
submits, progress events, causal receipts, and cancels into a single per-command
projection state.

The properties are deliberately negative where it matters: progress events
(`observed` / `accepted` / `started`) never complete a command; only a terminal
causal receipt does. Stale generations are discarded, duplicate submits are
idempotent no-ops, a cancel cannot override an already-applied command,
conflicting terminal outcomes fail closed instead of selecting a winner, and an
RPC `call` is derived behavior over the projection — it cannot resolve until the
projection holds a terminal receipt.

Terminal receipt semantics are imported from `LazilyFormal.Receipt` so the two
models cannot drift.
-/

import LazilyFormal.Receipt

namespace LazilyFormal.Command

open LazilyFormal.Receipt (ReceiptOutcome Generation)

/-- Folded projection status for one command. `absent` is the pre-submit state.
    `submitted` / `accepted` / `running` are non-terminal. `applied` / `rejected`
    / `cancelled` are terminal. `conflicted` is the fail-closed terminal reached
    when two distinct terminal outcomes collide. -/
inductive CommandStatus where
  | absent : CommandStatus
  | submitted : CommandStatus
  | accepted : CommandStatus
  | running : CommandStatus
  | applied : CommandStatus
  | rejected : CommandStatus
  | cancelled : CommandStatus
  | conflicted : CommandStatus
  deriving Repr, DecidableEq

/-- Terminal statuses close the command; no later input may change them. -/
def CommandStatus.isTerminal : CommandStatus → Bool
  | .absent => false
  | .submitted => false
  | .accepted => false
  | .running => false
  | .applied => true
  | .rejected => true
  | .cancelled => true
  | .conflicted => true

/-- Progress event kinds. All are non-terminal UX/diagnostics signals. -/
inductive EventKind where
  | observed : EventKind
  | accepted : EventKind
  | started : EventKind
  deriving Repr, DecidableEq

/-- The (always non-terminal) status a progress event advances to. -/
def progressStatus : EventKind → CommandStatus
  | .observed => .accepted
  | .accepted => .accepted
  | .started => .running

/-- The terminal command status a terminal receipt outcome maps to. Non-terminal
    receipt outcomes (`observed` / `accepted`) map to progress. -/
def terminalStatusOf : ReceiptOutcome → CommandStatus
  | .observed => .accepted
  | .accepted => .accepted
  | .applied => .applied
  | .rejected => .rejected

/-- One reducer input. Every non-submit input carries the authority generation it
    targets; a mismatch is stale and ignored. -/
inductive Input where
  /-- Submit a command at a generation. -/
  | submit : Generation → Input
  /-- A progress event at a generation. -/
  | progress : Generation → EventKind → Input
  /-- A causal receipt (terminal authority) at a generation. -/
  | receipt : Generation → ReceiptOutcome → Input
  /-- A cancel request at a generation. -/
  | cancel : Generation → Input
  deriving Repr

/-- Whether an input can drive a command to a terminal outcome. Only a terminal
    receipt or a cancel is terminal-capable; submits and progress never are. -/
def Input.isTerminalKind : Input → Bool
  | .submit _ => false
  | .progress _ _ => false
  | .receipt _ o => o.isTerminal
  | .cancel _ => true

/-- Per-command projection state. `generation` is meaningful once `status` leaves
    `absent`. -/
structure CmdState where
  generation : Generation
  status : CommandStatus
  deriving Repr, DecidableEq

/-- The pre-submit projection. -/
def initial : CmdState := { generation := 0, status := .absent }

/-- Whether an RPC `call` observing this projection may resolve. Deliberately just
    the terminal predicate — a `call` is derived behavior, never a separate
    authority. -/
def callResolved (s : CmdState) : Bool := s.status.isTerminal

/-- Fold one input into the projection. Pure kernel; a real implementation stores
    the returned state. -/
def step (s : CmdState) (inp : Input) : CmdState :=
  match inp with
  | .submit g =>
      match s.status with
      | .absent => { generation := g, status := .submitted }
      | _ => s -- idempotent: a command already present is unchanged by re-submit
  | .progress g k =>
      if s.status = .absent then s
      else if g ≠ s.generation then s -- stale generation
      else if s.status.isTerminal then s -- terminal is final
      else { s with status := progressStatus k }
  | .receipt g o =>
      if s.status = .absent then s
      else if g ≠ s.generation then s -- stale generation
      else if o.isTerminal then
        let incoming := terminalStatusOf o
        if s.status.isTerminal then
          if s.status = incoming then s -- idempotent terminal
          else { s with status := .conflicted } -- fail closed, no winner selection
        else { s with status := incoming }
      else -- non-terminal receipt (observed/accepted): record as progress
        if s.status.isTerminal then s
        else { s with status := terminalStatusOf o }
  | .cancel g =>
      if s.status = .absent then s
      else if g ≠ s.generation then s -- stale generation
      else if s.status.isTerminal then s -- cancel after terminal is ignored
      else { s with status := .cancelled }

/-- Fold a sequence of inputs from a starting projection. -/
def fold (s : CmdState) (inputs : List Input) : CmdState :=
  inputs.foldl step s

/-- Reconnect resync: applying a `CommandProjection` image replaces the local
    projection with the snapshot. -/
def resync (_ : CmdState) (snapshot : CmdState) : CmdState := snapshot

/-! ## Theorems -/

/-- Every progress event advances to a non-terminal status. -/
theorem progress_nonterminal (k : EventKind) :
    (progressStatus k).isTerminal = false := by
  cases k <;> rfl

/-- `accepted_nonterminal`: an `accepted` progress event cannot complete a
    command — the resulting projection is non-terminal. -/
theorem accepted_nonterminal (s : CmdState) (g : Generation)
    (hpresent : s.status ≠ .absent)
    (hgen : g = s.generation)
    (hnonterminal : s.status.isTerminal = false) :
    (step s (.progress g .accepted)).status.isTerminal = false := by
  have hstep : step s (.progress g .accepted)
      = { s with status := progressStatus .accepted } := by
    simp [step, hpresent, hgen, hnonterminal]
  rw [hstep]
  exact progress_nonterminal .accepted

/-- `stale_generation_noop`: a progress event from a non-current generation does
    not change the projection. -/
theorem stale_progress_noop (s : CmdState) (g : Generation) (k : EventKind)
    (hpresent : s.status ≠ .absent)
    (hstale : g ≠ s.generation) :
    step s (.progress g k) = s := by
  simp [step, hpresent, hstale]

/-- `stale_generation_noop`: a receipt from a non-current generation does not
    change the projection. -/
theorem stale_receipt_noop (s : CmdState) (g : Generation) (o : ReceiptOutcome)
    (hpresent : s.status ≠ .absent)
    (hstale : g ≠ s.generation) :
    step s (.receipt g o) = s := by
  simp [step, hpresent, hstale]

/-- `duplicate_submit_idempotent`: re-submitting an already-present command is a
    no-op regardless of the replay generation. -/
theorem duplicate_submit_idempotent (g g' : Generation) :
    step (step initial (.submit g)) (.submit g') = step initial (.submit g) := by
  simp [step, initial]

/-- `cancel_cannot_override_applied`: a cancel after `applied` is ignored — it
    never rewrites `applied` into `cancelled`. -/
theorem cancel_cannot_override_applied (s : CmdState) (g : Generation)
    (happlied : s.status = .applied) :
    step s (.cancel g) = s := by
  have hterm : s.status.isTerminal = true := by rw [happlied]; rfl
  have habsent : s.status ≠ .absent := by rw [happlied]; decide
  by_cases hg : g = s.generation
  · simp [step, habsent, hg, hterm]
  · simp [step, habsent, hg]

/-- `terminal_conflict_fails_closed`: a `rejected` receipt after an `applied`
    terminal does not select a winner; it drives the projection to `conflicted`
    (a distinct fail-closed terminal), never to `applied` or `rejected`. -/
theorem terminal_conflict_fails_closed (s : CmdState) (g : Generation)
    (happlied : s.status = .applied)
    (hgen : g = s.generation) :
    (step s (.receipt g .rejected)).status = .conflicted := by
  have habsent : s.status ≠ .absent := by rw [happlied]; decide
  simp [step, hgen, terminalStatusOf, ReceiptOutcome.isTerminal,
    CommandStatus.isTerminal, happlied]

/-- An idempotent terminal receipt (same outcome, same generation) leaves the
    projection unchanged. -/
theorem terminal_receipt_idempotent (s : CmdState) (g : Generation)
    (happlied : s.status = .applied)
    (hgen : g = s.generation) :
    step s (.receipt g .applied) = s := by
  have habsent : s.status ≠ .absent := by rw [happlied]; decide
  simp [step, hgen, terminalStatusOf, ReceiptOutcome.isTerminal,
    CommandStatus.isTerminal, happlied]

/-- `projection_reconnect_equiv`: resyncing from a fresh projection with a
    snapshot of a folded state reproduces exactly that folded state. Folding the
    events and then snapshotting is equivalent to applying the projection after
    reconnect. -/
theorem projection_reconnect_equiv (start : CmdState) (inputs : List Input) :
    resync initial (fold start inputs) = fold start inputs := by
  rfl

/-- A non-terminal receipt outcome maps to a non-terminal command status. -/
theorem terminalStatusOf_nonterminal (o : ReceiptOutcome)
    (ho : o.isTerminal = false) :
    (terminalStatusOf o).isTerminal = false := by
  cases o <;>
    simp_all [terminalStatusOf, ReceiptOutcome.isTerminal, CommandStatus.isTerminal]

/-- Helper: folding only non-terminal-kind inputs from a non-terminal projection
    keeps the projection non-terminal. -/
theorem fold_nonterminal_inputs (s : CmdState) (inputs : List Input)
    (hs : s.status.isTerminal = false)
    (hinputs : ∀ inp ∈ inputs, inp.isTerminalKind = false) :
    (fold s inputs).status.isTerminal = false := by
  induction inputs generalizing s with
  | nil => simpa [fold] using hs
  | cons inp rest ih =>
    have hhead : inp.isTerminalKind = false := hinputs inp (List.mem_cons_self)
    have htail : ∀ x ∈ rest, x.isTerminalKind = false := by
      intro x hx; exact hinputs x (List.mem_cons_of_mem inp hx)
    have hstep : (step s inp).status.isTerminal = false := by
      cases inp with
      | submit g =>
        cases hstatus : s.status <;>
          simp_all [step, CommandStatus.isTerminal]
      | progress g k =>
        by_cases habsent : s.status = .absent
        · simpa [step, habsent] using hs
        · by_cases hgen : g = s.generation
          · by_cases hterm : s.status.isTerminal = true
            · simp_all -- hterm (terminal) contradicts hs (non-terminal)
            · simp [step, habsent, hgen, hterm, progress_nonterminal]
          · simp [step, habsent, hgen]; simpa using hs
      | receipt g o =>
        -- receipt is non-terminal-kind ⇒ o.isTerminal = false
        have ho : o.isTerminal = false := by
          simpa [Input.isTerminalKind] using hhead
        by_cases habsent : s.status = .absent
        · simpa [step, habsent] using hs
        · by_cases hgen : g = s.generation
          · simp [step, habsent, hgen, ho, hs, terminalStatusOf_nonterminal o ho]
          · simp [step, habsent, hgen]; simpa using hs
      | cancel g =>
        -- cancel is terminal-kind, contradiction with hhead
        simp [Input.isTerminalKind] at hhead
    exact ih (step s inp) hstep htail

/-- `rpc_call_terminal_only`: a unary `call` observing a projection built from a
    submit followed by only progress/non-terminal inputs cannot resolve. It
    resolves only once a terminal receipt (or cancel) folds in. -/
theorem rpc_call_terminal_only (g : Generation) (inputs : List Input)
    (hinputs : ∀ inp ∈ inputs, inp.isTerminalKind = false) :
    callResolved (fold (step initial (.submit g)) inputs) = false := by
  have hs : (step initial (.submit g)).status.isTerminal = false := by
    simp [step, initial, CommandStatus.isTerminal]
  simpa [callResolved] using fold_nonterminal_inputs _ inputs hs hinputs

end LazilyFormal.Command
