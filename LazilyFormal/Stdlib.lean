/-
! Portable standard-library state machines.

This is the semantic authority behind
`lazily-spec/conformance/stdlib/{timer,timeout,revision_barrier}.json`.
Time is logical and caller-driven. The model deliberately owns no executor,
thread, transport, or effect-receipt storage.
-/

namespace LazilyFormal.Stdlib

/-! ## Timer -/

inductive TimerState where
  | pending (deadline lastNow : Nat)
  | fired (firedAt : Nat)
  deriving DecidableEq, Repr

inductive TimerObservation where
  | pending (deadline : Nat)
  | fired (firedAt : Nat)
  | unavailable
  deriving DecidableEq, Repr

def TimerState.terminal : TimerState → Prop
  | .pending .. => False
  | .fired .. => True

def TimerState.observe (state : TimerState) (now : Nat) :
    TimerObservation × TimerState :=
  match state with
  | .fired firedAt => (.fired firedAt, state)
  | .pending deadline lastNow =>
      if now < lastNow then
        (.unavailable, state)
      else if deadline ≤ now then
        (.fired now, .fired now)
      else
        (.pending deadline, .pending deadline now)

/-- A terminal timer observation is latched and idempotent. -/
theorem timer_terminal_replay (firedAt now : Nat) :
    (TimerState.fired firedAt).observe now =
      (.fired firedAt, .fired firedAt) := by
  rfl

/-- Timer terminality is monotone under every observation. -/
theorem timer_terminality_monotone (state : TimerState) (now : Nat)
    (h : state.terminal) : (state.observe now).2.terminal := by
  cases state with
  | pending deadline lastNow => simp [TimerState.terminal] at h
  | fired firedAt => simp [TimerState.observe, TimerState.terminal]

/-- A monotone observation strictly before the deadline cannot fire. -/
theorem timer_cannot_fire_before (deadline lastNow now : Nat)
    (hclock : lastNow ≤ now) (hbefore : now < deadline) :
    (TimerState.pending deadline lastNow).observe now =
      (.pending deadline, .pending deadline now) := by
  simp [TimerState.observe, Nat.not_lt.mpr hclock, Nat.not_le.mpr hbefore]

/-- A monotone observation at or after the deadline must fire. -/
theorem timer_must_fire_at_or_after (deadline lastNow now : Nat)
    (hclock : lastNow ≤ now) (hreached : deadline ≤ now) :
    (TimerState.pending deadline lastNow).observe now =
      (.fired now, .fired now) := by
  simp [TimerState.observe, Nat.not_lt.mpr hclock, hreached]

/-! ## Caller-driven timeout -/

inductive OperationProbe (α : Type) where
  | pending
  | completed (value : α)
  | unavailable
  deriving DecidableEq, Repr

inductive CancellationProbe where
  | pending
  | cancelled
  | unavailable
  deriving DecidableEq, Repr

inductive TimeoutState (α : Type) where
  | pending (deadline lastNow : Nat)
  | completed (value : α)
  | timedOut
  | cancelled
  | unavailable
  deriving DecidableEq, Repr

def TimeoutState.terminal : TimeoutState α → Prop
  | .pending .. => False
  | _ => True

def TimeoutState.poll (state : TimeoutState α) (now : Nat)
    (operation : OperationProbe α) (cancellation : CancellationProbe) :
    TimeoutState α :=
  match state with
  | .completed value => .completed value
  | .timedOut => .timedOut
  | .cancelled => .cancelled
  | .unavailable => .unavailable
  | .pending deadline lastNow =>
      if now < lastNow then
        .unavailable
      else if deadline ≤ now then
        .timedOut
      else
        match operation with
        | .completed value => .completed value
        | .unavailable => .unavailable
        | .pending =>
            match cancellation with
            | .pending => .pending deadline now
            | .cancelled => .cancelled
            | .unavailable => .unavailable

/-- Polling any terminal timeout state is an idempotent replay. -/
theorem timeout_terminal_replay (state : TimeoutState α) (now : Nat)
    (operation : OperationProbe α) (cancellation : CancellationProbe)
    (h : state.terminal) :
    state.poll now operation cancellation = state := by
  cases state <;> simp [TimeoutState.terminal] at h
  all_goals simp [TimeoutState.poll]

/-- Timeout terminality is monotone under every poll. -/
theorem timeout_terminality_monotone (state : TimeoutState α) (now : Nat)
    (operation : OperationProbe α) (cancellation : CancellationProbe)
    (h : state.terminal) :
    (state.poll now operation cancellation).terminal := by
  rw [timeout_terminal_replay state now operation cancellation h]
  exact h

/-- At the inclusive deadline no operation or cancellation result can win. -/
theorem timeout_deadline_dominates (deadline lastNow now : Nat)
    (operation : OperationProbe α) (cancellation : CancellationProbe)
    (hclock : lastNow ≤ now) (hreached : deadline ≤ now) :
    (TimeoutState.pending deadline lastNow).poll now operation cancellation =
      .timedOut := by
  simp [TimeoutState.poll, Nat.not_lt.mpr hclock, hreached]

/-- Before the deadline, completion wins a simultaneous cancellation. -/
theorem timeout_completion_wins_cancellation (deadline lastNow now : Nat)
    (value : α) (hclock : lastNow ≤ now) (hbefore : now < deadline) :
    (TimeoutState.pending deadline lastNow).poll now (.completed value)
        .cancelled = .completed value := by
  simp [TimeoutState.poll, Nat.not_lt.mpr hclock, Nat.not_le.mpr hbefore]

/-! ## Revision barrier -/

structure BarrierWaiting where
  revision : Nat
  generation : Nat
  required : Nat
  deadline : Option Nat
  lastNow : Nat
  deriving DecidableEq, Repr

inductive BarrierState where
  | waiting (wait : BarrierWaiting)
  | satisfied (revision : Nat)
  | timedOut (revision : Nat)
  | cancelled (revision : Nat)
  | disposed (revision : Nat)
  | unavailable (revision : Nat)
  deriving DecidableEq, Repr

def BarrierState.revision : BarrierState → Nat
  | .waiting wait => wait.revision
  | .satisfied revision
  | .timedOut revision
  | .cancelled revision
  | .disposed revision
  | .unavailable revision => revision

def BarrierState.terminal : BarrierState → Prop
  | .waiting .. => False
  | _ => True

def BarrierState.registerRecheck (state : BarrierState)
    (observedRevision : Nat) (predicate : Bool) : BarrierState :=
  match state with
  | .waiting wait =>
      let revision := max wait.revision observedRevision
      let wait' := {
        wait with
        revision
        generation := wait.generation + 1
      }
      if wait.required ≤ revision ∧ predicate = true then
        .satisfied revision
      else
        .waiting wait'
  | terminal => terminal

def BarrierState.advance (state : BarrierState) (observedRevision : Nat)
    (predicate : Bool) : BarrierState :=
  match state with
  | .waiting wait =>
      let revision := max wait.revision observedRevision
      let wait' := {
        wait with
        revision
        generation := wait.generation + 1
      }
      if wait.required ≤ revision ∧ predicate = true then
        .satisfied revision
      else
        .waiting wait'
  | terminal => terminal

def BarrierWaiting.resolve (wait : BarrierWaiting) (now : Nat)
    (predicate : Bool) (cancellation : CancellationProbe) : BarrierState :=
  if wait.required ≤ wait.revision ∧ predicate = true then
    .satisfied wait.revision
  else
    match cancellation with
    | .pending => .waiting { wait with lastNow := now }
    | .cancelled => .cancelled wait.revision
    | .unavailable => .unavailable wait.revision

def BarrierState.observe (state : BarrierState) (now : Nat)
    (predicate : Bool) (cancellation : CancellationProbe) : BarrierState :=
  match state with
  | .waiting wait =>
      if now < wait.lastNow then
        .unavailable wait.revision
      else
        match wait.deadline with
        | some deadline =>
            if deadline ≤ now then
              .timedOut wait.revision
            else
              wait.resolve now predicate cancellation
        | none => wait.resolve now predicate cancellation
  | terminal => terminal

def BarrierState.dispose : BarrierState → BarrierState
  | .waiting wait => .disposed wait.revision
  | terminal => terminal

def BarrierState.cancel : BarrierState → BarrierState
  | .waiting wait => .cancelled wait.revision
  | terminal => terminal

/-- Effect receipts are observations, never revision-barrier authority. -/
def BarrierState.observeReceipt (state : BarrierState) (_receipt : Nat) :
    BarrierState :=
  state

/-- Barrier revisions never decrease when an advance is observed. -/
theorem barrier_revision_monotone (state : BarrierState)
    (observedRevision : Nat) (predicate : Bool) :
    state.revision ≤ (state.advance observedRevision predicate).revision := by
  cases state with
  | waiting wait =>
      simp only [BarrierState.advance]
      split <;> simp [BarrierState.revision, Nat.le_max_left]
  | satisfied revision => simp [BarrierState.advance, BarrierState.revision]
  | timedOut revision => simp [BarrierState.advance, BarrierState.revision]
  | cancelled revision => simp [BarrierState.advance, BarrierState.revision]
  | disposed revision => simp [BarrierState.advance, BarrierState.revision]
  | unavailable revision => simp [BarrierState.advance, BarrierState.revision]

/-- Register-then-recheck observes an advance that raced with registration. -/
theorem barrier_registration_recheck_has_no_lost_wakeup
    (wait : BarrierWaiting) (observedRevision : Nat)
    (hreached : wait.required ≤ observedRevision) :
    (BarrierState.waiting wait).registerRecheck observedRevision true =
      .satisfied (max wait.revision observedRevision) := by
  simp [
    BarrierState.registerRecheck,
    Nat.le_trans hreached (Nat.le_max_right wait.revision observedRevision)
  ]

/-- A terminal barrier ignores every later revision advance. -/
theorem barrier_terminal_advance_latched (state : BarrierState)
    (observedRevision : Nat) (predicate : Bool) (h : state.terminal) :
    state.advance observedRevision predicate = state := by
  cases state <;> simp [BarrierState.terminal] at h
  all_goals simp [BarrierState.advance]

/-- Disposal cannot be overwritten by later advances. -/
theorem barrier_disposal_latched (revision observedRevision : Nat)
    (predicate : Bool) :
    (BarrierState.disposed revision).advance observedRevision predicate =
      .disposed revision := by
  rfl

/-- Cancellation cannot be overwritten by later advances. -/
theorem barrier_cancellation_latched (revision observedRevision : Nat)
    (predicate : Bool) :
    (BarrierState.cancelled revision).advance observedRevision predicate =
      .cancelled revision := by
  rfl

/-- Recording an effect receipt changes neither state nor revision. -/
theorem effect_receipt_is_not_barrier_authority (state : BarrierState)
    (receipt : Nat) :
    state.observeReceipt receipt = state ∧
      (state.observeReceipt receipt).revision = state.revision := by
  simp [BarrierState.observeReceipt]

end LazilyFormal.Stdlib
