/-
! Causal receipt projection — formal model.

The formal counterpart of `lazily-spec/protocol.md` § "Causal Receipts".
It models the pure reducer that turns receipt events into an outcome
projection for a command/effect causation id.

The important property is deliberately negative: a delivery-style observation is
not authority. `observed` and `accepted` receipts are non-terminal; only
`applied` and `rejected` terminal receipts complete the causation. Stale
generations are discarded, duplicate receipt ids are idempotent no-ops, and
conflicting terminal outcomes fail closed instead of selecting a winner.
-/

import LazilyFormal.Primitive

namespace LazilyFormal.Receipt

/-- Abstract receipt id, used as an idempotency key. -/
abbrev ReceiptId := Nat

/-- Abstract command/effect id that a receipt observes. -/
abbrev CausationId := Nat

/-- Abstract producer/editor generation. -/
abbrev Generation := Nat

/-- Generic receipt outcomes. `observed` / `accepted` are non-terminal; `applied`
    / `rejected` are terminal. -/
inductive ReceiptOutcome where
  | observed : ReceiptOutcome
  | accepted : ReceiptOutcome
  | applied : ReceiptOutcome
  | rejected : ReceiptOutcome
  deriving Repr, DecidableEq

/-- Whether an outcome is terminal for the causation projection. -/
def ReceiptOutcome.isTerminal : ReceiptOutcome → Bool
  | .observed => false
  | .accepted => false
  | .applied => true
  | .rejected => true

/-- One causal receipt event. Payload hashes and human reasons are wire/debug
    fields, so this pure model tracks only the fields that affect projection. -/
structure Receipt where
  receipt : ReceiptId
  causation : CausationId
  generation : Generation
  outcome : ReceiptOutcome
  deriving Repr

/-- Result of applying a receipt to the projection. -/
inductive ApplyResult where
  /-- Receipt was accepted into the projection. -/
  | recorded : ApplyResult
  /-- Same `receipt_id` was already seen. -/
  | duplicate : ApplyResult
  /-- Receipt belongs to an older/newer generation than the current authority. -/
  | staleGeneration : ApplyResult
  /-- A different terminal outcome already exists for this causation/generation. -/
  | terminalConflict : ApplyResult
  deriving Repr, DecidableEq

/-- Apply one receipt against the current generation, an optional existing terminal
    outcome for the causation id, and a receipt-id membership predicate.

This is a pure projection kernel. A real implementation stores the returned
receipt when the result is `recorded`; `duplicate`, `staleGeneration`, and
`terminalConflict` do not update the authoritative terminal projection.
-/
def apply
    (current : Generation)
    (existingTerminal : Option ReceiptOutcome)
    (seen : ReceiptId → Bool)
    (r : Receipt) : ApplyResult :=
  if seen r.receipt then
    .duplicate
  else if r.generation = current then
    if r.outcome.isTerminal then
      match existingTerminal with
      | none => .recorded
      | some prior =>
        if prior = r.outcome then .recorded else .terminalConflict
    else
      .recorded
  else
    .staleGeneration

/-! ## Theorems -/

theorem observed_nonterminal :
    ReceiptOutcome.observed.isTerminal = false := rfl

theorem accepted_nonterminal :
    ReceiptOutcome.accepted.isTerminal = false := rfl

theorem applied_terminal :
    ReceiptOutcome.applied.isTerminal = true := rfl

theorem rejected_terminal :
    ReceiptOutcome.rejected.isTerminal = true := rfl

/-- Duplicate receipt ids are idempotent no-ops independent of generation or
    outcome. -/
theorem duplicate_receipt_noop
    (current : Generation)
    (existing : Option ReceiptOutcome)
    (seen : ReceiptId → Bool)
    (r : Receipt)
    (hseen : seen r.receipt = true) :
    apply current existing seen r = .duplicate := by
  simp [apply, hseen]

/-- Stale-generation receipts are discarded before they can affect the current
    projection. -/
theorem stale_generation_discarded
    (current : Generation)
    (existing : Option ReceiptOutcome)
    (seen : ReceiptId → Bool)
    (r : Receipt)
    (hseen : seen r.receipt = false)
    (hstale : r.generation ≠ current) :
    apply current existing seen r = .staleGeneration := by
  simp [apply, hseen, hstale]

/-- Non-terminal receipts (`observed` / `accepted`) can be recorded for audit or
    progress UI, but they cannot conflict with or replace a terminal outcome. -/
theorem nonterminal_records_without_terminal_conflict
    (current : Generation)
    (existing : Option ReceiptOutcome)
    (seen : ReceiptId → Bool)
    (r : Receipt)
    (hseen : seen r.receipt = false)
    (hgen : r.generation = current)
    (hnonterminal : r.outcome.isTerminal = false) :
    apply current existing seen r = .recorded := by
  simp [apply, hseen, hgen, hnonterminal]

/-- A terminal receipt records successfully when no terminal outcome exists yet. -/
theorem first_terminal_records
    (current : Generation)
    (seen : ReceiptId → Bool)
    (r : Receipt)
    (hseen : seen r.receipt = false)
    (hgen : r.generation = current)
    (hterminal : r.outcome.isTerminal = true) :
    apply current none seen r = .recorded := by
  simp [apply, hseen, hgen, hterminal]

/-- A second different terminal outcome for the same causation/generation fails
    closed as a conflict. -/
theorem distinct_terminal_conflicts
    (current : Generation)
    (receipt : ReceiptId)
    (causation : CausationId)
    (prior incoming : ReceiptOutcome)
    (hincoming : incoming.isTerminal = true)
    (hdiff : prior ≠ incoming) :
    apply current (some prior) (fun _ => false)
      { receipt := receipt, causation := causation, generation := current, outcome := incoming } =
      .terminalConflict := by
  simp [apply, hincoming, hdiff]

end LazilyFormal.Receipt
