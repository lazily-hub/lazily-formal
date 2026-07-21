/-
! Async formula state machine — formal model.

The formal counterpart of `lazily-spec/docs/async.md` § "Async slot state
machine". Models the pure transition core of an async `FormulaCell` (a derived
node held in an arena *slot* — hence the `SlotState` name, in the storage sense
kept by the Cell kernel): the `Empty / Computing / Resolved / Error` lifecycle
with revision-tracked stale completion discard.

The headline invariant — "a stale completion is never published" — is the pure
state-machine core of conformance point 2 (`async.md:218-219`). The
concurrency-specific properties (waiter cancellation, the two benign `get_async`
races, one-in-flight-per-revision deduplication) are explicitly out of scope for
a pure Lean model: the spec itself notes they are "pinned by targeted
deterministic tests rather than exhaustive interleaving exploration"
(`async.md:236`).

`step` is a total function of `(slot, event)`, so the stale-discard guarantee
holds for *every* input — the universal result no finite deterministic test
suite can establish.
-/

import LazilyFormal.Primitive

namespace LazilyFormal.AsyncSlotState

/-- A slot's lifecycle state (`async.md:81-86`). -/
inductive SlotState where
  | empty     : SlotState
  | computing : SlotState
  | resolved  : SlotState
  | error     : SlotState
  deriving Repr

/-- A monotonic revision counter (`async.md:88-90`). -/
abbrev Revision := Nat

/-- An abstract slot value (the materialized payload). -/
abbrev Value := Nat

/-- An async slot: lifecycle state, monotonic revision, the revision recorded
for the in-flight computation (if any), and the optional cached value. -/
structure AsyncSlot where
  state : SlotState
  revision : Revision
  computeRev : Option Revision
  value : Option Value
  deriving Repr

/-- An event that drives the slot through its lifecycle (`async.md:94-105`). -/
inductive SlotEvent where
  | start       : SlotEvent
  | completeOk  : Revision → Value → SlotEvent
  | completeErr : Revision → SlotEvent
  | invalidate  : SlotEvent
  | retry       : SlotEvent
  | hardClear   : SlotEvent
  deriving Repr

/-- One transition of the slot state machine. A completion is accepted only when
its revision is the slot's current in-flight revision (`async.md:89-90`);
otherwise the result is discarded and the slot is unchanged. -/
def step (s : AsyncSlot) : SlotEvent → AsyncSlot
  | SlotEvent.start =>
    match s.state with
    | SlotState.empty => { s with state := SlotState.computing, computeRev := some s.revision }
    | _ => s
  | SlotEvent.completeOk r v =>
    match s.state with
    | SlotState.computing =>
      if some r = s.computeRev then
        { s with state := SlotState.resolved, value := some v, computeRev := none }
      else
        s
    | _ => s
  | SlotEvent.completeErr r =>
    match s.state with
    | SlotState.computing =>
      if some r = s.computeRev then
        { s with state := SlotState.error, computeRev := none }
      else
        s
    | _ => s
  | SlotEvent.invalidate =>
    let newRev := s.revision + 1
    match s.state with
    | SlotState.empty =>
      { s with state := SlotState.computing, revision := newRev, computeRev := some newRev }
    | SlotState.computing =>
      { s with state := SlotState.computing, revision := newRev, computeRev := some newRev }
    | SlotState.resolved =>
      { s with state := SlotState.computing, revision := newRev, computeRev := some newRev, value := none }
    | SlotState.error =>
      s
  | SlotEvent.retry =>
    match s.state with
    | SlotState.error => { s with state := SlotState.computing, computeRev := some s.revision }
    | _ => s
  | SlotEvent.hardClear =>
    { state := SlotState.empty, revision := s.revision + 1, computeRev := none, value := none }

-- --------------------------------------------------------------- well-formedness

/-- A slot is well-formed when its fields agree with its lifecycle state:
`Computing` carries an in-flight revision and no cached value; `Resolved` carries
a cached value and no in-flight revision; `Empty`/`Error` carry neither. -/
def AsyncSlot.WellFormed (s : AsyncSlot) : Prop :=
  match s.state with
  | SlotState.empty =>
    s.computeRev = none ∧ s.value = none
  | SlotState.computing =>
    s.computeRev ≠ none ∧ s.value = none
  | SlotState.resolved =>
    s.computeRev = none ∧ s.value ≠ none
  | SlotState.error =>
    s.computeRev = none ∧ s.value = none

-- --------------------------------------------------------------------- theorems

/-- A stale Ok-completion (revision mismatch) is discarded: the slot is
byte-identical. The pure-machine core of conformance point 2 (`async.md:218`):
"Revision tracking discards every stale completion; a stale value is never
published." -/
theorem stale_completeOk_discarded (s : AsyncSlot) (r : Revision) (v : Value)
    (hstale : some r ≠ s.computeRev) :
    step s (SlotEvent.completeOk r v) = s := by
  cases h : s.state <;> simp only [step, h]
  case computing =>
    split <;> (try rfl)
    next hacc => exact absurd hacc hstale

/-- A stale Err-completion (revision mismatch) is discarded. -/
theorem stale_completeErr_discarded (s : AsyncSlot) (r : Revision)
    (hstale : some r ≠ s.computeRev) :
    step s (SlotEvent.completeErr r) = s := by
  cases h : s.state <;> simp only [step, h]
  case computing =>
    split <;> (try rfl)
    next hacc => exact absurd hacc hstale

/-- A current Ok-completion (revision matches) publishes the value: the slot
transitions to Resolved, caches the value, and clears the in-flight revision.
Requires the slot to be Computing (the only state where a completion is accepted). -/
theorem current_completeOk_publishes (s : AsyncSlot) (r : Revision) (v : Value)
    (hcomp : s.state = SlotState.computing)
    (hcurrent : some r = s.computeRev) :
    (step s (SlotEvent.completeOk r v)).state = SlotState.resolved ∧
    (step s (SlotEvent.completeOk r v)).value = some v ∧
    (step s (SlotEvent.completeOk r v)).computeRev = none := by
  simp only [step, hcomp]
  split
  · simp_all
  · simp_all

/-- A current Err-completion (revision matches) transitions to Error.
Requires the slot to be Computing. -/
theorem current_completeErr_to_error (s : AsyncSlot) (r : Revision)
    (hcomp : s.state = SlotState.computing)
    (hcurrent : some r = s.computeRev) :
    (step s (SlotEvent.completeErr r)).state = SlotState.error ∧
    (step s (SlotEvent.completeErr r)).computeRev = none := by
  simp only [step, hcomp]
  split
  · simp_all
  · simp_all

/-- `step` preserves well-formedness: after any transition the slot's fields
remain consistent with its lifecycle state. -/
theorem step_preserves_wellFormed (s : AsyncSlot) (e : SlotEvent)
    (wf : s.WellFormed) : (step s e).WellFormed := by
  cases e
  all_goals cases h : s.state
  all_goals simp only [step, h]
  all_goals try split
  all_goals simp only [AsyncSlot.WellFormed] at *
  all_goals first | exact wf | simp_all

end LazilyFormal.AsyncSlotState
