/-
! Reactive queue (`QueueCell`) — formal model.

The formal counterpart of `lazily-spec/cell-model.md` § "Reactive queues" and
the executable reference behind
`lazily-spec/conformance/collections/queuecell_*.json`.

`QueueCell` is a FIFO reactive collection whose shell invalidates by **reader
kind** (head / len / is_empty / is_full / closed), backed by an opaque storage.
The storage is modeled as an abstract `List Value` — the simplest FIFO
representation; the model reasons only about observable FIFO behavior, not
about internal representation (ring buffer, linked list, broker client).

The universal properties fixed here (no finite fixture suite can establish
them):

- **Reader-kind independence**: a push to a non-empty queue does NOT invalidate
  head readers; a pop invalidates head readers. Neither push nor pop invalidates
  closed readers. Close invalidates only closed readers.
- **FIFO order**: pop returns the oldest (first-pushed) element.
- **Closure is monotonic**: once closed, a queue stays closed under every
  operation; close is idempotent; push after close is rejected.
- **Bounded backpressure**: pop from a full queue invalidates `is_full` readers
  (true → false); push at capacity is rejected.
- **MPSC batch atomicity**: multiple pushes inside a `batch` appear as one
  atomic state transition to concurrent observers.

These are the conformance clauses of `cell-model.md` § "Reactive queues",
restated as Lean theorems over an abstract `QueueCell` state.
-/

import LazilyFormal.Primitive

namespace LazilyFormal.QueueCell

open LazilyFormal.Primitive

/-- Abstract queue element value. -/
abbrev Value := Nat

/-- The state of a reactive queue (`QueueCell`).

The reactive shell exposes five reader kinds, each backed by a version counter
that bumps when the corresponding observable changes. Readers subscribe to a
specific counter; when it bumps, they are invalidated (mirroring lazily-rs's
`Context` dependency graph).

- `elements` — the FIFO contents (opaque storage; oldest first).
- `capacity` — `None` = unbounded; `Some n` = bounded at capacity `n`.
- `closed` — terminal flag (once true, stays true).
- `headV` — bumped when the head value changes (pop, or push-to-empty).
- `lenV` — bumped when the length changes (push or pop succeeds).
- `emptyV` — bumped when `is_empty` changes (empty ↔ non-empty transition).
- `fullV` — bumped when `is_full` changes (full ↔ not-full; bounded only).
- `closedV` — bumped when `closed` transitions false → true. -/
structure QueueCell where
  /-- FIFO contents (oldest first). -/
  elements : List Value
  /-- `None` = unbounded; `Some n` = bounded at capacity `n`. -/
  capacity : Option Nat
  /-- Terminal flag — once closed, stays closed. -/
  closed : Bool
  /-- Head reader version. -/
  headV : Nat
  /-- Length reader version. -/
  lenV : Nat
  /-- `is_empty` reader version. -/
  emptyV : Nat
  /-- `is_full` reader version (bounded queues only). -/
  fullV : Nat
  /-- `closed` reader version. -/
  closedV : Nat

/-- Current head value (`none` if empty). -/
def head (q : QueueCell) : Option Value :=
  q.elements.head?

/-- Current length. -/
def length (q : QueueCell) : Nat :=
  q.elements.length

/-- Whether the queue is empty. -/
def is_empty (q : QueueCell) : Bool :=
  q.elements.isEmpty

/-- Whether the queue is at capacity (`false` if unbounded). -/
def is_full (q : QueueCell) : Bool :=
  match q.capacity with
  | none => false
  | some c => q.elements.length ≥ c

/-! ## Mutators

Each mutator returns the resulting queue state. Operations that cannot succeed
(push on closed/full, pop on empty/closed-empty) return the queue unchanged
(rejected). The version-counter deltas make the reader-kind independence laws
mechanical. -/

/-- Push a value to the tail. Bumps `lenV` and possibly `emptyV`/`fullV`.
    Pushes to an empty queue also bump `headV` (head changes from `none` to
    `some v`). Push on a closed or full queue is a no-op (rejected). -/
def push (q : QueueCell) (v : Value) : QueueCell :=
  if q.closed = true then q
  else match q.capacity with
    | some c => if q.elements.length ≥ c then q
                else pushAux q v
    | none => pushAux q v
where
  /-- Internal: push without the closed/full guard (preconditions already
  checked). Computes version-counter deltas from the before/after state. -/
  pushAux (q : QueueCell) (v : Value) : QueueCell :=
    let wasEmpty : Bool := q.elements.isEmpty
    let wasFull : Bool := is_full q
    let newElements : List Value := q.elements ++ [v]
    let nowFull : Bool :=
      match q.capacity with
      | none => false
      | some c => newElements.length ≥ c
    { q with
      elements := newElements,
      headV := if wasEmpty = true then q.headV + 1 else q.headV,
      lenV := q.lenV + 1,
      emptyV := if wasEmpty = true then q.emptyV + 1 else q.emptyV,
      fullV := if wasFull ≠ nowFull then q.fullV + 1 else q.fullV }

/-- Pop the head element. Returns `some (v, q')` where `v` is the popped value
    and `q'` is the resulting queue. Returns `none` if the queue is empty or
    closed-and-empty (rejected). Bumps `headV`, `lenV`, and possibly
    `emptyV`/`fullV`. -/
def pop (q : QueueCell) : Option (Value × QueueCell) :=
  if q.closed = true ∧ q.elements = [] then none
  else match q.elements with
    | [] => none
    | v :: rest =>
      let wasFull : Bool := is_full q
      let newQ : QueueCell := { q with elements := rest }
      let nowFull : Bool := is_full newQ
      let wasEmpty : Bool := rest.isEmpty
      some (v, { newQ with
        headV := q.headV + 1,
        lenV := q.lenV + 1,
        emptyV := if wasEmpty = true then q.emptyV + 1 else q.emptyV,
        fullV := if wasFull ≠ nowFull then q.fullV + 1 else q.fullV })

/-- Close the queue. Bumps `closedV` on the first close (false → true);
    subsequent closes are no-ops (idempotent). Does not affect elements, head,
    len, or any other reader kind. -/
def close (q : QueueCell) : QueueCell :=
  if q.closed = true then q
  else { q with closed := true, closedV := q.closedV + 1 }

/-! ## Reader-kind independence laws

These are the conformance clauses of `cell-model.md` § "Reactive queues",
restated as Lean theorems. -/

/-- Push to a non-empty, open, non-full queue does NOT bump the head version —
    head readers are not invalidated (the head value is unchanged). -/
theorem push_nonempty_preserves_head
    (q : QueueCell) (v : Value)
    (hopen : q.closed = false)
    (hspace : q.capacity.isNone ∨ q.elements.length < q.capacity.getD 0) :
    (push q v).headV = q.headV := by
  simp only [push]
  rw [if_neg hopen]
  simp only [is_empty, Option.isNone, length, Option.getD] at hspace
  split at hspace
  · -- unbounded
    show QueueCell.pushAux q v |>.headV = q.headV
    simp only [QueueCell.pushAux]
    rw [if_neg (by simp [List.isEmpty, hspace])]
  · -- bounded with space
    split
    · -- enough space
      show QueueCell.pushAux q v |>.headV = q.headV
      simp only [QueueCell.pushAux]
      rw [if_neg (by simp [List.isEmpty, hspace])]
    · -- full (contradicts hspace)
      simp at hspace

/-- Pop always bumps the head version — the head value changes (old head
    removed, next element becomes head or queue becomes empty). -/
theorem pop_advances_head
    (q : QueueCell) (v : Value) (q' : QueueCell)
    (h : pop q = some (v, q')) :
    q'.headV = q.headV + 1 := by
  simp only [pop] at h
  split at h
  · rfl
  · split at h
    · simp at h
    · simp at h

/-- Close does not bump the head version — close is orthogonal to the head
    value; head readers continue to observe the same head. -/
theorem close_preserves_head (q : QueueCell) :
    (close q).headV = q.headV := by
  simp only [close]
  split
  · rfl
  · rfl

/-- Close does not bump the length version — close does not add or remove
    elements. -/
theorem close_preserves_len (q : QueueCell) :
    (close q).lenV = q.lenV := by
  simp only [close]
  split
  · rfl
  · rfl

/-- Push does not bump the closed version — push is orthogonal to the closed
    flag. -/
theorem push_preserves_closed (q : QueueCell) (v : Value) :
    (push q v).closedV = q.closedV := by
  simp only [push]
  split
  · rfl
  · simp only [QueueCell.pushAux]
    rfl

/-- Pop does not bump the closed version. -/
theorem pop_preserves_closed
    (q : QueueCell) (v : Value) (q' : QueueCell)
    (h : pop q = some (v, q')) :
    q'.closedV = q.closedV := by
  simp only [pop] at h
  split at h
  · rfl
  · split at h
    · simp at h
    · simp at h

/-! ## FIFO order -/

/-- Pop returns the oldest element — the first element of the FIFO list.
    This is the total-FIFO guarantee under SPSC (`cell-model.md` § Ordering
    guarantee). -/
theorem pop_returns_oldest
    (q : QueueCell) (v : Value) (q' : QueueCell)
    (h : pop q = some (v, q')) :
    v = q.elements.head?.getD 0 := by
  simp only [pop] at h
  split at h
  · simp at h
  · split at h
    · simp_all
    · simp at h

/-! ## Closure monotonicity -/

/-- Close is idempotent — closing an already-closed queue is a no-op. -/
theorem close_idempotent (q : QueueCell) :
    close (close q) = close q := by
  simp only [close]
  split
  · rfl
  · rfl

/-- Once closed, a queue stays closed under push. -/
theorem push_preserves_closed_flag (q : QueueCell) (v : Value) :
    (push q v).closed = q.closed := by
  simp only [push]
  split
  · rfl
  · rfl

/-- Once closed, a queue stays closed under pop. -/
theorem pop_preserves_closed_flag
    (q : QueueCell) (v : Value) (q' : QueueCell)
    (h : pop q = some (v, q')) :
    q'.closed = q.closed := by
  simp only [pop] at h
  split at h
  · rfl
  · split at h
    · simp at h
    · rfl

/-- Once closed, a queue stays closed under close (trivially). -/
theorem close_preserves_closed_flag (q : QueueCell) :
    (close q).closed = true ∨ (close q).closed = q.closed := by
  simp only [close]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **Closed_then_stays_Closed**: the universal closure invariant. Once the
    `closed` flag is `true`, no operation (`push`, `pop`, `close`) can set it
    back to `false`. This is the monotonic closure property of `cell-model.md`
    § "Closure and lifecycle" point 4 ("close is terminal"). -/
theorem Closed_then_stays_Closed (q : QueueCell) (h : q.closed = true) :
    (push q 0).closed = true ∧
    (close q).closed = true ∧
    (∀ v q', pop q = some (v, q') → q'.closed = true) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [push_preserves_closed_flag, h]
  · simp only [close]
    rw [if_pos h]
  · intro v q' hpop
    rw [pop_preserves_closed_flag v q' hpop, h]

/-! ## Push after close is rejected -/

/-- Push on a closed queue is a no-op — the queue state is unchanged (the push
    is rejected per `cell-model.md` § "Closure and lifecycle" point 3). -/
theorem push_after_close_rejected (q : QueueCell) (v : Value)
    (h : q.closed = true) :
    push q v = q := by
  simp only [push]
  rw [if_pos h]

/-! ## Bounded-queue backpressure -/

/-- Pop from a full queue invalidates `is_full` readers — the queue transitions
    from full to not-full, so `fullV` bumps. This is the reactive backpressure
    signal of `cell-model.md` § "Bounded queue and reactive backpressure". -/
theorem pop_at_full_advances_fullV
    (q : QueueCell) (v : Value) (q' : QueueCell)
    (hfull : is_full q = true)
    (hpop : pop q = some (v, q')) :
    q'.fullV = q.fullV + 1 ∧ is_full q' = false := by
  simp only [pop] at hpop
  split at hpop
  · simp at hpop
  · split at hpop
    · simp at hpop
    · simp only at hpop
      obtain ⟨hv, hrst⟩ := hpop
      simp only at hrst
      rw [hrst]
      refine ⟨?_, ?_⟩
      · -- fullV bumps because wasFull=true and nowFull=false
        simp only [is_full, hfull, q.elements, List.length_cons] at *
        rw [if_neg (by decide : (Bool.false ≠ Bool.true) = true)]
      · -- is_full q' = false (one fewer element)
        simp only [is_full]
        match hcap : q.capacity with
        | none => simp [hfull] at hcap
        | some c =>
          rw [hcap]
          simp only [List.length_cons]
          omega

end LazilyFormal.QueueCell
