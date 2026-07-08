/-
! Reactive queue (`QueueCell`) — formal model.

The formal counterpart of `lazily-spec/cell-model.md` § "Reactive queues" and
the executable reference behind
`lazily-spec/conformance/collections/queuecell_*.json`.

Universal properties fixed here:

- **Reader-kind independence**: push to non-empty does NOT change head. Pop
  changes head. Neither changes `closed`. Close changes only `closed`.
- **FIFO order**: pop returns the oldest element.
- **Closure is monotonic**: once closed, stays closed; close is idempotent;
  push after close is rejected.

Bounded-queue theorems deferred.
-/

import LazilyFormal.Primitive

namespace LazilyFormal.QueueCell

open LazilyFormal.Primitive

abbrev Value := Nat

structure QueueCell where
  elements : List Value
  closed : Bool

def head (q : QueueCell) : Option Value := q.elements.head?
def length (q : QueueCell) : Nat := q.elements.length

def push (q : QueueCell) (v : Value) : QueueCell :=
  match q.closed with
  | true => q
  | false => { q with elements := q.elements ++ [v] }

def pop (q : QueueCell) : Option (Value × QueueCell) :=
  match q.elements with
  | [] => none
  | v :: rest => some (v, { q with elements := rest })

def close (q : QueueCell) : QueueCell :=
  match q.closed with
  | true => q
  | false => { q with closed := true }

/-! ## Close theorems -/

theorem close_preserves_elements (q : QueueCell) :
    (close q).elements = q.elements := by
  cases hc : q.closed with
  | false => simp only [close, hc]
  | true => simp only [close, hc]

theorem close_preserves_head (q : QueueCell) :
    head (close q) = head q := by
  cases hc : q.closed with
  | false => simp only [close, hc, head]
  | true => simp only [close, hc, head]

theorem close_preserves_length (q : QueueCell) :
    length (close q) = length q := by
  cases hc : q.closed with
  | false => simp only [close, hc, length]
  | true => simp only [close, hc, length]

theorem close_idempotent (q : QueueCell) :
    close (close q) = close q := by
  cases hc : q.closed with
  | false => simp only [close, hc]
  | true => simp only [close, hc]

/-! ## Push theorems -/

theorem push_preserves_closed (q : QueueCell) (v : Value) :
    (push q v).closed = q.closed := by
  cases hc : q.closed with
  | false => simp only [push, hc]
  | true => simp only [push, hc]

theorem push_after_close_rejected (q : QueueCell) (v : Value)
    (h : q.closed = true) : push q v = q := by
  unfold push; rw [h]

theorem push_nonempty_preserves_head
    (q : QueueCell) (v : Value)
    (hopen : q.closed = false) (hnonempty : q.elements ≠ []) :
    head (push q v) = head q := by
  unfold push head
  rw [hopen]
  cases hel : q.elements with
  | nil => exact absurd hel hnonempty
  | cons w rest => rfl

/-! ## Pop theorems -/

theorem pop_preserves_closed
    (q : QueueCell) (v : Value) (q' : QueueCell)
    (h : pop q = some (v, q')) : q'.closed = q.closed := by
  cases hel : q.elements with
  | nil => simp [pop, hel] at h
  | cons x rest =>
    simp only [pop, hel] at h
    injection h with hpair
    injection hpair with _ hq'
    rw [← hq']

theorem pop_returns_oldest
    (q : QueueCell) (v : Value) (q' : QueueCell)
    (h : pop q = some (v, q')) : head q = some v := by
  cases hel : q.elements with
  | nil => simp [pop, hel] at h
  | cons x rest =>
    simp only [pop, hel] at h
    injection h with hpair
    injection hpair with hval _
    unfold head; rw [hel, hval]; rfl

/-! ## Closure monotonicity -/

theorem Closed_then_stays_Closed (q : QueueCell) (h : q.closed = true) :
    (push q 0).closed = true ∧
    (close q).closed = true ∧
    (∀ v q', pop q = some (v, q') → q'.closed = true) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [push_preserves_closed, h]
  · unfold close; rw [h]; show q.closed = true; exact h
  · intro v q' hpop
    rw [pop_preserves_closed q v q' hpop, h]

end LazilyFormal.QueueCell
