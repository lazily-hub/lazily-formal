/-
! Free-text character CRDT — delta sync convergence (#lztextsync).

The formal counterpart of `lazily-{rs,kt,js}` `TextCrdt.{version_vector,
delta_since, apply_delta}` and `lazily-spec/cell-model.md` § "Delta sync".

An element is identified by its `OpId`; once inserted, its character and left
origin are immutable (the same `OpId` is always the same insertion), so the only
per-element field that two replicas can disagree on is the **sticky tombstone**
(the delete op id, `min` on concurrent deletes). The whole replica state is thus a
pointwise join-semilattice over elements, and `merge` / `apply_delta` are its join.

Delta sync is a *lattice-complete restriction* of that join: `delta_since t s`
carries exactly the elements of `t` that `s` does not already subsume, and merging
the delta equals merging the whole of `t`. Bidirectional delta exchange therefore
converges to the same state as a full state merge — the universal property no
finite fixture suite can establish.
-/

namespace LazilyFormal.TextCrdtSync

/-- A globally-unique element / delete id (`(counter, peer)` collapses to a single
totally-ordered `Nat` for the merge algebra). -/
abbrev OpId := Nat

/-- The mergeable status of one element id:
- `none` — not inserted on this replica;
- `some none` — inserted and live;
- `some (some d)` — inserted and tombstoned by delete op `d`. -/
abbrev ElemStatus := Option (Option OpId)

/-- A whole replica state: each element id ↦ its status. -/
abbrev State := OpId → ElemStatus

/-- Sticky-min tombstone join: a delete on either side wins; concurrent deletes
converge to the smaller delete id (order-independent). -/
def joinDel : Option OpId → Option OpId → Option OpId
  | none,   d      => d
  | some a, none   => some a
  | some a, some b => some (min a b)

/-- Join of two element statuses: present wins over absent; two present elements
combine their tombstones. -/
def joinStatus : ElemStatus → ElemStatus → ElemStatus
  | none,   y      => y
  | some a, none   => some a
  | some a, some b => some (joinDel a b)

/-- Replica merge = pointwise status join. Models both `TextCrdt.merge` and
`TextCrdt.apply_delta` (a delta is just another `State`). -/
def merge (s t : State) : State := fun id => joinStatus (s id) (t id)

/-! ### The element-status join is a semilattice -/

theorem joinDel_comm (a b : Option OpId) : joinDel a b = joinDel b a := by
  cases a <;> cases b <;> simp [joinDel, Nat.min_comm]

theorem joinDel_assoc (a b c : Option OpId) :
    joinDel (joinDel a b) c = joinDel a (joinDel b c) := by
  cases a <;> cases b <;> cases c <;> simp [joinDel, Nat.min_assoc]

theorem joinDel_idem (a : Option OpId) : joinDel a a = a := by
  cases a <;> simp [joinDel]

theorem joinStatus_comm (x y : ElemStatus) : joinStatus x y = joinStatus y x := by
  cases x <;> cases y <;> simp [joinStatus, joinDel_comm]

theorem joinStatus_assoc (x y z : ElemStatus) :
    joinStatus (joinStatus x y) z = joinStatus x (joinStatus y z) := by
  cases x <;> cases y <;> cases z <;> simp [joinStatus, joinDel_assoc]

theorem joinStatus_idem (x : ElemStatus) : joinStatus x x = x := by
  cases x <;> simp [joinStatus, joinDel_idem]

/-- Joining an absent contribution is a no-op. -/
theorem joinStatus_none (x : ElemStatus) : joinStatus x none = x := by
  cases x <;> rfl

/-! ### `merge` inherits the semilattice laws (state convergence) -/

/-- Merge is commutative: order of a two-replica exchange does not matter. -/
theorem merge_comm (s t : State) : merge s t = merge t s := by
  funext id; simp [merge, joinStatus_comm]

/-- Merge is associative: batching / re-ordering deltas converges the same way. -/
theorem merge_assoc (s t u : State) :
    merge (merge s t) u = merge s (merge t u) := by
  funext id; simp [merge, joinStatus_assoc]

/-- Merge is idempotent: re-applying a known state / delta is a no-op. -/
theorem merge_idem (s : State) : merge s s = s := by
  funext id; simp [merge, joinStatus_idem]

/-! ### Delta sync is lattice-complete -/

/-- `s` already subsumes `t`'s contribution at `id` iff joining `t`'s element in
changes nothing. -/
def subsumes (s t : State) (id : OpId) : Prop := joinStatus (s id) (t id) = s id

/-- The delta `t` owes a partner whose state is `s`: exactly the elements `s` does
not already subsume. Models `delta_since` keyed off the partner's frontier. -/
noncomputable def deltaSince (t s : State) : State :=
  fun id => if joinStatus (s id) (t id) = s id then none else t id

/-- **Delta completeness.** Merging only the delta `deltaSince t s` into `s` yields
exactly the full merge `merge s t`: the omitted elements are precisely those `s`
already subsumes, so dropping them is invisible under the (idempotent) join. -/
theorem merge_deltaSince (s t : State) :
    merge s (deltaSince t s) = merge s t := by
  funext id
  simp only [merge, deltaSince]
  by_cases h : joinStatus (s id) (t id) = s id
  · rw [if_pos h, joinStatus_none, h]
  · rw [if_neg h]

/-- **Bidirectional delta-sync convergence.** After each replica applies the delta
the other owes it, both replicas equal the full state merge — i.e. they converge,
while shipping only deltas, never a whole snapshot. -/
theorem delta_sync_converges (s t : State) :
    merge s (deltaSince t s) = merge t (deltaSince s t) := by
  rw [merge_deltaSince, merge_deltaSince, merge_comm]

end LazilyFormal.TextCrdtSync
