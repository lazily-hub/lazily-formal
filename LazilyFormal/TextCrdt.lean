/-
! Free-text character CRDT — Fugue/RGA base convergence + order determinism.

The formal counterpart of `lazily-{rs,kt,js}` `TextCrdt` and
`lazily-spec/cell-model.md` § "Free-text CRDT + re-parse" — the *base* model behind
`lazily-spec/conformance/collections/textcrdt_convergence.json`. `TextCrdtSync` proves
the delta-sync lattice (`version_vector` / `delta_since` / `apply_delta`); this module
proves the two properties the base fixture pins that the lattice alone does not:

1. **Order is a pure function of the live element set.** Each character is an element
   with a globally-unique `OpId` and an immutable left `origin`; the sequence is a
   pre-order DFS of the origin tree with siblings sorted **descending** by `OpId`. Since
   `payloadOf` is fixed globally and the order is computed from the merged live set, two
   replicas that merge to the same set render byte-identical text — determinism by
   construction.
2. **Concurrent same-point inserts both survive, ordered by a deterministic tiebreak.**
   The sibling comparator (`>` on `OpId`) is a strict total order, so two inserts sharing
   a left origin never compare equal — both are kept and their relative order is fixed by
   `OpId` (the peer tiebreak is folded into the id), independent of merge order.

Presence + sticky tombstone form the same pointwise join-semilattice as `TextCrdtSync`;
`merge` here carries it so a delete is sticky and merge is commutative / associative /
idempotent (state convergence). What is *new* is that the order layer sits on top of that
set and inherits its convergence.
-/

namespace LazilyFormal.TextCrdt

/-- A globally-unique element / delete id. `(counter, peer)` collapses to a single
totally-ordered `Nat`, so the peer tiebreak is already inside the id. -/
abbrev OpId := Nat

/-- The immutable payload an `OpId` names: its character and its left origin (`none` for
the sequence head). Fixed globally — the same id is always the same insertion — so two
replicas can never disagree about it. -/
structure Payload where
  ch : Nat
  origin : Option OpId

/-- The mergeable per-id status: `none` = not inserted here; `some none` = live;
`some (some d)` = tombstoned by delete op `d`. Payload is *not* stored here (it is a pure
function of the id) so replicas cannot diverge on it. -/
abbrev Status := Option (Option OpId)

/-- A whole replica state: each element id ↦ its status. -/
abbrev State := OpId → Status

/-- Sticky-min tombstone join: a delete on either side wins; concurrent deletes converge
to the smaller delete id (order-independent). -/
def joinDel : Option OpId → Option OpId → Option OpId
  | none,   d      => d
  | some a, none   => some a
  | some a, some b => some (min a b)

/-- Join of two element statuses: present wins over absent; two present elements combine
their tombstones. -/
def joinStatus : Status → Status → Status
  | none,   y      => y
  | some a, none   => some a
  | some a, some b => some (joinDel a b)

/-- Replica merge = pointwise status join. -/
def merge (s t : State) : State := fun id => joinStatus (s id) (t id)

/-! ### State convergence: the presence/tombstone lattice -/

theorem joinDel_comm (a b : Option OpId) : joinDel a b = joinDel b a := by
  cases a <;> cases b <;> simp [joinDel, Nat.min_comm]

theorem joinDel_assoc (a b c : Option OpId) :
    joinDel (joinDel a b) c = joinDel a (joinDel b c) := by
  cases a <;> cases b <;> cases c <;> simp [joinDel, Nat.min_assoc]

theorem joinDel_idem (a : Option OpId) : joinDel a a = a := by
  cases a <;> simp [joinDel]

theorem joinStatus_comm (x y : Status) : joinStatus x y = joinStatus y x := by
  cases x <;> cases y <;> simp [joinStatus, joinDel_comm]

theorem joinStatus_assoc (x y z : Status) :
    joinStatus (joinStatus x y) z = joinStatus x (joinStatus y z) := by
  cases x <;> cases y <;> cases z <;> simp [joinStatus, joinDel_assoc]

theorem joinStatus_idem (x : Status) : joinStatus x x = x := by
  cases x <;> simp [joinStatus, joinDel_idem]

/-- Merge is commutative: a two-replica exchange converges regardless of direction. -/
theorem merge_comm (s t : State) : merge s t = merge t s := by
  funext id; simp [merge, joinStatus_comm]

/-- Merge is associative. -/
theorem merge_assoc (s t u : State) :
    merge (merge s t) u = merge s (merge t u) := by
  funext id; simp [merge, joinStatus_assoc]

/-- Merge is idempotent: re-applying a known state is a no-op. -/
theorem merge_idem (s : State) : merge s s = s := by
  funext id; simp [merge, joinStatus_idem]

/-! ### Membership: no concurrent insert is lost -/

/-- An id is *present* (inserted, tombstoned or not) on a replica. -/
def present (s : State) (id : OpId) : Prop := s id ≠ none

/-- An id is *live* (present and not tombstoned). -/
def live (s : State) (id : OpId) : Prop := s id = some none

/-- Presence is preserved by merge on each side — both sides of a concurrent same-point
insert survive into the merged state. -/
theorem present_merge_left {s t : State} {id : OpId} (h : present s id) :
    present (merge s t) id := by
  simp only [present, merge] at *
  cases hs : s id with
  | none => exact absurd hs h
  | some a => cases t id <;> simp [joinStatus]

theorem present_merge_right {s t : State} {id : OpId} (h : present t id) :
    present (merge s t) id := by
  rw [merge_comm]; exact present_merge_left h

/-- **Both concurrent inserts survive.** If replica `s` inserted `x` and replica `t`
inserted a distinct `y` at the same left origin, the merged state contains both. -/
theorem concurrent_inserts_both_present {s t : State} {x y : OpId}
    (hx : present s x) (hy : present t y) :
    present (merge s t) x ∧ present (merge s t) y :=
  ⟨present_merge_left hx, present_merge_right hy⟩

/-! ### Order determinism: the sibling comparator is a strict total order

Siblings sharing a left origin are laid out by **descending** `OpId`. `>` on `Nat` is a
strict total order, so two distinct sibling ids always compare — never equal — which fixes
their relative order deterministically (the peer tiebreak lives inside the id). The whole
sequence order is then a pure function of the live set; equal live sets render identical
text, so merged replicas converge on order for free. -/

/-- Sibling precedence: `x` precedes `y` iff it has the larger id (most-recent first). -/
def precedes (x y : OpId) : Prop := x > y

theorem precedes_irrefl (x : OpId) : ¬ precedes x x := by
  simp [precedes]

theorem precedes_trans {x y z : OpId} (hxy : precedes x y) (hyz : precedes y z) :
    precedes x z := Nat.lt_trans hyz hxy

theorem precedes_asymm {x y : OpId} (h : precedes x y) : ¬ precedes y x :=
  Nat.lt_asymm h

/-- **Deterministic tiebreak.** Two distinct siblings always compare one way or the other
— the order never depends on merge order or replica. -/
theorem precedes_total {x y : OpId} (h : x ≠ y) : precedes x y ∨ precedes y x :=
  (Nat.lt_or_gt_of_ne h).symm

/-! ### Text length is a function of the live set -/

/-- Rendered length over a finite id univ = count of live (present, untombstoned)
ids. Being a function of the (converged) state, it too converges. -/
def renderLen (s : State) (univ : List OpId) : Nat :=
  (univ.filter (fun id => decide (s id = some none))).length

/-- A tombstoned element does not contribute to rendered length: deleting `x` (already
present) can only shrink or preserve the count, never render `x`. -/
theorem tombstoned_not_rendered (s : State) (univ : List OpId) (x : OpId)
    (hx : s x = some (some 0)) :
    ¬ (x ∈ univ.filter (fun id => decide (s id = some none))) := by
  simp only [List.mem_filter, decide_eq_true_eq, not_and]
  intro _ hlive
  rw [hx] at hlive
  exact absurd hlive (by simp)

end LazilyFormal.TextCrdt
