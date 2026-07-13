import LazilyFormal.TextCrdtSync

/-!
`CrdtTree` contract (`#lzcrdttree`): an identity-preserving document state join,
delta synchronization, and empty-frontier snapshot are one semilattice.
-/

namespace LazilyFormal.CrdtTree

open LazilyFormal.TextCrdtSync

abbrev State := TextCrdtSync.State

def merge : State → State → State := TextCrdtSync.merge

theorem merge_comm (a b : State) : merge a b = merge b a :=
  TextCrdtSync.merge_comm a b

theorem merge_assoc (a b c : State) : merge (merge a b) c = merge a (merge b c) :=
  TextCrdtSync.merge_assoc a b c

theorem merge_idem (a : State) : merge a a = a :=
  TextCrdtSync.merge_idem a

/-- The empty document frontier/state. -/
def empty : State := fun _ => none

theorem merge_empty_left (state : State) : merge empty state = state := by
  funext id
  simp [merge, empty, TextCrdtSync.merge, TextCrdtSync.joinStatus]

/-- A full snapshot is the delta since an empty frontier. -/
noncomputable def snapshot (state : State) : State :=
  TextCrdtSync.deltaSince state empty

/-- Applying the empty-frontier snapshot reconstructs the identity-bearing state. -/
theorem snapshot_round_trip (state : State) : merge empty (snapshot state) = state := by
  unfold merge snapshot
  rw [TextCrdtSync.merge_deltaSince]
  exact merge_empty_left state

/-- Incremental exchange has the same result as a whole-state merge. -/
theorem delta_complete (current remote : State) :
    merge current (TextCrdtSync.deltaSince remote current) = merge current remote :=
  TextCrdtSync.merge_deltaSince current remote

end LazilyFormal.CrdtTree
