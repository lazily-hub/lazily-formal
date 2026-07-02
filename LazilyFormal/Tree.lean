/-
! Ordered keyed reactive tree — formal model.

The formal counterpart of `lazily-rs/src/cell_tree.rs` (`CellTree<Id, V>`) and
`lazily-spec/cell-model.md` § "Ordered keyed tree". Each node is
`(stable id, value cell, ordered keyed child collection)`; the model fixes the
two independence laws no finite fixture suite can establish:

- **Per-node value reactivity**: editing one node's value invalidates only that
  node's readers — never a sibling, a child, or an ancestor.
- **Per-level membership/order reactivity**: a sibling subtree (or descendant)
  change MUST NOT invalidate an unrelated level's child readers. Each node
  carries its own independent membership/order signals.
- **Atomic move preserves identity**: a child reorder keeps the child's cell
  identity, value, dependents, and lineage (`#lzcellmove`), bumping only the
  parent's order signal once.

The tree is still a **composition of cells** — not a new cell kind — so the
per-cell merge model of `Collection` and `Reactive` applies node-by-node.
-/

import LazilyFormal.Primitive

namespace LazilyFormal.Tree

open LazilyFormal.Primitive

/-- Abstract stable node identifier (survives reorder and value edits). -/
abbrev NodeId := Nat

/-- Abstract node value. -/
abbrev NodeValue := Nat

/-- One tree node: a value cell plus an ordered keyed child collection carrying
    its own independent per-level membership and order signals (mirroring
    `lazily-rs`'s per-node `CellMap`). -/
structure TreeNode where
  value : NodeValue
  /-- Ordered child ids. -/
  children : List NodeId
  /-- Per-level set-membership signal (bumps on add/remove only). -/
  membershipV : Nat
  /-- Per-level order signal (bumps on add/remove **and** move). -/
  orderV : Nat

/-- A reactive tree: nodes keyed by id (`none` for a non-existent / pruned
    node). Each node's per-level reactivity is independent of every other
    node's. -/
structure Tree where
  node : NodeId → Option TreeNode

/-- Update node `n`'s record to `t` (no-op if `n` is absent). -/
def setNode (tr : Tree) (n : NodeId) (t : TreeNode) : Tree :=
  { tr with node := fun m => if m = n then some t else tr.node m }

/-- Update a field of node `n` via `f` (no-op if `n` is absent). -/
def updateNode (tr : Tree) (n : NodeId) (f : TreeNode → TreeNode) : Tree :=
  match tr.node n with
  | some t => setNode tr n (f t)
  | none => tr

/-- Extract the value cell of node `m` (for clean statement of the value-
    preservation laws). -/
def nodeValue? (tr : Tree) (m : NodeId) : Option NodeValue :=
  match tr.node m with | some t => some t.value | none => none

/-- Extract the per-level order signal of node `m`. -/
def nodeOrderV? (tr : Tree) (m : NodeId) : Option Nat :=
  match tr.node m with | some t => some t.orderV | none => none

/-- Extract the per-level membership signal of node `m`. -/
def nodeMembershipV? (tr : Tree) (m : NodeId) : Option Nat :=
  match tr.node m with | some t => some t.membershipV | none => none

/-! ## Mutators

Each mutator returns the resulting tree. The field-update shape makes the
independence laws mechanical: value edits touch only `.value`; child insertions
bump the parent's `.membershipV` and `.orderV`; moves bump only `.orderV`. -/

/-- Edit node `n`'s value, leaving its children and per-level signals — and
    every other node — untouched. -/
def setNodeValue (tr : Tree) (n : NodeId) (v : NodeValue) : Tree :=
  updateNode tr n (fun t => { t with value := v })

/-- Insert `child` as a new member of `parent`'s child collection. Bumps
    `parent`'s membership **and** order signal; leaves every other node (and
    `parent`'s own value) untouched. -/
def insertChild (tr : Tree) (parent child : NodeId) : Tree :=
  match tr.node parent with
  | some t =>
    match t.children.contains child with
    | true => tr
    | false => setNode tr parent
        { t with children := t.children ++ [child],
                 membershipV := t.membershipV + 1, orderV := t.orderV + 1 }
  | none => tr

/-- A pure reorder within `parent`: move `child` to position `i`. Bumps
    **only** `parent`'s order signal; membership, every value cell, and every
    other node are untouched. The child keeps its identity (not remove +
    re-mint). -/
def moveChild (tr : Tree) (parent child : NodeId) (i : Nat) : Tree :=
  match tr.node parent with
  | some t =>
    match t.children.contains child with
    | true => setNode tr parent
        { t with children := (t.children.filter (fun c => c ≠ child)).insertIdx
                   (min i t.children.length - 1) child,
                 orderV := t.orderV + 1 }
    | false => tr
  | none => tr

/-! ## Per-node value reactivity

Editing one node's value cannot disturb any other node, nor the edited node's
own child collection / per-level signals. -/

/-- `setNode` at `n` leaves a different node `m ≠ n` untouched. -/
theorem setNode_ne {tr : Tree} {n : NodeId} (t : TreeNode) {m : NodeId}
    (hne : m ≠ n) : (setNode tr n t).node m = tr.node m := by
  simp only [setNode]
  by_cases h : m = n
  case pos => exact absurd h hne
  case neg => rw [if_neg h]

/-- `setNode` at `n` returns the supplied record at `n`. -/
theorem setNode_eq {tr : Tree} {n : NodeId} (t : TreeNode) :
    (setNode tr n t).node n = some t := by simp [setNode]

/-- Editing node `n`'s value leaves every other node's record byte-identical. -/
theorem setNodeValue_preserves_other_nodes
    (tr : Tree) (n : NodeId) (v : NodeValue) (m : NodeId) (hm : m ≠ n) :
    (setNodeValue tr n v).node m = tr.node m := by
  simp only [setNodeValue, updateNode]
  match h : tr.node n with
  | some t => exact setNode_ne _ hm
  | none => rfl

/-- Editing node `n`'s value leaves `n`'s own child collection and per-level
    signals untouched (only `.value` changes). -/
theorem setNodeValue_preserves_node_signals
    (tr : Tree) (n : NodeId) (v : NodeValue) (t : TreeNode)
    (h : tr.node n = some t) :
    nodeMembershipV? (setNodeValue tr n v) n = some t.membershipV ∧
    nodeOrderV? (setNodeValue tr n v) n = some t.orderV := by
  refine ⟨?_, ?_⟩
  · simp only [nodeMembershipV?, setNodeValue, updateNode, h, setNode_eq]
  · simp only [nodeOrderV?, setNodeValue, updateNode, h, setNode_eq]

/-! ## Atomic move — identity preservation

A pure reorder (`moveChild`) changes no value cell, anywhere, and leaves every
node other than the parent byte-identical. The child keeps its cell identity
(not remove + re-mint) and its value. -/

/-- `moveChild` leaves every node **other than `parent`** byte-identical — a
    sibling subtree change does not disturb an unrelated level's readers. -/
theorem moveChild_preserves_non_parent
    (tr : Tree) (parent child : NodeId) (i : Nat) (m : NodeId) (hm : m ≠ parent) :
    (moveChild tr parent child i).node m = tr.node m := by
  simp only [moveChild]
  split
  · -- `tr.node parent = some t`: inner match on `t.children.contains child`.
    split
    · exact setNode_ne _ hm
    · rfl
  · rfl

/-- `moveChild` leaves the parent's own value cell untouched — the universal
    form of "reordering a key MUST keep the entry's same cell handle,
    dependents, and lineage" (`cell-model.md` § Ordered keyed tree, atomic-move
    guarantee): only the child ordering and the per-level order signal change;
    no value cell does. -/
theorem moveChild_preserves_parent_value
    (tr : Tree) (parent child : NodeId) (i : Nat) (t : TreeNode)
    (h : tr.node parent = some t) (hmem : t.children.contains child = true) :
    nodeValue? (moveChild tr parent child i) parent = some t.value := by
  simp only [nodeValue?, moveChild, h, hmem, setNode_eq]

/-- `moveChild` advances `parent`'s per-level order signal by exactly one and
    leaves its membership signal unchanged — order readers (`child_ids`) are
    invalidated exactly once, `len`/`contains` readers not at all. -/
theorem moveChild_advances_order_signal_only
    (tr : Tree) (parent child : NodeId) (i : Nat) (t : TreeNode)
    (hparent : tr.node parent = some t) (hmem : t.children.contains child = true) :
    nodeOrderV? (moveChild tr parent child i) parent = some (t.orderV + 1) ∧
    nodeMembershipV? (moveChild tr parent child i) parent = some t.membershipV := by
  refine ⟨?_, ?_⟩
  · simp only [nodeOrderV?, moveChild, hparent, hmem, setNode_eq]
  · simp only [nodeMembershipV?, moveChild, hparent, hmem, setNode_eq]

end LazilyFormal.Tree
