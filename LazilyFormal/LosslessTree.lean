/-
! Lossless full-document tree CRDT — render algebra + convergence composition.

The formal counterpart of `lazily-{rs,…}` `lossless_tree_crdt` and
`lazily-spec/lossless-tree-crdt.md`, behind
`lazily-spec/conformance/lossless-tree/`.

The lossless invariant is `render(tree) == source_text`: every rendered byte lives
in a leaf, elements own structure only, and the ops that reshape leaves
(split / merge / edit) preserve the concatenation of the ordered leaf texts. Two
facts are pinned here:

- **Render is a pure, order-preserving concatenation** of the live leaf texts, so
  splitting a leaf into two adjacent pieces, merging two adjacent leaves, or
  editing one leaf leaves the *rendered document* exactly as required (unchanged
  for split/merge; changed only in the edited leaf's own contribution).
- **Convergence is the product** of two already-proven CRDTs: the move-aware child
  order ([`SeqCrdt`](LazilyFormal.SeqCrdt) register semilattice) and the per-leaf
  text ([`TextCrdtSync`](LazilyFormal.TextCrdtSync) status semilattice). Their
  product `merge` is commutative / associative / idempotent, so concurrent
  compatible tree operations converge.

Delta completeness and the non-contiguous-frontier soundness live in the sibling
`LazilyFormal.LosslessTreeSync`.
-/

import LazilyFormal.SeqCrdt
import LazilyFormal.TextCrdtSync

namespace LazilyFormal.LosslessTree

/-! ### Render algebra: the document is the flattened ordered leaf sequence

A leaf owns an exact text span (`List α` of characters/bytes); the live document is
the ordered list of those spans, and `render` is their concatenation. Elements own
no text of their own — only the structure that orders leaves — captured by
`elem_owns_no_text` below. -/

/-- The ordered live-leaf projection of a document: each leaf's exact text span. -/
abbrev Doc (α : Type) := List (List α)

/-- Render the document: concatenate the ordered leaf texts. A pure function of the
ordered leaf sequence, so it is deterministic (`render_congr`). -/
def render (d : Doc α) : List α := d.flatten

/-- **Render determinism.** Render depends only on the ordered leaf sequence, so two
replicas that converge to the same leaf sequence render byte-identically. -/
theorem render_congr {d₁ d₂ : Doc α} (h : d₁ = d₂) : render d₁ = render d₂ := by
  rw [h]

/-- **Split preserves render.** Splitting the leaf `x ++ y` into the two adjacent
leaves `x`, `y` does not change the rendered document. -/
theorem render_split (as bs : Doc α) (x y : List α) :
    render (as ++ (x ++ y) :: bs) = render (as ++ x :: y :: bs) := by
  simp [render, List.flatten_append, List.append_assoc]

/-- **Merge preserves render.** Merging the two adjacent leaves `x`, `y` into `x ++ y`
does not change the rendered document (the converse of `render_split`). -/
theorem render_merge (as bs : Doc α) (x y : List α) :
    render (as ++ x :: y :: bs) = render (as ++ (x ++ y) :: bs) :=
  (render_split as bs x y).symm

/-- **A leaf edit is local.** The rendered document decomposes as
`context-before ++ this-leaf ++ context-after`, so editing one leaf's text changes
only that middle term — the surrounding leaves' rendered contributions
(`as.flatten`, `bs.flatten`) are untouched, whatever the edit. -/
theorem edit_is_local (as bs : Doc α) (x : List α) :
    render (as ++ x :: bs) = as.flatten ++ x ++ bs.flatten := by
  simp [render, List.flatten_append, List.append_assoc]

/-! ### Elements own structure, not text -/

/-- A concrete-syntax tree node: a leaf owning exact text, or an element owning an
ordered list of children (never text of its own). -/
inductive Node (α : Type) where
  | leaf : List α → Node α
  | elem : List (Node α) → Node α

mutual
  /-- The ordered live-leaf projection of a node (its leaf texts in tree order). -/
  def leaves : Node α → Doc α
    | .leaf s => [s]
    | .elem cs => leavesForest cs
  /-- The ordered leaf projection of a forest of sibling nodes. -/
  def leavesForest : List (Node α) → Doc α
    | [] => []
    | c :: rest => leaves c ++ leavesForest rest
end

/-- Render a tree node: render its ordered leaf projection. -/
def renderNode (n : Node α) : List α := render (leaves n)

/-- **Elements own no text.** An element node's render is exactly the concatenation
of its descendants' leaf texts — it contributes nothing of its own. -/
theorem elem_owns_no_text (cs : List (Node α)) :
    renderNode (.elem cs) = render (leavesForest cs) := rfl

/-- A single leaf renders to exactly its own text. -/
theorem leaf_render (s : List α) : renderNode (.leaf s) = s := by
  simp [renderNode, render, leaves]

/-! ### Convergence is the product of two proven CRDTs

The tree CRDT state is a pair: the move-aware child-order registers (`SeqCrdt`) and
the per-leaf character statuses (`TextCrdtSync`). Merging is componentwise, so it
inherits the semilattice laws of each factor. -/

/-- The tree CRDT merge state: child-order registers × per-leaf text statuses. -/
abbrev TreeState := SeqCrdt.State × TextCrdtSync.State

/-- Merge two tree states componentwise: `SeqCrdt` order join on the structure,
`TextCrdtSync` status join on the leaf text. -/
def mergeTree (a b : TreeState) : TreeState :=
  (SeqCrdt.merge a.1 b.1, TextCrdtSync.merge a.2 b.2)

/-- **Tree merge is commutative** — a two-replica exchange converges regardless of
direction. -/
theorem mergeTree_comm (a b : TreeState) : mergeTree a b = mergeTree b a := by
  simp only [mergeTree, SeqCrdt.merge_comm a.1 b.1, TextCrdtSync.merge_comm a.2 b.2]

/-- **Tree merge is associative** — batching/re-ordering deltas converges the same. -/
theorem mergeTree_assoc (a b c : TreeState) :
    mergeTree (mergeTree a b) c = mergeTree a (mergeTree b c) := by
  simp only [mergeTree, SeqCrdt.merge_assoc, TextCrdtSync.merge_assoc]

/-- **Tree merge is idempotent** — re-applying a known state/delta is a no-op. -/
theorem mergeTree_idem (a : TreeState) : mergeTree a a = a := by
  simp only [mergeTree, SeqCrdt.merge_idem, TextCrdtSync.merge_idem]

end LazilyFormal.LosslessTree
