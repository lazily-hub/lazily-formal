/-
! Memoized semantic tree — incremental, glitch-free derivation.

The formal counterpart of `lazily-{rs,kt,js}` `SemTree` and
`lazily-spec/cell-model.md` § "Memoized semantic tree", behind
`lazily-spec/conformance/collections/semtree_incremental.json`.

A semantic tree layers one **memoized computed** per node over a syntactic tree: the
node's derived value folds `(weight of its own value, derived values of its children)`.
The fixture pins two incremental-derivation invariants (plus a removal case):

1. **Sibling subtrees stay cached.** `derived` of a node is a pure function of that node's
   subtree, so an edit that misses a subtree leaves the subtree literally unchanged
   (`setVal_miss`) — its memo slot never recomputes. Only the edited node's *ancestor
   chain* re-folds.
2. **Memo-equality guard.** If an edit leaves a subtree's *folded result* unchanged, the
   parent's fold — and hence every ancestor's — is unchanged
   (`parent_memo_guard`, `derivedForest_replace`), so no downstream consumer re-runs. This
   is the tree-level form of `Reactive.recomputeComputed_equal_preserves_dependents`.

Removal updates the derivation by exactly the dropped subtree's folded value
(`derivedForest_remove`) — cost proportional to the diff, not the document.

The fold is parameterised by a per-value weight `w : Nat → Nat` so one model covers both
`sum` (`w = id`) and `count_positive` (`w v = if v > 0 then 1 else 0`, the guard case).
-/

namespace LazilyFormal.SemTree

/-- A syntactic-tree node: a stable `id`, an input `value`, and ordered `children`. -/
inductive Tree where
  | node (id : Nat) (value : Nat) (children : List Tree)

/- The memoized derivation: a node folds its own weighted value with its children's
derived values. Mutually recursive with the forest fold over the child list. -/
mutual
  def derived (w : Nat → Nat) : Tree → Nat
    | .node _ v ch => w v + derivedForest w ch
  def derivedForest (w : Nat → Nat) : List Tree → Nat
    | [] => 0
    | t :: ts => derived w t + derivedForest w ts
end

/-- `sum` fold: `w = id`. -/
abbrev sumTree (t : Tree) : Nat := derived (fun v => v) t

/-- `count_positive` fold weight: a node contributes `1` iff its value is positive. -/
def countPos (v : Nat) : Nat := if v > 0 then 1 else 0

/-! ### Grounding in the fixture

The scenario-1 tree folds to `root = 133`, and the guard scenario's edit `7 → 9` leaves
`countPos` fixed at `1`. -/

/-- Scenario-1 tree: `root(0)[ a(1)[a1(10), a2(20)], b(2)[b1(100)] ]`. -/
def fixtureTree : Tree :=
  .node 0 0 [
    .node 1 1 [.node 10 10 [], .node 20 20 []],
    .node 2 2 [.node 100 100 []]
  ]

example : sumTree fixtureTree = 133 := rfl

/-- Memo-equality of the guard scenario: `countPos 7 = countPos 9`, so a `7 → 9` edit
does not change the folded count. -/
example : countPos 7 = countPos 9 := rfl

/-! ### Memo-equality guard: equal folded result ⇒ ancestors unchanged -/

/-- Replacing one child subtree by another with the **same** derived value leaves the whole
forest fold unchanged — the glitch-free memo-equality propagation. -/
theorem derivedForest_replace (w : Nat → Nat) (l₁ l₂ : List Tree) (t t' : Tree)
    (h : derived w t = derived w t') :
    derivedForest w (l₁ ++ t :: l₂) = derivedForest w (l₁ ++ t' :: l₂) := by
  induction l₁ with
  | nil => simp only [List.nil_append, derivedForest, h]
  | cons hd tl ih => simp only [List.cons_append, derivedForest, ih]

/-- **Memo guard.** If an edit changes a child subtree but keeps its folded result equal,
the parent node's derived value is unchanged — so no ancestor re-runs. -/
theorem parent_memo_guard (w : Nat → Nat) (id v : Nat) (l₁ l₂ : List Tree) (t t' : Tree)
    (h : derived w t = derived w t') :
    derived w (.node id v (l₁ ++ t :: l₂)) = derived w (.node id v (l₁ ++ t' :: l₂)) := by
  simp only [derived, derivedForest_replace w l₁ l₂ t t' h]

/-! ### Sibling subtrees stay cached: an edit that misses a subtree changes nothing -/

/- Does `id` occur anywhere in the tree / forest? -/
mutual
  def mem (id : Nat) : Tree → Bool
    | .node i _ ch => (i == id) || memForest id ch
  def memForest (id : Nat) : List Tree → Bool
    | [] => false
    | t :: ts => mem id t || memForest id ts
end

/- Set the `value` of the node named `id`, recursing structurally. -/
mutual
  def setVal (id nv : Nat) : Tree → Tree
    | .node i v ch =>
      .node i (if i == id then nv else v) (setValForest id nv ch)
  def setValForest (id nv : Nat) : List Tree → List Tree
    | [] => []
    | t :: ts => setVal id nv t :: setValForest id nv ts
end

/- **Sibling cache.** An edit whose target `id` is absent from a subtree leaves that
subtree literally unchanged — its memo slot is never recomputed. Proved mutually with the
forest version by structural recursion. -/
mutual
  theorem setVal_miss (id nv : Nat) :
      (t : Tree) → mem id t = false → setVal id nv t = t
    | .node i v ch, h => by
      simp only [mem, Bool.or_eq_false_iff] at h
      obtain ⟨hi, hch⟩ := h
      simp only [setVal, hi, Bool.false_eq_true, if_false,
        setValForest_miss id nv ch hch]
  theorem setValForest_miss (id nv : Nat) :
      (l : List Tree) → memForest id l = false → setValForest id nv l = l
    | [], _ => rfl
    | t :: ts, h => by
      simp only [memForest, Bool.or_eq_false_iff] at h
      obtain ⟨h1, h2⟩ := h
      simp only [setValForest, setVal_miss id nv t h1, setValForest_miss id nv ts h2]
end

/-- The derived value of a subtree missing the edit target is unchanged (memo hit). -/
theorem derived_setVal_miss (w : Nat → Nat) (id nv : Nat) (t : Tree)
    (h : mem id t = false) : derived w (setVal id nv t) = derived w t := by
  rw [setVal_miss id nv t h]

/-! ### Removal updates the derivation by the dropped subtree's fold -/

/-- Removing one child from a forest drops exactly that child's folded value. -/
theorem derivedForest_remove (w : Nat → Nat) (l₁ l₂ : List Tree) (t : Tree) :
    derivedForest w (l₁ ++ t :: l₂) = derivedForest w (l₁ ++ l₂) + derived w t := by
  induction l₁ with
  | nil => simp only [List.nil_append, derivedForest]; omega
  | cons hd tl ih => simp only [List.cons_append, derivedForest, ih]; omega

/-- **Removal updates derivation.** Dropping child `t` from node `id` reduces its derived
value by exactly `derived w t`. -/
theorem remove_child_updates (w : Nat → Nat) (id v : Nat) (l₁ l₂ : List Tree) (t : Tree) :
    derived w (.node id v (l₁ ++ t :: l₂))
      = derived w (.node id v (l₁ ++ l₂)) + derived w t := by
  simp only [derived, derivedForest_remove w l₁ l₂ t]; omega

end LazilyFormal.SemTree
