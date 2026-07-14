/-
! Stream windowing (`#lzwindow`) — formal model.

The formal counterpart of `lazily-spec/docs/windowing.md`. Window aggregation is
a `MergePolicy` fold; the correctness core is that **regrouping a stream into
windows preserves the fold**. Sequential regrouping is unconditional
(`window_fold_regroup`); computing per-window aggregates independently and
combining them equals the whole-stream fold under an associative merge with
identity (`windowed_merge`) — this is what lets `Sum`/`Max`/`SetUnion` windows
compose for free.
-/

namespace LazilyFormal.Windowing

/-- The window aggregate is the left-fold of its elements under the merge. -/
def aggregate (op : α → α → α) (init : α) (window : List α) : α :=
  window.foldl op init

theorem tumbling_emits_fold (op : α → α → α) (init : α) (w : List α) :
    aggregate op init w = w.foldl op init := rfl

/-- Sequential windowing preserves the fold: folding `xs` then `ys` equals
folding `xs ++ ys` (unconditional). -/
theorem window_fold_regroup (op : α → α → α) (init : α) (xs ys : List α) :
    List.foldl op (List.foldl op init xs) ys = List.foldl op init (xs ++ ys) := by
  rw [List.foldl_append]

/-- Fold homomorphism: folding `ys` from an accumulator equals combining the
accumulator with the fold of `ys` from the identity (associativity + two-sided
identity). -/
theorem foldl_hom (op : α → α → α) (e : α)
    (hassoc : ∀ a b c, op (op a b) c = op a (op b c))
    (hidl : ∀ a, op e a = a) (hidr : ∀ a, op a e = a) :
    ∀ (acc : α) (ys : List α), ys.foldl op acc = op acc (ys.foldl op e) := by
  intro acc ys
  induction ys generalizing acc with
  | nil => simp [List.foldl, hidr]
  | cons y rest ih =>
      simp only [List.foldl]
      rw [ih (op acc y), ih (op e y), hidl, hassoc]

/-- Per-window aggregates combine to the whole-stream aggregate: computing each
window's fold independently and merging equals folding the concatenation. -/
theorem windowed_merge (op : α → α → α) (e : α)
    (hassoc : ∀ a b c, op (op a b) c = op a (op b c))
    (hidl : ∀ a, op e a = a) (hidr : ∀ a, op a e = a) (xs ys : List α) :
    op (xs.foldl op e) (ys.foldl op e) = (xs ++ ys).foldl op e := by
  rw [List.foldl_append, foldl_hom op e hassoc hidl hidr (xs.foldl op e) ys]

end LazilyFormal.Windowing
