/-
! Keyed reconciliation — formal model.

The formal counterpart of `lazily-spec/cell-model.md` § "Keyed reconciliation".
Reconciling two keyed levels (a `prior` and a `target`) by **stable key, not
position**, emits the minimal `{insert, remove, move, update}` op set.

The model fixes the two conformance clauses of `cell-model.md:236-239`:

1. **Move-minimization** — keys already in relative order (the
   longest-increasing-subsequence (LIS) over their prior indices) MUST NOT move;
   only the remainder emit `move`.
2. **Stable-entry value preservation** — a stable entry (unchanged value, in the
   LIS) MUST NOT have its value cell invalidated by a sibling reorder: the
   reconcile emits neither an `update` nor a `move` for it.

Combined with `LazilyFormal.Collection` (`moveKey_preserves_values`,
`setEntryValue_preserves_siblings`), a stable entry's value cell is provably
untouched by the reconcile — the universal form of the conformance fixture
`lazily-spec/conformance/collections/keyed_reconciliation_lis.json`'s
`stable_keys_not_invalidated` expectation.
-/

import LazilyFormal.Primitive

namespace LazilyFormal.Reconciliation

abbrev Key := Nat

abbrev EntryValue := Nat

/-- A keyed level: an insertion-ordered list of keys plus a total value
function. (Values are total for convenience; only keys in `order` are
meaningful. `Nodup order` is assumed where it matters.) -/
structure Level where
  order : List Key
  values : Key → EntryValue

/-- The diff op set emitted by reconciling a prior level to a target level
(`cell-model.md:236`): the minimal `{insert, remove, move, update}` per key. -/
inductive Op where
  /-- A new key present in the target but not the prior: mint its cell. -/
  | insert : Key → EntryValue → Op
  /-- A dropped key present in the prior but not the target: tombstone its cell. -/
  | remove : Key → Op
  /-- A common key whose value changed: write its cell. -/
  | update : Key → EntryValue → Op
  /-- A common key not in the LIS: reposition it (a single move, not remove + insert). -/
  | move   : Key → Op
  deriving Repr

/-! ## The longest increasing subsequence (LIS)

`bestFrom p bound ks` is the longest subsequence of `ks` whose `p`-values are
strictly increasing and all strictly above `bound` (`none` = no lower bound).
`lisBy p ks = bestFrom p none ks` is the LIS the spec refers to: the maximal set
of common keys already in relative prior-index order, which a move-minimized
reconcile therefore leaves untouched. The "include-vs-skip" recursion makes
longest-ness definitional. -/

mutual
  /-- The include-`k` branch of `bestFrom`: `k` prepended to the LIS of `rest`
  above `p k`, when `k` itself clears `bound`; otherwise empty. -/
  def inclBranch (p : Key → Nat) (bound : Option Nat) (k : Key) (rest : List Key) :
      List Key :=
    match bound with
    | some b => if b < p k then k :: bestFrom p (some (p k)) rest else []
    | none => k :: bestFrom p (some (p k)) rest

  /-- The longest strictly-increasing (by `p`) subsequence of `ks` whose values
  all clear `bound`. The longer of the include-`k` and skip-`k` branches wins. -/
  def bestFrom (p : Key → Nat) (bound : Option Nat) : List Key → List Key
    | [] => []
    | k :: rest =>
      if (inclBranch p bound k rest).length ≥ (bestFrom p bound rest).length
      then inclBranch p bound k rest
      else bestFrom p bound rest
end

/-- The longest strictly-increasing (by `p`) subsequence of `ks`. -/
def lisBy (p : Key → Nat) (ks : List Key) : List Key :=
  bestFrom p none ks

/-! ## LIS correctness

`bestFrom` is sound (its result is strictly increasing and clears the bound),
a subsequence of its input, and longest. -/

/-- `l` is strictly increasing by `p`: every earlier key has a strictly smaller
`p`-value than every later key. -/
def StrictlyIncreasingBy (p : Key → Nat) (l : List Key) : Prop :=
  l.Pairwise (fun a b => p a < p b)

/-- Every `p`-value in `l` is strictly above `bound` (`none` = unconstrained). -/
def AllAbove (p : Key → Nat) (bound : Option Nat) (l : List Key) : Prop :=
  match bound with
  | some b => ∀ x ∈ l, b < p x
  | none => True

/-- `bestFrom` produces a strictly-increasing list that clears the bound. -/
theorem bestFrom_inv (p : Key → Nat) (bound : Option Nat) (ks : List Key) :
    StrictlyIncreasingBy p (bestFrom p bound ks) ∧ AllAbove p bound (bestFrom p bound ks) := by
  induction ks generalizing bound with
  | nil =>
    simp only [bestFrom]
    refine ⟨List.Pairwise.nil, ?_⟩
    cases bound with
    | none => trivial
    | some _ => intro _ hk; nomatch hk
  | cons k rest ih =>
    have ihRec := ih (some (p k))   -- invariant for the include branch's recursive call
    have ihSkip := ih bound         -- invariant for the skip branch
    -- Establish the invariant of the include branch `inclBranch p bound k rest`.
    have hIncl : StrictlyIncreasingBy p (inclBranch p bound k rest) ∧
                 AllAbove p bound (inclBranch p bound k rest) := by
      cases bound with
      | none =>
        have h : inclBranch p none k rest = k :: bestFrom p (some (p k)) rest := by
          simp only [inclBranch]
        rw [h]
        refine ⟨List.Pairwise.cons (fun j hj => ihRec.2 j hj) ihRec.1, ?_⟩
        trivial
      | some b =>
        by_cases hb : b < p k
        · have h1 : inclBranch p (some b) k rest = k :: bestFrom p (some (p k)) rest := by
            simp only [inclBranch, hb, if_true]
          rw [h1]
          refine ⟨List.Pairwise.cons (fun j hj => ihRec.2 j hj) ihRec.1, ?_⟩
          rintro j hj
          rcases List.mem_cons.mp hj with rfl | hmem
          · exact hb
          · exact Nat.lt_trans hb (ihRec.2 j hmem)
        · have h0 : inclBranch p (some b) k rest = [] := by
            simp only [inclBranch, hb, if_false]
          rw [h0]
          refine ⟨List.Pairwise.nil, fun _ hk => nomatch hk⟩
    -- `bestFrom` chooses the longer of `inclBranch` (hIncl) and the skip branch (ihSkip).
    simp only [bestFrom]
    split <;> assumption

/-- Every key of `bestFrom`'s result is a key of its input. -/
theorem bestFrom_subset (p : Key → Nat) (bound : Option Nat) (ks : List Key) :
    ∀ a, a ∈ bestFrom p bound ks → a ∈ ks := by
  induction ks generalizing bound with
  | nil => intro _ h; simp only [bestFrom] at h; nomatch h
  | cons k rest ih =>
    intro a h
    simp only [bestFrom] at h
    by_cases hcond : (inclBranch p bound k rest).length ≥ (bestFrom p bound rest).length
    · rw [if_pos hcond] at h
      -- h : a ∈ inclBranch p bound k rest
      cases bound with
      | none =>
        simp only [inclBranch] at h
        rcases List.mem_cons.mp h with rfl | hmem
        · exact List.mem_cons.mpr (Or.inl rfl)
        · exact List.mem_cons.mpr (Or.inr (ih (some (p k)) a hmem))
      | some b =>
        simp only [inclBranch] at h
        by_cases hb : b < p k
        · rw [if_pos hb] at h
          rcases List.mem_cons.mp h with rfl | hmem
          · exact List.mem_cons.mpr (Or.inl rfl)
          · exact List.mem_cons.mpr (Or.inr (ih (some (p k)) a hmem))
        · rw [if_neg hb] at h
          nomatch h
    · rw [if_neg hcond] at h
      exact List.mem_cons.mpr (Or.inr (ih bound a h))

/-- `bestFrom` is longest: any increasing subsequence of `ks` that clears `bound`
is no longer than `bestFrom`'s result. -/
theorem bestFrom_longest (p : Key → Nat) (bound : Option Nat) (ks : List Key) :
    ∀ s, StrictlyIncreasingBy p s → s.Sublist ks → AllAbove p bound s →
      s.length ≤ (bestFrom p bound ks).length := by
  induction ks generalizing bound with
  | nil =>
    intro s _ hs_sub _
    have h0 : s = [] := by cases hs_sub; rfl
    subst h0
    simp only [bestFrom, List.length_nil]
    omega
  | cons k rest ih =>
    intro s hs_inc hs_sub hs_above
    rcases List.sublist_cons_iff.mp hs_sub with hs' | ⟨s', hs_cons, hs'sub⟩
    · -- `s` is a subsequence of `rest` (does not use `k`)
      have hskip : s.length ≤ (bestFrom p bound rest).length :=
        ih bound s hs_inc hs' hs_above
      simp only [bestFrom]
      split
      · omega
      · omega
    · -- `s = k :: s'`, `s'` a subsequence of `rest`
      subst hs_cons
      cases hs_inc with
      | cons hhead htail =>
        have hs'above : AllAbove p (some (p k)) s' := fun j hj => hhead j hj
        have hrec : s'.length ≤ (bestFrom p (some (p k)) rest).length :=
          ih (some (p k)) s' htail hs'sub hs'above
        have hpkClears : inclBranch p bound k rest = k :: bestFrom p (some (p k)) rest := by
          cases bound with
          | none => simp only [inclBranch]
          | some b =>
            have hbpk : b < p k := hs_above k (List.mem_cons.mpr (Or.inl rfl))
            simp only [inclBranch, hbpk, if_true]
        have hinclLen : (inclBranch p bound k rest).length =
            (bestFrom p (some (p k)) rest).length + 1 := by
          rw [hpkClears, List.length_cons]
        have hslen : (k :: s').length = s'.length + 1 := by simp only [List.length_cons]
        simp only [bestFrom]
        split
        · omega
        · omega

/-- `lisBy` produces a strictly-increasing list (the chosen LIS). -/
theorem lisBy_increasing (p : Key → Nat) (ks : List Key) :
    StrictlyIncreasingBy p (lisBy p ks) :=
  (bestFrom_inv p none ks).1

/-- `lisBy` is longest: every increasing subsequence of `ks` is no longer than
`lisBy p ks`. This is the move-*minimized* half of conformance clause 1 — the
non-LIS remainder is as small as possible, so the emitted `move` set is minimal. -/
theorem lisBy_longest (p : Key → Nat) (ks : List Key) (s : List Key)
    (hs_inc : StrictlyIncreasingBy p s) (hs_sub : s.Sublist ks) :
    s.length ≤ (lisBy p ks).length :=
  bestFrom_longest p none ks s hs_inc hs_sub (by trivial)

/-- Every key of `lisBy`'s result is a key of its input. -/
theorem lisBy_subset (p : Key → Nat) (ks : List Key) :
    ∀ a, a ∈ lisBy p ks → a ∈ ks :=
  bestFrom_subset p none ks

/-! ## Reconciliation

Reconciling `prior` to `target` by stable key, emitting the minimal
`{insert, remove, move, update}` op set. Moves are emitted only for the common
keys that are *not* in the LIS; stable (LIS) keys are never moved, and a stable
key with an unchanged value is never updated either — so its value cell is
untouched by the reconcile. -/

/-- Index of `k` in `order` (0-based), or `order.length` if absent. Defined
without depending on `List.indexOf` so the model stays pure-stdlib. -/
def idxIn : List Key → Key → Nat
  | [], _ => 0
  | a :: as, k => if a = k then 0 else idxIn as k + 1

/-- The keys present in both `prior` and `target`, in `target` order. -/
def commonKeys (prior target : List Key) : List Key :=
  target.filter (fun k => k ∈ prior)

/-- The keys the reconcile leaves in place (the LIS over the common keys by
prior index): the maximal already-in-relative-order subset. -/
def stableKeys (prior target : List Key) : List Key :=
  lisBy (idxIn prior) (commonKeys prior target)

/-- The common keys the reconcile repositions (common keys not in the LIS). -/
def movedKeys (prior target : List Key) : List Key :=
  (commonKeys prior target).filter (fun k => k ∉ stableKeys prior target)

/-- The remove ops: one per prior-only key. -/
def removeOps (prior target : Level) : List Op :=
  (prior.order.filter (fun k => k ∉ target.order)).map Op.remove
/-- The insert ops: one per target-only key. -/
def insertOps (prior target : Level) : List Op :=
  (target.order.filter (fun k => k ∉ prior.order)).map (fun k => Op.insert k (target.values k))
/-- The update ops: one per common key whose value changed. -/
def updateOps (prior target : Level) : List Op :=
  (commonKeys prior.order target.order).filter
    (fun k => prior.values k ≠ target.values k) |>.map (fun k => Op.update k (target.values k))
/-- The move ops: one per common non-LIS key. -/
def moveOps (prior target : Level) : List Op :=
  (movedKeys prior.order target.order).map Op.move

/-- The reconcile op set (`cell-model.md:236`): the minimal
`{insert, remove, move, update}` per key. -/
def reconcileOps (prior target : Level) : List Op :=
  removeOps prior target ++ insertOps prior target ++ updateOps prior target ++ moveOps prior target

/-- Membership in a 4-way append flattens to a 4-way disjunction (right-assoc). -/
theorem mem_append4 {α : Type} (a : α) (l₁ l₂ l₃ l₄ : List α) :
    a ∈ l₁ ++ l₂ ++ l₃ ++ l₄ ↔ a ∈ l₁ ∨ a ∈ l₂ ∨ a ∈ l₃ ∨ a ∈ l₄ := by
  simp [List.mem_append]

/-- `Op.move k` is in the reconcile iff `k` is a common non-LIS key. -/
theorem mem_reconcile_move_iff (prior target : Level) (k : Key) :
    Op.move k ∈ reconcileOps prior target ↔ k ∈ movedKeys prior.order target.order := by
  constructor
  · intro hin
    unfold reconcileOps at hin
    rw [mem_append4] at hin
    rcases hin with h | h | h | h
    · rw [removeOps, List.mem_map] at h; obtain ⟨a, _, heq⟩ := h; exact Op.noConfusion heq
    · rw [insertOps, List.mem_map] at h; obtain ⟨a, _, heq⟩ := h; exact Op.noConfusion heq
    · rw [updateOps, List.mem_map] at h; obtain ⟨a, _, heq⟩ := h; exact Op.noConfusion heq
    · rw [moveOps, List.mem_map] at h
      obtain ⟨a, ha, heq⟩ := h
      have h1 : a = k := by injection heq
      rwa [h1] at ha
  · intro hmem
    unfold reconcileOps
    rw [mem_append4]
    exact Or.inr (Or.inr (Or.inr (List.mem_map.mpr ⟨k, hmem, rfl⟩)))

/-- Move-minimization (conformance clause 1, `cell-model.md:238`): a stable (LIS)
key is never moved — only the non-LIS common keys emit `move`. -/
theorem reconcile_move_minimized (prior target : Level) (k : Key)
    (hstab : k ∈ stableKeys prior.order target.order) :
    Op.move k ∉ reconcileOps prior target := by
  rw [mem_reconcile_move_iff]
  intro hmem
  simp only [movedKeys, List.mem_filter, decide_eq_true_iff] at hmem
  exact absurd hstab hmem.2

/-- `Op.update k` is in the reconcile iff `k` is a common key whose value
changed. -/
theorem mem_reconcile_update_iff (prior target : Level) (k : Key) :
    Op.update k (target.values k) ∈ reconcileOps prior target ↔
      k ∈ commonKeys prior.order target.order ∧ prior.values k ≠ target.values k := by
  constructor
  · intro hin
    unfold reconcileOps at hin
    rw [mem_append4] at hin
    rcases hin with h | h | h | h
    · rw [removeOps, List.mem_map] at h; obtain ⟨a, _, heq⟩ := h; exact Op.noConfusion heq
    · rw [insertOps, List.mem_map] at h; obtain ⟨a, _, heq⟩ := h; exact Op.noConfusion heq
    · rw [updateOps, List.mem_map] at h
      obtain ⟨a, ha, heq⟩ := h
      injection heq with h1 _
      subst h1
      simp only [List.mem_filter, decide_eq_true_iff] at ha
      exact ha
    · rw [moveOps, List.mem_map] at h; obtain ⟨a, _, heq⟩ := h; exact Op.noConfusion heq
  · intro ⟨hck, hne⟩
    unfold reconcileOps
    rw [mem_append4]
    exact Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨k, by
      simp only [List.mem_filter, decide_eq_true_iff]; exact ⟨hck, hne⟩, rfl⟩)))

/-- Stable-entry value preservation (conformance clause 2, `cell-model.md:239`):
a stable entry (unchanged value, in the LIS) is neither moved nor updated by the
reconcile, so its value cell is untouched. Combined with
`LazilyFormal.Collection` (`moveKey_preserves_values`,
`setEntryValue_preserves_siblings`), a stable entry's value cell is provably not
invalidated by a sibling reorder. -/
theorem reconcile_stable_not_invalidated (prior target : Level) (k : Key)
    (hstab : k ∈ stableKeys prior.order target.order)
    (heq : prior.values k = target.values k) :
    Op.move k ∉ reconcileOps prior target ∧
    Op.update k (target.values k) ∉ reconcileOps prior target := by
  refine ⟨reconcile_move_minimized prior target k hstab, ?_⟩
  rw [mem_reconcile_update_iff]
  intro ⟨_, hne⟩
  exact absurd heq hne

end LazilyFormal.Reconciliation
