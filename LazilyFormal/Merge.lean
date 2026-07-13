/-
! Merge algebra (`MergePolicy`) — formal model (Phase 1, `#relaycell`).

The formal counterpart of `lazily-spec/docs/reactive-graph.md` § "MergeCell and
the merge algebra" and `lazily-spec/docs/relaycell-backpressure-analysis.md` §2.
The executable reference behind
`lazily-spec/conformance/collections/mergecell_algebra.json` and each binding's
`merge_laws` property tests.

A merge policy is an **associative** fold `⊕ : T → T → T`. Associativity is the
irreducible core (§2); commutativity and idempotency are the independent
transport-selected branches. The central results fixed here:

- **`coalesceSound`** — associativity licenses *variable flush points*: a run of
  accumulated ops `o :: rest` may be coalesced into a single summary op
  `rest.foldl ⊕ o` and merging that summary is equivalent to applying the ops
  one by one. This is exactly what a bounded relay does when it flushes a
  backpressure window; the converged egress is unchanged.
- **`flushGroupingIrrelevant`** — flushing at arbitrary batch boundaries (the
  left fold over a flattened stream) equals folding chunk-by-chunk. Together with
  `coalesceSound`, the converged state is independent of *where* the relay flushes
  and *whether* it coalesces each window.
- `Cell ≡ MergeCell KeepLatest`: the keep-latest band replaces, matching a plain
  cell's `set`.

Modeled as an explicit `MergePolicy` value (not a typeclass) because several
policies inhabit the same carrier `Nat` (Sum, Max) — instance resolution would be
ambiguous; a relay carries its policy as data anyway.
-/

namespace LazilyFormal.Merge

/-- A merge policy on `T`: an associative fold `⊕ : T → T → T`. Associativity is a
    law, not a flag (analysis §2). -/
structure MergePolicy (T : Type) where
  merge : T → T → T
  assoc : ∀ a b c, merge (merge a b) c = merge a (merge b c)

/-- The reordering-tax branch: `⊕` is commutative. -/
def Commutative {T : Type} (P : MergePolicy T) : Prop :=
  ∀ a b : T, P.merge a b = P.merge b a

/-- The durability-tax branch: re-applying an op is a no-op (`(a⊕b)⊕b = a⊕b`) —
    the property that makes the `==` store-guard free dedup. -/
def Idempotent {T : Type} (P : MergePolicy T) : Prop :=
  ∀ a b : T, P.merge (P.merge a b) b = P.merge a b

/-- Apply a run of ops to a state by left fold (the accumulation window). -/
def applyOps {T : Type} (P : MergePolicy T) (s : T) (ops : List T) : T :=
  ops.foldl P.merge s

/-- Coalesce a nonempty accumulation window `o :: rest` into one summary op. -/
def coalesce {T : Type} (P : MergePolicy T) (o : T) (rest : List T) : T :=
  rest.foldl P.merge o

/-- Left-fold homomorphism under associativity: folding from `merge s a` factors
    the leading `s` out of the fold. -/
theorem foldl_merge_hom {T : Type} (P : MergePolicy T) (s a : T) (l : List T) :
    l.foldl P.merge (P.merge s a) = P.merge s (l.foldl P.merge a) := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [P.assoc]
    exact ih (P.merge a x)

/-- **Coalescence soundness.** Applying a run `o :: rest` one op at a time equals
    merging the state with the run's coalesced summary. This is what licenses a
    bounded relay to flush a backpressure window as a single merged op. -/
theorem coalesceSound {T : Type} (P : MergePolicy T) (s o : T) (rest : List T) :
    applyOps P s (o :: rest) = P.merge s (coalesce P o rest) := by
  simp only [applyOps, coalesce, List.foldl_cons]
  exact foldl_merge_hom P s o rest

/-- Applying two runs back-to-back equals flushing at their boundary. -/
theorem applyOps_append {T : Type} (P : MergePolicy T) (s : T) (xs ys : List T) :
    applyOps P s (xs ++ ys) = applyOps P (applyOps P s xs) ys := by
  simp [applyOps, List.foldl_append]

/-- **Flush points are irrelevant.** Applying a flattened op stream equals folding
    it chunk-by-chunk (flushing at each chunk boundary). Combined with
    `coalesceSound`, the converged state is independent of both *where* a relay
    flushes and *whether* it coalesces each window. -/
theorem flushGroupingIrrelevant {T : Type} (P : MergePolicy T) (s : T)
    (chunks : List (List T)) :
    applyOps P s chunks.flatten = chunks.foldl (fun acc c => applyOps P acc c) s := by
  induction chunks generalizing s with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.flatten_cons, List.foldl_cons]
    rw [applyOps_append]
    exact ih (applyOps P s c)

/-! ## KeepLatest — the band behind a plain Cell (`Cell ≡ MergeCell KeepLatest`) -/

/-- Keep-latest policy: `old ⊕ op = op`. -/
def keepLatest (T : Type) : MergePolicy T where
  merge := fun _ b => b
  assoc := by intro a b c; rfl

/-- KeepLatest replaces: a plain cell's `set` is exactly this policy's merge, so
    `Cell ≡ MergeCell KeepLatest`. -/
theorem keepLatest_replaces {T : Type} (a b : T) :
    (keepLatest T).merge a b = b := rfl

/-- KeepLatest is idempotent (the band law) … -/
theorem keepLatest_idempotent (T : Type) : Idempotent (keepLatest T) := by
  intro a b; rfl

/-- … but not commutative in general (the CRDT-vs-LWW branch). -/
theorem keepLatest_not_commutative : ¬ Commutative (keepLatest Bool) := by
  intro h
  have := h true false
  simp [keepLatest] at this

/-! ## Sum — commutative monoid (assoc + comm, NOT idempotent) -/

def sumNat : MergePolicy Nat where
  merge := Nat.add
  assoc := by intro a b c; exact Nat.add_assoc a b c

theorem sum_commutative : Commutative sumNat := by
  intro a b; exact Nat.add_comm a b

theorem sum_not_idempotent : ¬ Idempotent sumNat := by
  intro h; have := h 0 1; simp [sumNat] at this

/-! ## Max — semilattice (assoc + comm + idempotent) -/

def maxNat : MergePolicy Nat where
  merge := Nat.max
  assoc := fun a b c => Nat.max_assoc a b c

theorem max_commutative : Commutative maxNat :=
  fun a b => Nat.max_comm a b

theorem max_idempotent : Idempotent maxNat :=
  fun a b => (Nat.max_assoc a b b).trans (congrArg (Nat.max a) (Nat.max_self b))

end LazilyFormal.Merge
