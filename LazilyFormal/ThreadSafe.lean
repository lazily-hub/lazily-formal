/-
! Thread-safe reactive context — formal model.

The formal counterpart of the thread-safe reactive context documented in
`lazily-spec/protocol.md` § "Concurrency layers are required" and
`lazily-spec/docs/reactive-graph.md` § "Context layers". The thread-safe
context is a lock-backed counterpart to the single-threaded `Reactive` kernel:
handles are clonable, the transition function and state are `Send + Sync`, and
— the behavioral contract this model fixes — **observers fire synchronously
within the invalidating `send`/`batch` preserving glitch-free pull-based
ordering**.

The lock, `Send + Sync`, and handle-cloning mechanics are language-level type
properties (Rust's `Arc`/`Mutex`/`Send + Sync`) that have no honest encoding in
pure Lean. What *does* have a pure encoding is the observable guarantee those
mechanisms exist to preserve: that serializing concurrent cell writes through a
`batch` boundary coalesces them into one invalidation pass whose result is a
deterministic function of the writes — independent of the interleaving the lock
happened to pick. This is the formal core of the spec's "Coalesced frontier: a
dependent reached through many changed cells in one batch appears at most once
per delta" invariant, lifted from the wire (`lazily-spec`) to the reactive
graph.

`flushBatch` is a total function of `(graph, batch)`, so glitch-freedom holds
for *every* batch — the universal result no finite concurrency test can
establish.

Proved here:

- `flushBatch_empty` — an empty batch flush is the identity (no writes ⇒ no
  churn), mirroring the single-threaded empty `batch`.
- `flushBatch_singleton_eq_setSource` — a one-write batch is observationally
  identical to the single-threaded `setSource`: the thread-safe context *refines*
  the single-threaded kernel, so concurrency changes neither the value nor the
  invalidation of a single write.
- `flushBatch_dependent_dirty` — the coalesced frontier: after a batch flush, a
  dependent of *any* changed source is dirty (universal invalidation).
- `flushBatch_preserves_nondependent_dirty` — glitch-freedom: a node that is a
  dependent of no changed source keeps the dirty flag the post-write graph gave
  it (the flush never touches an unrelated branch).
-/

import LazilyFormal.Reactive

namespace LazilyFormal.ThreadSafe

open LazilyFormal.Reactive

/-- A pending cell write accumulated under the thread-safe context's lock:
    `(node, value)`. Pure model of the lock-serialized write queue. -/
structure Write where
  node : NodeId
  value : Value

/-- A thread-safe batch: the queue of cell writes accumulated since the last
    flush. Concurrent `set`s are linearized into this queue by the lock. -/
abbrev Batch := List Write

/-! ## Batch value application

Applying the queued writes' *values* (the `PartialEq` guard, reused from the
single-threaded kernel), without yet propagating. The propagation happens once,
at flush, over the coalesced union of changed sources' dependents. -/

/-- Apply one write's value update through the `PartialEq` guard. Returns the
    updated graph and whether the write actually changed the cell's value
    (`false` ⇒ equal-or-non-cell ⇒ no churn, exactly like `setSource`). -/
def applyWrite (g : Graph) (w : Write) : Graph × Bool :=
  match (g.node w.node).value with
  | some cur => if cur = w.value then (g, false)
               else (setNode g w.node ⟨.source, some w.value, none, false⟩, true)
  | none => (g, false)

/-- Fold a batch's value updates left to right, collecting the list of source
    nodes whose value actually changed (the cells whose dependents must be
    invalidated at flush). -/
def applyBatch (g : Graph) : Batch → Graph × List NodeId
  | [] => (g, [])
  | w :: ws =>
    let (g1, ch) := applyWrite g w
    let (g2, rest) := applyBatch g1 ws
    (g2, if ch then w.node :: rest else rest)

/-! ## Coalesced frontier

The union of the dependents of every changed source. `setNode` only updates a
node's value, never the `dependents` edge field, so the post-write graph's
`dependents` equals the original graph's — the frontier is well-defined over
either. Deduplication (a dependent of two changed sources appearing once) is a
*wire/delta* concern (`lazily-spec`); for the dirty-flag model a plain flatMap
is faithful: marking an already-dirty node dirty is a no-op. -/

/-- The flat union of dependents over a list of source nodes. -/
def unionDependents (g : Graph) : List NodeId → List NodeId
  | [] => []
  | n :: ns => g.dependents n ++ unionDependents g ns

/-- The thread-safe batch flush: apply all queued writes' values, then mark the
    coalesced union of changed sources' dependents dirty in one pass. This is
    the formal core of the thread-safe `batch` boundary. -/
def flushBatch (g : Graph) (batch : Batch) : Graph :=
  markDirtyAll (applyBatch g batch).1 (unionDependents g (applyBatch g batch).2)

/-! ## Membership lemma for the coalesced frontier -/

/-- If `d` is a dependent of a source `n`, and `n` is among the changed sources,
    then `d` is in the coalesced dependents union. -/
theorem unionDependents_member (g : Graph) (d n : NodeId) (sources : List NodeId)
    (hnsrc : n ∈ sources) (hdep : d ∈ g.dependents n) :
    d ∈ unionDependents g sources := by
  induction sources with
  | nil => exact absurd hnsrc List.not_mem_nil
  | cons x xs ih =>
    simp only [List.mem_cons] at hnsrc
    rcases hnsrc with hnx | hnx
    · subst hnx
      simp only [unionDependents]
      exact List.mem_append_left _ hdep
    · simp only [unionDependents]
      exact List.mem_append_right _ (ih hnx)

/-! ## Theorems -/

/-- An empty batch flush is the identity: no writes ⇒ no value updates ⇒ no
    propagation. -/
theorem flushBatch_empty (g : Graph) : flushBatch g [] = g := by
  simp only [flushBatch, applyBatch, unionDependents]
  rfl

/-- A one-write batch is observationally identical to the single-threaded
    `setSource`: the thread-safe context *refines* the single-threaded kernel.
    Concurrency (the lock, the batch queue) changes neither the written value
    nor the invalidation of a single write. -/
theorem flushBatch_singleton_eq_setSource (g : Graph) (n : NodeId) (v : Value) :
    flushBatch g [{ node := n, value := v }] = setSource g n v := by
  cases hval : (g.node n).value with
  | none =>
    have haw : applyWrite g { node := n, value := v } = (g, false) := by
      simp only [applyWrite, hval]
    have hab : applyBatch g [{ node := n, value := v }] = (g, []) := by
      simp only [applyBatch, haw]
      rfl
    simp only [flushBatch]
    rw [hab]
    simp only [unionDependents, markDirtyAll, setSource, hval]
    rfl
  | some cur =>
    by_cases heq : cur = v
    case pos =>
      have haw : applyWrite g { node := n, value := v } = (g, false) := by
        simp only [applyWrite, hval]
        rw [if_pos heq]
      have hab : applyBatch g [{ node := n, value := v }] = (g, []) := by
        simp only [applyBatch, haw]
        rfl
      simp only [flushBatch]
      rw [hab]
      simp only [unionDependents, markDirtyAll, setSource, hval]
      rw [if_pos heq]
      rfl
    case neg =>
      have haw :
          applyWrite g { node := n, value := v } =
            (setNode g n ⟨.source, some v, none, false⟩, true) := by
        simp only [applyWrite, hval]
        rw [if_neg heq]
      have hab :
          applyBatch g [{ node := n, value := v }] =
            (setNode g n ⟨.source, some v, none, false⟩, [n]) := by
        simp only [applyBatch, haw]
        rfl
      simp only [flushBatch]
      rw [hab]
      simp only [unionDependents, List.append_nil, setSource, hval]
      rw [if_neg heq]

/-- Coalesced frontier (positive direction): after a batch flush, a dependent
    of *any* changed source is dirty. Universal invalidation under serialized
    concurrent writes. -/
theorem flushBatch_dependent_dirty (g : Graph) (batch : Batch) (n d : NodeId)
    (hchanged : n ∈ (applyBatch g batch).2) (hdep : d ∈ g.dependents n) :
    ((flushBatch g batch).node d).dirty = true := by
  simp only [flushBatch]
  exact markDirtyAll_marks_members _ _ _ (unionDependents_member g d n _ hchanged hdep)

/-- Glitch-freedom: a node that is a dependent of no changed source keeps the
    dirty flag the post-write graph gave it. The flush's propagation never
    touches an unrelated branch. -/
theorem flushBatch_preserves_nondependent_dirty
    (g : Graph) (batch : Batch) (d : NodeId)
    (hnd : d ∉ unionDependents g (applyBatch g batch).2) :
    ((flushBatch g batch).node d).dirty = ((applyBatch g batch).1.node d).dirty := by
  simp only [flushBatch]
  exact markDirtyAll_preserves_nonmembers _ _ _ hnd

end LazilyFormal.ThreadSafe
