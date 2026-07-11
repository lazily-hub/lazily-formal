/-
! Async ReactiveFamily materialization — formal model (eventual transparency).

The async flavor of `Materialization`: keys map to async reactive nodes whose
derived (slot) entries resolve *asynchronously*. Allocation (the present-set axis)
is already modelled in `Materialization`; this module adds the orthogonal
**resolution** axis that async introduces — a derived slot is `pending` until it is
driven (an `AsyncContext.get_async` on the handle), then `resolved`. Input cells
are resolved at build.

A non-blocking read therefore returns `Option Value`: `none` while pending,
`some v` once resolved — exactly the Rust `AsyncReactiveFamily::observe`
signature. The single-threaded family's transparency law (`observe` yields the
canonical value under either mode) weakens, for the async family, to **eventual
transparency**: once a node resolves, its observed value is the canonical value —
identical to what the synchronous family observes.

Proved here:

- `eventual_transparency` — driving a node to resolution then reading it yields
  `some (spec.val id)`: the resolved value is the canonical value. The headline law.
- `async_resolved_matches_sync` — the resolved async read equals (modulo `some`)
  the value the synchronous `Materialization.observe` returns from a canonical
  state. The async family and the sync family agree on resolved values.
- `observe_pending_is_none` — an unresolved (pending) read is `none`, never a stale
  or junk value.
- `cell_resolved_at_build` — input cells are resolved at build (always `some`).
- `resolve_monotone` — resolution only grows the resolved set (no un-resolution).
- `resolve_preserves_observe` — resolving one node never changes another resolved
  node's observed value.

The `Canonical` invariant (a resolved node caches its spec value) carries warm-read
correctness through `resolve`, exactly as in `Materialization`.
-/

import LazilyFormal.Materialization

namespace LazilyFormal.AsyncMaterialization

open LazilyFormal.Materialization (Spec NodeId Value Mat EntryKind)

/-- Async runtime state: which nodes have **resolved** and the value cached at each.
    A node with `resolved = false` is pending — allocated but not yet driven to a
    value (the async first-touch case). Orthogonal to the `Materialization.Mat`
    present/allocation axis. -/
structure AsyncMat where
  resolved : NodeId → Bool
  stored : NodeId → Value

/-- An async state is **canonical** when every resolved node caches its spec value —
    the cache-correctness invariant that makes a resolved read return the canonical
    value. -/
def Canonical (s : Spec) (m : AsyncMat) : Prop :=
  ∀ n, m.resolved n = true → m.stored n = s.val n

/-- Eager async build: input cells resolve immediately with their value; derived
    slots start **pending** (allocation may be eager, but the async value is only
    produced when the slot is driven). -/
def buildEager (s : Spec) : AsyncMat :=
  { resolved := s.isInput
  , stored := fun n => if s.isInput n = true then s.val n else 0 }

/-- Drive `id` to resolution: if already resolved, return unchanged (a warm read);
    else resolve it and cache its canonical value (the async completion). -/
def resolve (s : Spec) (m : AsyncMat) (id : NodeId) : AsyncMat :=
  if m.resolved id = true then m
  else
    { resolved := fun n => if n = id then true else m.resolved n
    , stored := fun n => if n = id then s.val n else m.stored n }

/-- Non-blocking observe: `some value` once resolved, `none` while pending. The
    `Spec` is unused (the cached value already carries canonicity) but kept for API
    symmetry with the synchronous `Materialization.observe`. -/
def observeAsync (_s : Spec) (m : AsyncMat) (id : NodeId) : Option Value :=
  if m.resolved id = true then some (m.stored id) else none

/-! ## Build states are canonical -/

theorem buildEager_canonical (s : Spec) : Canonical s (buildEager s) := by
  intro n hn
  have hin : s.isInput n = true := hn
  show (if s.isInput n = true then s.val n else 0) = s.val n
  rw [if_pos hin]

/-! ## Resolution preserves canonicity and self-reads -/

/-- Resolving a node preserves the cache-correctness invariant. -/
theorem resolve_canonical (s : Spec) (m : AsyncMat) (id : NodeId)
    (hc : Canonical s m) : Canonical s (resolve s m id) := by
  unfold resolve
  by_cases hp : m.resolved id = true
  · rw [if_pos hp]; exact hc
  · rw [if_neg hp]
    intro n hn
    by_cases hnid : n = id
    · show (if n = id then s.val n else m.stored n) = s.val n
      rw [if_pos hnid]
    · show (if n = id then s.val n else m.stored n) = s.val n
      have hn' : m.resolved n = true := by
        have : (if n = id then true else m.resolved n) = true := hn
        rwa [if_neg hnid] at this
      rw [if_neg hnid]; exact hc n hn'

/-- After resolving `id`, it is resolved. -/
theorem resolve_resolved_self (s : Spec) (m : AsyncMat) (id : NodeId) :
    (resolve s m id).resolved id = true := by
  unfold resolve
  by_cases hp : m.resolved id = true
  · rw [if_pos hp]; exact hp
  · rw [if_neg hp]
    show (if id = id then true else m.resolved id) = true
    rw [if_pos rfl]

/-- After resolving `id`, its cache holds the canonical value. -/
theorem resolve_stored_self (s : Spec) (m : AsyncMat) (id : NodeId)
    (hc : Canonical s m) : (resolve s m id).stored id = s.val id := by
  unfold resolve
  by_cases hp : m.resolved id = true
  · rw [if_pos hp]; exact hc id hp
  · rw [if_neg hp]
    show (if id = id then s.val id else m.stored id) = s.val id
    rw [if_pos rfl]

/-! ## Eventual transparency — the headline law -/

/-- **Eventual transparency.** Driving a node to resolution then reading it yields
    `some (spec.val id)` — the resolved value is the canonical value. Async changes
    *when* a value is observable (pending → resolved), never *what* is observed. -/
theorem eventual_transparency (s : Spec) (m : AsyncMat) (id : NodeId)
    (hc : Canonical s m) :
    observeAsync s (resolve s m id) id = some (s.val id) := by
  unfold observeAsync
  rw [if_pos (resolve_resolved_self s m id), resolve_stored_self s m id hc]

/-- The resolved async read equals (modulo `some`) the value the **synchronous**
    family's `observe` returns from a canonical state: the async and sync families
    agree on resolved values. -/
theorem async_resolved_matches_sync (s : Spec) (m : AsyncMat) (id : NodeId)
    (hc : Canonical s m) (sm : Mat) (hsc : Materialization.Canonical s sm) :
    observeAsync s (resolve s m id) id = some (Materialization.observe s sm id) := by
  rw [eventual_transparency s m id hc,
      Materialization.observe_eq_val_of_canonical s sm hsc id]

/-- A pending (unresolved) read is `none` — never a stale or junk value. -/
theorem observe_pending_is_none (s : Spec) (m : AsyncMat) (id : NodeId)
    (hp : m.resolved id = false) : observeAsync s m id = none := by
  simp [observeAsync, hp]

/-! ## Resolution monotonicity and no-churn -/

/-- Resolution only *grows* the resolved set: a resolved node is never un-resolved. -/
theorem resolve_monotone (s : Spec) (m : AsyncMat) (id n : NodeId)
    (h : m.resolved n = true) : (resolve s m id).resolved n = true := by
  unfold resolve
  by_cases hp : m.resolved id = true
  · rw [if_pos hp]; exact h
  · rw [if_neg hp]
    show (if n = id then true else m.resolved n) = true
    by_cases hnid : n = id
    · rw [if_pos hnid]
    · rw [if_neg hnid]; exact h

/-- **No churn from resolution.** Resolving one node never changes another node's
    observed value. -/
theorem resolve_preserves_observe (s : Spec) (m : AsyncMat) (hc : Canonical s m)
    (id other : NodeId) (hother : m.resolved other = true) :
    observeAsync s (resolve s m id) other = observeAsync s m other := by
  unfold observeAsync
  rw [if_pos (resolve_monotone s m id other hother), if_pos hother]
  have hc' : Canonical s (resolve s m id) := resolve_canonical s m id hc
  rw [hc' other (resolve_monotone s m id other hother), hc other hother]

/-! ## Input cells resolve at build -/

/-- An input `cell` entry is resolved at build — always `some`, never pending. The
    async statement of "input cells are always materialized". -/
theorem cell_resolved_at_build (s : Spec) (id : NodeId)
    (hcell : s.kind id = EntryKind.cell) : (buildEager s).resolved id = true := by
  have hin : s.isInput id = true := by
    by_cases h : s.isInput id = true
    · exact h
    · simp [Spec.kind, h] at hcell
  exact hin

end LazilyFormal.AsyncMaterialization
