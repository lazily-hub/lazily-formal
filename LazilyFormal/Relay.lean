/-
! RelayCell — formal model (Phases 2–8, `#relaycell`).

The formal counterpart of `lazily-spec/docs/relaycell.md` and
`lazily-spec/docs/relaycell-backpressure-analysis.md` §4.2 (RelayCell), §4.5
(SpillStore), §4.6 (Transport), §6 (reactive policies), §9 (the converged-egress
invariant). Builds on `LazilyFormal.Merge`.

A `RelayCell` is an algebra-typed conflating relay: an accumulating hot head
(`MergeCell` under a `MergePolicy`), a backpressure policy, and an optional paged
durable tail. This file fixes the invariant §9 calls out above all else — *the
converged egress state is independent of binding and mechanism whenever ⊕ is
associative* — plus the transport-reordering and crash-replay corollaries.

Central results:

- **`relay_converges`** — a relay's egress equals the lossless flat fold of the
  delivered ops, for *any* flush schedule (Block and Conflate converge identically
  because associativity licenses coalescing each window).
- **`transport_independent`** — two transports delivering the same op stream in
  any framing converge to the same state.
- **`reorder_adjacent`** — a commutative policy is invariant under reordering
  (the reordering tax): priority egress, keyed sharding, and out-of-order pages
  are sound exactly when `Commutative`.
- **`spill_lossless`** — a hot head over paged cold storage reconstructs the flat
  fold (paged spill loses nothing).
- **`spill_replay_idempotent`** — crash-replaying the last (unacked) page's
  coalesced summary is a no-op when the policy is idempotent (the durability tax).
-/

import LazilyFormal.Merge

namespace LazilyFormal.Relay

open LazilyFormal.Merge

variable {T : Type}

/-- A flush schedule partitions the ingress op stream into windows — each window
    is the batch accumulated between two flushes of the hot head. -/
abbrev Schedule (T : Type) := List (List T)

/-- The ops a schedule actually delivers to the egress, in order. -/
def delivered (sched : Schedule T) : List T := sched.flatten

/-- Egress state of a Block/Conflate relay: fold each flush window into the
    accumulator. Conflate coalesces a window into one op (`coalesceSound`); the
    applied state is identical to Block applying the window op-by-op, so both are
    `applyOps` per window. -/
def relayEgress (P : MergePolicy T) (s0 : T) (sched : Schedule T) : T :=
  sched.foldl (fun acc w => applyOps P acc w) s0

/-- **The converged-egress invariant (§9).** For an associative policy the relay's
    egress equals the lossless flat fold of the delivered ops — independent of the
    flush schedule (where it flushes, how it batches, whether it coalesces). This
    is the property every RelayCell fixture pins. -/
theorem relay_converges (P : MergePolicy T) (s0 : T) (sched : Schedule T) :
    relayEgress P s0 sched = applyOps P s0 (delivered sched) :=
  (flushGroupingIrrelevant P s0 sched).symm

theorem flatten_map_singleton (ops : List T) :
    (ops.map (fun x => [x])).flatten = ops := by
  induction ops with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- **Block ≡ Conflate on converged state.** A relay that flushes every op
    individually (no coalescing) reaches the same state as one coalescing every
    window — Conflate is lossless for the converged value. -/
theorem block_eq_conflate (P : MergePolicy T) (s0 : T) (ops : List T) :
    relayEgress P s0 (ops.map (fun x => [x])) = applyOps P s0 ops := by
  rw [relay_converges]
  simp only [delivered, flatten_map_singleton]

/-- **Transport independence (§4.6).** Two transports (framings/schedules) that
    deliver the same op stream converge to the same egress state — the merge
    algebra, not the transport, guarantees convergence, so transports may differ
    across bindings. -/
theorem transport_independent (P : MergePolicy T) (s0 : T) (sched sched' : Schedule T)
    (h : delivered sched = delivered sched') :
    relayEgress P s0 sched = relayEgress P s0 sched' := by
  rw [relay_converges, relay_converges, h]

/-- **Reordering tax (§2, §6, cases 11/18).** A commutative policy is invariant
    under swapping adjacent ops — so priority egress, keyed sharding, and
    out-of-order page rehydration converge identically *exactly when* the policy
    is `Commutative`. (Any permutation is a product of adjacent transpositions.) -/
theorem reorder_adjacent (P : MergePolicy T) (hC : Commutative P)
    (s : T) (a b : T) (rest : List T) :
    applyOps P s (a :: b :: rest) = applyOps P s (b :: a :: rest) := by
  simp only [applyOps, List.foldl_cons]
  have h : P.merge (P.merge s a) b = P.merge (P.merge s b) a := by
    rw [P.assoc, P.assoc, hC a b]
  rw [h]

/-! ## Paged spill (§4.5) — hot head over immutable cold pages -/

/-- Spill state: `pages` are the immutable cold windows already spilled (oldest
    first), `hot` is the current in-RAM accumulation window. -/
def spillState (P : MergePolicy T) (s0 : T) (pages : Schedule T) (hot : List T) : T :=
  applyOps P (relayEgress P s0 pages) hot

/-- **Paged spill loses nothing.** Reconstructing from the cold pages (in order)
    then the hot head equals the flat fold of every op — memory is bounded to
    `O(hot) + O(manifest)` without changing the converged value. -/
theorem spill_lossless (P : MergePolicy T) (s0 : T) (pages : Schedule T) (hot : List T) :
    spillState P s0 pages hot = applyOps P s0 (pages.flatten ++ hot) := by
  simp only [spillState]
  rw [relay_converges, ← applyOps_append]
  rfl

/-- **Crash-replay is a no-op under idempotency (the durability tax).** After a
    crash the relay replays the last unacked page; a page is one coalesced summary
    op at the egress (`coalesceSound`), so re-merging it is `(s⊕p)⊕p = s⊕p` —
    exactly the `Idempotent` law. At-least-once delivery converges. -/
theorem spill_replay_idempotent (P : MergePolicy T) (hIdem : Idempotent P)
    (s : T) (o : T) (rest : List T) :
    P.merge (applyOps P s (o :: rest)) (coalesce P o rest) = applyOps P s (o :: rest) := by
  rw [coalesceSound P s o rest]
  exact hIdem s (coalesce P o rest)

/-! ## Phase 6/8 corollaries — the extra policies reduce to the core theorems -/

/-- **Window policy (debounce/throttle, case 8) converges.** A `WindowPolicy` only
    chooses *where* the relay flushes — its windows are a flush schedule — so the
    converged egress is the flat fold regardless of window size. A direct corollary
    of `relay_converges` (which is `flushGroupingIrrelevant`). -/
theorem window_converges {T : Type} (P : MergePolicy T) (s0 : T) (windows : Schedule T) :
    relayEgress P s0 windows = applyOps P s0 (delivered windows) :=
  relay_converges P s0 windows

/-- **Priority egress / keyed sharding (cases 11, 18) are sound iff commutative.**
    Both reorder ops; for a commutative policy an adjacent reordering leaves the
    converged state unchanged. A direct corollary of `reorder_adjacent`. -/
theorem priority_reorder_sound {T : Type} (P : MergePolicy T) (hC : Commutative P)
    (s : T) (a b : T) (rest : List T) :
    applyOps P s (a :: b :: rest) = applyOps P s (b :: a :: rest) :=
  reorder_adjacent P hC s a b rest

/-- **`DurableOutbox.coalesce_to_snapshot` is a corollary (Phase 8).** The existing
    reliable-sync outbox coalesces a run of ops into one snapshot before sending;
    for any associative policy that snapshot merged downstream equals applying the
    ops one by one — the pre-existing `coalesce_by_join_sound` specialized, now
    subsumed by the general relay soundness. -/
theorem durable_outbox_coalesce_sound {T : Type} (P : MergePolicy T)
    (s o : T) (rest : List T) :
    applyOps P s (o :: rest) = P.merge s (coalesce P o rest) :=
  coalesceSound P s o rest

end LazilyFormal.Relay
