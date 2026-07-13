# lazily-formal

Language-agnostic **Lean 4** formal model for the lazily reactive-signals
family — the neutral home for the formal artifacts every binding depends on
*equally*. Not owned by `lazily-rs` (which would create Rust-centrism) and not
buried in `lazily-spec` (a wire-protocol repo).

`lazily-formal` is the **formal** layer; `lazily-spec` is the **wire** layer.
This repo owns the executable reference *behind* the cross-language
state-chart conformance fixtures: a total, deterministic `send` whose type is
itself the confluence proof that all bindings agree on *every* input, not just
the tested ones. It also owns the formal models of the lazily reactive-signals
data-structure family — `Slot`, `Cell`, `Signal`, `Effect`, `CellMap`,
`SlotMap`, `CellTree`, the thread-safe batch context, and the async
effect lifecycle — that every binding implements.

## Feature Set

The full `lazily` capability set and its cross-language coverage across every
binding (`lazily-rs`, `lazily-py`, `lazily-kt`, `lazily-js`, `lazily-dart`,
`lazily-zig`, `lazily-go`, `lazily-cpp`). Legend: ✅ shipped · `~` partial · `—` absent or not applicable.
This table is generated from [`lazily-spec/coverage.json`](../lazily-spec/coverage.json)
— the canonical matrix with per-cell notes and platform carve-outs lives in
lazily-spec's [Cross-Language Coverage](../lazily-spec/docs/coverage.md). It is
kept in sync by lazily-spec's `scripts/sync-coverage.mjs`; run `make coverage-sync`
in `lazily-spec` after editing `coverage.json`.

<!-- coverage-table:start -->
| Feature | Rust | Python | Kotlin | JS | Dart | Zig | Go | C++ |
| --------- | :----: | :------: | :------: | :--: | :----: | :---: | :--: | :---: |
| Reactive graph — `Cell` / `Slot` / `Signal` / `Effect` / memo / batch | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Keyed-map materialization (`SlotMap`) — mint-on-access derived slots: transparency + deferral (`#lzmatmode`) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Thread-safe keyed map (`ThreadSafeSlotMap`) — `Send + Sync` + materialization confluence (`#lzmatmode`) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Async keyed map (`AsyncSlotMap`) — eventual transparency (`#lzmatmode`) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Keyed-map sync — membership propagation + materialize-on-ingest + derived-aggregate transparency (`#lzfamilysync`) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Thread-safe context (lock-backed) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Async reactive context | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Flat state machine | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Harel state charts | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Keyed reactive maps (`ReactiveMap`: `CellMap` / `SlotMap`) + `CellTree` + reconcile | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Memoized semantic tree (`SemTree`) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Stable-id alignment (manufactured identity) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Reactive queue (`QueueCell` SPSC/MPSC + `QueueStorage` adapter) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Merge algebra + `MergeCell` — associative `MergePolicy` (`KeepLatest`/`Sum`/`Max`/`SetUnion`/`RawFifo`), `Cell ≡ MergeCell<KeepLatest>`, `Reactive`/`Source` split (`#relaycell`) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| RelayCell — conflating relay + `BackpressurePolicy` + `SpillStore` + `Transport` + Inbox/Outbox + Rate/Window/Expiry/Priority/keyed policies (`#relaycell`) | ✅ | — | — | — | — | — | — | — |
| Free-text character CRDT (`TextCrdt`) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| `TextCrdt` delta sync (`version_vector` / `delta_since` / `apply_delta`) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Move-aware sequence CRDT (`SeqCrdt`) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Lossless tree CRDT core (`LosslessTreeCrdt`, M1) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Lossless tree — dotted-frontier anti-entropy | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Lossless tree — concurrent merge convergence | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Registers (LWW / MV) + `PnCounter` + `CellCrdt` | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| IPC wire — `Snapshot` + `Delta` + `CrdtSync` | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Shared-memory blob path (`ShmBlobArena`) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Cross-process zero-copy transport (`BlobBackend` / shm / arrow) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Distributed CRDT plane (`CrdtPlaneRuntime` / anti-entropy) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Reliable sync — resync coordinator + at-least-once durable outbox + OR-set/LWW liveness (`#lzsync`) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Reliable-sync transport seam + full-duplex `SyncDriver` loop (`IpcSink`/`IpcSource`, `#sync-driver`) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Distributed plane — WebRTC transport + signaling | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| State projection / mirror | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Causal receipts (`CausalReceipts` outcome projection) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Message-passing + RPC command plane (`command-plane-v1`) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| C-ABI FFI boundary | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Permission boundary (`PeerPermissions` / `RemoteOp`) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Capability negotiation (`SessionHandshake`) | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
| Instrumentation / benchmarks | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ | ✅ |
<!-- coverage-table:end -->

CRDT convergence and the wire protocol are pinned by the shared conformance fixtures
and JSON Schemas in `lazily-spec` and the Lean models in this repo.
## Architecture

Layered primitive → flat kernels → full chart → reactive data-structure family
→ collection-level CRDTs → concurrency contexts → async lifecycle → distributed
signaling:

- **`LazilyFormal/Primitive.lean`** — shared abstract types
  (`StateId`, `EventId`, `ActionId`, `GuardId`, `Configuration`, `GuardResolver`).
  Intentionally abstract `Nat` stand-ins: the model fixes *behavior*, not wire
  encoding — the wire encoding is fixed by `lazily-spec` conformance fixtures.
- **`LazilyFormal/StateMachine.lean`** — the flat FSM kernel
  (`State → Event → Option State`) + theorems (guard rejection, self-transition,
  `sends` flag, transition preservation). Ported from lazily-spec so this repo
  is the canonical home for the kernel. The pure transition core a
  single-region chart compiles down to, and the layer whose transitions surface
  on the IPC wire.
- **`LazilyFormal/StateChart.lean`** — the full Harel/SCXML model: `Kind`
  (atomic / compound / parallel / history shallow + deep / final), `Transition`,
  `Chart` + `WellFormed`, `History`, `StepResult`; transition selection
  (`enabled`, conflict resolution via disjoint exit sets), LCA exit/enter sets,
  descent, history record-on-exit / restore-on-enter, and `send`.
- **`LazilyFormal/Reactive.lean`** — the flat reactive graph kernel: the
  `Slot -> Cell -> Signal -> Effect` family (node kinds, reverse subscription
  edges, the `PartialEq` cell-write guard, the memo-equality suppression guard,
  eager-`Signal` materialization). The pure reactive core every binding's
  `Context` implements, and the layer whose changes surface on the IPC wire as
  `CellSet` / `SlotValue` / `Invalidate`.
- **`LazilyFormal/ThreadSafe.lean`** — the thread-safe reactive context
  (`lazily-spec` § "Concurrency layers are required"): a batch flush that
  serializes concurrent cell writes into one coalesced invalidation pass. The
  pure core of the thread-safe `batch` boundary; proves it *refines* the
  single-threaded kernel (a one-write batch is identical to `setCell`), the
  coalesced frontier (a dependent of any changed source is dirtied), and
  glitch-freedom (a non-dependent branch is untouched).
- **`LazilyFormal/Collection.lean`** — the keyed reactive collection
  (`CellMap` / `SlotMap`, the `ReactiveMap` specializations): independent value /
  set-membership / order signals and atomic identity-preserving move.
- **`LazilyFormal/Tree.lean`** — the ordered keyed reactive tree (`CellTree`):
  per-node value reactivity, per-level membership/order reactivity, atomic-move
  identity preservation.
- **`LazilyFormal/Reconciliation.lean`** — keyed reconciliation (`cell-model.md`
  § "Keyed reconciliation"): the move-minimized `{insert, remove, move, update}`
  op set a level diff emits by stable key, built on a longest-increasing-
  subsequence (LIS) kernel. The executable reference behind
  `lazily-spec/conformance/collections/keyed_reconciliation_lis.json`.
- **`LazilyFormal/SemTree.lean`** — the memoized semantic tree (`cell-model.md`
  § "Memoized semantic tree"): one memo slot per node folding
  `(weighted node value, child derived values)`, parameterised by the per-value
  weight so one model covers both `sum` and `count_positive`. Proves the
  incremental / glitch-free guarantees — a sibling subtree stays cached when an
  edit misses it (`setVal_miss`), and an edit that preserves a subtree's folded
  result leaves every ancestor's fold unchanged (`parent_memo_guard`) — plus that
  removal drops exactly the removed subtree's fold. The executable reference
  behind `lazily-spec/conformance/collections/semtree_incremental.json`.
- **`LazilyFormal/StableId.lean`** — manufactured identity for text
  (`cell-model.md` § "Manufactured identity for text"): the `a:` (anchored) and
  `c:` (content) keyspaces as distinct `Key` constructors — disjoint by
  construction (`keyspaces_disjoint`) — an anchored key surviving a full body
  rewrite, a content key surviving reflow but changing on edit
  (`content_key_eq_iff`), and word-LCS similarity alignment classifying an
  `Edited` block (key inherited, ratio `≥ 0.5`) apart from a genuine `Inserted`
  one (`lcs_self`, `classify_self`). The executable reference behind
  `lazily-spec/conformance/collections/stableid_alignment.json`.
- **`LazilyFormal/TextCrdt.lean`** — the base Fugue/RGA character CRDT
  (`cell-model.md` § "Free-text CRDT + re-parse"): presence + sticky tombstone as
  a pointwise join-semilattice (merge commutative / associative / idempotent), no
  concurrent same-point insert lost (`concurrent_inserts_both_present`), and the
  sibling comparator (descending `OpId`) a strict total order so order is a
  deterministic function of the live set (`precedes_total`). Complements
  `TextCrdtSync` (which proves the delta-sync lattice); backs
  `lazily-spec/conformance/collections/textcrdt_convergence.json`.
- **`LazilyFormal/SeqCrdt.lean`** — the move-aware sequence CRDT (`cell-model.md`
  § "Move-aware sequence order"): each element three independent LWW registers
  (value / position / deleted), a move a *single* LWW position reassignment.
  Proves the register join is a semilattice, merge is commutative / associative /
  idempotent, concurrent moves converge to the later stamp with no duplication
  (`concurrent_move_lww`), and a concurrent move + value edit both apply because
  the registers are independent (`concurrent_move_and_value`). The executable
  reference behind `lazily-spec/conformance/collections/seqcrdt_convergence.json`.
- **`LazilyFormal/AsyncSlotState.lean`** — the async slot state machine
  (`Empty / Computing / Resolved / Error`) from `lazily-spec/docs/async.md`
  § "Async slot state machine". Models the pure transition core with
  revision-tracked stale-completion discard. Concurrency properties (waiter
  cancellation, benign races) are out of scope per the spec (`async.md:236`).
- **`LazilyFormal/AsyncEffect.lean`** — the async effect lifecycle
  (`lazily-spec/docs/async.md` § "Async effects" + § "Batch support"). Models
  the pure scheduling core of an async effect: cleanup-before-body
  serialization (a body cannot start while a cleanup is pending), batch-boundary
  scheduling (a dependency invalidation only ever *queues* a rerun, never starts
  one inline; the body fires only on the executor / after the outermost batch
  exits), and disposal (terminal, pending reruns removed). Covers async
  conformance points 6, 7, and the disposal clause of point 3; the
  concurrency-specific properties (waiter cancellation, benign races, compute-
  context dependency tracking) are out of scope per the spec (`async.md:236`).
- **`LazilyFormal/TopicCell.lean`** — the broadcast topic model: one append log,
  independent non-destructive durable cursors, ephemeral session cursors that do
  not hold retention, atomic snapshot/restore, and GC at the slowest durable
  cursor. Backs `lazily-spec/conformance/collections/topiccell_*.json`.
- **`LazilyFormal/Receipt.lean`** — the causal receipt projection
  (`lazily-spec/protocol.md` § "Causal Receipts"): duplicate receipt ids are
  idempotent, stale generations are discarded, `observed` / `accepted` are
  non-terminal, `applied` / `rejected` are terminal, and distinct terminal
  outcomes conflict rather than being auto-resolved.

## Scope — what is modeled

`StateChart` models the full chart subset of `lazily-spec/docs/state-charts.md`:

- Compound (hierarchical) states with default initial descent.
- Orthogonal (parallel) regions.
- Shallow **and** deep history — record-on-exit / restore-on-enter.
- Entry, exit, and transition actions (exit innermost-first → transition →
  entry outermost-first).
- Named guards, resolved host-side (`GuardResolver`); fail-closed when absent.
- External **and** internal transitions (LCA-based exit/enter sets).

Out of scope here (handled elsewhere): the wire encoding, CRDT/IPC semantics,
and `run` actions / `{"expr": …}` context guards / `final`-completion (`done`)
— the model fixes the *behavioral core*, not the host-evaluated surface.

## What is proved

Lean proofs (`make check` builds all of them). Grouped by guarantee:

**Flat kernel (`StateMachine`)**
- `guard_rejection_preserves_state` — a `none` transition leaves the state unchanged.
- `accepted_transition_advances_state` — an accepted `some next` advances to `next`.
- `self_transition_preserves_state` — a self-targeted transition preserves state.
- `self_transition_sends_false` / `changed_transition_sends_true` — the `sends`
  flag matches whether the state actually changed.
- `send_preserves_transition` — `send` never changes the transition function.

**Rejection & actions (`StateChart`)**
- `enabled_empty_rejects` — no enabled, guard-passing transition ⇒ configuration
  and history unchanged.
- `send_actions_empty_when_rejected` — a rejected `send` fires no actions.
- `stepActions_sourcing` — every fired action is sourced from an exited state's
  `exit`, a taken transition's `action`, or an entered state's `entry`.

**Well-formedness invariants (`StateChart`, the `*_in_states` family)**
Under `WellFormed`, every computed set stays inside the chart's declared
`states`: `children_in_states`, `activeLeaves_in_cfg`, `ancestors(Aux)_in_states`,
`enterSubtree_in_states`, `pathBelow_in_states`, `restoreStart_in_states`,
`restoreViaHistory_in_states`, `regionOf_in_states`, `enterSet_in_states`,
`enabledForLeafAux_in_states`, `enabled_in_states`, and
`send_cfg_in_states` (a `send` over a well-formed chart keeps the configuration
inside `states`).

**Conflict-resolution transparency (`StateChart`)**
- `sendTaken_subset_enabled` — the conflict-resolving `keepTrans` fold only
  drops elements, never invents them.
- `keepTrans_appends_of_disjoint` / `foldl_keepTrans_appends_all` — when an
  enabled transition's exit set is disjoint from the accumulator, it is appended.
- `sendTaken_eq_enabled_of_pairwise_disjoint` — under pairwise-disjoint exit
  sets, `keepTrans` is transparent: every enabled transition is taken.

**History (`StateChart`)**
- `recordHistory_idempotent` — recording history for the same exit set twice is
  the same as recording once.

**Parallel-region confluence (`StateChart` — the headline universal result)**
- `parallel_region_confluence` — when enabled transitions are pairwise
  non-conflicting (orthogonal regions, i.e. disjoint LCA exit sets), every
  enabled transition is taken and the resulting configuration depends only on
  the enabled *set*, not its order. Invariant under any reordering of `enabled`.
  Backed by the order-free membership lemmas `mem_zip_fst`, `zip_map_eq`,
  `filter_notContains_mem`, `applyTakenCfg_mem_iff`, `perm_flatMap_mem`, and
  `send_cfg_eq_applyTakenCfg_take`. The LCA is region-scoped via `sourceLeaf`
  (which resolves the active leaf in the transition source's own region), so the
  pairwise-disjoint hypothesis is genuinely satisfiable by real orthogonal
  regions and the resulting exit sets never span a sibling region — matching
  `lazily-spec`'s "sibling regions are untouched" invariant.

**Single-region refinement (`StateChart`)**
- `single_region_enabled_at_most_one` — with one active leaf, at most one
  transition is enabled.
- `single_region_refines_flat_machine` — a single-region chart's `send` refines
  the flat `StateMachine` kernel derived in `flatMachine`: the new active leaf
  equals the flat machine's transition target.
  - Reject case: from pointer well-formedness.
  - Take case: derived from `Chart.Coherent` — the structural well-formedness
    (kinds match the tree; default descents resolve to a unique leaf; the root
    is a common ancestor) that the model's loose `WellFormed` does not pin down.
    All four take-case consequences are proven from the three `Coherent` fields
    (no transition-specific hypothesis).

`parallel_region_confluence` is unconditional modulo the pairwise-disjoint
hypothesis; `single_region_refines_flat_machine` is proved under `Chart.Coherent`
(reject case needs no `Coherent`).

**Reactive graph kernel (`Reactive`) — the `Slot / Cell / Signal / Effect` family**
- `setCell_equal_preserves_graph` — the `PartialEq` cell-write guard: an equal
  write leaves the whole graph byte-identical (universal form of the wire
  invariant "equal `set_cell` emits no `CellSet` and no downstream ops").
- `setCell_different_invalidates_dependents` — a strictly-different write marks
  every direct dependent dirty.
- `recomputeSlot_equal_preserves_dependents` — memo-equality suppression: a slot
  that recomputes to an equal value leaves its downstream dependents untouched.
- `recomputeSlot_different_invalidates_dependents` — a strictly-different
  recompute marks every direct dependent dirty.
- `signal_materialized_after_recompute` — an eager `Signal`'s backing slot is
  always materialized (concrete value, not dirty) after its puller runs; the
  universal form of "a changed eager Signal emits `SlotValue`, never bare
  `Invalidate`, for its backing slot".

**SlotMap materialization (`Materialization`) — eager default / lazy opt-in (`#lzmatmode`)**

The materialization axis of a `SlotMap` — the keyed map whose
entries are input cells (`EntryKind.cell`, a `CellHandle`) or derived slots
(`EntryKind.slot`, a `SlotHandle`). Entry kind is orthogonal to mode.
- `cell_entries_materialized_in_every_mode` / `slot_entries_deferred_under_lazy` —
  entry *kind* ⟂ materialization *mode*: a `cell` (input) entry is present under
  either mode; an unread `slot` (derived) entry is deferred under lazy. This is
  the handle-kind axis the Rust `ReactiveMap<K, V, H>` abstracts over.
- `observe_canonical` — the headline transparency law: a read yields the node's
  spec value under *either* mode (`observe (build mode spec) id = spec.val id`).
- `eager_lazy_observationally_equivalent` / `observe_mode_independent` — the value
  read from a node is independent of the materialization mode; opting into lazy
  never changes an observed value.
- `materialize_preserves_observe` — no churn from allocation: materializing one
  node never changes another node's observed value.
- `materialize_present_monotone` / `lazy_present_subset_eager` — deferral, not
  de-allocation: lazy only *grows* the materialized set, which is a subset of the
  eager (all-present) set.
- `eager_materializes_all` / `lazy_defers_slots` — eager allocates every node up
  front; lazy leaves an unread derived slot unallocated (the memory / first-touch
  advantage).
- `default_mode_eager` — the default materialization mode is eager.

**Thread-safe reactive context (`ThreadSafe`) — the lock-serialized batch boundary**
- `flushBatch_empty` — an empty batch flush is the identity.
- `flushBatch_singleton_eq_setCell` — a one-write batch is observationally
  identical to the single-threaded `setCell`: the thread-safe context *refines*
  the single-threaded kernel (concurrency changes neither value nor
  invalidation of a single write).
- `flushBatch_dependent_dirty` — the coalesced frontier: after a batch flush, a
  dependent of *any* changed source is dirty (universal invalidation under
  serialized concurrent writes).
- `flushBatch_preserves_nondependent_dirty` — glitch-freedom: a node that is a
  dependent of no changed source keeps the dirty flag the post-write graph gave
  it (the flush never touches an unrelated branch).

**Keyed collection (`Collection`) — `CellMap` / `SlotMap`**
- `setEntryValue_preserves_{membership,order,siblings}` — updating one entry's
  value leaves the membership signal, the order signal, and every sibling's
  value cell untouched.
- `moveKey_preserves_{membership,values}` / `moveKey_advances_order` — a pure
  reorder (`move_to`) leaves set-membership and every value cell untouched and
  bumps only the order signal once: the wire invariant "a pure reorder MUST NOT
  invalidate set-membership readers".
- `addKey_advances_membership_and_order` — adding a key bumps both signals.
- `Family.get_idempotent_after_first` — the same key resolves to the same cell
  handle on every request (per-key identity stability across the factory).

**Ordered keyed tree (`Tree`) — `CellTree`**
- `setNodeValue_preserves_other_nodes` / `setNodeValue_preserves_node_signals` —
  per-node value reactivity: editing one node's value leaves every other node,
  and the edited node's own child collection / per-level signals, untouched.
- `moveChild_preserves_non_parent` / `moveChild_preserves_parent_value` —
  per-level reactivity: a sibling-subtree change does not disturb an unrelated
  level, and an atomic move keeps the child's cell identity and value.
- `moveChild_advances_order_signal_only` — an atomic move bumps the parent's
  per-level order signal by exactly one and leaves its membership signal
  unchanged.

**Keyed reconciliation (`Reconciliation`) — LIS move-minimized level diff**
- `lisBy_longest` — the chosen LIS is genuinely longest: every increasing
  subsequence of the input is no longer, so the emitted `move` set is minimal
  (`cell-model.md` move-minimized clause).
- `reconcile_move_minimized` — a stable (LIS) key is never moved: only the
  non-LIS common keys emit `move` (`cell-model.md:238`).
- `reconcile_stable_not_invalidated` — a stable entry (unchanged value, in the
  LIS) is neither moved nor updated, so its value cell is untouched by the
  reconcile (`cell-model.md:239`). Combined with `Collection`'s
  `moveKey_preserves_values` / `setEntryValue_preserves_siblings`, a stable
  entry's value cell is provably not invalidated by a sibling reorder — the
  universal form of the `keyed_reconciliation_lis.json`
  `stable_keys_not_invalidated` expectation.

**Async slot state (`AsyncSlotState`) — the `Empty / Computing / Resolved / Error` lifecycle**
- `stale_completeOk_discarded` / `stale_completeErr_discarded` — a stale
  completion (revision mismatch) leaves the slot byte-identical: the universal
  form of conformance point 2 (`async.md:218`), "Revision tracking discards
  every stale completion; a stale value is never published."
- `current_completeOk_publishes` / `current_completeErr_to_error` — a current
  completion (revision matches) publishes the value / transitions to Error.
- `step_preserves_wellFormed` — after any transition the slot's fields remain
  consistent with its lifecycle state.

**Async effect lifecycle (`AsyncEffect`) — cleanup-before-body + batch-boundary scheduling**
- `fire_blocked_during_cleanup` — cleanup-before-body (conformance point 6): a
  body rerun cannot start while a cleanup future is pending.
- `invalidate_from_idle_schedules` / `invalidate_yields_pending_or_disposed` —
  batch-boundary scheduling (conformance point 7): a dependency invalidation
  only ever *queues* a rerun (`scheduled` / `cleanupRunningScheduled`), never
  starts one inline; the body fires only on the executor.
- `cleanupDone_resumes_deferred` — serialized resumption (conformance point 6):
  when a cleanup completes and a rerun was queued during it, the deferred rerun
  becomes runnable.
- `dispose_absorbing` / `disposed_terminal` — disposal (conformance point 3):
  `dispose` is absorbing and terminal; no event revives a disposed effect.

**Causal receipt projection (`Receipt`) — command/effect outcomes**
- `observed_nonterminal` / `accepted_nonterminal` — ACK-like observations are not
  terminal authority.
- `applied_terminal` / `rejected_terminal` — applied/rejected complete a
  causation.
- `duplicate_receipt_noop` — duplicate receipt ids are idempotent no-ops.
- `stale_generation_discarded` — receipts outside the current generation cannot
  affect the current projection.
- `distinct_terminal_conflicts` — conflicting terminal outcomes fail closed.

**Broadcast topic (`TopicCell`) — durable multi-cursor fan-out**
- `broadcast_delivery` / `publish_visible_to_new_durable` — one publish is
  independently visible to every subscriber without an assignment decision.
- `advance_preserves_elements` / `advance_preserves_other_readStream` — a read is
  non-destructive and advances only that subscriber; `advance_at_end_noop` keeps
  cursors bounded at an empty tail.
- `restore_snapshot` / `restart_preserves_cursor` — an atomic durable snapshot
  recovers the log and every subscriber cursor across restart.
- `minCursor_le_cursor` / `gc_at_min_preserves_readStream` — the slowest durable
  cursor is the retention frontier; collecting below it preserves every future
  durable read.
- `state_conflation_effect_lossless` — a lagging state-topic subscriber may keep
  only the newest value without changing the final LWW effect.

**Reliable sync (`ReliableSync`) — gap recovery, at-least-once outbox, multi-epoch delta, liveness (`#lzsync`)**
- `multi_epoch_apply_eq_fold` (`multi_epoch_apply_eq_fold_state`) — a coalesced
  multi-epoch-span `Delta` (`epoch > base_epoch + 1`, N ops) produces the same
  state as its expansion into N single-op unit deltas; `applyDelta_advances_epoch`
  — the coalesced delta advances `last_epoch` straight to `d.epoch` (atomic).
- `resync_convergence` — a receiver that drops an arbitrary delta suffix then
  adopts the resync `Snapshot` reaches the same graph as one that saw every delta
  (gap recovery is state-equivalent, not lossy).
- `ingest_apply_on_contiguous` / `ingest_ignore_on_redelivery` /
  `ingest_request_on_gap` — the `ResyncCoordinator` decision table
  (Apply / Ignore / RequestSnapshot); `step_redelivery_noop` — a re-delivered
  (`base_epoch < last`) delta leaves `(state, last)` unchanged.
- `outbox_at_least_once_exactly_once_effect`
  (`stepRun_ignore_redelivered_prefix`) — replaying already-applied frames before
  the new frames reaches the identical `(state, last)` as delivering only the new
  frames once: no op lost, none doubled (at-least-once + idempotent apply =
  exactly-once effect).
- `crdt_liveness_convergence_under_retry` — the OR-set / LWW liveness join is a
  semilattice (`joinReg_{comm,assoc,idem}`, `joinOR_{comm,assoc,idem}`), so
  out-of-order and re-delivered liveness ops converge and a retry is a no-op;
  `orset_add_wins_over_stale_remove` — a re-open (unshadowed add tag) beats a
  lagging close.

### By construction (not a theorem, but the strongest guarantee)

- **Determinism** — `send` is a total function of
  `(chart, history, configuration, event, guard resolver)`, so a given input
  tuple yields a unique `StepResult`. This confluence guarantee is what no
  finite fixture suite can establish.
- **Chart immutability** — Lean is pure, and `send` returns a `StepResult`
  (`cfg` / `history` / `actions`) that carries no replacement `Chart`; the chart
  definition simply cannot be mutated by a step.

## lazily-spec compliance coverage

`lazily-spec`'s Binding Conformance Matrix splits into **wire** layers (owned
by `lazily-spec`'s own Lean model: IPC Snapshot/Delta, C-ABI FFI, the register /
`PnCounter` / `CellCrdt` + IPC `CrdtSync` layer, permission, capability
negotiation, shared-memory payload) and **compute** layers (owned here) —
including the collection-level text/sequence CRDTs whose order is a pure function
of the element set. Every compute layer that has a pure-machine core is modeled:

| lazily-spec compute layer (`MUST`) | lazily-formal module | Status |
|-------------------------------------|----------------------|--------|
| Reactive core (Cell / Slot / Effect / Signal) | `Reactive.lean` | modeled |
| SlotMap materialization (eager default / lazy opt-in, `#lzmatmode`) | `Materialization.lean` | modeled (contract; unified cell/slot map); Rust + C++ impls shipped (`SlotMap`) |
| Keyed cell collections (`CellMap`/`CellTree`, reconciliation) | `Collection.lean`, `Tree.lean`, `Reconciliation.lean` | modeled |
| Memoized semantic tree (`SemTree`) | `SemTree.lean` | modeled |
| Manufactured identity / stable-id alignment | `StableId.lean` | modeled |
| Broadcast topic (`TopicCell`) — fan-out, durable cursor restart, retention GC | `TopicCell.lean` | modeled |
| Free-text character CRDT (`TextCrdt`, base convergence + delta sync) | `TextCrdt.lean`, `TextCrdtSync.lean` | modeled |
| Move-aware sequence CRDT (`SeqCrdt`) | `SeqCrdt.lean` | modeled |
| Reactive family sync — membership propagation + materialize-on-ingest + derived-aggregate transparency (`#lzfamilysync`) | `FamilySync.lean` | modeled |
| Reliable sync — resync convergence + at-least-once outbox (exactly-once effect) + multi-epoch delta fold + OR-set/LWW liveness convergence (`#lzsync`) | `ReliableSync.lean` | modeled |
| Distributed signaling (peer-connection FSM + roster) | `Signaling.lean`, `SignalingRoster.lean` | modeled |
| Flat state machine | `StateMachine.lean` | modeled |
| Harel state charts | `StateChart.lean` | modeled |
| Thread-safe reactive context (`MUST²`, platform-conditional) | `ThreadSafe.lean` | modeled |
| Async reactive context (`MUST²`, platform-conditional) | `AsyncSlotState.lean` (slot state machine, points 1–2) + `AsyncEffect.lean` (effect serialization, batch-boundary scheduling, disposal; points 3-disposal, 6, 7) | modeled |
| Causal receipts (`MUST`) | `Receipt.lean` | modeled |

The async concurrency-specific properties — waiter cancellation (point 3's
waiter clause), the two benign `get_async` races (point 4), and compute-context
dependency registration across `.await` (point 5) — are, per `async.md:236`,
pinned by targeted deterministic tests at the binding level, not by a pure
total-function model (they are properties of real-executor interleavings a
synchronization-model checker cannot shim).

## Role vs. lazily-spec and the bindings

`lazily-formal` is the **formal** layer; `lazily-spec` is the **wire** layer.

| Repo | Owns |
|------|------|
| `lazily-formal` (this) | formal models: flat FSM kernel + full Harel chart + reactive graph kernel (Slot/Cell/Signal/Effect) + SlotMap materialization (unified cell/slot map, eager default / lazy opt-in, observational transparency) + thread-safe batch context + keyed collection (CellMap/SlotMap) + ordered tree (CellTree) + memoized semantic tree (SemTree) + manufactured identity (StableId) + free-text CRDT (TextCrdt base + delta sync) + move-aware sequence CRDT (SeqCrdt) + distributed signaling (peer FSM + roster) + async slot state + async effect lifecycle + causal receipt projection; universal proofs |
| `lazily-spec` | wire protocol + JSON schemas + IPC/CRDT Lean proofs + conformance fixtures (incl. `conformance/statechart/`) |
| `lazily-rs` / `lazily-py` / `lazily-zig` / `lazily-kt` / `lazily-js` / `lazily-dart` / `lazily-go` / `lazily-cpp` | native implementations; replay the shared conformance fixtures |

## Verify

```bash
make check   # == lake build
```

Pinned to Lean 4.30.0 via `lean-toolchain`. No external dependencies (pure stdlib).
