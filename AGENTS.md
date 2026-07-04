# lazily-formal

Language-agnostic Lean 4 formal model for the lazily reactive-signals family —
the neutral home formal artifacts every binding depends on equally.

## Architecture

- `LazilyFormal/Primitive.lean` — shared abstract types (`StateId`, `EventId`,
  `ActionId`, `GuardId`, `Configuration`, `GuardResolver`).
- `LazilyFormal/StateMachine.lean` — flat FSM kernel (`State → Event → Option
  State`) + theorems (guard rejection, self-transition, equivalence). Ported
  from lazily-spec; the pure core a single-region chart compiles down to.
- `LazilyFormal/StateChart.lean` — full Harel/SCXML model: `Kind` (atomic /
  compound / parallel / history shallow+deep / final), `Transition`, `Chart`,
  `History`,   `StepResult`; transition selection (enabled, conflict resolution),
  region-aware LCA exit/enter sets (via `sourceLeaf`, which resolves the active
  leaf in the transition source's own region so a sibling region is never
  spanned — `lazily-spec/docs/state-charts.md`'s "sibling regions are untouched"
  invariant), descent, history record-on-exit / restore-on-enter, and
  `send` (deterministic by construction). Theorems: `enabled_empty_rejects`,
  `send_actions_empty_when_rejected`, `stepActions_sourcing`,
  `recordHistory_idempotent`, the `*_in_states` well-formedness family
  (incl. `send_cfg_in_states`),   `parallel_region_confluence` (with its
  `sendTaken_eq_enabled_of_pairwise_disjoint` transparency lemma — the
  pairwise-disjoint hypothesis now holds for genuine orthogonal regions because
  the LCA exit sets are region-scoped), and
  `single_region_refines_flat_machine` (reject case from pointer
  well-formedness; take case derived from `Chart.Coherent`, the structural
  well-formedness the loose `WellFormed` does not pin down). Chart immutability
  holds by construction (pure Lean; `StepResult` carries no replacement `Chart`).
- `LazilyFormal/Reactive.lean` — flat reactive graph kernel: the
  `Slot -> Cell -> Signal -> Effect` family with reverse subscription edges,
  the `PartialEq` cell-write guard, the memo-equality suppression guard, and
  eager-`Signal` materialization. Theorems:
  `setCell_equal_preserves_graph` (the universal "no churn on equal" guard),
  `setCell_different_invalidates_dependents`,
  `recomputeSlot_equal_preserves_dependents` (memo suppression),
  `recomputeSlot_different_invalidates_dependents`,
  `signal_materialized_after_recompute` (a Signal always has a materialized
  value after its puller runs).
- `LazilyFormal/ThreadSafe.lean` — thread-safe reactive context
  (`lazily-spec/protocol.md` § "Concurrency layers are required"): a batch
  flush that serializes concurrent cell writes into one coalesced invalidation
  pass. The pure core of the thread-safe `batch` boundary; the
  lock/`Send + Sync` mechanics are language-level and have no pure encoding.
  Theorems: `flushBatch_empty`, `flushBatch_singleton_eq_setCell` (refines the
  single-threaded kernel), `flushBatch_dependent_dirty` (coalesced frontier),
  `flushBatch_preserves_nondependent_dirty` (glitch-freedom).
- `LazilyFormal/Collection.lean` — keyed reactive collection (`CellMap` +
  `CellFamily`): independent value/membership/order signals, atomic move.
  Theorems: `setEntryValue_preserves_{membership,order,siblings}`,
  `moveKey_preserves_{membership,values}`, `moveKey_advances_order`,
  `addKey_advances_membership_and_order`, `Family.get_idempotent_after_first`
  (per-key identity stability).
- `LazilyFormal/Tree.lean` — ordered keyed reactive tree (`CellTree`): per-node
  value reactivity and per-level membership/order reactivity, atomic-move
  identity preservation. Theorems:
  `setNodeValue_preserves_{other_nodes,node_signals}`,
  `moveChild_preserves_{non_parent,parent_value}`,
  `moveChild_advances_order_signal_only`.
- `LazilyFormal/Reconciliation.lean` — keyed reconciliation
  (`lazily-spec/cell-model.md` § "Keyed reconciliation"): the move-minimized
  `{insert, remove, move, update}` op set a level diff emits by stable key, over
  a longest-increasing-subsequence (LIS) kernel. Theorems: `lisBy_longest`
  (the chosen LIS is longest → `move` set minimal), `reconcile_move_minimized`
  (a stable/LIS key is never moved), `reconcile_stable_not_invalidated`
  (a stable entry with unchanged value is neither moved nor updated → its value
  cell is untouched). The executable reference behind
  `lazily-spec/conformance/collections/keyed_reconciliation_lis.json`.
- `LazilyFormal/SemTree.lean` — the memoized semantic tree
  (`lazily-spec/cell-model.md` § "Memoized semantic tree"): one memo slot per
  node folds `(weighted node value, child derived values)`, parameterised by the
  per-value weight so one model covers `sum` and `count_positive`. Theorems:
  `derivedForest_replace` / `parent_memo_guard` (equal folded result ⇒ ancestors
  unchanged, the tree-level memo-equality guard), `setVal_miss` /
  `derived_setVal_miss` (an edit that misses a subtree leaves it — and its memo
  slot — untouched, sibling cache), `derivedForest_remove` / `remove_child_updates`
  (removal drops exactly the removed subtree's fold). Backs
  `lazily-spec/conformance/collections/semtree_incremental.json`.
- `LazilyFormal/StableId.lean` — manufactured identity for text
  (`lazily-spec/cell-model.md` § "Manufactured identity for text"): the `a:`
  (anchored) and `c:` (content) keyspaces as distinct `Key` constructors.
  Theorems: `keyspaces_disjoint` / `anchored_content_never_collide` (a:/c: never
  collide), `anchored_survives_rewrite` (anchored key survives a full body
  rewrite), `content_key_eq_iff` / `content_key_changes_on_edit` (content key
  survives reflow, changes on edit), `lcs_self` / `classify_self` (word-LCS
  similarity ≥ 0.5 ⇒ `Edited`/key-inherited, else `Inserted`). Backs
  `lazily-spec/conformance/collections/stableid_alignment.json`.
- `LazilyFormal/TextCrdt.lean` — the base Fugue/RGA character CRDT
  (`lazily-spec/cell-model.md` § "Free-text CRDT + re-parse"): presence + sticky
  tombstone as a pointwise join-semilattice (complements `TextCrdtSync`, which
  proves the delta-sync lattice). Theorems: `merge_comm` / `merge_assoc` /
  `merge_idem` (state convergence), `concurrent_inserts_both_present` (no
  same-point insert lost), `precedes_total` / `precedes_asymm` (the descending-
  `OpId` sibling comparator is a strict total order ⇒ order is a deterministic
  function of the live set). Backs
  `lazily-spec/conformance/collections/textcrdt_convergence.json`.
- `LazilyFormal/SeqCrdt.lean` — the move-aware sequence CRDT
  (`lazily-spec/cell-model.md` § "Move-aware sequence order"): each element three
  independent LWW registers (value / position / deleted), a move a single LWW
  position reassignment. Theorems: `joinReg_{comm,assoc,idem}` (the register join
  is a semilattice), `merge_{comm,assoc,idem}` (state convergence),
  `concurrent_move_lww` (concurrent moves converge to the later stamp, no
  duplication), `concurrent_move_and_value` (a concurrent move + value edit both
  apply — independent registers), `remove_lww` (LWW tombstone). Backs
  `lazily-spec/conformance/collections/seqcrdt_convergence.json`.
- `LazilyFormal/AsyncSlotState.lean` — the async slot state machine
  (`Empty / Computing / Resolved / Error`) from
  `lazily-spec/docs/async.md` § "Async slot state machine". Models the pure
  transition core with revision-tracked stale completion discard. Theorems:
  `stale_completeOk_discarded` / `stale_completeErr_discarded` (a stale
  completion leaves the slot byte-identical — the universal form of conformance
  point 2), `current_completeOk_publishes` / `current_completeErr_to_error`
  (a current completion publishes), `step_preserves_wellFormed`. Concurrency
  properties (waiter cancellation, benign races) are out of scope per the spec
  (`async.md:236`).
- `LazilyFormal/AsyncEffect.lean` — the async effect lifecycle
  (`lazily-spec/docs/async.md` § "Async effects" + § "Batch support"). Models
  the pure scheduling core of an async effect. Theorems:
  `fire_blocked_during_cleanup` (cleanup-before-body, conformance point 6),
  `invalidate_from_idle_schedules` / `invalidate_yields_pending_or_disposed`
  (batch-boundary scheduling — invalidation only queues, never runs inline;
  conformance point 7), `cleanupDone_resumes_deferred` (serialized resumption,
  point 6), `dispose_absorbing` / `disposed_terminal` (disposal, point 3).
  Covers async conformance points 3-disposal, 6, 7; the concurrency-specific
  properties (waiter cancellation, benign races, compute-context dependency
  tracking) are out of scope per the spec (`async.md:236`).

`send` is a total function, so confluence/determinism is by construction — the
universal guarantee every binding inherits by replaying the shared conformance
fixtures in `lazily-spec/conformance/statechart/`.

## Role

This is the **formal** layer; `lazily-spec` is the **wire** layer. lazily-formal
owns primitive types + the flat kernel + the full Harel chart + the reactive
graph kernel (Slot/Cell/Signal/Effect) + the keyed collection (CellMap/CellFamily)
+ the ordered tree (CellTree) + the memoized semantic tree (SemTree) + manufactured
identity (StableId) + the collection-level CRDTs (TextCrdt base + delta sync,
SeqCrdt) + distributed signaling (peer FSM + roster); every
`lazily-spec/conformance/collections/*.json` fixture now has an executable
reference here. lazily-spec owns the wire protocol (IPC Snapshot/Delta, the
register/`PnCounter`/`CellCrdt` + `CrdtSync` layer, FFI, permission, capability
negotiation) + its own Lean proofs + the conformance fixtures. lazily-formal is
the executable reference behind the fixtures, not a wire artifact.

## Commands

```bash
make check   # == lake build
```

Pinned to Lean 4.30.0; pure stdlib, no dependencies.

<!-- tsift:code-navigation v=0.1.73 -->
## Code Navigation

Keep this block self-contained for Codex/OpenCode prompt reuse.

Run `tsift status` at session start from the owning repo root. Prefer bounded
digest commands over raw transcript/diff reads; only read full source files when
tsift results are insufficient.

For local verification, run `make check` before committing.
