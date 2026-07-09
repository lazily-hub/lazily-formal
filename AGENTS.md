# lazily-formal

Language-agnostic Lean 4 formal model for the lazily reactive-signals family —
the neutral home formal artifacts every binding depends on equally.

## Commit & Push

Commit and push completed work at the end of every turn that changed code,
proofs, docs, or fixtures — do not leave finished work uncommitted. Run `make
check` first and ensure it is green; stage only the files that belong to the
change (never secrets or private customer names — see the workspace
`runbooks/private-name-hygiene.md`); write a concise commit message in the
repo's existing style; push to the current branch on `origin`. This standing
rule overrides the harness default of "commit only when explicitly asked" for
this repo.

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
- `LazilyFormal/QueueCell.lean` — the reactive queue (`QueueCell`) from
  `lazily-spec/cell-model.md` § "Reactive queues": a FIFO reactive collection
  whose shell invalidates by reader kind (head/len/is_empty/closed). Theorems:
  `close_preserves_{elements,head,length}` (close is orthogonal to queue state),
  `close_idempotent` (close is a no-op on closed), `push_preserves_closed` /
  `pop_preserves_closed` (neither push nor pop changes the closed flag),
  `push_after_close_rejected` (push on closed is a no-op), `push_nonempty_preserves_head`
  (push to non-empty does NOT invalidate head readers — the core reader-kind
  independence law), `pop_returns_oldest` (total-FIFO under SPSC),
  `Closed_then_stays_Closed` (the universal closure invariant — once closed, no
  operation reopens). Bounded-queue (`capacity`/`is_full`) theorems deferred.
  Backs `lazily-spec/conformance/collections/queuecell_*.json`.
- `LazilyFormal/TopicCell.lean` — broadcast topic stub (structure + key
  invariants declared, proofs deferred to distributed-queue PRD Phase 3).
- `LazilyFormal/WorkQueueCell.lean` — competing-consumer work queue stub
  (structure + delivery-state model + key invariants declared, proofs deferred
  to PRD Phase 2 consensus core).
- `LazilyFormal/ZeroCopyTransport.lean` — the cross-process zero-copy transport
  (`lazily-spec/docs/zero-copy-transport.md`): a backend-agnostic descriptor
  model where a producer spills large payloads to a blob backend (POSIX `shm` /
  Apache Arrow / in-process) and ships a `Descriptor`; the receiver resolves it
  zero-copy. Theorems: `resolve_write` / `transport_roundtrip` (spill-then-resolve
  identity — zero-copy correctness, the consumer reads the backend's own bytes),
  `resolve_wrong_backend` (backend-kind isolation → receiver routes by `kind`),
  `resolve_stale_generation` (ABA safety — a reused/freed slot is not misread),
  `resolve_corrupt_checksum` (corrupted descriptors rejected). Holds for every
  backend that maintains its issued-table semantics.

`send` is a total function, so confluence/determinism is by construction — the
universal guarantee every binding inherits by replaying the shared conformance
fixtures in `lazily-spec/conformance/statechart/`.

## Role

This is the **formal** layer; `lazily-spec` is the **wire** layer. lazily-formal
owns primitive types + the flat kernel + the full Harel chart + the reactive
graph kernel (Slot/Cell/Signal/Effect) + the keyed collection (CellMap/CellFamily)
+ the ordered tree (CellTree) + the memoized semantic tree (SemTree) + manufactured
identity (StableId) + the collection-level CRDTs (TextCrdt base + delta sync,
SeqCrdt) + distributed signaling (peer FSM + roster) + the reactive queue
(QueueCell; TopicCell/WorkQueueCell stubs); every
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

<!-- tsift:code-navigation v=0.1.74 -->
## Code Navigation

Keep this block self-contained for Codex/OpenCode prompt reuse. If this repository also ships current `.claude/skills/tsift/SKILL.md` or `runbooks/code-navigation.md`, use those deeper runbooks for command detail instead of expanding this block.

Run `tsift status` at session start from the owning repo root. If the task or file lives under a git submodule (for example `src/tsift/...`), switch to that submodule root first so the harness loads the narrower local instructions and repo state instead of the superproject root. If status prints a `run:` recommendation for stale or missing tsift state, run `tsift status --fix` before relying on tsift results; when the harness cannot perform write commands, ask the user to run the printed command instead. Codex projects can install a prompt-time auto-reindex hook with `tsift init --codex`; OpenCode projects can install per-project tsift command shortcuts with `tsift init --opencode`.

Use the commands listed in its `use:` output:
- `tsift --envelope source-read <file> --budget normal` — AST-symbol projection with span metadata and source-window expansion commands (prefer over cat/head for source code files)
- `tsift --envelope symbol-read <symbol> --budget normal` — token-budgeted symbol body, AST span metadata, child refs, and graph/source expansion commands
- `tsift --envelope search <query> --budget normal` — AST-aware hybrid search preview (prefer over grep/rg)
- `tsift --envelope explain <symbol> --budget normal` — callers, callees, community preview
- `tsift graph <symbol> --callers` / `--callees` — call graph navigation
- `tsift summarize <symbol>` — cached summary (only when listed in `use:`)
- `tsift workflow search` — ordered exact/search/explain/summarize/digest recipe that preserves result handles across expansions

When a search envelope includes `report.scale_guard`, run one of its `narrow_commands` before dispatching parallel agents. The guard means the original result set or corpus is broad enough that fan-out should start from a narrower cited handle, path, or exact query.

Prefer bounded digest commands over raw transcript, diff, and verbose-log reads:
- `tsift --envelope session-review <path> --next-context --budget normal` or `tsift --envelope context-pack <path> --budget normal` instead of replaying long session docs, JSONL transcripts, or agent-doc runtime logs with `cat`, `tail`, or `sed`.
- `tsift diff-digest [path]` (`--cached`, `--revision <rev>`) instead of `git diff`, `git show`, or patch-style `git log`.
- `tsift --envelope digest-runner --kind test --path . --shell-command '<test command>'` / `tsift --envelope digest-runner --kind log --path . --shell-command '<build command>'` for noisy test/build/install output, or let the rewrite/hooks create those artifact-backed envelopes for `cargo test`, `pytest`, and verbose cargo commands.
- If RTK is installed, digest-runner delegates supported generic command families through `rtk rewrite` and records the chosen compact filter in `report.filter` while preserving tsift artifact handles.
- Codex, OpenCode, and other harnesses without Claude-style `PreToolUse` hooks should run `tsift rewrite --run '<command>'` before broad `rg`/recursive grep, raw transcript/session/log reads, `git diff`/`git show`/single-patch `git log`, `cargo test`/`pytest`, and cargo build/check/clippy/install commands so the same search, session-digest, diff-digest, and digest-runner rewrites apply manually. OpenCode can install this path as `/tsift-rewrite-run` with `tsift init --opencode`.

For local verification, run `make check` before committing. After local changes, check the latest GitHub Actions CI run with `gh run list --workflow CI --limit 1` and fix any failing tests before calling the work complete.

Only read full source files when tsift results are insufficient.
<!-- /tsift:code-navigation -->
