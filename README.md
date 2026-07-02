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
`CellFamily`, `CellTree` — that every binding implements.

## Architecture

Eight modules, layered primitive → flat kernels → full chart → reactive
data-structure family → async lifecycle:

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
- **`LazilyFormal/Collection.lean`** — the keyed reactive collection
  (`CellMap` + `CellFamily`): independent value / set-membership / order
  signals and atomic identity-preserving move.
- **`LazilyFormal/Tree.lean`** — the ordered keyed reactive tree (`CellTree`):
  per-node value reactivity, per-level membership/order reactivity, atomic-move
  identity preservation.
- **`LazilyFormal/Reconciliation.lean`** — keyed reconciliation (`cell-model.md`
  § "Keyed reconciliation"): the move-minimized `{insert, remove, move, update}`
  op set a level diff emits by stable key, built on a longest-increasing-
  subsequence (LIS) kernel. The executable reference behind
  `lazily-spec/conformance/collections/keyed_reconciliation_lis.json`.
- **`LazilyFormal/AsyncSlotState.lean`** — the async slot state machine
  (`Empty / Computing / Resolved / Error`) from `lazily-spec/docs/async.md`
  § "Async slot state machine". Models the pure transition core with
  revision-tracked stale-completion discard. Concurrency properties (waiter
  cancellation, benign races) are out of scope per the spec (`async.md:236`).

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

**Keyed collection (`Collection`) — `CellMap` / `CellFamily`**
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

### By construction (not a theorem, but the strongest guarantee)

- **Determinism** — `send` is a total function of
  `(chart, history, configuration, event, guard resolver)`, so a given input
  tuple yields a unique `StepResult`. This confluence guarantee is what no
  finite fixture suite can establish.
- **Chart immutability** — Lean is pure, and `send` returns a `StepResult`
  (`cfg` / `history` / `actions`) that carries no replacement `Chart`; the chart
  definition simply cannot be mutated by a step.

## Role vs. lazily-spec and the bindings

`lazily-formal` is the **formal** layer; `lazily-spec` is the **wire** layer.

| Repo | Owns |
|------|------|
| `lazily-formal` (this) | formal models: flat FSM kernel + full Harel chart + reactive graph kernel (Slot/Cell/Signal/Effect) + keyed collection (CellMap/CellFamily) + ordered tree (CellTree); universal proofs |
| `lazily-spec` | wire protocol + JSON schemas + IPC/CRDT Lean proofs + conformance fixtures (incl. `conformance/statechart/`) |
| `lazily-rs` / `lazily-py` / `lazily-zig` / `lazily-kt` / `lazily-js` / `lazily-dart` | native implementations; replay the shared conformance fixtures |

## Verify

```bash
make check   # == lake build
```

Pinned to Lean 4.30.0 via `lean-toolchain`. No external dependencies (pure stdlib).
