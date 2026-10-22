/-
! Reactive graph kernel — formal model.

The flat reactive core shared by every lazily binding (`lazily-rs`,
`lazily-py`, `lazily-zig`, `lazily-kt`, `lazily-js`, `lazily-dart`). It models
the **Cell kernel** — `Cell` is the value-bearing node concept, and its two
kinds are the `source` cell (handle `Source<T, M>`) and the `computed` cell
(handle `Computed<T>`), plus the value-less `effect` sink. (v2 naming: there is
no `Cell<T, K>` genus handle — `Cell` names the concept, `Source`/`Computed` are
the concrete handles.) Documented in `lazily-spec/docs/reactive-graph.md` and
implemented in `lazily-rs/src/{context,slot,cell,signal,effect}.rs`. An eager
value is a *driven* `computed` (`computed().eager()`), not a fourth kind.

This is the formal counterpart of the *behavioral core* of the reactive graph:

- the closed node-kind partition (source / computed / effect — no `Signal` kind),
- the unified owned/shared read domain (`Source` and `Computed`, never `Effect`),
- the reverse subscription edge set (`source → its direct dependents`),
- the `PartialEq` source-write guard,
- the computed-equality suppression guard (computed cells are guarded by default), and
- the eager (driven-computed) materialization invariant.

Like the `StateMachine` kernel, this is the layer whose state changes surface
on the lazily-spec IPC wire as `CellSet` / `SlotValue` / `Invalidate` ops (the
wire names are unchanged by the kernel rename — a slot is the storage position
that holds a node); the wire linkage itself stays in `lazily-spec`. The model
fixes *behavior*, not wire encoding — values are abstract `Nat` stand-ins,
exactly like the rest of `LazilyFormal`.

Proved here:

- `readShared_eq_readCell` / `trackedSharedRead_eq_trackedRead` — a shared-owner
  read (Rust `Context::get_rc`) accepts the same two cell kinds, returns the same
  value, and attributes the same dependency edge as the ordinary read. Runtime
  ownership/refcount mechanics are intentionally outside this pure value model.
- `setSource_equal_preserves_graph` — the `PartialEq` source-write guard: an equal
  write leaves the whole graph byte-identical (no churn, no downstream
  invalidation). Universal form of the wire-level "equal `set` emits no
  `CellSet` and no downstream ops" invariant.
- `setSource_different_invalidates_dependents` — a strictly-different write marks
  every direct dependent dirty.
- `recomputeComputed_equal_preserves_dependents` — the computed guard: a `computed`
  that recomputes with its guard returning `true` leaves every *downstream*
  dependent untouched. (The `Slot` in the identifier is the storage sense.)
- `recomputeComputed_different_invalidates_dependents` — a strictly-different
  recompute marks every direct dependent dirty.
- `signal_materialized_after_recompute` — a driven `computed`'s backing node is
  always materialized after the puller runs (no observable "unset" intermediate
  state). A driven computed = `computed` + puller `effect` (`computed().eager()`);
  universal form of the wire-level "changed eager value emits `SlotValue`, never
  bare `Invalidate` for its backing node" invariant.
- `disposeScope_eq_disposeAll` and friends — explicit disposal detaches edges in
  *both* directions, and ending a teardown scope (`scope()`) is observationally
  equal to disposing each member individually. See § "Disposal and teardown
  scopes" below.
- `disposeHandle_stale_noop` / `disposeHandle_generation_mismatch_noop` /
  `disposeHandle_kind_mismatch_noop` — public disposal validates a handle's
  generation and node kind before it reaches the graph mutation primitive.
  A stale or cross-kind-recycled handle leaves graph state and cleanup history
  byte-identical; only a matching live effect appends a cleanup event.
- `disposeHandle_same_kind_aba_noop` /
  `disposeHandle_cross_kind_recycled_noop` — both recycling cases are stated
  end to end as whole-arena no-ops, while
  `disposeHandle_generation_mismatch_refines_conformance` projects that stronger
  result onto the successor node, its reverse edges, and cleanup history that
  the executable stale-handle fixture observes.
- `hybrid_serves_stale_value_at_depth_two` — eager cone marking and lazy pull
  are each sound, but *combining* one-level marking with a cache-trusting read
  loses writes at depth 2. A shipped defect in two bindings, reduced to three
  nodes. See § "Staleness discovery" below.

The guards are total functions of `(graph, node, value)`, so the
"no churn on equal" guarantee is by construction — but the theorems make it
*observable* as graph-equality / dirty-flag statements, the property no finite
fixture suite can establish.
-/

import LazilyFormal.Primitive

namespace LazilyFormal.Reactive

open LazilyFormal.Primitive

/-- Abstract reactive node identifier (a `SlotId` in `lazily-rs`). -/
abbrev NodeId := Nat

/-- Abstract node payload. The model exercises *equality* and *identity*, never
    the type — so an opaque `Nat` stand-in is sufficient (mirrors the rest of
    `LazilyFormal`, which fixes behavior, not wire encoding). -/
abbrev Value := Nat

/-- Kind of a reactive node — the **Cell kernel** partition. A node's value comes
    either from outside it (`source`) or from upstream of it (`computed`); an
    `effect` is a value-less **sink**. An eager value is not a separate kind: a
    *driven* `computed` is a `computed` paired with a puller `effect` (see
    [`signal_materialized_after_recompute`]), exactly the `computed().eager()`
    construction in `lazily-rs/src/signal.rs`. -/
inductive NodeKind where
  | source   -- a `SourceCell`: written from outside; always set (was `cell`)
  | computed  -- a `ComputedCell`: memoized derived value, recomputed lazily on read (was `slot`)
  | effect   -- a value-less sink: a side-effecting computation that re-runs on invalidation
  | disposed -- a torn-down node: its arena slot is cleared and its id is free
  deriving Repr, DecidableEq

/-- The runtime state of one reactive node. A `source` carries a concrete value; a
    `computed` carries an optional cached value and an optional equality guard; an
    `effect` carries a pending flag (modeled by `dirty`) and never a value. -/
structure NodeState where
  kind : NodeKind
  /-- A `source`'s value, or a `computed`'s last cached value. `none` for a dirty
      computed or an `effect` (effects have no value of their own — the sink
      position). -/
  value : Option Value
  /-- Equality guard for a `computed` (guarded by default): `some eq` suppresses
      downstream invalidation when a recompute yields an equal value (`lazily-rs`'s
      `ctx.computed`). `none` ⇒ every recompute churns downstream. -/
  memoEq : Option (Value → Value → Bool)
  /-- `true` when the node must be recomputed/rerun before its next observed
      read. Set by invalidation; cleared by recompute. -/
  dirty : Bool

/-- A reactive graph: nodes keyed by id and the **reverse** subscription edge
    set (`source → its direct dependents`). A dependent is invalidated whenever
    a node it is subscribed to changes; the forward edge set is re-discovered on
    each recompute in the real runtime (dynamic dependencies), which the model
    captures by treating `dependents` as the post-recompute reverse-edge
    snapshot — sufficient for stating the universal invalidation laws. -/
structure Graph where
  node : NodeId → NodeState
  dependents : NodeId → List NodeId   -- source → nodes subscribed to it

/-- A graph is well-formed when no node is its own dependent — the structural
    invariant that lets the invalidation theorems distinguish the writer (cleared
    by a successful recompute) from its downstream subscribers (marked dirty). -/
def Graph.WellFormed (g : Graph) : Prop :=
  ∀ n, n ∉ g.dependents n

/-! ## The Cell kernel partition (`#lzcellkernel`)

The node enumeration is closed: every reactive node is a `source`, a `computed`,
an `effect`, or `disposed`. There is no `Signal` kind — an eager value is a driven
`computed` (a `computed` paired with a puller `effect`), not a fourth constructor.
The value-bearing kinds `source`/`computed` are the two kinds of `Cell` (value
from outside vs. from upstream), surfaced as the `Source`/`Computed` handles;
`effect` is the value-less sink. (v2: `Cell` is the concept, not a `Cell<T, K>`
genus handle.) This section is `lazily-cell-kernel-design.md` §1, §9.2.2, and §3 rendered
as proofs — the design asks the formal model to *confirm these are expressible*. -/

/-- Every node kind is one of exactly four constructors — the closed kernel. In
    particular there is no separate eager/`Signal` kind to dispatch on. -/
theorem node_kind_partition (k : NodeKind) :
    k = .source ∨ k = .computed ∨ k = .effect ∨ k = .disposed := by
  cases k <;> simp

/-- `Cell` (the value-bearing node concept): a node that bears a readable value is
    a `source` or a `computed`. -/
def IsCell (k : NodeKind) : Prop := k = .source ∨ k = .computed

/-- **Writer is a sink (§9.2.2).** The value-less `effect` is not a `Cell`: it
    occupies the sink position, nothing can read it, and a writer — which produces
    no value — is always one. -/
theorem effect_is_the_sink : ¬ IsCell .effect := by simp [IsCell]

/-- Every live node is therefore a `Cell` (value-bearing) or the sink `effect` —
    the §1 partition with both sides covered and no leftover. -/
theorem live_node_is_cell_or_sink (k : NodeKind) (h : k ≠ .disposed) :
    IsCell k ∨ k = .effect := by
  cases k <;> simp_all [IsCell]

/-- **Kind-restricted write protection (§3).** The write capability is exactly the
    `source` kind — `set`/`merge` live on the `Source<T, M>` handle alone.
    This is the property the design asks the formal model to confirm is
    expressible; it is, as a decidable predicate on the kind. -/
def Writable (k : NodeKind) : Prop := k = .source

theorem computed_not_writable : ¬ Writable .computed := by simp [Writable]
theorem effect_not_writable  : ¬ Writable .effect  := by simp [Writable]

/-! ## Unified shared-owner reads (`#lzrsgetarc`)

An ordinary read and a shared-owner read are two result representations of the
same Cell-kernel observation. In Rust the latter is `Context::get_rc`: it avoids
requiring `T : Clone` and, when the value is heap-backed, returns another owner
of the stored allocation. The formal model is intentionally ownership-agnostic,
so it states the portable semantic content:

* both `source` and `computed` are readable through either mode;
* `effect` and `disposed` are not value-bearing and return no value;
* the shared read observes exactly the value the ordinary read observes.

Dirty-computed refresh is modeled by [`recomputeComputed`] before the observation,
just as every other read theorem in this file reasons about the graph state at
the observation boundary. Allocation identity, refcount bumps, and inline-value
fallbacks are language/runtime facts rather than graph semantics. -/

/-- Read the currently materialized value of either Cell kind. This total
    function returns `none` for the value-less sink and disposed arena entries. -/
def readCell (g : Graph) (id : NodeId) : Option Value :=
  match (g.node id).kind with
  | .source | .computed => (g.node id).value
  | .effect | .disposed => none

/-- Shared-owner read at the pure graph layer. The representation is abstracted
    away, leaving the value observation that every binding must preserve. -/
def readShared (g : Graph) (id : NodeId) : Option Value :=
  readCell g id

/-- A shared-owner read is observationally identical to an ordinary read for
    every graph and node. -/
theorem readShared_eq_readCell (g : Graph) (id : NodeId) :
    readShared g id = readCell g id := by
  rfl

/-- The shared read covers the source kind, not only computed values. -/
theorem readShared_source
    (g : Graph) (id : NodeId) (hkind : (g.node id).kind = .source) :
    readShared g id = (g.node id).value := by
  simp [readShared, readCell, hkind]

/-- The same shared read covers the computed kind. -/
theorem readShared_computed
    (g : Graph) (id : NodeId) (hkind : (g.node id).kind = .computed) :
    readShared g id = (g.node id).value := by
  simp [readShared, readCell, hkind]

/-- Effects remain unreadable through the shared read surface. -/
theorem readShared_effect
    (g : Graph) (id : NodeId) (hkind : (g.node id).kind = .effect) :
    readShared g id = none := by
  simp [readShared, readCell, hkind]

/-- Replace a single node's state. -/
def setNode (g : Graph) (id : NodeId) (s : NodeState) : Graph :=
  { g with node := fun n => if n = id then s else g.node n }

/-- Mark node `id` dirty (leaving its other fields intact). -/
def markDirty (g : Graph) (id : NodeId) : Graph :=
  setNode g id { (g.node id) with dirty := true }

/-- Mark every node in `ds` dirty, folding left to right. -/
def markDirtyAll (g : Graph) (ds : List NodeId) : Graph :=
  ds.foldl (fun acc d => markDirty acc d) g

/-! ## Fold-membership lemmas

Universal facts about the `markDirtyAll` fold: a true dirty flag is monotone
(once true, it stays true through the fold); a member gets marked; a non-member
is untouched. -/

/-- `setNode` at `id` leaves a different node `d ≠ id` untouched. -/
theorem setNode_ne {g : Graph} {id : NodeId} (s : NodeState) {d : NodeId}
    (hne : id ≠ d) : (setNode g id s).node d = g.node d := by
  simp only [setNode]
  by_cases h : d = id
  case pos => exact absurd h.symm hne
  case neg => rw [if_neg h]

/-- `setNode` at `id` returns the supplied state at `id`. -/
theorem setNode_eq {g : Graph} {id : NodeId} (s : NodeState) :
    (setNode g id s).node id = s := by simp [setNode]

/-- `markDirty` either sets a node's dirty flag (when applied at that node) or
    leaves it unchanged (when applied elsewhere). In particular, a dirty flag
    already `true` stays `true`. -/
theorem markDirty_at (g : Graph) (x d : NodeId) :
    ((markDirty g x).node d).dirty = true ∨
    ((markDirty g x).node d).dirty = (g.node d).dirty := by
  by_cases heq : x = d
  · subst heq
    left
    simp [markDirty, setNode]
  · right
    rw [markDirty, setNode_ne (s := { (g.node x) with dirty := true }) heq]

/-- Folding `markDirty` over `ds` never lowers a node's dirty flag. -/
theorem markDirtyAll_mono_true (g : Graph) (ds : List NodeId) (d : NodeId)
    (htrue : (g.node d).dirty = true) :
    ((markDirtyAll g ds).node d).dirty = true := by
  induction ds generalizing g with
  | nil => exact htrue
  | cons x xs ih =>
    simp only [markDirtyAll, List.foldl_cons]
    rcases markDirty_at g x d with h | h
    · exact ih (markDirty g x) h
    · exact ih (markDirty g x) (h ▸ htrue)

/-- Folding `markDirty` over a list sets the dirty flag of every member. -/
theorem markDirtyAll_marks_members
    (g : Graph) (ds : List NodeId) (d : NodeId) (hmem : d ∈ ds) :
    ((markDirtyAll g ds).node d).dirty = true := by
  induction ds generalizing g with
  | nil => exact absurd hmem List.not_mem_nil
  | cons x xs ih =>
    show ((markDirtyAll (markDirty g x) xs).node d).dirty = true
    by_cases hxd : x = d
    · -- `x = d`: this step marks `d`; the rest of the fold is monotone-true.
      rw [hxd]
      have hstep : ((markDirty g d).node d).dirty = true := by
        simp [markDirty, setNode]
      exact markDirtyAll_mono_true (markDirty g d) xs d hstep
    · -- `x ≠ d`: this step does not touch `d`; recurse via `xs`.
      have hxs : d ∈ xs := by
        rcases List.mem_cons.mp hmem with hdx | hxs
        · exact absurd hdx.symm hxd
        · exact hxs
      exact ih (markDirty g x) hxs

/-- Folding `markDirty` over `ds` leaves a non-member's whole node state
    unchanged (only `.dirty` of members is touched). -/
theorem markDirtyAll_preserves_nonmember_node
    (g : Graph) (ds : List NodeId) (d : NodeId) (hnmem : d ∉ ds) :
    (markDirtyAll g ds).node d = g.node d := by
  induction ds generalizing g with
  | nil => rfl
  | cons x xs ih =>
    show (markDirtyAll (markDirty g x) xs).node d = g.node d
    have hx : x ≠ d := fun heq => hnmem (heq ▸ List.mem_cons_self)
    have hxs : d ∉ xs := fun hcontra => hnmem (List.mem_cons_of_mem _ hcontra)
    rw [ih (markDirty g x) hxs]
    simp only [markDirty]
    exact setNode_ne (s := { (g.node x) with dirty := true }) hx

/-- Folding `markDirty` over `ds` never touches a node outside `ds`. -/
theorem markDirtyAll_preserves_nonmembers
    (g : Graph) (ds : List NodeId) (d : NodeId) (hnmem : d ∉ ds) :
    ((markDirtyAll g ds).node d).dirty = (g.node d).dirty :=
  congrArg NodeState.dirty (markDirtyAll_preserves_nonmember_node g ds d hnmem)

/-! ## Cell writes — the `PartialEq` guard

The single-writer cell-write primitive (`lazily-rs`: `Source::set` /
`Context::set`). The `PartialEq` guard is the universal "no churn on
equal" guarantee that surfaces on the wire as "equal `set` emits no
`CellSet` and no downstream ops" (`lazily-spec/protocol.md` § Consistency
invariants). -/

/-- `setSource g id v`: the `PartialEq`-guarded cell write. If `id`'s current
    value equals `v`, the graph is returned **unchanged** — no value update, no
    downstream invalidation. Otherwise the value is updated and every direct
    dependent is marked dirty. -/
def setSource (g : Graph) (id : NodeId) (v : Value) : Graph :=
  match (g.node id).value with
  | some cur =>
    if cur = v then g
    else markDirtyAll (setNode g id ⟨.source, some v, none, false⟩) (g.dependents id)
  | none => g   -- not a settable node; no-op

/-- `setSource` of an equal value is the identity on the graph — the formal
    statement of the wire-level "equal `set` emits no `CellSet` and no
    downstream ops" invariant. The whole graph is byte-identical, not just the
    node's value. -/
theorem setSource_equal_preserves_graph
    (g : Graph) (id : NodeId) (cur v : Value)
    (hcur : (g.node id).value = some cur)
    (heq : cur = v) :
    setSource g id v = g := by
  simp [setSource, hcur, heq]

/-- `setSource` of a strictly different value marks every direct dependent dirty. -/
theorem setSource_different_invalidates_dependents
    (g : Graph) (id : NodeId) (cur v : Value)
    (hcur : (g.node id).value = some cur)
    (hne : cur ≠ v)
    (d : NodeId) (hdep : d ∈ g.dependents id) :
    ((setSource g id v).node d).dirty = true := by
  simp only [setSource, hcur, hne, if_false]
  exact markDirtyAll_marks_members _ _ _ hdep

/-! ## Computed recompute — the equality guard

The `ComputedCell` recompute primitive (`lazily-rs`: `ctx.computed` /
`Context::get`). The guard is the universal "no churn on equal recompute"
guarantee that surfaces on the wire as "an equal computed recompute emits no
`SlotValue` and no downstream `Invalidate`". The wire keeps `SlotValue` because
`slot` still names the arena storage position; the formal transition follows the
public handle vocabulary and is therefore `recomputeComputed`. -/

/-- `recomputeComputed g id newVal`: clear `id`'s dirty flag and cache `newVal`.
    If `id` carries an equality guard and `newVal` equals its prior cached
    value, downstream dependents are **not** marked dirty (computed suppression).
    Otherwise every direct dependent is marked dirty. -/
def recomputeComputed (g : Graph) (id : NodeId) (newVal : Value) : Graph :=
  let prior := (g.node id).value
  let suppressed : Bool :=
    match prior, (g.node id).memoEq with
    | some old, some eq => eq old newVal
    | _, _ => false
  let cleared := setNode g id ⟨.computed, some newVal, (g.node id).memoEq, false⟩
  match suppressed with
  | true => cleared
  | false => markDirtyAll cleared (g.dependents id)

/-- Equality suppression: a `computed` that recomputes with its guard
    returning `true` leaves every *downstream* dependent (`d ≠ id`) untouched.
    The universal form of the wire-level "equal computed recompute emits no
    `Invalidate`" invariant. -/
theorem recomputeComputed_equal_preserves_dependents
    (g : Graph) (id : NodeId) (newVal : Value)
    (hsup : (match (g.node id).value, (g.node id).memoEq with
             | some old, some eq => eq old newVal
             | _, _ => false) = true)
    (d : NodeId) (hdne : d ≠ id) :
    ((recomputeComputed g id newVal).node d).dirty = (g.node d).dirty := by
  simp only [recomputeComputed, hsup]
  exact (congrArg NodeState.dirty
          (setNode_ne (s := ⟨.computed, some newVal, (g.node id).memoEq, false⟩) hdne.symm))

/-- A strictly-different recompute (the computed guard, if present, returns `false`)
    marks every direct dependent dirty. -/
theorem recomputeComputed_different_invalidates_dependents
    (g : Graph) (id : NodeId) (newVal : Value)
    (hsup : (match (g.node id).value, (g.node id).memoEq with
             | some old, some eq => eq old newVal
             | _, _ => false) = false)
    (d : NodeId) (hdep : d ∈ g.dependents id) :
    ((recomputeComputed g id newVal).node d).dirty = true := by
  simp only [recomputeComputed, hsup]
  exact markDirtyAll_marks_members _ _ _ hdep

/-! ### `computed_ripple_when` — the custom propagate guard

`memoEq` is an **arbitrary** `Value → Value → Bool`, so the two theorems above
already characterise every kind of guard the surface exposes — they never assume
`memoEq` is `(· = ·)`:

* `computed(f)` installs `memoEq = (· = ·)` (natural equality).
* `computed_ripple_when(f, changed)`
  (`lazily-rs/src/context.rs`, `Context::computed_ripple_when`) installs
  `memoEq = fun old new => ¬ changed old new` — the guard **suppresses** exactly
  when the value did **not** meaningfully change, i.e. propagates iff
  `changed old new`.
* The public surface never constructs a computed with `memoEq = none`: every
  `computed` is guarded. The `none` branch keeps the transition total for
  malformed or legacy graph states and conservatively propagates.

This is the model's evidence that `computed_ripple_when` is a **propagate**
guard, never a compute guard: `recomputeComputed` *receives* `newVal` (the compute
already ran; the predicate needs `new`), and the guard only governs whether the
dependents are marked dirty. `changed` MUST be pure in `(old, new)`; value-carried
state (a version/counter field) is a fine input and keeps the recompute
deterministic. -/

/-- `computed_ripple_when` suppression, stated directly: with the guard
    `memoEq = fun o n => ¬ changed o n`, a recompute whose `changed old newVal`
    is `false` leaves every downstream dependent (`d ≠ id`) untouched. A thin
    specialisation of `recomputeComputed_equal_preserves_dependents`. -/
theorem recomputeComputed_ripple_when_false_preserves_dependents
    (g : Graph) (id : NodeId) (newVal old : Value) (changed : Value → Value → Bool)
    (hval : (g.node id).value = some old)
    (hguard : (g.node id).memoEq = some (fun o n => ! changed o n))
    (hkeep : changed old newVal = false)
    (d : NodeId) (hdne : d ≠ id) :
    ((recomputeComputed g id newVal).node d).dirty = (g.node d).dirty := by
  refine recomputeComputed_equal_preserves_dependents g id newVal ?_ d hdne
  simp only [hval, hguard, hkeep, Bool.not_false]

/-! ## Fortified dependency tracking — edge attribution (`#lzcellkernel`)

A derived cell discovers its dependencies dynamically: a recompute runs the
compute function and records every cell it reads as an edge. The recorded set is
re-bound each recompute (dynamic deps), so the `dependents` snapshot above is
exactly the last recompute's reads.

The runtime attributes each read to *the node being recomputed*. The **fortified
compute view** (`lazily-rs/src/context.rs`, `Compute` — the value-node id
threaded through `ComputeOps`) carries that node id **as a value**, not as an
ambient thread-local, so misattribution is impossible **by construction**: the
node is a parameter of the read, not a mutable ambient that a nested or
post-`await` read could clobber. Model a recompute of `n` as registering an edge
`(dep, n)` for each read `dep`; then every edge is attributed to `n`. -/

/-- A dependency edge `(dependency, dependent)`. -/
abbrev Edge := NodeId × NodeId

/-- The edges the recompute of `n` registers when its compute reads `deps`,
    through the value-threaded compute view: each read attributes to `n`. -/
def registerReads (n : NodeId) (deps : List NodeId) : List Edge :=
  deps.map (fun dep => (dep, n))

/-- **Edge attribution (fortification).** Every dependency edge registered during
    the recompute of `n` has `n` as its dependent. Because the recomputing node
    is a *value* parameter of the compute view (not an ambient carrier that a
    nested / post-`await` read could clobber), this holds by construction — the
    formal counterpart of `lazily-rs`'s non-escapable, sole-surface `Compute`
    and of the spec's edge-attribution invariant (`cell-model.md` §"Dependency
    tracking"). -/
theorem registerReads_dependent_is_recomputing_node
    (n : NodeId) (deps : List NodeId) (e : Edge) (he : e ∈ registerReads n deps) :
    e.2 = n := by
  simp only [registerReads, List.mem_map] at he
  obtain ⟨_dep, _, rfl⟩ := he
  rfl

/-- Edges registered by a typed read. The total formal function rejects the
    non-cell kinds that the concrete handle API makes unrepresentable. -/
def registeredReadEdges (g : Graph) (reader target : NodeId) : List Edge :=
  match (g.node target).kind with
  | .source | .computed => registerReads reader [target]
  | .effect | .disposed => []

/-- Ordinary tracked read: observed value plus the dependency edge attributed
    to the node currently being recomputed. -/
def trackedRead (g : Graph) (reader target : NodeId) : Option Value × List Edge :=
  (readCell g target, registeredReadEdges g reader target)

/-- Shared-owner tracked read. It differs only in result representation at the
    runtime boundary, which this pure model erases. -/
def trackedSharedRead (g : Graph) (reader target : NodeId) : Option Value × List Edge :=
  (readShared g target, registeredReadEdges g reader target)

/-- Shared and ordinary reads have identical value and dependency-tracking
    behavior — in particular, a shared read of a `Source` cannot miss the edge. -/
theorem trackedSharedRead_eq_trackedRead
    (g : Graph) (reader target : NodeId) :
    trackedSharedRead g reader target = trackedRead g reader target := by
  simp [trackedSharedRead, trackedRead, readShared_eq_readCell]

/-- A shared read of either Cell kind registers exactly the edge from the read
    target to the recomputing node. -/
theorem trackedSharedRead_registers_edge
    (g : Graph) (reader target : NodeId)
    (hcell : IsCell (g.node target).kind) :
    (target, reader) ∈ (trackedSharedRead g reader target).2 := by
  rcases hcell with hsource | hcomputed
  · simp [trackedSharedRead, registeredReadEdges, hsource, registerReads]
  · simp [trackedSharedRead, registeredReadEdges, hcomputed, registerReads]

/-! ## Driven computed — eager materialization

A *driven* `computed` (`computed().eager()`, `lazily-rs/src/signal.rs`) is a
`computed` paired with a puller `effect` that re-materializes it immediately after
every invalidation. The universal observable property is that a reader never
observes an unset intermediate state: after the puller runs, the value is
concrete. This is the formal form of the wire-level "changed eager value emits
`SlotValue`, never a bare `Invalidate` for its backing node" invariant.

This is the *graph* half of the claim, and it is all this kernel can state:
`recomputeComputed` receives the new value from its caller, so the model has no notion
of *running* a computation and therefore cannot say that the puller changes only
the timing of compute, nor how many times compute ran. `LazilyFormal.Signal`
re-models the driven computed at that resolution — compute as a function of the
sources, with its invocations counted — and proves the two properties this
section cannot reach: `signal_read_equiv_lazy_memo` (a driven computed and a bare
lazy computed agree on every read under every program) and
`batch_pull_runs_at_most_once` (N batched writes cost one pull, not N). -/

/-- Run the puller: recompute the backing computed to `newVal`. By construction the
    puller runs *immediately* after invalidation (it is itself a dependent
    `effect`), so after [`signalPull`] the backing computed is materialized
    regardless of whether the value changed. -/
def signalPull (g : Graph) (slotId : NodeId) (newVal : Value) : Graph :=
  recomputeComputed g slotId newVal

/-- After the puller runs, the backing computed carries a concrete cached
    value (no `none` / unset intermediate) and is not dirty. This is the
    universal form of the wire invariant "a changed eager value emits
    `SlotValue`, not bare `Invalidate`, for its backing node" — observable at
    every input, not just the fixture-tested ones. Holds under `WellFormed`
    (the computed node is not its own dependent). -/
theorem signal_materialized_after_recompute
    (g : Graph) (slotId : NodeId) (newVal : Value) (hwf : g.WellFormed) :
    ((signalPull g slotId newVal).node slotId).value = some newVal ∧
    ((signalPull g slotId newVal).node slotId).dirty = false := by
  have hnot_self : slotId ∉ g.dependents slotId := hwf slotId
  -- The `cleared` node state at `slotId` is `⟨.computed, some newVal, _, false⟩`;
  -- on both branches (suppressed or not) the dependents fold cannot re-touch
  -- `slotId` itself (no self-edge), so `cleared`'s fields survive.
  have hcleared_value :
      ((setNode g slotId ⟨.computed, some newVal, (g.node slotId).memoEq, false⟩).node slotId).value
        = some newVal :=
    congrArg NodeState.value (setNode_eq _)
  have hcleared_dirty :
      ((setNode g slotId ⟨.computed, some newVal, (g.node slotId).memoEq, false⟩).node slotId).dirty
        = false :=
    congrArg NodeState.dirty (setNode_eq _)
  refine ⟨?_, ?_⟩
  · -- value = some newVal
    simp only [signalPull, recomputeComputed]
    by_cases hsup :
        (match (g.node slotId).value, (g.node slotId).memoEq with
         | some a, some eq => eq a newVal
         | _, _ => false) = true
    case pos => simp only [hsup]; exact hcleared_value
    case neg =>
      simp only [hsup]
      rw [markDirtyAll_preserves_nonmember_node _ _ _ hnot_self]
      exact hcleared_value
  · -- dirty = false
    simp only [signalPull, recomputeComputed]
    by_cases hsup :
        (match (g.node slotId).value, (g.node slotId).memoEq with
         | some a, some eq => eq a newVal
         | _, _ => false) = true
    case pos => simp only [hsup]; exact hcleared_dirty
    case neg =>
      simp only [hsup]
      rw [markDirtyAll_preserves_nonmember_node _ _ _ hnot_self]
      exact hcleared_dirty

/-! ## Disposal and teardown scopes

Explicit teardown (`lazily-rs/src/context.rs`: `Context::dispose_slot`,
`Context::dispose_cell`, `Context::scope` / `TeardownScope`), specified in
`lazily-spec/docs/reactive-graph.md` § "Lifecycle".

Handles are copyable ids, not owners, so dropping every handle to a node
reclaims nothing: without an explicit disposal call the node and its edge on
each dependency survive for the life of the context — unbounded growth in both
memory and propagation cost under subscribe/unsubscribe churn. The model
therefore makes disposal a *graph* operation, not a refcount:

- **Both directions.** `disposeNode` clears the node's own reverse-edge list
  (nothing is subscribed to a dead node) *and* removes it from every other
  node's list (a dead node is subscribed to nothing). Modeling only one
  direction would leave exactly the leak the runtime's
  `remove_dependent_edges_locked` / `remove_dependency_edges_locked` pair
  exists to close.
- **Reading a disposed node is an error.** Modeled by the `.disposed` kind with
  no value: there is no value to observe, so any law phrased over
  `.value = some _` is simply unavailable at a disposed id. The model does not
  encode the *throw*; it fixes the observable state that makes reading
  meaningless.
- **Public disposal is identity-fenced.** `disposeHandle` validates the slot's
  generation and current node kind before calling `disposeNode`. A stale handle
  is an idempotent whole-arena no-op, including the cleanup log. This closes
  same-kind ABA as well as cross-kind recycling; only a matching live `effect`
  may append its cleanup event.
- **A teardown scope is a set and a moment, nothing more.** `Scope` records the
  ids created through it (`TeardownScope.owned`), and `disposeScope` tears the
  whole set down in one pass. The load-bearing theorem is
  [`disposeScope_eq_disposeAll`]: that one pass is *observationally equal* to
  disposing each member individually, so a scope can introduce no disposal
  semantics of its own. Scoping bounds teardown, **not visibility** — the
  model needs no visibility construct to say so, because reads in this model are
  plain `Graph.node` lookups unrestricted by scope, exactly matching "a scope's
  nodes read parent-owned or sibling-owned nodes freely".
- **The scope hazard is the single-disposal hazard.** Since scope teardown *is*
  the fold of single disposals, it inherits the caveat verbatim: ending a scope
  tears down its nodes even if something outside still reads them.

Proved here:

- `disposeNode_detaches_both_directions` — after disposal the id appears in no
  node's dependents list anywhere, and its own list is empty.
- `disposeNode_idempotent` — disposing twice equals disposing once.
- `disposeScope_eq_disposeAll` — scope teardown equals the fold of individual
  disposals (cited by name from `lazily-spec/docs/reactive-graph.md`).
- `disposeAll_preserves_nonmember_node` / `disposeAll_preserves_nonmembers` —
  a node outside the scope keeps its state and its dirty flag.
- `disposeAll_order_independent` — teardown does not depend on the order the
  scope recorded its members.
- `disposeNode_recycled_id_inherits_nothing` — a re-minted node at a disposed
  id starts with an empty reverse-edge set. `dispose_slot` pushes the id onto
  `free_ids`, so a later `computed`/`cell` can land on it; without the edge
  detach above, the fresh node would alias a stale index and inherit
  invalidations meant for its dead predecessor.
- `disposeHandle_stale_noop`, `disposeHandle_generation_mismatch_noop`, and
  `disposeHandle_kind_mismatch_noop` — rejected handles mutate nothing.
- `disposeHandle_matching_effect_runs_cleanup` and
  `disposeHandle_stale_runs_no_cleanup` — cleanup belongs only to the matching
  live effect occupant.
- `disposeHandle_recycled_old_handle_noop` — after a slot is recycled, the old
  generation cannot delete its successor, even when the successor has the same
  node kind.
- `disposeHandle_same_kind_aba_noop` and
  `disposeHandle_cross_kind_recycled_noop` — the two recycling classes named by
  the normative spec are whole-arena no-ops.
- `disposeHandle_generation_mismatch_refines_conformance` and
  `disposeHandle_recycled_old_handle_refines_conformance` — the stronger no-op
  law preserves exactly the successor node/value/kind, reverse edges, and
  cleanup log observed by the executable stale-handle conformance matrix.
- `disposeHandleScope_eq_disposeHandles` and
  `disposeHandles_stale_head_noop` — a scope retains full occupant identities,
  is a reverse-creation-order fold of validated disposals, and skips stale
  members. -/

/-- The cleared arena entry left behind by disposal: no kind of live node, no
    value, no memo guard, not scheduled. -/
def disposedState : NodeState := ⟨.disposed, none, none, false⟩

/-- Tear down node `id`: clear its arena entry and detach its edges in **both**
    directions — its own dependents list is emptied, and it is removed from
    every other node's dependents list. Mirrors `Context::dispose_slot`'s
    `remove_dependent_edges_locked` + `remove_dependency_edges_locked` pair
    (`dispose_cell` is the same operation on a node with no dependencies).

    Removal is by `filter`, not `erase`: a duplicated subscription must not
    survive its subscriber. -/
def disposeNode (g : Graph) (id : NodeId) : Graph where
  node := fun n => if n = id then disposedState else g.node n
  dependents := fun n =>
    if n = id then [] else (g.dependents n).filter (fun d => d != id)

/-! ### Generation- and kind-checked public disposal (`#lzstalehandlespec`)

`disposeNode` above is the trusted graph mutation primitive: it assumes the
caller has already resolved the exact live occupant. Public handles cannot make
that assumption. An arena slot can be recycled, so the handle identity is the
triple `(slot, generation, kind)`. Disposal checks all three fields before it
detaches an edge or runs a cleanup.

The cleanup log makes the effect half observable. It is intentionally outside
`Graph`: cleanups are side effects, while `Graph` remains the pure node/edge
state used by the existing scope proofs. -/

/-- Public identity for one reactive-node occupant. `slot` alone is not an
    identity: recycling keeps the slot but advances `generation`. -/
structure Handle where
  slot : NodeId
  generation : Nat
  kind : NodeKind
  deriving Repr, DecidableEq

/-- Arena authority needed to validate a handle before graph mutation. -/
structure Arena where
  graph : Graph
  generation : NodeId → Nat
  /-- Effect cleanups, in the order in which matching live effects were
      disposed. Non-effects and rejected handles never append here. -/
  cleanupLog : List NodeId

/-- A handle matches exactly one live occupant: generation and kind agree and
    the handle does not name the cleared `disposed` sentinel. -/
def Handle.Matches (h : Handle) (a : Arena) : Prop :=
  h.kind ≠ .disposed ∧
    a.generation h.slot = h.generation ∧
    (a.graph.node h.slot).kind = h.kind

instance (h : Handle) (a : Arena) : Decidable (h.Matches a) := by
  unfold Handle.Matches
  infer_instance

/-- Dispose through a public handle. Validation is sequenced before every
    mutation: a mismatch returns the entire arena unchanged. A successful
    disposal clears/detaches the matching node, advances the slot generation,
    and appends a cleanup event exactly when that occupant is an effect. -/
def disposeHandle (a : Arena) (h : Handle) : Arena :=
  if h.Matches a then
    { graph := disposeNode a.graph h.slot
      generation := fun n => if n = h.slot then a.generation n + 1 else a.generation n
      cleanupLog := if h.kind = .effect then a.cleanupLog ++ [h.slot] else a.cleanupLog }
  else
    a

/-- The complete stale-handle contract: validation failure is an idempotent
    no-op over graph state, generations, and cleanup history. -/
theorem disposeHandle_stale_noop (a : Arena) (h : Handle)
    (stale : ¬ h.Matches a) : disposeHandle a h = a := by
  simp [disposeHandle, stale]

/-- A generation mismatch (including same-kind ABA recycling) cannot delete the
    current occupant or run any cleanup. -/
theorem disposeHandle_generation_mismatch_noop (a : Arena) (h : Handle)
    (stale : a.generation h.slot ≠ h.generation) : disposeHandle a h = a := by
  apply disposeHandle_stale_noop
  intro valid
  exact stale valid.2.1

/-- A cross-kind recycled slot is also rejected before mutation, independently
    of whether its generation representation happened to compare equal. -/
theorem disposeHandle_kind_mismatch_noop (a : Arena) (h : Handle)
    (crossKind : (a.graph.node h.slot).kind ≠ h.kind) : disposeHandle a h = a := by
  apply disposeHandle_stale_noop
  intro valid
  exact crossKind valid.2.2

/-- A matching handle reaches the raw graph primitive and therefore performs
    the normal bidirectional detach. -/
theorem disposeHandle_matching_graph (a : Arena) (h : Handle)
    (valid : h.Matches a) :
    (disposeHandle a h).graph = disposeNode a.graph h.slot := by
  simp [disposeHandle, valid]

/-- Only a matching live effect may run cleanup. -/
theorem disposeHandle_matching_effect_runs_cleanup (a : Arena) (h : Handle)
    (valid : h.Matches a) (effect : h.kind = .effect) :
    (disposeHandle a h).cleanupLog = a.cleanupLog ++ [h.slot] := by
  simp [disposeHandle, valid, effect]

/-- Matching live source/computed disposal changes no cleanup history. -/
theorem disposeHandle_matching_non_effect_runs_no_cleanup (a : Arena) (h : Handle)
    (valid : h.Matches a) (notEffect : h.kind ≠ .effect) :
    (disposeHandle a h).cleanupLog = a.cleanupLog := by
  simp [disposeHandle, valid, notEffect]

/-- Stale effect disposal cannot run the cleanup belonging to a recycled
    occupant. This is a named projection of the whole-arena no-op theorem. -/
theorem disposeHandle_stale_runs_no_cleanup (a : Arena) (h : Handle)
    (stale : ¬ h.Matches a) :
    (disposeHandle a h).cleanupLog = a.cleanupLog := by
  rw [disposeHandle_stale_noop a h stale]

/-- The observable projection exercised by the executable stale-handle
    conformance matrix. `node` equality preserves kind, readability,
    writability, value, and dirty state; `dependents` equality preserves the
    model's complete reverse-edge snapshot; cleanup equality prevents either
    the dead occupant's or the successor's cleanup from running. -/
def Arena.SuccessorObservationPreserved
    (before after : Arena) (successor : NodeId) : Prop :=
  after.graph.node successor = before.graph.node successor ∧
  after.graph.dependents successor = before.graph.dependents successor ∧
  after.cleanupLog = before.cleanupLog

/-- A rejected stale handle preserves every conformance-visible successor
    observation. This is a projection of the stronger whole-arena no-op law. -/
theorem disposeHandle_stale_preserves_successor_observation
    (a : Arena) (h : Handle) (successor : NodeId)
    (stale : ¬ h.Matches a) :
    Arena.SuccessorObservationPreserved a (disposeHandle a h) successor := by
  rw [disposeHandle_stale_noop a h stale]
  exact ⟨rfl, rfl, rfl⟩

/-- The refinement obligation shared by all nine stale-handle-kind ×
    successor-kind conformance scenarios: once occupant generations differ,
    disposal through the old handle preserves the successor node, its reverse
    edges, and cleanup history. -/
theorem disposeHandle_generation_mismatch_refines_conformance
    (a : Arena) (h : Handle) (successor : NodeId)
    (stale : a.generation h.slot ≠ h.generation) :
    Arena.SuccessorObservationPreserved a (disposeHandle a h) successor := by
  apply disposeHandle_stale_preserves_successor_observation
  intro valid
  exact stale valid.2.1

/-- A successful disposal advances the slot generation, making every copy of
    the just-disposed handle stale before that slot can be occupied again. -/
theorem disposeHandle_matching_advances_generation (a : Arena) (h : Handle)
    (valid : h.Matches a) :
    (disposeHandle a h).generation h.slot = a.generation h.slot + 1 := by
  simp [disposeHandle, valid]

/-- Re-mint a node in an already-cleared slot. The current generation is retained;
    it was advanced by the successful disposal that freed the slot. -/
def recycleNode (a : Arena) (slot : NodeId) (fresh : NodeState) : Arena :=
  { a with graph := setNode a.graph slot fresh }

/-- The ABA case, stated end to end: after a matching occupant is disposed and
    its slot is recycled (even to the same kind), the old handle cannot delete
    the successor or run its cleanup. -/
theorem disposeHandle_recycled_old_handle_noop
    (a : Arena) (h : Handle) (fresh : NodeState) (valid : h.Matches a) :
    let recycled := recycleNode (disposeHandle a h) h.slot fresh
    disposeHandle recycled h = recycled := by
  apply disposeHandle_generation_mismatch_noop
  simp [recycleNode, disposeHandle, valid, valid.2.1]

/-- Same-kind ABA, named exactly as the normative disposal contract states it:
    generation fencing makes the old handle a whole-arena no-op even though a
    kind check alone cannot distinguish the successor. -/
theorem disposeHandle_same_kind_aba_noop
    (a : Arena) (h : Handle) (fresh : NodeState) (valid : h.Matches a)
    (_sameKind : fresh.kind = h.kind) :
    let recycled := recycleNode (disposeHandle a h) h.slot fresh
    disposeHandle recycled h = recycled := by
  exact disposeHandle_recycled_old_handle_noop a h fresh valid

/-- Cross-kind recycling is independently fenced by the kind check and leaves
    the whole arena unchanged. -/
theorem disposeHandle_cross_kind_recycled_noop
    (a : Arena) (h : Handle) (fresh : NodeState) (valid : h.Matches a)
    (crossKind : fresh.kind ≠ h.kind) :
    let recycled := recycleNode (disposeHandle a h) h.slot fresh
    disposeHandle recycled h = recycled := by
  apply disposeHandle_kind_mismatch_noop
  simpa [recycleNode, setNode] using crossKind

/-- End-to-end refinement from slot recycling to the executable fixture's
    observations. Because this theorem is polymorphic in both node kinds, it
    discharges the full stale-handle-kind × successor-kind matrix rather than
    enumerating nine logically identical cases. -/
theorem disposeHandle_recycled_old_handle_refines_conformance
    (a : Arena) (h : Handle) (fresh : NodeState) (valid : h.Matches a) :
    let recycled := recycleNode (disposeHandle a h) h.slot fresh
    Arena.SuccessorObservationPreserved
      recycled (disposeHandle recycled h) h.slot := by
  dsimp only
  rw [disposeHandle_recycled_old_handle_noop a h fresh valid]
  exact ⟨rfl, rfl, rfl⟩

/-- Dispose a sequence of public handles. Every member crosses the same
    generation-and-kind validation as an individual disposal. -/
def disposeHandles (a : Arena) (handles : List Handle) : Arena :=
  handles.foldl disposeHandle a

/-- Public teardown-scope membership retains occupant identities, not raw
    recyclable slots. -/
structure HandleScope where
  members : List Handle

/-- End a public teardown scope in reverse creation order so observable effect
    cleanup order is fixed. Graph-state order independence is proved below by
    the raw, already-validated `disposeScope_eq_disposeAll` theorem. -/
def disposeHandleScope (a : Arena) (scope : HandleScope) : Arena :=
  disposeHandles a scope.members.reverse

/-- Scope teardown is exactly a fold of individually validated disposals. -/
theorem disposeHandleScope_eq_disposeHandles (a : Arena) (scope : HandleScope) :
    disposeHandleScope a scope = disposeHandles a scope.members.reverse := rfl

/-- A stale scope member is skipped without changing the arena before the
    remaining members are processed. In particular it cannot delete a node
    that recycled the member's slot before scope teardown. -/
theorem disposeHandles_stale_head_noop
    (a : Arena) (h : Handle) (rest : List Handle) (stale : ¬ h.Matches a) :
    disposeHandles a (h :: rest) = disposeHandles a rest := by
  simp [disposeHandles, disposeHandle_stale_noop a h stale]

/-- Dispose every node in `ids`, folding left to right — the individual-disposal
    baseline that [`disposeScope_eq_disposeAll`] measures scope teardown
    against. Mirrors [`markDirtyAll`]. -/
def disposeAll (g : Graph) (ids : List NodeId) : Graph :=
  ids.foldl (fun acc d => disposeNode acc d) g

/-- Raw graph-state projection of a teardown scope after public
    generation/kind validation has selected the matching live members. Public
    scope membership is `HandleScope`; this id set exists to prove that the
    graph mutation itself is order-independent. -/
structure Scope where
  members : List NodeId

/-- End a teardown scope: clear every member and detach every edge touching a
    member, in one pass. Deliberately *not* defined as a fold, so that
    [`disposeScope_eq_disposeAll`] has content: it is the independent
    "whole set, one moment" reading of scope teardown. -/
def disposeScope (g : Graph) (grp : Scope) : Graph where
  node := fun n => if n ∈ grp.members then disposedState else g.node n
  dependents := fun n =>
    if n ∈ grp.members then []
    else (g.dependents n).filter (fun d => decide (d ∉ grp.members))

/-- Componentwise equality of graphs. -/
theorem Graph.ext' {g h : Graph}
    (hn : g.node = h.node) (hd : g.dependents = h.dependents) : g = h := by
  cases g; cases h; simp_all

/-- Disposal clears the node's arena entry: the id names no live node, so there
    is no value to read. -/
theorem disposeNode_clears_node (g : Graph) (id : NodeId) :
    (disposeNode g id).node id = disposedState := by simp [disposeNode]

/-- Disposal detaches edges in **both** directions: the disposed id occurs in no
    node's dependents list anywhere in the graph, and its own dependents list is
    empty. The pair is what keeps teardown from leaking — one direction alone
    would leave either a dangling subscriber or a dangling subscription. -/
theorem disposeNode_detaches_both_directions (g : Graph) (id : NodeId) :
    (∀ n, id ∉ (disposeNode g id).dependents n) ∧
    (disposeNode g id).dependents id = [] := by
  refine ⟨fun n => ?_, by simp [disposeNode]⟩
  by_cases h : n = id
  · simp [disposeNode, h]
  · simp [disposeNode, h, List.mem_filter]

/-- Disposal is idempotent: a second teardown of the same id is a no-op, so a
    double `dispose` (or a scope whose member list repeats an id) is harmless. -/
theorem disposeNode_idempotent (g : Graph) (id : NodeId) :
    disposeNode (disposeNode g id) id = disposeNode g id := by
  refine Graph.ext' (funext fun n => ?_) (funext fun n => ?_)
  · by_cases h : n = id <;> simp [disposeNode, h]
  · by_cases h : n = id
    · simp [disposeNode, h]
    · simp [disposeNode, h, List.filter_filter]

/-- A member list that is empty leaves the graph untouched. -/
private theorem disposeScope_nil (g : Graph) : disposeScope g ⟨[]⟩ = g := by
  refine Graph.ext' (funext fun n => ?_) (funext fun n => ?_) <;>
    simp [disposeScope]

/-- Peeling one member off a scope teardown is the same as disposing that member
    first and tearing down the rest — the step that turns the one-pass scope
    definition into the individual-disposal fold. -/
private theorem disposeScope_cons (g : Graph) (x : NodeId) (xs : List NodeId) :
    disposeScope g ⟨x :: xs⟩ = disposeScope (disposeNode g x) ⟨xs⟩ := by
  refine Graph.ext' (funext fun n => ?_) (funext fun n => ?_)
  · by_cases hxs : n ∈ xs
    · simp [disposeScope, disposeNode, hxs]
    · by_cases hx : n = x <;> simp [disposeScope, disposeNode, hxs, hx]
  · by_cases hxs : n ∈ xs
    · simp [disposeScope, disposeNode, hxs]
    · by_cases hx : n = x
      · simp [disposeScope, disposeNode, hx]
      · have hcons : n ∉ x :: xs := by simp [hx, hxs]
        simp only [disposeScope, disposeNode, if_neg hcons, if_neg hxs, if_neg hx,
          List.filter_filter]
        refine List.filter_congr fun d _ => ?_
        by_cases hdx : d = x <;> simp [hdx]

/-- **Scope teardown equals the fold of individual disposals.**

    Ending a teardown scope is observationally equal to disposing each of its
    members one at a time: the graphs are identical, node for node and edge for
    edge. A scope therefore introduces *no disposal semantics of its own* — it
    names a set and a moment, and nothing else. Two consequences the spec leans
    on: a scope cannot be safer than single disposal (it inherits the "tears
    down nodes something outside may still read" hazard verbatim), and a binding
    may implement `scope()` as a recorded id list plus a teardown loop without
    changing observable behavior.

    Cited by name from `lazily-spec/docs/reactive-graph.md` § "Lifecycle". -/
theorem disposeScope_eq_disposeAll (g : Graph) (grp : Scope) :
    disposeScope g grp = disposeAll g grp.members := by
  obtain ⟨ms⟩ := grp
  induction ms generalizing g with
  | nil => simpa [disposeAll] using disposeScope_nil g
  | cons x xs ih =>
    show disposeScope g ⟨x :: xs⟩ = disposeAll g (x :: xs)
    rw [disposeScope_cons g x xs, ih (disposeNode g x)]
    rfl

/-- Disposing a scope leaves a node outside it completely untouched: same kind,
    same value, same memo guard, same dirty flag. Mirrors
    [`markDirtyAll_preserves_nonmember_node`].

    Note this is the *node state*. A survivor's reverse-edge list is still
    pruned of disposed members — that pruning is the point of
    [`disposeNode_detaches_both_directions`], not a violation of this law. -/
theorem disposeAll_preserves_nonmember_node
    (g : Graph) (ids : List NodeId) (d : NodeId) (hnmem : d ∉ ids) :
    (disposeAll g ids).node d = g.node d := by
  rw [← disposeScope_eq_disposeAll g ⟨ids⟩]
  simp [disposeScope, hnmem]

/-- A node outside a disposed scope keeps its dirty flag: teardown of a scope
    schedules no work anywhere else. -/
theorem disposeAll_preserves_nonmembers
    (g : Graph) (ids : List NodeId) (d : NodeId) (hnmem : d ∉ ids) :
    ((disposeAll g ids).node d).dirty = (g.node d).dirty :=
  congrArg NodeState.dirty (disposeAll_preserves_nonmember_node g ids d hnmem)

/-- Scope teardown depends only on the *set* of members, not on the order or
    multiplicity in which the scope recorded them. Falls out of
    [`disposeScope_eq_disposeAll`]: the one-pass definition consults membership
    alone, so any two member lists with the same members tear down identically.

    This is what makes `TeardownScope.owned` free to be a plain `Vec` appended in
    creation order: reversing it, deduplicating it, or draining it in any order
    yields the same graph. -/
theorem disposeAll_order_independent
    (g : Graph) (ids ids' : List NodeId) (hmem : ∀ n, n ∈ ids ↔ n ∈ ids') :
    disposeAll g ids = disposeAll g ids' := by
  rw [← disposeScope_eq_disposeAll g ⟨ids⟩, ← disposeScope_eq_disposeAll g ⟨ids'⟩]
  refine Graph.ext' (funext fun n => ?_) (funext fun n => ?_)
  · simp [disposeScope, hmem n]
  · simp only [disposeScope, hmem n]
    by_cases h : n ∈ ids'
    · simp [h]
    · simp only [if_neg h]
      exact List.filter_congr fun d _ => by simp [hmem d]

/-- A recycled id inherits nothing: a node minted at a disposed id starts with
    an empty reverse-edge set.

    `dispose_slot` pushes the id onto `free_ids`, so a later `computed`/`cell`
    can land on exactly this slot. This is the model-level statement of a real
    hazard — a binding that recycles ids without detaching the dead node's edges
    leaves a stale index aliased onto an unrelated node, which then receives
    invalidations meant for its predecessor and, worse, keeps a dead
    subscription list alive. Detaching at disposal time is what makes recycling
    sound. -/
theorem disposeNode_recycled_id_inherits_nothing
    (g : Graph) (id : NodeId) (fresh : NodeState) :
    (setNode (disposeNode g id) id fresh).node id = fresh ∧
    (setNode (disposeNode g id) id fresh).dependents id = [] ∧
    (∀ n, id ∉ (setNode (disposeNode g id) id fresh).dependents n) := by
  refine ⟨setNode_eq _, by simp [setNode, disposeNode], fun n => ?_⟩
  simpa only [setNode] using (disposeNode_detaches_both_directions g id).1 n

/-! ## Staleness discovery: why the hybrid strategy is unsound

Two strategies for making a write observable at transitive depth are both
*correct*, and the family permits either:

- **Eager marking** — a write walks the whole dependent cone and marks every
  transitive node dirty. Reads then trust the flag.
- **Lazy pull** — a write marks little or nothing, and every read refreshes its
  own dependencies recursively before deciding whether to recompute. This is the
  strategy `reactive-graph.md` describes: "On `get`, a computed first refreshes its
  own dependencies (recursively, lazy pull), then recomputes only if any
  dependency actually changed."

`setSource` above implements the second: it marks only *direct* dependents, which
is sufficient precisely because a read is expected to recurse. That is not an
incompleteness in this model — it is the lazy strategy, stated.

**The unsound combination is the hybrid**: mark one level eagerly, *and* let
reads short-circuit on a clean node. Each half is fine; together they lose
writes at depth 2 and beyond, because the mark never reaches the node and the
read never looks past it.

This is not hypothetical. It shipped in two bindings and was found on
2026-07-19 (`lazily-dart` `c91a32a`, `lazily-go` `bdfdbce`). Both tracked async
slot staleness with a revision counter and a `Resolved` state whose read path
returned the cached value directly, while their invalidation handler notified
only the written cell's immediate dependents. A chain `cell -> a -> b` served a
stale `b` indefinitely. The theorem below is that failure, reduced to three
nodes. -/

/-- A read that trusts the dirty flag and does **not** refresh dependencies:
    a clean node serves its cached value. This is the short-circuiting half of
    the hybrid — `AsyncSlotResolved` in `lazily-go`, `AsyncSlotState.resolved`
    in `lazily-dart`. -/
def cachedRead (g : Graph) (id : NodeId) : Option Value :=
  if (g.node id).dirty then none else (g.node id).value

/-- A three-node chain `0 -> 1 -> 2`: a source cell, a computed reading it, and a
    computed reading that computed. Values are seeded consistently with `src = v`. -/
def chain (v : Value) : Graph :=
  { node := fun n =>
      if n = 0 then ⟨.source, some v, none, false⟩
      else if n = 1 then ⟨.computed, some (v + 10), none, false⟩
      else if n = 2 then ⟨.computed, some (v + 110), none, false⟩
      else ⟨.disposed, none, none, false⟩
  , dependents := fun n =>
      if n = 0 then [1] else if n = 1 then [2] else [] }

/-- One-level invalidation reaches the direct dependent. -/
theorem chain_setSource_marks_depth_one :
    (((setSource (chain 1) 0 2).node 1).dirty) = true := by
  decide

/-- **It does not reach depth two.** The transitive dependent stays clean. -/
theorem chain_setSource_leaves_depth_two_clean :
    (((setSource (chain 1) 0 2).node 2).dirty) = false := by
  decide

/-- **The hybrid loses the write.** After a source write, a cache-trusting read
    of the depth-2 node returns the value computed from the *old* source — the
    graph reports `111`, derived from `src = 1`, when `src` is now `2` and the
    consistent answer is `112`.

    This is the whole defect. Under lazy pull the same graph is correct, because
    the read of node 2 would refresh node 1 first and observe the change; under
    eager cone marking it is correct, because node 2 would carry the dirty flag.
    Combining "mark one level" with "trust the flag" is what loses the write, and
    neither half looks wrong in isolation — which is why this shipped twice. -/
theorem hybrid_serves_stale_value_at_depth_two :
    cachedRead (setSource (chain 1) 0 2) 2 = some 111 := by
  decide

/-- Eager marking over the transitive cone repairs it: marking node 1's
    dependents as well leaves nothing clean to serve a stale read. Stated as the
    fix actually applied in both bindings — the invalidation walk continues
    through a dependent slot instead of stopping at it. -/
theorem cone_marking_reaches_depth_two :
    ((markDirtyAll (setSource (chain 1) 0 2) ((chain 1).dependents 1)).node 2).dirty = true := by
  decide

/-- And the repaired graph no longer serves a cached value at depth two — the
    read must recompute rather than answering from cache. -/
theorem cone_marking_refuses_stale_read :
    cachedRead (markDirtyAll (setSource (chain 1) 0 2) ((chain 1).dependents 1)) 2 = none := by
  decide

end LazilyFormal.Reactive
