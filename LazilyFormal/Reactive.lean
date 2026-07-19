/-
! Reactive graph kernel — formal model.

The flat reactive core shared by every lazily binding (`lazily-rs`,
`lazily-py`, `lazily-zig`, `lazily-kt`, `lazily-js`, `lazily-dart`). It models
the `Slot -> Cell -> Signal -> Effect` family documented in
`lazily-spec/protocol.md` § "Consistency invariants" and implemented in
`lazily-rs/src/{context,slot,cell,signal,effect}.rs`.

This is the formal counterpart of the *behavioral core* of the reactive graph:

- node kinds (cell / slot / effect),
- the reverse subscription edge set (`source → its direct dependents`),
- the `PartialEq` cell-write guard,
- the memo-equality suppression guard, and
- the eager-`Signal` materialization invariant.

Like the `StateMachine` kernel, this is the layer whose state changes surface
on the lazily-spec IPC wire as `CellSet` / `SlotValue` / `Invalidate` ops; the
wire linkage itself stays in `lazily-spec`. The model fixes *behavior*, not
wire encoding — values are abstract `Nat` stand-ins, exactly like the rest of
`LazilyFormal`.

Proved here:

- `setCell_equal_preserves_graph` — the `PartialEq` cell-write guard: an equal
  write leaves the whole graph byte-identical (no churn, no downstream
  invalidation). Universal form of the wire-level "equal `set_cell` emits no
  `CellSet` and no downstream ops" invariant.
- `setCell_different_invalidates_dependents` — a strictly-different write marks
  every direct dependent dirty.
- `recomputeSlot_equal_preserves_dependents` — the memo guard: a slot that
  recomputes with its memo guard returning `true` leaves every *downstream*
  dependent untouched.
- `recomputeSlot_different_invalidates_dependents` — a strictly-different
  recompute marks every direct dependent dirty.
- `signal_materialized_after_recompute` — an eager `Signal`'s backing slot is
  always materialized after the puller runs (no observable "unset" intermediate
  state). `Signal = Slot + puller Effect`; universal form of the wire-level
  "changed eager Signal emits `SlotValue`, never bare `Invalidate` for its
  backing slot" invariant.
- `disposeScope_eq_disposeAll` and friends — explicit disposal detaches edges in
  *both* directions, and ending a teardown scope (`scope()`) is observationally
  equal to disposing each member individually. See § "Disposal and teardown
  scopes" below.

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

/-- Kind of a reactive node. A `Signal` is not a separate kind: it is a `slot`
    paired with a puller `effect` (see [`signal_materialized_after_recompute`]),
    exactly as in `lazily-rs/src/signal.rs`. -/
inductive NodeKind where
  | cell     -- a single-writer always-set input value
  | slot     -- a memoized derived value, recomputed lazily on read
  | effect   -- a side-effecting reactive computation that re-runs on invalidation
  | disposed -- a torn-down node: its arena entry is cleared and its id is free
  deriving Repr

/-- The runtime state of one reactive node. Cells carry a concrete value; slots
    carry an optional cached value and an optional memo-equality predicate;
    effects carry a pending flag (modeled by `dirty`). -/
structure NodeState where
  kind : NodeKind
  /-- Cell value, or a slot's last cached value. `none` for a dirty slot or an
      effect (effects have no value of their own). -/
  value : Option Value
  /-- Memo-equality guard for slots: `some eq` suppresses downstream
      invalidation when a recompute yields an equal value (`lazily-rs`'s
      `ctx.memo`). `none` ⇒ every recompute churns downstream. -/
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

The single-writer cell-write primitive (`lazily-rs`: `CellHandle::set` /
`Context::set_cell`). The `PartialEq` guard is the universal "no churn on
equal" guarantee that surfaces on the wire as "equal `set_cell` emits no
`CellSet` and no downstream ops" (`lazily-spec/protocol.md` § Consistency
invariants). -/

/-- `setCell g id v`: the `PartialEq`-guarded cell write. If `id`'s current
    value equals `v`, the graph is returned **unchanged** — no value update, no
    downstream invalidation. Otherwise the value is updated and every direct
    dependent is marked dirty. -/
def setCell (g : Graph) (id : NodeId) (v : Value) : Graph :=
  match (g.node id).value with
  | some cur =>
    if cur = v then g
    else markDirtyAll (setNode g id ⟨.cell, some v, none, false⟩) (g.dependents id)
  | none => g   -- not a settable node; no-op

/-- `setCell` of an equal value is the identity on the graph — the formal
    statement of the wire-level "equal `set_cell` emits no `CellSet` and no
    downstream ops" invariant. The whole graph is byte-identical, not just the
    node's value. -/
theorem setCell_equal_preserves_graph
    (g : Graph) (id : NodeId) (cur v : Value)
    (hcur : (g.node id).value = some cur)
    (heq : cur = v) :
    setCell g id v = g := by
  simp [setCell, hcur, heq]

/-- `setCell` of a strictly different value marks every direct dependent dirty. -/
theorem setCell_different_invalidates_dependents
    (g : Graph) (id : NodeId) (cur v : Value)
    (hcur : (g.node id).value = some cur)
    (hne : cur ≠ v)
    (d : NodeId) (hdep : d ∈ g.dependents id) :
    ((setCell g id v).node d).dirty = true := by
  simp only [setCell, hcur, hne, if_false]
  exact markDirtyAll_marks_members _ _ _ hdep

/-! ## Slot recompute — the memo-equality guard

The memoized-slot recompute primitive (`lazily-rs`: `ctx.memo` /
`Context::get`). The memo guard is the universal "no churn on equal recompute"
guarantee that surfaces on the wire as "an equal memo recompute emits no
`SlotValue` and no downstream `Invalidate`". -/

/-- `recomputeSlot g id newVal`: clear `id`'s dirty flag and cache `newVal`.
    If `id` carries a memo-equality guard and `newVal` equals its prior cached
    value, downstream dependents are **not** marked dirty (memo suppression).
    Otherwise every direct dependent is marked dirty. -/
def recomputeSlot (g : Graph) (id : NodeId) (newVal : Value) : Graph :=
  let prior := (g.node id).value
  let suppressed : Bool :=
    match prior, (g.node id).memoEq with
    | some old, some eq => eq old newVal
    | _, _ => false
  let cleared := setNode g id ⟨.slot, some newVal, (g.node id).memoEq, false⟩
  match suppressed with
  | true => cleared
  | false => markDirtyAll cleared (g.dependents id)

/-- Memo-equality suppression: a slot that recomputes with its memo guard
    returning `true` leaves every *downstream* dependent (`d ≠ id`) untouched.
    The universal form of the wire-level "equal memo recompute emits no
    `Invalidate`" invariant. -/
theorem recomputeSlot_equal_preserves_dependents
    (g : Graph) (id : NodeId) (newVal : Value)
    (hsup : (match (g.node id).value, (g.node id).memoEq with
             | some old, some eq => eq old newVal
             | _, _ => false) = true)
    (d : NodeId) (hdne : d ≠ id) :
    ((recomputeSlot g id newVal).node d).dirty = (g.node d).dirty := by
  simp only [recomputeSlot, hsup]
  exact (congrArg NodeState.dirty
          (setNode_ne (s := ⟨.slot, some newVal, (g.node id).memoEq, false⟩) hdne.symm))

/-- A strictly-different recompute (the memo guard, if present, returns `false`)
    marks every direct dependent dirty. -/
theorem recomputeSlot_different_invalidates_dependents
    (g : Graph) (id : NodeId) (newVal : Value)
    (hsup : (match (g.node id).value, (g.node id).memoEq with
             | some old, some eq => eq old newVal
             | _, _ => false) = false)
    (d : NodeId) (hdep : d ∈ g.dependents id) :
    ((recomputeSlot g id newVal).node d).dirty = true := by
  simp only [recomputeSlot, hsup]
  exact markDirtyAll_marks_members _ _ _ hdep

/-! ## Signal — eager materialization

A `Signal` (`lazily-rs/src/signal.rs`) is a memoized slot paired with a puller
effect that re-materializes the slot immediately after every invalidation. The
universal observable property is that a reader of a signal never observes an
unset intermediate state: after the puller runs, the backing slot's value is
concrete. This is the formal form of the wire-level "changed eager Signal emits
`SlotValue`, never a bare `Invalidate` for its backing slot" invariant. -/

/-- Run the signal's puller: recompute the backing slot to `newVal`. By
    construction the puller runs *immediately* after invalidation (it is itself
    a dependent), so after [`signalPull`] the backing slot is materialized
    regardless of whether the value changed. -/
def signalPull (g : Graph) (slotId : NodeId) (newVal : Value) : Graph :=
  recomputeSlot g slotId newVal

/-- After the signal puller runs, the backing slot carries a concrete cached
    value (no `none` / unset intermediate) and is not dirty. This is the
    universal form of the wire invariant "a changed eager Signal emits
    `SlotValue`, not bare `Invalidate`, for its backing slot" — observable at
    every input, not just the fixture-tested ones. Holds under `WellFormed`
    (the signal slot is not its own dependent). -/
theorem signal_materialized_after_recompute
    (g : Graph) (slotId : NodeId) (newVal : Value) (hwf : g.WellFormed) :
    ((signalPull g slotId newVal).node slotId).value = some newVal ∧
    ((signalPull g slotId newVal).node slotId).dirty = false := by
  have hnot_self : slotId ∉ g.dependents slotId := hwf slotId
  -- The `cleared` node state at `slotId` is `⟨.slot, some newVal, _, false⟩`;
  -- on both branches (suppressed or not) the dependents fold cannot re-touch
  -- `slotId` itself (no self-edge), so `cleared`'s fields survive.
  have hcleared_value :
      ((setNode g slotId ⟨.slot, some newVal, (g.node slotId).memoEq, false⟩).node slotId).value
        = some newVal :=
    congrArg NodeState.value (setNode_eq _)
  have hcleared_dirty :
      ((setNode g slotId ⟨.slot, some newVal, (g.node slotId).memoEq, false⟩).node slotId).dirty
        = false :=
    congrArg NodeState.dirty (setNode_eq _)
  refine ⟨?_, ?_⟩
  · -- value = some newVal
    simp only [signalPull, recomputeSlot]
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
    simp only [signalPull, recomputeSlot]
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
  invalidations meant for its dead predecessor. -/

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

/-- Dispose every node in `ids`, folding left to right — the individual-disposal
    baseline that [`disposeScope_eq_disposeAll`] measures scope teardown
    against. Mirrors [`markDirtyAll`]. -/
def disposeAll (g : Graph) (ids : List NodeId) : Graph :=
  ids.foldl (fun acc d => disposeNode acc d) g

/-- A teardown scope (`TeardownScope`): the ids created through it. It records
    *only* ids — the node kinds are read back from the graph at teardown — which
    is why the scope needs no disposal logic of its own. -/
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

/-! ## Observers: `on_write` delivery (`#lzdartobservercow`)

An **observer** is an out-of-band callback list hanging off a single cell. It is
*not* a node in the graph and has no dependency edges, which is what separates it
from an `Effect` — and the separation is observable, not merely structural.

The normative clause (`reactive-graph.md`, "Delivery is per write") is that each
write passing the `==` store-guard invokes every live registration exactly once,
**at the moment of the write, whatever the batch depth**. A `batch` does not
coalesce observer delivery.

The model below makes that falsifiable by recording invocations in a log, so a
coalescing implementation is not merely "different" but provably produces a
shorter log. The payoff is `observers_count_writes_effects_count_settles`: over a
run of writes, the observer log grows linearly while a dependent's `dirty` flag
saturates. That is the formal content of "an observer is a function of the write
*sequence*; an effect is a function of the settled *state*." -/

/-- One observer invocation: the cell written, and the value it was set to. -/
abbrev ObsLog := List (NodeId × Value)

/-- A graph plus observer registrations and the invocation log. `obs id` is the
    number of live registrations on cell `id`; the contract fixes only how many
    invocations a write produces, never how the collection is represented. -/
structure OGraph where
  graph : Graph
  obs : NodeId → Nat
  log : ObsLog

/-- A write under the observer contract. The store-guard is checked first and is
    **not** suspended inside a batch: writing the value a cell already holds is
    not a write, so it neither invalidates nor notifies. Otherwise the cell is
    set and every live registration is appended to the log, in one block per
    write — registration order within a write is fixed by the *firing order*
    clause and is not what this model is about. -/
def onWrite (og : OGraph) (id : NodeId) (v : Value) : OGraph :=
  match (og.graph.node id).value with
  | some cur =>
    if cur = v then og
    else { graph := setCell og.graph id v
         , obs := og.obs
         , log := og.log ++ List.replicate (og.obs id) (id, v) }
  | none => og

/-- Apply a sequence of writes, left to right. A `batch` is exactly this: a
    grouping of writes with no delivery semantics of its own. -/
def applyWrites (og : OGraph) (ws : List (NodeId × Value)) : OGraph :=
  ws.foldl (fun acc w => onWrite acc w.1 w.2) og

/-- **Batching is not a delivery boundary.** Splitting a run of writes into two
    groups — which is all a `batch`, or a nested `batch`, does to a write
    sequence — produces exactly the same state and exactly the same log. This is
    the formal statement of "delivery is per write, whatever the batch depth":
    batch structure is invisible to observers by construction, so no batch depth
    or nesting arrangement can coalesce anything. -/
theorem applyWrites_append (og : OGraph) (ws1 ws2 : List (NodeId × Value)) :
    applyWrites og (ws1 ++ ws2) = applyWrites (applyWrites og ws1) ws2 := by
  simp [applyWrites, List.foldl_append]

/-- The store-guard survives inside a batch: an equal write logs nothing and
    leaves the whole `OGraph` untouched. -/
theorem onWrite_equal_no_delivery
    (og : OGraph) (id : NodeId) (cur v : Value)
    (hcur : (og.graph.node id).value = some cur)
    (heq : cur = v) :
    onWrite og id v = og := by
  simp [onWrite, hcur, heq]

/-- A changing write delivers to every live registration exactly once. -/
theorem onWrite_different_delivers_once
    (og : OGraph) (id : NodeId) (cur v : Value)
    (hcur : (og.graph.node id).value = some cur)
    (hne : cur ≠ v) :
    (onWrite og id v).log = og.log ++ List.replicate (og.obs id) (id, v) := by
  simp [onWrite, hcur, hne]

/-- `markDirtyAll` only ever sets `dirty`, so every node's *value* survives the
    fold. Needed to chain two writes: the second write's store-guard reads the
    value the first one committed. -/
theorem markDirtyAll_preserves_value (g : Graph) (ds : List NodeId) (n : NodeId) :
    ((markDirtyAll g ds).node n).value = (g.node n).value := by
  induction ds generalizing g with
  | nil => rfl
  | cons x xs ih =>
    have hstep : markDirtyAll g (x :: xs) = markDirtyAll (markDirty g x) xs := by
      simp [markDirtyAll]
    rw [hstep, ih (markDirty g x)]
    simp only [markDirty, setNode]
    by_cases h : n = x
    · subst h; simp
    · simp [h]

/-- Chaining lemma: after `setCell` commits `v`, the cell reads back as `v`. -/
theorem setCell_commits_value
    (g : Graph) (id : NodeId) (cur v : Value)
    (hcur : (g.node id).value = some cur) (hne : cur ≠ v) :
    ((setCell g id v).node id).value = some v := by
  simp only [setCell, hcur, if_neg hne]
  rw [markDirtyAll_preserves_value]
  simp [setNode]

/-- A changing `setCell` leaves an already-dirty node dirty, provided it is not
    the written cell itself (the write clears the writer's own flag). -/
theorem setCell_preserves_dirty_of_ne
    (g : Graph) (id d : NodeId) (cur v : Value)
    (hcur : (g.node id).value = some cur) (hne : cur ≠ v) (hd : d ≠ id)
    (hdirty : (g.node d).dirty = true) :
    ((setCell g id v).node d).dirty = true := by
  simp only [setCell, hcur, if_neg hne]
  exact markDirtyAll_mono_true _ _ d (by simpa [setNode, hd] using hdirty)

/-- **The discriminating theorem.** Two distinct writes to one cell — the shape
    of `batch { set 3; set 4 }` — deliver `2 * obs id` invocations, not
    `obs id`. A coalescing implementation produces the latter, so this is the
    proposition that fails against `lazily-py` at the time of writing and holds
    for `lazily-dart`, `lazily-go`, and `lazily-zig`.

    Stated on log *length* deliberately: the clause is about how many times a
    callback runs, and length is exactly that, independent of how any binding
    represents its collection. -/
theorem two_distinct_writes_deliver_twice
    (og : OGraph) (id : NodeId) (v0 v1 v2 : Value)
    (hcur : (og.graph.node id).value = some v0)
    (h01 : v0 ≠ v1) (h12 : v1 ≠ v2) :
    (applyWrites og [(id, v1), (id, v2)]).log.length
      = og.log.length + 2 * og.obs id := by
  have hset := setCell_commits_value og.graph id v0 v1 hcur h01
  simp only [applyWrites, List.foldl_cons, List.foldl_nil, onWrite, hcur,
    if_neg h01, hset, if_neg h12, List.length_append, List.length_replicate]
  omega

/-- **Observers count writes; effects count settles.**

    Over the same run of `n` distinct writes, the observer log grows by
    `n * obs id` while a dependent's `dirty` flag is merely `true` — it was set
    by the first write and saturates. That asymmetry is not an implementation
    detail to be optimized away: it is the entire reason both mechanisms exist.
    An `Effect` cannot report intermediate transitions because `dirty` is a
    `Bool` and cannot count; an observer cannot report the settled value because
    it has already fired by the time the cone settles.

    So neither is a cheaper spelling of the other, and a binding that coalesces
    observer delivery has not optimized its observers — it has deleted the only
    capability that distinguishes them from effects. -/
theorem observers_count_writes_effects_count_settles
    (og : OGraph) (id : NodeId) (d : NodeId) (v0 v1 v2 : Value)
    (hcur : (og.graph.node id).value = some v0)
    (h01 : v0 ≠ v1) (h12 : v1 ≠ v2)
    (hd : d ≠ id)
    (hdirty : ((setCell og.graph id v1).node d).dirty = true) :
    (applyWrites og [(id, v1), (id, v2)]).log.length
        = og.log.length + 2 * og.obs id
      ∧ (((applyWrites og [(id, v1), (id, v2)]).graph).node d).dirty = true := by
  refine ⟨two_distinct_writes_deliver_twice og id v0 v1 v2 hcur h01 h12, ?_⟩
  have hset := setCell_commits_value og.graph id v0 v1 hcur h01
  have hgraph : (applyWrites og [(id, v1), (id, v2)]).graph
      = setCell (setCell og.graph id v1) id v2 := by
    simp only [applyWrites, List.foldl_cons, List.foldl_nil, onWrite, hcur,
      if_neg h01, hset, if_neg h12]
  rw [hgraph]
  exact setCell_preserves_dirty_of_ne _ id d v1 v2 hset h12 hd hdirty

end LazilyFormal.Reactive
