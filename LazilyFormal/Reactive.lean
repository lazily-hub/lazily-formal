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

end LazilyFormal.Reactive
