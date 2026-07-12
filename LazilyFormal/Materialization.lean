/-
! Materialization — formal model (caller-provided recipe; eager default / lazy opt-in).

`lazily-spec/cell-model.md` § "Materialization" fixes an axis orthogonal to cell
*kind*: **when a derived cell's backing node is allocated**, not what it computes.
Materialization is a **caller-provided recipe** — a keyed collection plus a per-key
factory whose *return type* is the choice: an **input cell** or eager **signal**
(always materialized) vs a lazy **slot** (`SlotHandle`, allocated on first observe).
It is *not* a bespoke primitive: it is simply what `SlotMap` (a
`ReactiveMap<K, V, H>` specialization) does, and what conforms is the observable
behavior below, not any type. (This recipe framing exists because pinning a *type* let one binding —
`lazily-zig`'s spreadsheet benchmark — diverge; pinning the *behavior* here and in
the fixtures is what keeps implementations convergent.)

Entry *kind* (`EntryKind.cell` / `EntryKind.slot`, below) is the handle-kind axis,
orthogonal to `Mode`: choosing lazy defers only `slot` entries, never `cell` ones
(`cell_entries_materialized_in_every_mode`). Two choices govern the derived (`slot`)
entries:

- **Eager (default)** — every derived node is allocated at build time (the shared
  high-performance core; a read is a direct node access).
- **Lazy (opt-in)** — a derived node is allocated on its *first observe* ("materialize
  on pull"), keyed rather than handle-addressed; never-observed derived cells are
  never allocated. Lazy is a keyed overlay on the eager core, not a second engine.

This module fixes the *contract* that lets the two coexist: materialization is
**observationally transparent** — it changes allocation timing and memory, never
observed values. That is the property no finite fixture suite can establish, and the
one an implementation must not violate when it offers an opt-in lazy factory.

Like the rest of `LazilyFormal`, values are abstract `Nat` stand-ins: the model
fixes *when materialization happens*, not how a value is computed. A `Spec` fixes
each node's canonical fully-evaluated value (`val`) and whether it is an input
cell (`isInput`, always materialized) or a derived slot (materialized eagerly or
lazily). `observe` models a read: it materializes the node if absent (the lazy
pull), then returns its stored value — a warm read returns the cached value, a
cold read computes and caches it.

Proved here:

- `observe_canonical` — a read yields the node's spec value under **either** mode:
  `observe (build mode spec) id = spec.val id`. The headline transparency law.
- `eager_lazy_observationally_equivalent` / `observe_mode_independent` — the value
  read from a node is independent of the materialization mode. Opting into lazy
  never changes an observed value.
- `materialize_preserves_observe` — materializing one node never changes another
  node's observed value (no churn from allocation).
- `materialize_present_monotone` / `lazy_present_subset_eager` — lazy only *grows*
  the materialized set (deferral, not de-allocation); the lazy set is a subset of
  the eager set (the memory-dominance direction).
- `eager_materializes_all` / `lazy_defers_slots` — eager allocates every node up
  front; lazy leaves an unread derived cell unallocated (the memory / first-touch
  advantage).
- `default_mode_eager` — the default mode is eager.

The `Canonical` invariant (a materialized node's cache equals its spec value)
carries the correctness of the warm-read cache through `materialize`, so the
transparency laws hold for cached reads, not only freshly-computed ones.
-/

namespace LazilyFormal.Materialization

/-- Abstract reactive node identifier (a keyed address or `SlotId`). -/
abbrev NodeId := Nat

/-- Abstract node payload — the model exercises equality of *values*, never their
    type, so a `Nat` stand-in suffices (as elsewhere in `LazilyFormal`). -/
abbrev Value := Nat

/-- Materialization strategy for derived (slot) nodes. `eager` is the shared core
    and the required default; `lazy` is the opt-in keyed overlay. -/
inductive Mode where
  | eager
  | lazy
  deriving Repr, DecidableEq

/-- The default materialization mode. Implementations MUST default to eager. -/
def Mode.default : Mode := Mode.eager

/-- The two entry kinds a `SlotMap` holds. A `cell` entry is an input
    (`CellHandle`) — always materialized, its value set directly. A `slot` entry
    is derived (`SlotHandle`) — materialized eagerly or lazily per `Mode`. This is
    the handle-kind axis the Rust `ReactiveMap<K, V, H>` abstracts over, kept
    orthogonal to `Mode`. -/
inductive EntryKind where
  | cell
  | slot
  deriving Repr, DecidableEq

/-- The static description of a graph: each node's canonical fully-evaluated value
    and whether it is an input cell (always materialized) or a derived slot. -/
structure Spec where
  /-- The canonical, fully-evaluated value of every node. -/
  val : NodeId → Value
  /-- `true` for an input cell (materialized in every mode), `false` for a derived
      slot (materialized eagerly, or lazily on first read). -/
  isInput : NodeId → Bool

/-- A node's `SlotMap` entry kind: input cells are `cell`, derived slots
    are `slot`. This is `isInput` read as the handle-kind axis. -/
def Spec.kind (s : Spec) (id : NodeId) : EntryKind :=
  if s.isInput id then EntryKind.cell else EntryKind.slot

/-- Runtime materialization state: which nodes are currently allocated
    (`present`) and the value cached at each. A node with `present = false` has
    not been allocated yet — the lazy "never touched" case. -/
structure Mat where
  present : NodeId → Bool
  stored : NodeId → Value

/-- A materialization state is **canonical** when every currently-present node
    caches its spec value. This is the cache-correctness invariant that makes a
    warm (cached) read observationally identical to a cold (computed) read. -/
def Canonical (s : Spec) (m : Mat) : Prop :=
  ∀ n, m.present n = true → m.stored n = s.val n

/-- Eager build: allocate every node with its canonical value up front. -/
def buildEager (s : Spec) : Mat :=
  { present := fun _ => true, stored := s.val }

/-- Lazy build: allocate only input cells; derived slots start unmaterialized.
    An absent slot's `stored` slot holds a junk default until first read. -/
def buildLazy (s : Spec) : Mat :=
  { present := s.isInput
  , stored := fun n => if s.isInput n = true then s.val n else 0 }

/-- Build a graph under the chosen materialization mode. -/
def build : Mode → Spec → Mat
  | Mode.eager, s => buildEager s
  | Mode.lazy, s => buildLazy s

/-- Materialize `id`: if already present, return unchanged (a warm read); else
    allocate it and cache its canonical value (the lazy pull on first read). -/
def materialize (s : Spec) (m : Mat) (id : NodeId) : Mat :=
  if m.present id = true then m
  else
    { present := fun n => if n = id then true else m.present n
    , stored := fun n => if n = id then s.val n else m.stored n }

/-- Observe a node: a read materializes it if absent (the lazy pull), then returns
    the cached value. Warm reads return the cache; cold reads compute and cache. -/
def observe (s : Spec) (m : Mat) (id : NodeId) : Value :=
  (materialize s m id).stored id

/-! ## The default is eager -/

/-- The default materialization mode is eager. -/
theorem default_mode_eager : Mode.default = Mode.eager := rfl

/-! ## Build states are canonical -/

theorem buildEager_canonical (s : Spec) : Canonical s (buildEager s) := by
  intro n _; rfl

theorem buildLazy_canonical (s : Spec) : Canonical s (buildLazy s) := by
  intro n hn
  have hin : s.isInput n = true := hn
  show (if s.isInput n = true then s.val n else 0) = s.val n
  rw [if_pos hin]

/-- A graph built under any mode starts canonical. -/
theorem build_canonical (s : Spec) (mode : Mode) : Canonical s (build mode s) := by
  cases mode
  · exact buildEager_canonical s
  · exact buildLazy_canonical s

/-! ## Materialization preserves canonicity and self-reads -/

/-- Materializing a node preserves the cache-correctness invariant. -/
theorem materialize_canonical (s : Spec) (m : Mat) (id : NodeId)
    (hc : Canonical s m) : Canonical s (materialize s m id) := by
  unfold materialize
  by_cases hp : m.present id = true
  · rw [if_pos hp]; exact hc
  · rw [if_neg hp]
    intro n hn
    by_cases hnid : n = id
    · show (if n = id then s.val n else m.stored n) = s.val n
      rw [if_pos hnid]
    · show (if n = id then s.val n else m.stored n) = s.val n
      have hn' : m.present n = true := by
        have : (if n = id then true else m.present n) = true := hn
        rwa [if_neg hnid] at this
      rw [if_neg hnid]; exact hc n hn'

/-- After materializing `id`, its cache holds the canonical value. -/
theorem materialize_stored_self (s : Spec) (m : Mat) (id : NodeId)
    (hc : Canonical s m) : (materialize s m id).stored id = s.val id := by
  unfold materialize
  by_cases hp : m.present id = true
  · rw [if_pos hp]; exact hc id hp
  · rw [if_neg hp]
    show (if id = id then s.val id else m.stored id) = s.val id
    rw [if_pos rfl]

/-! ## Observational transparency — the headline laws -/

/-- A read yields the node's canonical value, from any canonical state. -/
theorem observe_eq_val_of_canonical (s : Spec) (m : Mat) (hc : Canonical s m)
    (id : NodeId) : observe s m id = s.val id :=
  materialize_stored_self s m id hc

/-- **Headline transparency law.** A read yields the node's spec value under
    *either* materialization mode — eager or lazy. Choosing lazy does not change
    what a read observes; it only changes when the node was allocated. -/
theorem observe_canonical (s : Spec) (mode : Mode) (id : NodeId) :
    observe s (build mode s) id = s.val id :=
  observe_eq_val_of_canonical s (build mode s) (build_canonical s mode) id

/-- Eager and lazy are observationally equivalent: identical read values. -/
theorem eager_lazy_observationally_equivalent (s : Spec) (id : NodeId) :
    observe s (build Mode.eager s) id = observe s (build Mode.lazy s) id := by
  rw [observe_canonical s Mode.eager id, observe_canonical s Mode.lazy id]

/-- The observed value of a node is independent of the materialization mode. -/
theorem observe_mode_independent (s : Spec) (m₁ m₂ : Mode) (id : NodeId) :
    observe s (build m₁ s) id = observe s (build m₂ s) id := by
  rw [observe_canonical s m₁ id, observe_canonical s m₂ id]

/-- **No churn from allocation.** Materializing one node never changes another
    node's observed value. -/
theorem materialize_preserves_observe (s : Spec) (m : Mat) (hc : Canonical s m)
    (id other : NodeId) :
    observe s (materialize s m id) other = observe s m other := by
  rw [observe_eq_val_of_canonical s (materialize s m id)
        (materialize_canonical s m id hc) other,
      observe_eq_val_of_canonical s m hc other]

/-! ## Deferral, not de-allocation — the memory laws -/

/-- Lazy materialization only *grows* the present set: a materialized node is
    never silently dropped. -/
theorem materialize_present_monotone (s : Spec) (m : Mat) (id n : NodeId)
    (h : m.present n = true) : (materialize s m id).present n = true := by
  unfold materialize
  by_cases hp : m.present id = true
  · rw [if_pos hp]; exact h
  · rw [if_neg hp]
    show (if n = id then true else m.present n) = true
    by_cases hnid : n = id
    · rw [if_pos hnid]
    · rw [if_neg hnid]; exact h

/-- Eager allocates every node up front. -/
theorem eager_materializes_all (s : Spec) (id : NodeId) :
    (build Mode.eager s).present id = true := rfl

/-- Lazy leaves an unread derived slot unallocated — the memory / first-touch
    advantage: a 10M-cell workbook whose slots are never read costs O(inputs). -/
theorem lazy_defers_slots (s : Spec) (id : NodeId)
    (hslot : s.isInput id = false) : (build Mode.lazy s).present id = false :=
  hslot

/-- The lazy present set is a subset of the eager present set (eager dominates on
    what is allocated). Stated as the membership direction. -/
theorem lazy_present_subset_eager (s : Spec) (id : NodeId)
    (_h : (build Mode.lazy s).present id = true) :
    (build Mode.eager s).present id = true := rfl

/-! ## Entry kind is orthogonal to materialization mode -/

/-- A `cell` (input) entry is materialized under **either** mode — the formal
    statement that a `SlotMap`'s entry *kind* is orthogonal to its
    materialization *mode*. Choosing lazy defers only `slot` (derived) entries;
    a `cell` (input) entry is always present, eager or lazy. -/
theorem cell_entries_materialized_in_every_mode (s : Spec) (mode : Mode) (id : NodeId)
    (hcell : s.kind id = EntryKind.cell) : (build mode s).present id = true := by
  have hin : s.isInput id = true := by
    by_cases h : s.isInput id = true
    · exact h
    · simp [Spec.kind, h] at hcell
  cases mode
  · rfl
  · exact hin

/-- Conversely, an unread `slot` (derived) entry is deferred under lazy — the
    memory advantage restated on the entry-kind axis. -/
theorem slot_entries_deferred_under_lazy (s : Spec) (id : NodeId)
    (hslot : s.kind id = EntryKind.slot) : (build Mode.lazy s).present id = false := by
  have hin : s.isInput id = false := by
    cases hb : s.isInput id with
    | false => rfl
    | true => simp [Spec.kind, hb] at hslot
  exact hin

/-! ## Thread-safe flavor — materialization confluence

The `ThreadSafeSlotMap` (`Arc<Mutex<..>>`-backed) shares this exact abstract
model: its per-key `materialize` is the same operation, only serialized by a mutex.
A mutex admits a concurrent workload as *some* sequential order of the per-key
materializations. What makes that safe — what lets a `Send + Sync` map serve
observations from any thread with no per-key locking of the value axis — is that
materialization is **confluent**: the present set and every observed value are
independent of the order in which keys are materialized. These theorems prove that
order-independence, so the thread-safe map is observationally identical to the
single-threaded `SlotMap` regardless of interleaving. -/

/-- A node is present after materializing `a` iff it was the target `a` or was
    already present. Independent of whether `a` had been materialized before —
    the union characterization that drives order-independence. -/
theorem materialize_present_iff (s : Spec) (m : Mat) (a n : NodeId) :
    (materialize s m a).present n = true ↔ (n = a ∨ m.present n = true) := by
  unfold materialize
  by_cases hp : m.present a = true
  · rw [if_pos hp]
    apply Iff.intro
    · intro h; exact Or.inr h
    · intro h
      cases h with
      | inl hna => rw [hna]; exact hp
      | inr hn => exact hn
  · rw [if_neg hp]
    show (if n = a then true else m.present n) = true ↔ (n = a ∨ m.present n = true)
    by_cases hna : n = a
    · rw [if_pos hna]
      exact Iff.intro (fun _ => Or.inl hna) (fun _ => rfl)
    · rw [if_neg hna]
      apply Iff.intro
      · intro h; exact Or.inr h
      · intro h
        cases h with
        | inl h' => exact absurd h' hna
        | inr h' => exact h'

/-- **Present-set confluence.** Materializing `a` then `b` allocates the same set
    of nodes as `b` then `a` — the present set does not depend on order. This is
    the structural justification for mutex-serialized concurrent materialization:
    whatever order the lock admits, the allocated set is identical. -/
theorem materialize_present_comm (s : Spec) (m : Mat) (a b n : NodeId) :
    (materialize s (materialize s m a) b).present n = true
      ↔ (materialize s (materialize s m b) a).present n = true := by
  rw [materialize_present_iff s (materialize s m a) b n,
      materialize_present_iff s m a n,
      materialize_present_iff s (materialize s m b) a n,
      materialize_present_iff s m b n]
  apply Iff.intro
  · intro h
    cases h with
    | inl hb => exact Or.inr (Or.inl hb)
    | inr h2 =>
      cases h2 with
      | inl ha => exact Or.inl ha
      | inr hp => exact Or.inr (Or.inr hp)
  · intro h
    cases h with
    | inl ha => exact Or.inr (Or.inl ha)
    | inr h2 =>
      cases h2 with
      | inl hb => exact Or.inl hb
      | inr hp => exact Or.inr (Or.inr hp)

/-- **Observation confluence.** From a canonical state, the value read at any node
    is the same whether `a` or `b` was materialized first — observed values are
    order-independent. Together with `materialize_present_comm`, any serialization
    a mutex admits yields the same observable map. -/
theorem materialize_observe_comm (s : Spec) (m : Mat) (hc : Canonical s m)
    (a b n : NodeId) :
    observe s (materialize s (materialize s m a) b) n
      = observe s (materialize s (materialize s m b) a) n := by
  rw [observe_eq_val_of_canonical s _
        (materialize_canonical s _ b (materialize_canonical s m a hc)) n,
      observe_eq_val_of_canonical s _
        (materialize_canonical s _ a (materialize_canonical s m b hc)) n]

end LazilyFormal.Materialization
