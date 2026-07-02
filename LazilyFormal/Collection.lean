/-
! Keyed reactive collections — formal model.

The formal counterpart of `lazily-rs/src/cell_family.rs` (`CellMap` /
`CellFamily`) and the `lazily-spec/cell-model.md` § "Keyed cell collections"
specification. `CellMap` is a hash collection whose **membership is itself
reactive**, with one independently-tracked value cell per entry; `CellFamily`
layers a value factory on top that lazily mints and caches one cell per key.

The universal properties fixed here (no finite fixture suite can establish
them):

- **Three independent reactive signals**: per-entry value, set-membership, and
  order. The model fixes the wire-level "a pure reorder (`move_to`) MUST NOT
  invalidate set-membership readers (`len` / `contains`)" invariant and its
  duals.
- **Atomic move preserves identity**: a reorder keeps each entry's cell
  identity (not remove + re-mint), bumping only the order signal once.
- **CellFamily memoizes per key**: requesting the same key twice returns the
  same cell (identity stability across the factory).

These are the "value, set-membership, and order reactivity are independent"
conformance clauses of `cell-model.md`, restated as Lean theorems over an
abstract `Collection` state.
-/

import LazilyFormal.Primitive

namespace LazilyFormal.Collection

open LazilyFormal.Primitive

/-- Abstract key for a collection entry (a `K` in `lazily-rs`). -/
abbrev Key := Nat

/-- Abstract per-entry value. The model exercises equality and identity. -/
abbrev EntryValue := Nat

/-- The state of one keyed reactive collection (`CellMap`).

The three independent reactive signals are modeled explicitly as monotonic
version counters, mirroring `lazily-rs`'s `membership` and `order_signal`
cells (`src/cell_family.rs`):

- `values` — per-key value cells (independently tracked).
- `membershipV` — the set-membership version; bumped on `add`/`remove` only.
- `orderV` — the order version; bumped on `add`/`remove` **and** on `move`.

A reader of `len`/`contains` subscribes to `membershipV`; a reader of `keys`
subscribes to `orderV`; a reader of `get k` subscribes to `values[k]` alone. -/
structure Collection where
  /-- Insertion-ordered authoritative key list. -/
  order : List Key
  /-- Per-key value cells. -/
  values : Key → Option EntryValue
  /-- Set-membership version (bumps on add/remove only). -/
  membershipV : Nat
  /-- Order version (bumps on add/remove **and** move). -/
  orderV : Nat

/-- `true` iff `k` is a member of the collection. -/
def contains (c : Collection) (k : Key) : Bool :=
  c.order.contains k

/-! ## Mutators

Each mutator returns the resulting collection. The version-counter deltas make
the independence laws mechanical: `setEntryValue` touches neither version;
`addKey`/`removeKey` bump both; `moveKey` bumps only `orderV`. -/

/-- Update the value cell at `k` (which must be a member). Leaves membership
    and order signals untouched. -/
def setEntryValue (c : Collection) (k : Key) (v : EntryValue) : Collection :=
  { c with values := fun j => if j = k then some v else c.values j }

/-- Insert `k` as a new member at the end, minting its value cell. Bumps both
    the membership and the order signal. (No-op if `k` is already a member.) -/
def addKey (c : Collection) (k : Key) (v : EntryValue) : Collection :=
  match c.order.contains k with
  | true => c
  | false => { c with order := c.order ++ [k],
                       values := fun j => if j = k then some v else c.values j,
                       membershipV := c.membershipV + 1,
                       orderV := c.orderV + 1 }

/-- Remove `k` from the collection. Bumps both the membership and the order
    signal. (No-op if `k` is not a member.) -/
def removeKey (c : Collection) (k : Key) : Collection :=
  match c.order.contains k with
  | true => { c with order := c.order.filter (fun j => j ≠ k),
                      membershipV := c.membershipV + 1,
                      orderV := c.orderV + 1 }
  | false => c

/-- A pure reorder: move `k` to position `i`. Bumps **only** the order signal;
    membership and every entry's value cell are untouched. This is the formal
    counterpart of `lazily-rs`'s `CellMap::move_to` (`#lzcellmove`). -/
def moveKey (c : Collection) (k : Key) (i : Nat) : Collection :=
  match c.order.contains k with
  | true => { c with order := (c.order.filter (fun j => j ≠ k)).insertIdx
                       (min i c.order.length - 1) k,
                       orderV := c.orderV + 1 }
  | false => c

/-! ## The independence laws

These are the three conformance clauses of `cell-model.md` § "Keyed cell
collections" point 2, restated as theorems. -/

/-- Updating one entry's value leaves the set-membership signal unchanged —
    `len`/`contains` readers are not invalidated. -/
theorem setEntryValue_preserves_membership
    (c : Collection) (k : Key) (v : EntryValue) :
    (setEntryValue c k v).membershipV = c.membershipV := by
  rfl

/-- Updating one entry's value leaves the order signal unchanged. -/
theorem setEntryValue_preserves_order
    (c : Collection) (k : Key) (v : EntryValue) :
    (setEntryValue c k v).orderV = c.orderV := by
  rfl

/-- Updating one entry's value leaves every *sibling* entry's value cell
    untouched — fine-grained per-entry reactivity. -/
theorem setEntryValue_preserves_siblings
    (c : Collection) (k v : EntryValue) (sib : Key) (hsib : sib ≠ k) :
    (setEntryValue c k v).values sib = c.values sib := by
  simp [setEntryValue, hsib]

/-- A pure reorder leaves the set-membership signal unchanged — the wire-level
    invariant "a pure reorder (`move_to`) MUST NOT invalidate set-membership
    readers (`len` / `contains`)" (`cell-model.md` § Keyed cell collections). -/
theorem moveKey_preserves_membership
    (c : Collection) (k : Key) (i : Nat) :
    (moveKey c k i).membershipV = c.membershipV := by
  simp only [moveKey]
  split
  · rfl
  · rfl

/-- A pure reorder leaves every entry's value cell untouched — atomic move
    keeps each entry's cell identity (`cell-model.md` § 4: "reordering a key
    MUST keep the entry's same cell handle, dependents, and lineage"). -/
theorem moveKey_preserves_values
    (c : Collection) (k : Key) (i : Nat) (j : Key) :
    (moveKey c k i).values j = c.values j := by
  simp only [moveKey]
  split
  · rfl
  · rfl

/-- A pure reorder strictly advances the order signal — order readers
    (`keys`) are invalidated exactly once. -/
theorem moveKey_advances_order
    (c : Collection) (k : Key) (i : Nat) (hmem : c.order.contains k = true) :
    (moveKey c k i).orderV = c.orderV + 1 := by
  simp only [moveKey, hmem]

/-- Adding a new key strictly advances both the membership and the order
    signal. -/
theorem addKey_advances_membership_and_order
    (c : Collection) (k : Key) (v : EntryValue) (hnew : c.order.contains k = false) :
    (addKey c k v).membershipV = c.membershipV + 1 ∧
    (addKey c k v).orderV = c.orderV + 1 := by
  refine ⟨?_, ?_⟩
  · simp only [addKey, hnew]
  · simp only [addKey, hnew]

/-! ## CellFamily — per-key memoization

`CellFamily` (`lazily-rs/src/cell_family.rs:315`) layers a value factory on
top of `CellMap`: a parameterized factory that lazily mints and caches one
cell per key on first access. The universal guarantee is identity stability —
the same key resolves to the same cell handle across requests. -/

/-- A `CellFamily` is a `Collection` plus a per-key factory memo table that
    records which keys have already been minted. -/
structure Family where
  coll : Collection
  /-- The set of keys whose cell has been minted by the factory so far. -/
  minted : List Key

/-- `Family.get k` (the lazy mint): if `k` has already been minted, return the
    collection unchanged (identity-stable handle); otherwise mint `k` and
    record it in `minted`. -/
def Family.get (f : Family) (k : Key) (v : EntryValue) : Family :=
  match f.minted.contains k with
  | true => f
  | false => { f with coll := addKey f.coll k v, minted := f.minted ++ [k] }

/-- If `k` is already minted, `Family.get` is the identity (no-op). -/
theorem Family.get_of_mem (f : Family) (k : Key) (v : EntryValue)
    (h : f.minted.contains k = true) : Family.get f k v = f := by
  simp only [Family.get, h]

/-- If `k` is not yet minted, `Family.get` extends `minted` by `[k]`. -/
theorem Family.get_minted_eq (f : Family) (k : Key) (v : EntryValue)
    (h : f.minted.contains k = false) :
    Family.get f k v = { coll := addKey f.coll k v, minted := f.minted ++ [k] } := by
  simp only [Family.get, h]

/-- Requesting the same key twice returns the identical family state the
    second time — the universal form of "CellFamily lazily mints and caches
    one cell per key" (`cell-model.md` § Keyed cell collections, point 3:
    "A key resolves to a stable handle for the key's lifetime"). -/
theorem Family.get_idempotent_after_first
    (f : Family) (k : Key) (v : EntryValue) :
    Family.get (Family.get f k v) k v = Family.get f k v := by
  match h : f.minted.contains k with
  | true =>
    -- First get is a no-op (f1 = f); the second is too.
    have hf : Family.get f k v = f := Family.get_of_mem f k v h
    simp only [hf]
  | false =>
    -- First get mints: f1.minted = f.minted ++ [k].
    have hf : Family.get f k v = { coll := addKey f.coll k v, minted := f.minted ++ [k] } :=
      Family.get_minted_eq f k v h
    rw [hf]
    -- Second get: f1.minted = f.minted ++ [k] ⊇ [k], so k is minted ⇒ no-op.
    have hsecond : (f.minted ++ [k]).contains k = true := by
      rw [List.contains_append]; simp
    exact Family.get_of_mem
      { coll := addKey f.coll k v, minted := f.minted ++ [k] } k v hsecond

end LazilyFormal.Collection
