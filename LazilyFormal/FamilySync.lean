/-
! Reactive keyed map — distributed membership + value sync convergence (#lzfamilysync).

A keyed reactive map (`ReactiveMap` / `SlotMap`; `Collection.lean`) is a *local* keyed
reactive collection.
This module fixes the missing distributed contract: what happens when a map key
is added or updated on one replica and its keyed op reaches another. The plain CRDT
plane (`lazily-rs/src/crdt_plane.rs`, pre-`#lzfamilysync`) *drops* a keyed op whose
entry is not already registered locally — so a map key added on one replica never
appears on another, and any derived aggregate (a count over the map) diverges.

Map-granularity sync closes that gap: an inbound keyed op **materializes** the
absent entry (seeded from the op's converged register) instead of dropping it. This
module proves that materialize-on-ingest is *exactly the pointwise CRDT merge*, so it
inherits the full semilattice convergence — and that the two agent-doc-relevant
properties follow:

- **Membership propagation** (`present_merge`) — after sync a key is present iff it was
  present on *either* replica; a remote-added key can never be lost
  (`applyOp_present`, `applyOp_absent_adopts`).
- **Eventual transparency of a derived aggregate** (`aggregate_converges`) — once two
  replicas converge to the same merged state, any count over the map agrees,
  regardless of op delivery order (`applyOp_comm`). This is the property a live-editor /
  open-document count relies on to converge across editors.

Values are abstract: each entry is an LWW register `(stamp, value)` (mirroring
`SeqCrdt.lean`), the join is the register semilattice, `none` is the not-yet-
materialized bottom, and a map state is the pointwise product over keys.
-/

namespace LazilyFormal.FamilySync

/-- Abstract map key. -/
abbrev Key := Nat

/-- An LWW register `(stamp, value)`: the larger stamp wins; on an equal stamp the
larger value wins so the join stays commutative and associative (as in `SeqCrdt`). -/
abbrev Reg := Nat × Nat

/-- LWW register join. -/
def joinReg (a b : Reg) : Reg :=
  if a.1 > b.1 then a
  else if b.1 > a.1 then b
  else (a.1, max a.2 b.2)

/-! ### The register join is a semilattice -/

theorem joinReg_comm (a b : Reg) : joinReg a b = joinReg b a := by
  obtain ⟨as, av⟩ := a; obtain ⟨bs, bv⟩ := b
  simp only [joinReg]
  repeat' split
  all_goals simp_all [Prod.ext_iff, Nat.max_comm]
  all_goals omega

theorem joinReg_idem (a : Reg) : joinReg a a = a := by
  obtain ⟨as, av⟩ := a
  simp [joinReg]

theorem joinReg_assoc (a b c : Reg) :
    joinReg (joinReg a b) c = joinReg a (joinReg b c) := by
  obtain ⟨as, av⟩ := a; obtain ⟨bs, bv⟩ := b; obtain ⟨cs, cv⟩ := c
  simp only [joinReg]
  repeat' split
  all_goals simp_all [Prod.ext_iff, Nat.max_assoc]
  all_goals omega

/-! ### The optional-register join: `none` is the not-yet-materialized bottom -/

/-- Join two optional registers. `none` (an absent / not-yet-materialized key) is the
identity, so joining a present entry with an absent one **materializes** it — the
formal statement of materialize-on-ingest. -/
def joinOpt (a b : Option Reg) : Option Reg :=
  match a, b with
  | none, x => x
  | x, none => x
  | some x, some y => some (joinReg x y)

theorem joinOpt_none_right (a : Option Reg) : joinOpt a none = a := by
  cases a <;> simp [joinOpt]

theorem joinOpt_comm (a b : Option Reg) : joinOpt a b = joinOpt b a := by
  cases a <;> cases b <;> simp [joinOpt, joinReg_comm]

theorem joinOpt_idem (a : Option Reg) : joinOpt a a = a := by
  cases a <;> simp [joinOpt, joinReg_idem]

theorem joinOpt_assoc (a b c : Option Reg) :
    joinOpt (joinOpt a b) c = joinOpt a (joinOpt b c) := by
  cases a <;> cases b <;> cases c <;> simp [joinOpt, joinReg_assoc]

/-! ### A map state is the pointwise product over keys -/

/-- A whole replica's map: key ↦ register (absent key ↦ `none`). -/
abbrev State := Key → Option Reg

/-- Merge two map replicas: pointwise optional-register join. -/
def merge (s t : State) : State := fun k => joinOpt (s k) (t k)

theorem merge_comm (s t : State) : merge s t = merge t s := by
  funext k; simp only [merge]; exact joinOpt_comm (s k) (t k)

theorem merge_assoc (s t u : State) :
    merge (merge s t) u = merge s (merge t u) := by
  funext k; simp only [merge]; exact joinOpt_assoc (s k) (t k) (u k)

theorem merge_idem (s : State) : merge s s = s := by
  funext k; simp only [merge]; exact joinOpt_idem (s k)

/-- Whether a map key is currently materialized (present) in a replica. -/
def present (s : State) (k : Key) : Bool := (s k).isSome

/-- **Membership propagation.** After merging, a key is present iff it was present on
*either* replica — a map key added on one side is never lost, it is the union. -/
theorem present_merge (s t : State) (k : Key) :
    present (merge s t) k = (present s k || present t k) := by
  simp only [present, merge, joinOpt]
  cases s k <;> cases t k <;> simp

/-! ### A keyed op and materialize-on-ingest -/

/-- A keyed op: the origin replica's converged register for `key`. -/
structure Op where
  key : Key
  reg : Reg

/-- The single-entry map state carrying just `k ↦ r`. -/
def single (k : Key) (r : Reg) : State := fun x => if x = k then some r else none

/-- **Materialize-on-ingest.** Applying a keyed op joins that key's register,
**creating the entry if absent** (the dropped-op gap, closed). -/
def applyOp (s : State) (o : Op) : State :=
  fun k => if k = o.key then joinOpt (s k) (some o.reg) else s k

/-- The headline bridge: applying a keyed op is **exactly** merging the op's
single-entry state. So materialize-on-ingest is the CRDT merge, and it inherits every
convergence law proved above (commutativity, associativity, idempotence). -/
theorem applyOp_eq_merge (s : State) (o : Op) :
    applyOp s o = merge s (single o.key o.reg) := by
  funext k
  simp only [applyOp, merge, single]
  by_cases hk : k = o.key
  · simp [hk]
  · simp [hk, joinOpt_none_right]

/-- Ingesting a keyed op **always** makes its key present: a remote-added key can never
be dropped (the `#lzfamilysync` correctness gap). -/
theorem applyOp_present (s : State) (o : Op) : present (applyOp s o) o.key = true := by
  simp only [present, applyOp, if_true]
  cases s o.key <;> simp [joinOpt]

/-- A key absent locally **adopts the remote value** on ingest — the materialized entry
is seeded from the op's converged register. -/
theorem applyOp_absent_adopts (s : State) (o : Op) (h : s o.key = none) :
    applyOp s o o.key = some o.reg := by
  simp [applyOp, joinOpt, h]

/-- **Op-delivery confluence.** Two keyed ops applied in either order yield the same
state — so a replica converges regardless of the order it ingests map ops. Follows
from the merge semilattice via `applyOp_eq_merge`. -/
theorem applyOp_comm (s : State) (o p : Op) :
    applyOp (applyOp s o) p = applyOp (applyOp s p) o := by
  simp only [applyOp_eq_merge]
  rw [merge_assoc, merge_assoc, merge_comm (single o.key o.reg) (single p.key p.reg)]

/-- Applying an op is idempotent up to the register join — re-delivering the same op
never changes the converged state (safe, resumable anti-entropy). -/
theorem applyOp_idem (s : State) (o : Op) :
    applyOp (applyOp s o) o = applyOp s o := by
  simp only [applyOp_eq_merge]
  rw [merge_assoc, merge_idem]

/-! ### Eventual transparency of a derived aggregate -/

/-- A derived aggregate over the map: the number of keys in `keys` whose entry
satisfies `p` (e.g. "is live" / "is open"). This models a map's reactive derived
count. -/
def countWhere (s : State) (keys : List Key) (p : Reg → Bool) : Nat :=
  (keys.filter (fun k => match s k with | some r => p r | none => false)).length

/-- **Eventual transparency of a derived aggregate.** Once two replicas converge to the
same merged state, any derived count over the map agrees — independent of which
replica computes it (the state is identical) and, via `merge_comm`, independent of the
sync direction. This is the convergence a live-editor / open-document count relies on. -/
theorem aggregate_converges (s t : State) (keys : List Key) (p : Reg → Bool) :
    countWhere (merge s t) keys p = countWhere (merge t s) keys p := by
  rw [merge_comm]

/-- Batching / re-ordering the merges of three replicas converges the same aggregate
(associativity lifted to the derived count). -/
theorem aggregate_batch_invariant (s t u : State) (keys : List Key) (p : Reg → Bool) :
    countWhere (merge (merge s t) u) keys p = countWhere (merge s (merge t u)) keys p := by
  rw [merge_assoc]

end LazilyFormal.FamilySync
