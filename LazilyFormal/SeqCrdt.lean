/-
! Move-aware sequence CRDT — per-element LWW registers + move-as-reassignment.

The formal counterpart of `lazily-{rs,kt,js}` `SeqCrdt` and
`lazily-spec/cell-model.md` § "Move-aware sequence order", behind
`lazily-spec/conformance/collections/seqcrdt_convergence.json`.

Sibling order under concurrency is a *composition above* per-cell value merge. Each
element is three **independent** last-writer-wins registers — `value`, `position`
(a fractional-index order key, tiebroken by peer), and `deleted` — each stamped by an
HLC. The two load-bearing facts the fixture pins:

- a **move is a single LWW reassignment of `position`**, never delete+reinsert, so two
  concurrent moves of the same element converge to the later stamp *without duplication*
  (it stays one id-keyed element), and a concurrent move + value-edit of one element both
  apply because `position` and `value` are independent registers;
- `merge` is commutative / associative / idempotent — each register is an LWW join
  (max by `(stamp, val)`), the element is their product, and the sequence state is the
  pointwise product over ids.

An HLC stamp folds the peer tiebreak inside itself, so distinct writes carry distinct
stamps; on the degenerate equal-stamp case the register still converges by taking the
larger value, keeping the join a genuine semilattice.
-/

namespace LazilyFormal.SeqCrdt

/-- An LWW register: `(stamp, val)`. `stamp` is the HLC (peer folded in); `val` is the
written payload (an order key for `position`, a datum for `value`, a `0/1` flag for
`deleted`). -/
abbrev Reg := Nat × Nat

/-- LWW register join: the larger stamp wins; on an equal stamp the larger value wins so
the join stays commutative and associative even in the degenerate tie. -/
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

/-- The later write wins the register. -/
theorem joinReg_lt_right {a b : Reg} (h : a.1 < b.1) : joinReg a b = b := by
  obtain ⟨as, av⟩ := a; obtain ⟨bs, bv⟩ := b
  simp only [joinReg] at *
  have h1 : ¬ as > bs := by omega
  have h2 : bs > as := h
  simp [h1, h2]

theorem joinReg_gt_left {a b : Reg} (h : b.1 < a.1) : joinReg a b = a := by
  rw [joinReg_comm]; exact joinReg_lt_right h

/-! ### An element is the product of three independent registers -/

/-- A sequence element: three independent LWW registers. `position.2` is the order key
(fractional index ⊗ peer); `deleted.2` is `0` (live) or `1` (tombstoned). -/
structure Elem where
  value : Reg
  position : Reg
  deleted : Reg

/-- Element merge = pointwise register join. -/
def mergeElem (a b : Elem) : Elem :=
  { value := joinReg a.value b.value
    position := joinReg a.position b.position
    deleted := joinReg a.deleted b.deleted }

theorem mergeElem_comm (a b : Elem) : mergeElem a b = mergeElem b a := by
  simp [mergeElem, joinReg_comm a.value b.value, joinReg_comm a.position b.position,
        joinReg_comm a.deleted b.deleted]

theorem mergeElem_assoc (a b c : Elem) :
    mergeElem (mergeElem a b) c = mergeElem a (mergeElem b c) := by
  simp [mergeElem, joinReg_assoc]

theorem mergeElem_idem (a : Elem) : mergeElem a a = a := by
  simp [mergeElem, joinReg_idem]

/-! ### The sequence state is the pointwise product over ids -/

/-- A whole replica: element id ↦ element (absent id ↦ `none`). -/
abbrev State := Nat → Option Elem

/-- Merge two present elements; a present element on one side alone carries through. -/
def merge (s t : State) : State := fun id =>
  match s id, t id with
  | some a, some b => some (mergeElem a b)
  | some a, none   => some a
  | none,   some b => some b
  | none,   none   => none

theorem merge_comm (s t : State) : merge s t = merge t s := by
  funext id
  simp only [merge]
  cases s id <;> cases t id <;> simp [mergeElem_comm]

theorem merge_assoc (s t u : State) :
    merge (merge s t) u = merge s (merge t u) := by
  funext id
  simp only [merge]
  cases s id <;> cases t id <;> cases u id <;> simp [mergeElem_assoc]

theorem merge_idem (s : State) : merge s s = s := by
  funext id
  simp only [merge]
  cases s id <;> simp [mergeElem_idem]

/-! ### Move is a single LWW position reassignment -/

/-- A move rewrites only the `position` register with a fresh stamp — value and deleted
untouched (it is *not* delete+reinsert). -/
def move (e : Elem) (key stamp : Nat) : Elem := { e with position := (stamp, key) }

/-- A value edit rewrites only the `value` register. -/
def setValue (e : Elem) (v stamp : Nat) : Elem := { e with value := (v, stamp) }

/-- A remove flips the `deleted` register to a tombstone (`1`) with a fresh stamp. -/
def remove (e : Elem) (stamp : Nat) : Elem := { e with deleted := (stamp, 1) }

/-- Move touches neither the value nor the deleted register (register independence). -/
theorem move_preserves_value (e : Elem) (key stamp : Nat) :
    (move e key stamp).value = e.value := rfl

theorem move_preserves_deleted (e : Elem) (key stamp : Nat) :
    (move e key stamp).deleted = e.deleted := rfl

/-- **Concurrent moves converge to the later stamp — no duplication.** Two replicas move
the *same* id; the merge keeps one element whose `position` is the later move's, and whose
`value` is unchanged (idempotent). -/
theorem concurrent_move_lww (e : Elem) (k1 s1 k2 s2 : Nat) (h : s1 < s2) :
    (mergeElem (move e k1 s1) (move e k2 s2)).position = (s2, k2)
    ∧ (mergeElem (move e k1 s1) (move e k2 s2)).value = e.value := by
  refine ⟨?_, ?_⟩
  · show joinReg (s1, k1) (s2, k2) = (s2, k2)
    exact joinReg_lt_right (by simpa using h)
  · show joinReg e.value e.value = e.value
    exact joinReg_idem e.value

/-- **Concurrent move and value edit both apply.** One replica moves the element, another
edits its value; because `position` and `value` are independent registers, the merge
carries the new position *and* the new value. -/
theorem concurrent_move_and_value (e : Elem) (k sM v sV : Nat)
    (hM : e.position.1 < sM) (hV : e.value.1 < v) :
    (mergeElem (move e k sM) (setValue e v sV)).position = (sM, k)
    ∧ (mergeElem (move e k sM) (setValue e v sV)).value = (v, sV) := by
  refine ⟨?_, ?_⟩
  · show joinReg (sM, k) e.position = (sM, k)
    exact joinReg_gt_left (by simpa using hM)
  · show joinReg e.value (v, sV) = (v, sV)
    exact joinReg_lt_right (by simpa using hV)

/-- **Remove is an LWW tombstone that a later genuine resurrection can win.** Merging a
removed copy with an untouched copy keeps the tombstone; a re-add with a strictly later
stamp wins by LWW (matching "a genuine resurrection wins"). -/
theorem remove_lww (e : Elem) (sDel : Nat) (h : e.deleted.1 < sDel) :
    (mergeElem (remove e sDel) e).deleted = (sDel, 1) := by
  show joinReg (sDel, 1) e.deleted = (sDel, 1)
  exact joinReg_gt_left (by simpa using h)

/-- Order over a finite id universe: live (untombstoned) ids sorted by their `position`
order key. Being a pure function of the converged state, the order converges too. -/
def orderKeyOf (e : Elem) : Nat := e.position.2

/-- A tombstoned element is skipped by order/contains (its `deleted` flag is `1`). -/
def isLive (e : Elem) : Bool := e.deleted.2 == 0

end LazilyFormal.SeqCrdt
