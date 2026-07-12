/-
! GraphView — the consumer-side materialized view (`#lzsync` 3B clean split).

lazily's reactive graph is a *compute* engine (cells + derived slots wired by closures).
Its cross-process consumers receive materialized *values* (Snapshot/Delta node payloads),
never the recompute closures — closures don't serialize — so a consumer is a value
**mirror**, not a reactive graph. `GraphView` (lazily-kt/js) is that mirror: fold the
value stream into a queryable node projection.

`ReliableSync.lean` proves the abstract fold (multi-epoch = fold, resync convergence,
outbox exactly-once) and dedups re-delivery at the *coordinator* by epoch
(`step_redelivery_noop`, relying on `base_epoch < last_epoch`). This module proves the
**complementary GraphView guarantee: the fold itself is idempotent** — re-applying a
delta's ops reaches the same graph *independent of any epoch dedup*, because each
`DeltaOp` is a last-write overwrite. So a `GraphView` converges under duplicate
delivery as defense-in-depth even if a dedup layer is bypassed or absent.
-/
import LazilyFormal.ReliableSync

namespace LazilyFormal.GraphView

open LazilyFormal.ReliableSync

/-- A node is *touched* by `ops` when some op writes it. -/
def Touched (ops : List Op) (k : Node) : Prop := ∃ o ∈ ops, o.node = k

/-- One op is idempotent: re-overwriting `node := val` changes nothing. -/
theorem applyOp_idempotent (s : GState) (o : Op) :
    applyOp (applyOp s o) o = applyOp s o := by
  funext k
  simp only [applyOp]
  by_cases h : k = o.node <;> simp [h]

/-- A node untouched by `ops` keeps its base value through the whole fold. -/
theorem applyOps_untouched (s : GState) (ops : List Op) (k : Node)
    (h : ∀ o ∈ ops, o.node ≠ k) : applyOps s ops k = s k := by
  induction ops generalizing s with
  | nil => rfl
  | cons o os ih =>
    rw [applyOps_cons, ih (applyOp s o) (fun o' ho' => h o' (List.mem_cons_of_mem o ho'))]
    have hne : o.node ≠ k := h o (by simp)
    simp only [applyOp]
    rw [if_neg (fun hk : k = o.node => hne hk.symm)]

/-- A touched node's folded value is independent of the base state: the last write to it
wins over whatever was underneath. -/
theorem applyOps_touched_indep (s t : GState) (ops : List Op) (k : Node)
    (h : Touched ops k) : applyOps s ops k = applyOps t ops k := by
  induction ops generalizing s t with
  | nil => rcases h with ⟨o, ho, _⟩; exact absurd ho (by simp)
  | cons o os ih =>
    rw [applyOps_cons, applyOps_cons]
    by_cases hos : Touched os k
    · exact ih (applyOp s o) (applyOp t o) hos
    · have ho : o.node = k := by
        rcases h with ⟨o', ho', hn⟩
        rcases List.mem_cons.mp ho' with rfl | hm
        · exact hn
        · exact absurd (⟨o', hm, hn⟩ : Touched os k) hos
      have hnu : ∀ o' ∈ os, o'.node ≠ k := fun o' ho' hn => hos ⟨o', ho', hn⟩
      rw [applyOps_untouched (applyOp s o) os k hnu, applyOps_untouched (applyOp t o) os k hnu]
      simp only [applyOp]
      rw [if_pos ho.symm, if_pos ho.symm]

/-- **GraphView fold idempotence.** Applying a delta's ops, then re-applying the same
ops (a re-delivered / re-emitted frame), reaches the identical graph — a no-op — with no
epoch dedup required. The mirror is convergent under duplicate delivery. -/
theorem applyOps_idempotent (s : GState) (ops : List Op) :
    applyOps (applyOps s ops) ops = applyOps s ops := by
  funext k
  by_cases h : Touched ops k
  · exact applyOps_touched_indep (applyOps s ops) s ops k h
  · have hnu : ∀ o ∈ ops, o.node ≠ k := fun o ho hn => h ⟨o, ho, hn⟩
    rw [applyOps_untouched (applyOps s ops) ops k hnu]

/-- Corollary: re-applying a whole `Delta`'s ops is a state no-op (the epoch advance is
separately atomic, `applyDelta_advances_epoch`). -/
theorem applyDelta_state_idempotent (s : GState) (d : Delta) :
    applyOps (applyOps s d.ops) d.ops = applyOps s d.ops :=
  applyOps_idempotent s d.ops

end LazilyFormal.GraphView
