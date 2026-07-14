/-
! Embedded-service plane (`#lzservice`) — formal model.

The formal counterpart of `lazily-spec/docs/service.md`. Proves the health
aggregation (worst component dominates), readiness (all conditions hold), and the
service registry's durability: the projection is the fold of the log, so
`replay` reconstructs it and a fresh registration resolves.
-/

namespace LazilyFormal.Service

/-! ## Health aggregation -/

inductive Health where
  | healthy
  | degraded
  | unhealthy
  deriving DecidableEq

/-- Aggregate probes `(up, critical)`: unhealthy if a critical probe is down,
else degraded if any is down, else healthy. -/
def health (probes : List (Bool × Bool)) : Health :=
  if probes.any (fun p => p.2 && !p.1) then Health.unhealthy
  else if probes.any (fun p => !p.1) then Health.degraded
  else Health.healthy

/-- Health is Unhealthy iff a critical probe is down. -/
theorem health_unhealthy_iff (probes : List (Bool × Bool)) :
    health probes = Health.unhealthy ↔ probes.any (fun p => p.2 && !p.1) = true := by
  unfold health
  by_cases h : probes.any (fun p => p.2 && !p.1) = true
  · simp [h]
  · simp only [h]
    by_cases h2 : probes.any (fun p => !p.1) = true <;> simp [h2]

/-- When every probe is up, health is Healthy. -/
theorem health_all_up_healthy (probes : List (Bool × Bool))
    (h : probes.any (fun p => !p.1) = false) : health probes = Health.healthy := by
  unfold health
  have hc : probes.any (fun p => p.2 && !p.1) = false := by
    rw [List.any_eq_false] at h ⊢
    intro p hp
    have hup := h p hp
    simp [hup]
  simp [hc, h]

/-! ## Readiness -/

def ready (conds : List Bool) : Bool := conds.all id

/-- Readiness holds iff every condition is true. -/
theorem ready_iff_all (conds : List Bool) :
    ready conds = true ↔ ∀ b ∈ conds, b = true := by
  simp [ready, List.all_eq_true]

/-! ## Service registry durability -/

inductive RegOp where
  | reg : Nat → Nat → RegOp
  | dereg : Nat → RegOp

def applyOp (m : Nat → Option Nat) : RegOp → (Nat → Option Nat)
  | RegOp.reg s e => fun k => if k = s then some e else m k
  | RegOp.dereg s => fun k => if k = s then none else m k

/-- The projection is the left-fold of the durable log. -/
def project (log : List RegOp) : Nat → Option Nat :=
  log.foldl applyOp (fun _ => none)

def replay (log : List RegOp) : Nat → Option Nat := project log

/-- Replaying the log reconstructs the projection unchanged. -/
theorem registry_replay_reconstructs (log : List RegOp) : replay log = project log := rfl

/-- A fresh registration resolves to its endpoint. -/
theorem register_resolves (log : List RegOp) (s e : Nat) :
    project (log ++ [RegOp.reg s e]) s = some e := by
  simp [project, List.foldl_append, applyOp]

end LazilyFormal.Service
