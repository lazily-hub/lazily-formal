/-
! Fault-tolerance primitives (`#lzresilience`) — formal model.

The formal counterpart of `lazily-spec/docs/resilience.md`. Proves the
circuit-breaker transition safety, retry-backoff boundedness + monotonicity,
bulkhead boundedness, and timeout monotonicity.
-/

namespace LazilyFormal.Resilience

/-! ## Circuit breaker -/

inductive BreakerState where
  | closed
  | open
  | halfOpen
  deriving DecidableEq

/-- `allow` on an Open breaker: transitions to HalfOpen at the deadline, else
fast-fails. -/
def allowOpen (openUntil now : Nat) : BreakerState × Bool :=
  if openUntil ≤ now then (BreakerState.halfOpen, true) else (BreakerState.open, false)

/-- Before the deadline, an Open breaker fast-fails. -/
theorem open_fast_fails (openUntil now : Nat) (h : now < openUntil) :
    (allowOpen openUntil now).2 = false := by
  have hnle : ¬ (openUntil ≤ now) := Nat.not_le.mpr h
  simp [allowOpen, hnle]

/-- At the deadline, an Open breaker transitions to HalfOpen and probes. -/
theorem open_probes_at_deadline (openUntil now : Nat) (h : openUntil ≤ now) :
    allowOpen openUntil now = (BreakerState.halfOpen, true) := by
  simp [allowOpen, h]

/-- A HalfOpen outcome: success closes, failure re-opens. -/
def recordHalfOpen (success : Bool) : BreakerState :=
  if success then BreakerState.closed else BreakerState.open

theorem halfopen_success_closes : recordHalfOpen true = BreakerState.closed := rfl
theorem halfopen_failure_reopens : recordHalfOpen false = BreakerState.open := rfl

/-! ## Retry backoff -/

def retryDelay (base cap attempt : Nat) : Nat := min cap (base * 2 ^ attempt)

/-- Backoff is bounded by `cap`. -/
theorem retry_bounded (base cap attempt : Nat) : retryDelay base cap attempt ≤ cap := by
  simp only [retryDelay]
  exact Nat.min_le_left _ _

/-- Backoff is monotone in the attempt (up to the cap). -/
theorem retry_monotone (base cap a : Nat) :
    retryDelay base cap a ≤ retryDelay base cap (a + 1) := by
  simp only [retryDelay]
  have hpow : (2 : Nat) ^ a ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by decide) (Nat.le_succ a)
  have hx : base * 2 ^ a ≤ base * 2 ^ (a + 1) := Nat.mul_le_mul (Nat.le_refl base) hpow
  omega

/-! ## Bulkhead -/

structure Bulkhead where
  capacity : Nat
  inUse : Nat

def Bulkhead.acquire (b : Bulkhead) : Bool × Bulkhead :=
  if b.inUse < b.capacity then (true, { b with inUse := b.inUse + 1 }) else (false, b)

/-- `inUse` never exceeds `capacity`. -/
theorem bulkhead_bounded (b : Bulkhead) (h : b.inUse ≤ b.capacity) :
    (b.acquire).2.inUse ≤ b.capacity := by
  unfold Bulkhead.acquire
  by_cases hc : b.inUse < b.capacity
  · simp [hc]; exact hc
  · simp [hc]; exact h

/-! ## Timeout -/

structure Timeout where
  deadline : Nat
  timedOut : Bool

def Timeout.tick (t : Timeout) (now : Nat) : Bool × Timeout :=
  if t.timedOut then (false, t)
  else if t.deadline ≤ now then (true, { t with timedOut := true })
  else (false, t)

/-- Once timed out, a timeout stays timed out. -/
theorem timeout_monotone (t : Timeout) (now : Nat) (h : t.timedOut = true) :
    (t.tick now).2.timedOut = true := by
  simp [Timeout.tick, h]

/-- Before the deadline, a timeout does not fire. -/
theorem timeout_no_fire_before (t : Timeout) (now : Nat)
    (ht : t.timedOut = false) (h : now < t.deadline) : (t.tick now).1 = false := by
  have hnle : ¬ (t.deadline ≤ now) := Nat.not_le.mpr h
  simp [Timeout.tick, ht, hnle]

end LazilyFormal.Resilience
