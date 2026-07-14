/-
! Distributed coordination (`#lzcoord`) — formal model.

The formal counterpart of `lazily-spec/docs/coordination.md`. Proves the safety
invariants the coordination primitives rely on: lease **fencing-token
monotonicity** (a stale holder always carries a smaller token), **semaphore
boundedness**, and the **quorum gate** opening exactly at strict majority.
-/

namespace LazilyFormal.Coordination

/-! ## Lease + fencing token -/

structure Lease where
  holder : Option Nat
  expiry : Nat
  fence : Nat

/-- Grant when free or expired (a new grant increments the fence); a renew by the
current holder keeps the same fence; held-by-another is rejected. -/
def Lease.acquire (l : Lease) (peer now ttl : Nat) : Option Nat × Lease :=
  match l.holder with
  | none =>
      let f := l.fence + 1
      (some f, { holder := some peer, expiry := now + ttl, fence := f })
  | some h =>
      if l.expiry ≤ now then
        let f := l.fence + 1
        (some f, { holder := some peer, expiry := now + ttl, fence := f })
      else if h = peer then
        (some l.fence, { l with expiry := now + ttl })
      else
        (none, l)

/-- The fencing token never decreases under `acquire`. -/
theorem acquire_fence_monotone (l : Lease) (peer now ttl : Nat) :
    l.fence ≤ (l.acquire peer now ttl).2.fence := by
  unfold Lease.acquire
  cases l.holder with
  | none => exact Nat.le_succ _
  | some h =>
      by_cases he : l.expiry ≤ now
      · simp [he, Nat.le_succ]
      · by_cases hp : h = peer <;> simp [he, hp]

/-- A renew by the live holder keeps the same fence. -/
theorem renew_keeps_fence (l : Lease) (peer now ttl : Nat)
    (h : l.holder = some peer) (hlive : ¬ l.expiry ≤ now) :
    (l.acquire peer now ttl).2.fence = l.fence := by
  unfold Lease.acquire
  rw [h]
  simp [hlive]

/-! ## Semaphore -/

structure Semaphore where
  capacity : Nat
  acquired : Nat

def Semaphore.available (s : Semaphore) : Nat := s.capacity - s.acquired

def Semaphore.acquire (s : Semaphore) : Bool × Semaphore :=
  if s.acquired < s.capacity then (true, { s with acquired := s.acquired + 1 })
  else (false, s)

/-- `acquired` never exceeds `capacity`. -/
theorem semaphore_bounded (s : Semaphore) (h : s.acquired ≤ s.capacity) :
    (s.acquire).2.acquired ≤ s.capacity := by
  unfold Semaphore.acquire
  by_cases hc : s.acquired < s.capacity
  · simp [hc]; exact hc
  · simp [hc]; exact h

/-- An acquire with room increments `acquired`. -/
theorem acquire_increments (s : Semaphore) (h : s.acquired < s.capacity) :
    (s.acquire).2.acquired = s.acquired + 1 := by
  simp [Semaphore.acquire, h]

/-! ## Quorum gate -/

def quorumThreshold (total : Nat) : Nat := total / 2 + 1

def quorumOpen (votes total : Nat) : Bool := votes ≥ quorumThreshold total

/-- The quorum gate opens exactly at strict majority (`⌊total/2⌋ + 1`). -/
theorem quorum_opens_at_majority (votes total : Nat) :
    quorumOpen votes total = true ↔ votes ≥ total / 2 + 1 := by
  simp [quorumOpen, quorumThreshold]

end LazilyFormal.Coordination
