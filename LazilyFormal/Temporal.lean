/-
! Temporal source primitives (`#lztime`) — formal model.

The formal counterpart of `lazily-spec/docs/temporal-sources.md` and the
executable reference behind `lazily-spec/conformance/temporal/*.json`.

Time is a monotone logical clock (`now : Nat`). Each source is a pure compute
core with a `tick` transition; the reactive bindings project a source's fire
edge onto a `Cell`. This file pins the load-bearing invariants:

- **Timer fires at most once** and stays fired (`timer_stays_fired`,
  `timer_fire_idempotent`, `timer_no_fire_before`).
- **Interval / Cron count is monotone** under `tick`
  (`interval_count_monotone`, `cron_count_monotone`) and a below-frontier tick
  is a no-op (`interval_no_fire_before_next`).
- **Deadline expiry is monotone and value-preserving**
  (`deadline_expired_monotone`, `deadline_preserves_value`).
-/

namespace LazilyFormal.Temporal

/-! ## Single-shot timer -/

structure Timer where
  fireAt : Nat
  fired : Bool

/-- Advance to logical time `now`. Returns `(edge, timer')`: `edge` is `true`
only on the first tick with `fireAt ≤ now`. -/
def Timer.tick (t : Timer) (now : Nat) : Bool × Timer :=
  if t.fired then (false, t)
  else if t.fireAt ≤ now then (true, { t with fired := true })
  else (false, t)

def Timer.value (t : Timer) : Option Unit := if t.fired then some () else none

/-- A tick on an already-fired timer is a no-op with no edge (idempotent fire). -/
theorem timer_fire_idempotent (t : Timer) (now : Nat) (h : t.fired = true) :
    Timer.tick t now = (false, t) := by
  simp [Timer.tick, h]

/-- Once fired, a timer stays fired under any subsequent tick. -/
theorem timer_stays_fired (t : Timer) (now : Nat) (h : t.fired = true) :
    (Timer.tick t now).2.fired = true := by
  simp [Timer.tick, h]

/-- Before the fire time, a tick does not fire and does not change state. -/
theorem timer_no_fire_before (t : Timer) (now : Nat)
    (hf : t.fired = false) (hlt : now < t.fireAt) :
    Timer.tick t now = (false, t) := by
  have : ¬ (t.fireAt ≤ now) := Nat.not_le.mpr hlt
  simp [Timer.tick, hf, this]

/-- The edge fires exactly when a not-yet-fired timer reaches its fire time. -/
theorem timer_edge_iff (t : Timer) (now : Nat) (hf : t.fired = false) :
    (Timer.tick t now).1 = true ↔ t.fireAt ≤ now := by
  by_cases h : t.fireAt ≤ now <;> simp [Timer.tick, hf, h]

/-! ## Periodic interval -/

structure Interval where
  period : Nat
  next : Nat
  count : Nat

/-- Boundaries crossed on a single tick: 0 if `now` is below the frontier,
else `(now − next)/period + 1` (every boundary in `(frontier, now]`). -/
def firesThisTick (next period now : Nat) : Nat :=
  if now < next then 0 else (now - next) / period + 1

def Interval.tick (iv : Interval) (now : Nat) : Interval :=
  let f := firesThisTick iv.next iv.period now
  { iv with count := iv.count + f, next := iv.next + f * iv.period }

/-- `count` never decreases under a tick. -/
theorem interval_count_monotone (iv : Interval) (now : Nat) :
    iv.count ≤ (iv.tick now).count := by
  simp [Interval.tick, Nat.le_add_right]

/-- A tick below the next boundary is a no-op (no fire). -/
theorem interval_no_fire_before_next (iv : Interval) (now : Nat)
    (h : now < iv.next) : iv.tick now = iv := by
  have hf : firesThisTick iv.next iv.period now = 0 := by
    simp [firesThisTick, h]
  simp [Interval.tick, hf]

/-! ## Cron pattern -/

/-- Count of `m ∈ 1..=n` with `m mod cycle = o` (0 ≤ o < cycle). -/
def countUpto (n o cycle : Nat) : Nat :=
  if o = 0 then n / cycle
  else if o ≤ n then (n - o) / cycle + 1 else 0

/-- Matching ticks in `(lo, hi]` across all offsets. -/
def matchesIn (offsets : List Nat) (cycle lo hi : Nat) : Nat :=
  offsets.foldl (fun acc o => acc + (countUpto hi o cycle - countUpto lo o cycle)) 0

structure Cron where
  cycle : Nat
  offsets : List Nat
  cursor : Nat
  count : Nat

def Cron.tick (c : Cron) (now : Nat) : Cron :=
  let f := matchesIn c.offsets c.cycle c.cursor now
  { c with count := c.count + f, cursor := now }

/-- `count` never decreases under a tick. -/
theorem cron_count_monotone (c : Cron) (now : Nat) :
    c.count ≤ (c.tick now).count := by
  simp [Cron.tick, Nat.le_add_right]

/-- A cron tick always advances the cursor to `now`. -/
theorem cron_cursor_advances (c : Cron) (now : Nat) :
    (c.tick now).cursor = now := by
  simp [Cron.tick]

/-! ## Value + deadline -/

inductive Deadlined (α : Type) where
  | live : α → Deadlined α
  | expired : α → Deadlined α

structure Deadline (α : Type) where
  value : α
  deadline : Nat
  isExpired : Bool

def Deadline.tick (d : Deadline α) (now : Nat) : Deadline α :=
  if d.isExpired then d
  else if d.deadline ≤ now then { d with isExpired := true } else d

def Deadline.state (d : Deadline α) : Deadlined α :=
  if d.isExpired then Deadlined.expired d.value else Deadlined.live d.value

/-- Expiry preserves the carried value in every branch. -/
theorem deadline_preserves_value (d : Deadline α) (now : Nat) :
    (d.tick now).value = d.value := by
  unfold Deadline.tick
  by_cases he : d.isExpired
  · simp [he]
  · by_cases hd : d.deadline ≤ now <;> simp [he, hd]

/-- Once expired, a deadline stays expired under any subsequent tick. -/
theorem deadline_expired_monotone (d : Deadline α) (now : Nat)
    (h : d.isExpired = true) : (d.tick now).isExpired = true := by
  simp [Deadline.tick, h]

/-- Before the deadline, a tick is a no-op (still `Live`). -/
theorem deadline_no_expiry_before (d : Deadline α) (now : Nat)
    (he : d.isExpired = false) (hlt : now < d.deadline) : d.tick now = d := by
  have : ¬ (d.deadline ≤ now) := Nat.not_le.mpr hlt
  simp [Deadline.tick, he, this]

end LazilyFormal.Temporal
