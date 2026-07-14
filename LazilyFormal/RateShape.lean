/-
! Rate-shaping source primitives (`#lzrateshape`) — formal model.

The formal counterpart of `lazily-spec/docs/rate-shaping.md` and the reference
behind `lazily-spec/conformance/rateshape/*.json`. Time is the same monotone
logical clock (`now : Nat`) as `#lztime`. Each operator is a pure decision core;
the reactive cell projects its emit edge onto a `Cell`.

Invariants pinned here:

- **Debounce** emits nothing before its (reset-on-input) deadline and, once the
  quiet period elapses, emits the latest value (`debounce_no_emit_before`,
  `debounce_emits_after_input`).
- **Leading throttle** drops every input inside an open window and passes once
  the window elapses (`throttle_leading_drops_in_window`,
  `throttle_leading_emits_past`) — at most one emit per window.
- **Count sampling** emits exactly on multiples of `n`
  (`sample_count_emits_iff`).
- **Probabilistic sampling** threshold is monotone in `rate`
  (`prob_sample_monotone`) with the `rate = 0` / passing endpoints. Draws and
  rate are modeled as `Nat` thresholds abstracting the `[0,1)` draw.
-/

namespace LazilyFormal.RateShape

/-! ## Debounce -/

structure Debounce (α : Type) where
  quiet : Nat
  pending : Option α
  fireAt : Nat
  armed : Bool

def Debounce.input (d : Debounce α) (now : Nat) (v : α) : Debounce α :=
  { d with pending := some v, fireAt := now + d.quiet, armed := true }

def Debounce.tick (d : Debounce α) (now : Nat) : Option α × Debounce α :=
  match d.pending, d.armed with
  | some v, true =>
      if d.fireAt ≤ now then (some v, { d with pending := none, armed := false })
      else (none, d)
  | _, _ => (none, d)

/-- Before the (reset-on-input) deadline, a tick emits nothing. -/
theorem debounce_no_emit_before (d : Debounce α) (now : Nat) (v : α)
    (hp : d.pending = some v) (ha : d.armed = true) (hlt : now < d.fireAt) :
    (d.tick now).1 = none := by
  simp only [Debounce.tick, hp, ha]
  rw [if_neg (Nat.not_le.mpr hlt)]

/-- After an input at `now`, a tick at `now' ≥ now + quiet` emits that latest value. -/
theorem debounce_emits_after_input (d : Debounce α) (now now' : Nat) (v : α)
    (hle : now + d.quiet ≤ now') :
    ((d.input now v).tick now').1 = some v := by
  unfold Debounce.input Debounce.tick
  simp only
  rw [if_pos hle]

/-! ## Leading throttle -/

structure ThrottleLeading (α : Type) where
  window : Nat
  windowEnd : Option Nat

def ThrottleLeading.input (t : ThrottleLeading α) (now : Nat) (v : α) :
    Option α × ThrottleLeading α :=
  match t.windowEnd with
  | some we =>
      if now < we then (none, t)
      else (some v, { t with windowEnd := some (now + t.window) })
  | none => (some v, { t with windowEnd := some (now + t.window) })

/-- An input inside an open window drops. -/
theorem throttle_leading_drops_in_window (t : ThrottleLeading α) (now we : Nat) (v : α)
    (h : t.windowEnd = some we) (hlt : now < we) : (t.input now v).1 = none := by
  simp only [ThrottleLeading.input, h]
  rw [if_pos hlt]

/-- An input at/after the window boundary passes. -/
theorem throttle_leading_emits_past (t : ThrottleLeading α) (now we : Nat) (v : α)
    (h : t.windowEnd = some we) (hge : we ≤ now) : (t.input now v).1 = some v := by
  simp only [ThrottleLeading.input, h]
  rw [if_neg (Nat.not_lt.mpr hge)]

/-! ## Count sampling -/

structure SampleCount where
  n : Nat
  counter : Nat

def SampleCount.input (s : SampleCount) : Bool × SampleCount :=
  let c := s.counter + 1
  (if c % s.n = 0 then true else false, { s with counter := c })

/-- Count sampling emits exactly on multiples of `n`. -/
theorem sample_count_emits_iff (s : SampleCount) :
    (s.input).1 = true ↔ (s.counter + 1) % s.n = 0 := by
  simp only [SampleCount.input]
  by_cases h : (s.counter + 1) % s.n = 0 <;> simp [h]

/-! ## Probabilistic sampling

Draws and `rate` are `Nat` thresholds abstracting the `[0,1)` draw; a draw passes
iff `draw < rate`. -/

def shouldSample (draw rate : Nat) : Bool := draw < rate

/-- A higher `rate` passes a superset of draws. -/
theorem prob_sample_monotone (draw r1 r2 : Nat) (hle : r1 ≤ r2)
    (h : shouldSample draw r1 = true) : shouldSample draw r2 = true := by
  simp only [shouldSample, decide_eq_true_eq] at *
  exact Nat.lt_of_lt_of_le h hle

/-- `rate = 0` drops everything. -/
theorem prob_sample_zero (draw : Nat) : shouldSample draw 0 = false := by
  simp [shouldSample]

/-- Any draw below `rate` passes. -/
theorem prob_sample_passes (draw rate : Nat) (h : draw < rate) :
    shouldSample draw rate = true := by
  simp [shouldSample, h]

end LazilyFormal.RateShape
