/-
! Transport-agnostic reactive ingress — formal model (`#designimplementtransport`).

The formal counterpart of `lazily-spec/docs/transport-ingress.md`, over
`LazilyFormal.Merge`. An ingress scope is a keyed admission plane: a generation
fence, an in-order watermark, a bounded reorder buffer, and a coalescing hot
window under a `MergePolicy`.

The results this file fixes, in the order the spec presents them:

- **`fence_monotone`** — a scope's generation never decreases, whatever arrives.
- **`buffered_is_invisible`** — at the current fence, a `buffered` outcome moves
  neither the window nor the watermark, which is what licenses the empty
  invalidation set the reactive shells rely on — and
  **`handoff_that_buffers_resets_the_baseline`**, the case where it does not, which
  is the defect this model found in the Rust reference.

  (The watermark is deliberately NOT claimed monotone: a generation handoff resets
  it, by design. Monotonicity holds within a generation, which is exactly what
  `admitCurrent` is factored out to express.)
- **`stale_generation_rejected`** / **`duplicate_rejected`** — the two refusal
  classes, and `fence_outranks_dedupe`: a zombie generation replaying an already
  delivered sequence is reported as a fence violation, not a duplicate. That
  ordering is the contract, not an implementation detail.
- **`handoff_resets_baseline`** — a newer incarnation's first envelope is the
  whole window: the superseded delta is discarded rather than folded in.
- **`reorder_needs_no_commutativity`** — the interesting one. `Relay.reorder_adjacent`
  needs `Commutative` to tolerate reordering, because a relay merges ops in
  *arrival* order. Ingress does not: the reorder buffer replays in *sequence*
  order, so a merely associative `⊕` converges to the in-order fold. The buffer
  buys what the algebra would otherwise have to pay for.
-/

import LazilyFormal.Merge

namespace LazilyFormal.Ingress

open LazilyFormal.Merge

variable {T : Type}

/-- One decoded inbound message. `gen` fences a producer incarnation, `seq`
    orders within it. Freshness lives in the reactive shell (it needs an observed
    clock) and is deliberately outside this model: it is a *filter* on arrival,
    not part of the ordering algebra. -/
structure Envelope (T : Type) where
  gen : Nat
  seq : Nat
  payload : T

/-- A keyed admission plane. `delivered` is the in-order watermark (`none` before
    the first delivery); `pending` is the bounded reorder buffer; `window` is the
    coalesced hot head. -/
structure Scope (T : Type) where
  gen : Nat
  delivered : Option Nat
  pending : List (Nat × T)
  window : Option T

/-- The first sequence not yet delivered in order. -/
def Scope.expected (s : Scope T) : Nat :=
  match s.delivered with
  | none => 0
  | some n => n + 1

/-- An empty scope at generation `g`. -/
def Scope.fresh (g : Nat) : Scope T :=
  { gen := g, delivered := none, pending := [], window := none }

/-- What admission decided. `refuse` carries which of the two refusal classes it
    was, because the spec's ordering claim is exactly about *which* one fires. -/
inductive Refusal
  | staleGeneration
  | duplicate
  | reorderWindowFull
  deriving DecidableEq, Repr

inductive Outcome
  | delivered (watermark : Nat)
  | buffered (gapFrom : Nat)
  | refuse (why : Refusal)
  deriving DecidableEq, Repr

/-- Fold one payload into the hot window. -/
def mergeInto (P : MergePolicy T) (w : Option T) (op : T) : Option T :=
  match w with
  | none => some op
  | some cur => some (P.merge cur op)

/-- Flush every buffered successor the latest delivery unblocked, in **sequence**
    order. `fuel` bounds the recursion; the reorder buffer is bounded by
    `reorderWindow`, so any `fuel ≥ pending.length` is enough. -/
def flush (P : MergePolicy T) (s : Scope T) : Nat → Scope T
  | 0 => s
  | fuel + 1 =>
    let next := s.expected
    match s.pending.find? (fun kv => kv.1 == next) with
    | none => s
    | some kv =>
      flush P
        { s with
          pending := s.pending.filter (fun x => !(x.1 == next)),
          delivered := some next,
          window := mergeInto P s.window kv.2 }
        fuel

/-- Admission at the **current** fence: dedupe, then ordering, then delivery.
    Splitting this out of [`admit`] is not cosmetic — it is what lets every proof
    below case on three comparisons instead of five nested `if`s. -/
def admitCurrent (P : MergePolicy T) (reorderWindow : Nat) (s : Scope T)
    (e : Envelope T) : Scope T × Outcome :=
  if e.seq < s.expected then
    (s, Outcome.refuse Refusal.duplicate)
  else if s.expected < e.seq then
    if s.pending.any (fun kv => kv.1 == e.seq) then
      (s, Outcome.refuse Refusal.duplicate)
    else if reorderWindow ≤ s.pending.length then
      (s, Outcome.refuse Refusal.reorderWindowFull)
    else
      ({ s with pending := (e.seq, e.payload) :: s.pending }, Outcome.buffered s.expected)
  else
    let s' :=
      { s with delivered := some e.seq, window := mergeInto P s.window e.payload }
    let s'' := flush P s' (s'.pending.length + 1)
    (s'', Outcome.delivered (match s''.delivered with | none => e.seq | some n => n))

/-- The admission algebra. The test order is normative and mirrors the spec: the
    fence outranks everything, and a newer incarnation resets the sequence space,
    the reorder buffer, AND the window — its first envelope is a baseline, not a
    delta. Backpressure is a shell concern (it needs a reactive policy) and is
    modelled in `Relay`. -/
def admit (P : MergePolicy T) (reorderWindow : Nat) (s : Scope T) (e : Envelope T) :
    Scope T × Outcome :=
  if e.gen < s.gen then
    (s, Outcome.refuse Refusal.staleGeneration)
  else if s.gen < e.gen then
    admitCurrent P reorderWindow (Scope.fresh e.gen) e
  else
    admitCurrent P reorderWindow s e

/-! ## The fence and the watermark are monotone -/

/-- `flush` never touches the generation — it only ever moves the watermark. -/
theorem flush_gen (P : MergePolicy T) (s : Scope T) (fuel : Nat) :
    (flush P s fuel).gen = s.gen := by
  induction fuel generalizing s with
  | zero => simp [flush]
  | succ n ih =>
    unfold flush
    cases h : s.pending.find? (fun kv => kv.1 == s.expected) with
    | none => simp [h]
    | some kv => simp [h, ih]

/-- Admission at the current fence leaves the fence alone. -/
theorem admitCurrent_gen (P : MergePolicy T) (rw : Nat) (s : Scope T) (e : Envelope T) :
    (admitCurrent P rw s e).1.gen = s.gen := by
  unfold admitCurrent
  by_cases h1 : e.seq < s.expected
  · simp [h1]
  · by_cases h2 : s.expected < e.seq
    · by_cases h3 : (s.pending.any fun kv => kv.1 == e.seq) = true
      · simp [h1, h2, h3]
      · by_cases h4 : rw ≤ s.pending.length
        · simp [h1, h2, h3, h4]
        · simp [h1, h2, h3, h4]
    · simp [h1, h2, flush_gen]

/-- **The generation fence is monotone.** No arrival can lower it: a lower
    generation is refused outright, an equal one leaves it, and a higher one raises
    it. This is what makes a zombie producer harmless rather than corrupting. -/
theorem fence_monotone (P : MergePolicy T) (rw : Nat) (s : Scope T) (e : Envelope T) :
    s.gen ≤ (admit P rw s e).1.gen := by
  unfold admit
  by_cases h1 : e.gen < s.gen
  · simp [h1]
  · by_cases h2 : s.gen < e.gen
    · simp [h1, h2, admitCurrent_gen, Scope.fresh]
      exact Nat.le_of_lt h2
    · simp [h1, h2, admitCurrent_gen]

/-! ## A buffered envelope is invisible — and exactly when it is not -/

/-- At the current fence, a `buffered` outcome moves neither the window nor the
    watermark. -/
theorem admitCurrent_buffered_is_invisible (P : MergePolicy T) (rw : Nat)
    (s : Scope T) (e : Envelope T) (g : Nat)
    (h : (admitCurrent P rw s e).2 = Outcome.buffered g) :
    (admitCurrent P rw s e).1.window = s.window ∧
      (admitCurrent P rw s e).1.delivered = s.delivered := by
  unfold admitCurrent at h ⊢
  by_cases h1 : e.seq < s.expected
  · simp [h1] at h
  · by_cases h2 : s.expected < e.seq
    · by_cases h3 : (s.pending.any fun kv => kv.1 == e.seq) = true
      · simp [h1, h2, h3] at h
      · by_cases h4 : rw ≤ s.pending.length
        · simp [h1, h2, h3, h4] at h
        · simp [h1, h2, h3, h4]
    · simp [h1, h2] at h

/-- **`buffered` moves nothing a reader can observe, at the current generation.**
    This is the licence the reactive shells use to return an empty invalidation
    set — and the property whose absence would make an out-of-order arrival
    re-render every consumer.

    The `e.gen = s.gen` hypothesis is not decoration: see
    `handoff_that_buffers_resets_the_baseline` for what happens without it. Trying
    to prove this theorem *unconditionally* is what found the corresponding defect
    in the Rust reference, where a handoff that buffered cleared the window while
    reporting no invalidation at all. -/
theorem buffered_is_invisible (P : MergePolicy T) (rw : Nat) (s : Scope T)
    (e : Envelope T) (g : Nat) (hgen : e.gen = s.gen)
    (h : (admit P rw s e).2 = Outcome.buffered g) :
    (admit P rw s e).1.window = s.window ∧
      (admit P rw s e).1.delivered = s.delivered := by
  have h1 : ¬ e.gen < s.gen := by simp [hgen]
  have h2 : ¬ s.gen < e.gen := by simp [hgen]
  unfold admit at h ⊢
  simp only [h1, h2, if_false] at h ⊢
  exact admitCurrent_buffered_is_invisible P rw s e g h

/-- **A handoff that buffers is NOT invisible.** A newer incarnation arriving out
    of order resets the fence, the watermark, and the window *before* parking the
    envelope. Reporting that transition as an empty invalidation set would strand
    every reader on the superseded generation's value — which is precisely the bug
    this theorem exists to forbid. -/
theorem handoff_that_buffers_resets_the_baseline (P : MergePolicy T) (rw : Nat)
    (s : Scope T) (e : Envelope T) (hgen : s.gen < e.gen) (hseq : 0 < e.seq)
    (hrw : 0 < rw) :
    (admit P rw s e).1.window = none ∧
      (admit P rw s e).1.delivered = none ∧
      (admit P rw s e).1.gen = e.gen ∧
      (admit P rw s e).2 = Outcome.buffered 0 := by
  have hnlt : ¬ e.gen < s.gen := Nat.not_lt.mpr (Nat.le_of_lt hgen)
  unfold admit
  simp only [hnlt, hgen, if_false, if_true]
  unfold admitCurrent
  simp [Scope.fresh, Scope.expected, hseq, Nat.not_le.mpr hrw]

/-! ## The two refusal classes, and their order -/

/-- A generation below the fence is refused as a fence violation. -/
theorem stale_generation_rejected (P : MergePolicy T) (rw : Nat) (s : Scope T)
    (e : Envelope T) (h : e.gen < s.gen) :
    admit P rw s e = (s, Outcome.refuse Refusal.staleGeneration) := by
  unfold admit; simp [h]

/-- **The fence outranks dedupe.** A zombie replaying a sequence we have already
    delivered is reported as `staleGeneration`, never as `duplicate`. Testing the
    sequence first would hide the zombie behind a benign-looking retry — the
    ordering is the contract, not an implementation detail. -/
theorem fence_outranks_dedupe (P : MergePolicy T) (rw : Nat) (s : Scope T)
    (e : Envelope T) (hgen : e.gen < s.gen) (_hseq : e.seq < s.expected) :
    (admit P rw s e).2 = Outcome.refuse Refusal.staleGeneration := by
  simp [stale_generation_rejected P rw s e hgen]

/-- An already-delivered sequence at the current fence is a duplicate. -/
theorem duplicate_rejected (P : MergePolicy T) (rw : Nat) (s : Scope T)
    (e : Envelope T) (hgen : e.gen = s.gen) (hseq : e.seq < s.expected) :
    admit P rw s e = (s, Outcome.refuse Refusal.duplicate) := by
  have h1 : ¬ e.gen < s.gen := by simp [hgen]
  have h2 : ¬ s.gen < e.gen := by simp [hgen]
  unfold admit
  simp only [h1, h2, if_false]
  unfold admitCurrent
  simp [hseq]

/-! ## A handoff is a baseline, not a continuation -/

/-- **The new incarnation's first envelope is the whole window.** Whatever the old
    generation had accumulated — undrained window and buffered successors alike —
    is discarded. Folding a superseded delta into a fresh baseline is the
    build-skew corruption the fence exists to prevent. -/
theorem handoff_resets_baseline (P : MergePolicy T) (rw : Nat) (s : Scope T)
    (e : Envelope T) (hgen : s.gen < e.gen) (hseq : e.seq = 0) :
    (admit P rw s e).1.window = some e.payload ∧
      (admit P rw s e).1.pending = [] ∧
      (admit P rw s e).1.gen = e.gen := by
  have hnlt : ¬ e.gen < s.gen := Nat.not_lt.mpr (Nat.le_of_lt hgen)
  unfold admit
  simp only [hnlt, hgen, if_false, if_true]
  unfold admitCurrent
  simp [Scope.fresh, Scope.expected, hseq, mergeInto, flush]

/-! ## Reordering costs no commutativity -/

/-- Deliver a contiguous run in order: the reference against which any arrival
    permutation is measured. -/
def inOrderWindow (P : MergePolicy T) : List T → Option T
  | [] => none
  | op :: rest => rest.foldl (fun w x => mergeInto P w x) (some op)

/-- **Two-element reordering converges without commutativity.**

    Sequence 1 arriving before sequence 0 buffers, and the delivery of 0 flushes 1
    *in sequence order* — so the window is `a ⊕ b`, the in-order fold, for any
    associative `⊕`. Contrast `Relay.reorder_adjacent`, which needs `Commutative`
    precisely because a relay has no buffer and merges in arrival order. The
    reorder buffer is what converts the reordering tax into a bounded-memory cost.
-/
theorem reorder_needs_no_commutativity (P : MergePolicy T) (rw : Nat) (a b : T)
    (hrw : 0 < rw) :
    (admit P rw
        (admit P rw (Scope.fresh 1) { gen := 1, seq := 1, payload := b }).1
        { gen := 1, seq := 0, payload := a }).1.window
      = inOrderWindow P [a, b] := by
  have hinner :
      (admit P rw (Scope.fresh 1) { gen := 1, seq := 1, payload := b }).1
        = ({ gen := 1, delivered := none, pending := [(1, b)], window := none } :
            Scope T) := by
    simp [admit, admitCurrent, Scope.fresh, Scope.expected, Nat.not_le.mpr hrw]
  rw [hinner]
  simp [admit, admitCurrent, Scope.expected, mergeInto, flush, inOrderWindow]

/-- The same run arriving in order lands the same window, so the buffer is not
    changing the answer — it is only changing when the answer is complete. -/
theorem in_order_matches_reference (P : MergePolicy T) (rw : Nat) (a b : T) :
    (admit P rw
        (admit P rw (Scope.fresh 1) { gen := 1, seq := 0, payload := a }).1
        { gen := 1, seq := 1, payload := b }).1.window
      = inOrderWindow P [a, b] := by
  have hinner :
      (admit P rw (Scope.fresh 1) { gen := 1, seq := 0, payload := a }).1
        = ({ gen := 1, delivered := some 0, pending := [], window := some a } :
            Scope T) := by
    simp [admit, admitCurrent, Scope.fresh, Scope.expected, mergeInto, flush]
  rw [hinner]
  simp [admit, admitCurrent, Scope.expected, mergeInto, flush, inOrderWindow]

end LazilyFormal.Ingress
