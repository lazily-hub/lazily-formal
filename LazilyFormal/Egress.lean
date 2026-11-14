/-
! Transport-agnostic reactive egress — formal model (`#lzegress`).

The formal counterpart of the lazily-spec `EgressCore<T>` contract
(`lazily-spec/docs/transport-egress.md`). The core, rather than its transport
Effect, owns sequence assignment, the pending queue and bounded unacknowledged
window, the cumulative acknowledgement watermark, the retry budget with bounded
exponential backoff and exhaustion, and the producer-generation fence.

`step` is the total reducer over every core operation. It returns the next
state, the reader-kind invalidations (`Change`) the reactive shells emit, and
the API outcome. `LazilyFormal.Conformance.EgressCorpus` replays every
`lazily-spec/conformance/egress/egress_*.json` trace through `step` inside the
kernel, so the model and the canonical corpus cannot drift.

Universal results:

* `step_nextSequence_monotone`, `enqueue_sequence_monotone` — sequence
  assignment is monotone; `enqueue` hands out exactly the old boundary.
* `step_watermark_monotone`, `acknowledgement_monotone` — the cumulative ACK
  watermark never moves backward under any operation.
* `ack_beyond_sent_refused`, `ack_beyondSent_iff` — an ACK at or beyond
  `nextSequence` acknowledges never-assigned data and is refused without
  changing state or invalidating a reader; `step_preserves_ackInv` — hence the
  watermark lies inside the assigned sequence space and below every retained
  record after every operation, and `retained_record_ack_advances` — a genuine
  ACK for any retained record advances (no record is ever stranded).
* `stale_generation_preserves_state` — every send-side transition from a
  fenced (stale) attachment changes no state and invalidates no reader.
* `reconnect_advances_and_preserves_ack` — a legitimate reconnect strictly
  advances the fence, preserves the sequence space and watermark, empties the
  window, and rewrites every retained envelope to the new generation.
* `step_window_bounded` — the unacknowledged window never exceeds
  `inflightLimit`.
* `step_preserves_inv` — no retained record is ever duplicated: retained
  sequences are pairwise distinct, all below `nextSequence`, and all above the
  acknowledgement watermark.
* `fail_retrying_within_budget`, `fail_exhausted_is_terminal` — scheduled
  retries are bounded by the budget, and an exhausted record can never be
  scheduled again.
* `step_change_sound` — every change to a reader projection is reported as an
  invalidation of that reader (no stale reader); in particular a reconnect that
  replays nothing still invalidates `pending` when it rewrites retained
  never-claimed envelopes to the new generation.
-/

namespace LazilyFormal.Egress

/-- Egress policy. `retryBudget` counts retries after the first attempt. -/
structure Policy where
  inflightLimit : Nat
  retryBudget : Nat
  retryBase : Nat
  retryCeiling : Nat
  deriving Repr, DecidableEq

/-- One send attempt. `(generation, sequence)` is the transport idempotency
identity. -/
structure Envelope (T : Type) where
  generation : Nat
  sequence : Nat
  attempt : Nat
  payload : T
  deriving Repr, DecidableEq

/-- The retry projection: the most recent failure's evidence. -/
structure Retry where
  sequence : Nat
  attempt : Nat
  backoff : Nat
  exhausted : Bool
  deriving Repr, DecidableEq

/-- Pure egress delivery authority. `failed` holds the retry-parked records
(the projection exposes only the most recent failure through `retry`). -/
structure State (T : Type) where
  policy : Policy
  generation : Nat
  nextSequence : Nat
  ackedThrough : Option Nat
  pending : List (Envelope T)
  inflight : List (Envelope T)
  failed : List (Envelope T)
  retry : Option Retry
  deriving Repr, DecidableEq

/-- Reader-kind invalidations emitted by one transition. -/
structure Change where
  pending : Bool
  inflight : Bool
  ackedThrough : Bool
  retry : Bool
  deriving Repr, DecidableEq

/-- The empty change: no reader is invalidated. -/
def Change.none : Change := ⟨false, false, false, false⟩

inductive ClaimResult (T : Type) where
  | claimed (envelope : Envelope T)
  | empty
  | windowFull
  | staleGeneration (current : Nat)
  deriving Repr, DecidableEq

inductive AckResult where
  | advanced (through : Nat)
  | unchanged (through : Option Nat)
  /-- `through ≥ nextSequence`: the peer acknowledged a sequence that was never
  assigned (so never sent). A protocol error, refused without effect. -/
  | beyondSent (nextSequence : Nat)
  | staleGeneration (current : Nat)
  deriving Repr, DecidableEq

inductive FailResult where
  | retrying (retry : Retry)
  | exhausted (retry : Retry)
  | unknownSequence
  | staleGeneration (current : Nat)
  deriving Repr, DecidableEq

inductive RetryResult where
  | scheduled (sequence : Nat)
  | unknownSequence
  | staleGeneration (current : Nat)
  deriving Repr, DecidableEq

inductive ReconnectResult where
  | advanced (generation replayed : Nat)
  | unchanged (generation : Nat)
  | staleGeneration (current : Nat)
  deriving Repr, DecidableEq

/-- Every core operation. Send-side operations carry the generation captured by
the transport attachment that issues them. -/
inductive Op (T : Type) where
  | enqueue (payload : T)
  | claim (generation : Nat)
  | ack (generation through : Nat)
  | fail (generation sequence : Nat)
  | retryNow (generation sequence : Nat)
  | reconnect (generation : Nat)
  deriving Repr, DecidableEq

inductive Outcome (T : Type) where
  | sequence (sequence : Nat)
  | claim (result : ClaimResult T)
  | ack (result : AckResult)
  | fail (result : FailResult)
  | retry (result : RetryResult)
  | reconnect (result : ReconnectResult)
  deriving Repr, DecidableEq

variable {T : Type}

/-- Empty core attached to a transport generation. -/
def State.empty (policy : Policy) (generation : Nat) : State T :=
  { policy := policy
    generation := generation
    nextSequence := 0
    ackedThrough := none
    pending := []
    inflight := []
    failed := []
    retry := none }

/-- Insert before the first record with a larger sequence (sequence order). -/
def insertOrdered (e : Envelope T) : List (Envelope T) → List (Envelope T)
  | [] => [e]
  | x :: xs => if e.sequence < x.sequence then e :: x :: xs else x :: insertOrdered e xs

/-- `backoff(attempt) = min(retry_ceiling, retry_base * 2^(attempt - 1))`. -/
def retryBackoff (base ceiling attempt : Nat) : Nat :=
  min ceiling (base * 2 ^ (attempt - 1))

def rewriteGeneration (generation : Nat) (envelope : Envelope T) : Envelope T :=
  { envelope with generation := generation }

/-- Projection of an optional watermark used by monotonicity theorems. -/
def watermark : Option Nat → Nat
  | none => 0
  | some through => through

/-- Is `through` at or below the current watermark (a no-op ACK)? -/
def ackCovered (current : Option Nat) (through : Nat) : Bool :=
  match current with
  | none => false
  | some c => decide (through ≤ c)

/-- Does the retry projection refer to `sequence`? -/
def retryIs (retry : Option Retry) (sequence : Nat) : Bool :=
  match retry with
  | none => false
  | some r => decide (r.sequence = sequence)

/-- Does the retry projection refer to a sequence at or below `through`? -/
def retryAtOrBelow (retry : Option Retry) (through : Nat) : Bool :=
  match retry with
  | none => false
  | some r => decide (r.sequence ≤ through)

/-- Assign the next sequence and place the value in the pending projection. -/
def enqueue (s : State T) (payload : T) : State T × Change × Nat :=
  let sequence := s.nextSequence
  ({ s with
      nextSequence := sequence + 1
      pending := s.pending ++ [{
        generation := s.generation
        sequence := sequence
        attempt := 0
        payload := payload }] },
   { Change.none with pending := true },
   sequence)

/-- Move the oldest pending record into the unacknowledged window. -/
def claim (s : State T) (generation : Nat) : State T × Change × ClaimResult T :=
  if generation ≠ s.generation then
    (s, Change.none, .staleGeneration s.generation)
  else if s.policy.inflightLimit ≤ s.inflight.length then
    (s, Change.none, .windowFull)
  else
    match s.pending with
    | [] => (s, Change.none, .empty)
    | r :: rest =>
        let e : Envelope T := { r with generation := s.generation, attempt := r.attempt + 1 }
        let retryChanged := retryIs s.retry e.sequence
        ({ s with
            pending := rest
            inflight := insertOrdered e s.inflight
            retry := if retryChanged then none else s.retry },
         { pending := true, inflight := true, ackedThrough := false, retry := retryChanged },
         .claimed e)

/-- Keep only records strictly above a cumulative acknowledgement. -/
def above (through : Nat) (e : Envelope T) : Bool := decide (through < e.sequence)

/-- Advance the cumulative watermark and prune every record at or below it. An
acknowledgement beyond the assigned sequence space (`through ≥ nextSequence`) is
refused: it changes no state and invalidates no reader. -/
def ack (s : State T) (generation through : Nat) : State T × Change × AckResult :=
  if generation ≠ s.generation then
    (s, Change.none, .staleGeneration s.generation)
  else if s.nextSequence ≤ through then
    (s, Change.none, .beyondSent s.nextSequence)
  else if ackCovered s.ackedThrough through then
    (s, Change.none, .unchanged s.ackedThrough)
  else
    let pending := s.pending.filter (above through)
    let inflight := s.inflight.filter (above through)
    let retryChanged := retryAtOrBelow s.retry through
    ({ s with
        ackedThrough := some through
        pending := pending
        inflight := inflight
        failed := s.failed.filter (above through)
        retry := if retryChanged then none else s.retry },
     { pending := decide (pending.length ≠ s.pending.length)
       inflight := decide (inflight.length ≠ s.inflight.length)
       ackedThrough := true
       retry := retryChanged },
     .advanced through)

/-- Is this record the one with `sequence`? -/
def hasSeq (sequence : Nat) (e : Envelope T) : Bool := decide (e.sequence = sequence)

/-- Park a failed in-flight record while budget remains; otherwise it is
terminally exhausted. -/
def fail (s : State T) (generation sequence : Nat) : State T × Change × FailResult :=
  if generation ≠ s.generation then
    (s, Change.none, .staleGeneration s.generation)
  else
    match s.inflight.find? (hasSeq sequence) with
    | none => (s, Change.none, .unknownSequence)
    | some r =>
        let exhausted := decide (s.policy.retryBudget < r.attempt)
        let retry : Retry :=
          { sequence := sequence
            attempt := r.attempt
            backoff := retryBackoff s.policy.retryBase s.policy.retryCeiling r.attempt
            exhausted := exhausted }
        ({ s with
            inflight := s.inflight.filter (fun e => !hasSeq sequence e)
            failed := if exhausted then s.failed else insertOrdered r s.failed
            retry := some retry },
         { pending := false, inflight := true, ackedThrough := false, retry := true },
         if exhausted then .exhausted retry else .retrying retry)

/-- Return a parked (non-exhausted) record to pending in sequence order. -/
def retryNow (s : State T) (generation sequence : Nat) : State T × Change × RetryResult :=
  if generation ≠ s.generation then
    (s, Change.none, .staleGeneration s.generation)
  else
    match s.failed.find? (hasSeq sequence) with
    | none => (s, Change.none, .unknownSequence)
    | some r =>
        let retryChanged := retryIs s.retry sequence
        ({ s with
            failed := s.failed.filter (fun e => !hasSeq sequence e)
            pending := insertOrdered r s.pending
            retry := if retryChanged then none else s.retry },
         { pending := true, inflight := false, ackedThrough := false, retry := retryChanged },
         .scheduled sequence)

/-- Insert every record of `rs` into `acc` in sequence order. -/
def insertAll (acc : List (Envelope T)) (rs : List (Envelope T)) : List (Envelope T) :=
  rs.foldl (fun acc r => insertOrdered r acc) acc

/-- Fence the old attachment: strictly advance the generation, preserve the
sequence space and the watermark, and replay every unacknowledged in-flight or
retry-parked record through pending under the new generation. -/
def reconnect (s : State T) (generation : Nat) : State T × Change × ReconnectResult :=
  if generation < s.generation then
    (s, Change.none, .staleGeneration s.generation)
  else if generation = s.generation then
    (s, Change.none, .unchanged s.generation)
  else
    let replayed := s.inflight.length + s.failed.length
    ({ s with
        generation := generation
        pending := (insertAll (insertAll s.pending s.inflight) s.failed).map
          (rewriteGeneration generation)
        inflight := []
        failed := []
        retry := none },
     -- Rewriting the retained envelopes' generation changes the `pending`
     -- projection whenever anything is retained, not only when records replay.
     { pending := decide (0 < replayed) || !s.pending.isEmpty
       inflight := decide (0 < replayed)
       ackedThrough := false
       retry := s.retry.isSome },
     .advanced generation replayed)

/-- The total reducer over every core operation. -/
def step (s : State T) : Op T → State T × Change × Outcome T
  | .enqueue payload =>
      let (s', c, n) := enqueue s payload
      (s', c, .sequence n)
  | .claim g =>
      let (s', c, r) := claim s g
      (s', c, .claim r)
  | .ack g through =>
      let (s', c, r) := ack s g through
      (s', c, .ack r)
  | .fail g sequence =>
      let (s', c, r) := fail s g sequence
      (s', c, .fail r)
  | .retryNow g sequence =>
      let (s', c, r) := retryNow s g sequence
      (s', c, .retry r)
  | .reconnect g =>
      let (s', c, r) := reconnect s g
      (s', c, .reconnect r)

/-! ### Conformance replay

One corpus step: the operation, the returned outcome, and the full projected
state after the step (exactly the fields every binding runner must assert). -/

structure Expected (T : Type) where
  op : Op T
  returns : Outcome T
  generation : Nat
  nextSequence : Nat
  pending : List (Envelope T)
  inflight : List (Envelope T)
  ackedThrough : Option Nat
  retry : Option Retry
  invalidates : Change
  deriving Repr, DecidableEq

/-- Does one step from `s` produce exactly the expected outcome, projection, and
invalidations? -/
def stepMatches [DecidableEq T] (s : State T) (e : Expected T) : Bool :=
  let (s', c, out) := step s e.op
  decide (out = e.returns) && decide (s'.generation = e.generation) &&
    decide (s'.nextSequence = e.nextSequence) && decide (s'.pending = e.pending) &&
    decide (s'.inflight = e.inflight) && decide (s'.ackedThrough = e.ackedThrough) &&
    decide (s'.retry = e.retry) && decide (c = e.invalidates)

/-- Replay a whole trace, asserting every step. -/
def replay [DecidableEq T] : State T → List (Expected T) → Bool
  | _, [] => true
  | s, e :: es => stepMatches s e && replay (step s e.op).1 es

/-! ### Sequence assignment -/

/-- Enqueue allocates exactly one fresh, larger sequence boundary. -/
theorem enqueue_sequence_monotone (s : State T) (payload : T) :
    s.nextSequence < (enqueue s payload).1.nextSequence := by
  simp [enqueue]

/-- Enqueue hands out the old boundary as the new record's sequence. -/
theorem enqueue_returns_boundary (s : State T) (payload : T) :
    (enqueue s payload).2.2 = s.nextSequence := rfl

private theorem insertAll_nil_left (rs : List (Envelope T)) :
    ∀ acc : List (Envelope T), (insertAll acc rs).length = acc.length + rs.length := by
  induction rs with
  | nil => intro acc; simp [insertAll]
  | cons r rs ih =>
      intro acc
      have hlen : ∀ l : List (Envelope T), (insertOrdered r l).length = l.length + 1 := by
        intro l
        induction l with
        | nil => simp [insertOrdered]
        | cons x xs ihx =>
            simp only [insertOrdered]
            split <;> simp [ihx]
      simp only [insertAll, List.foldl_cons] at *
      rw [ih]
      simp [hlen]
      omega

/-- No operation moves the sequence boundary backward. -/
theorem step_nextSequence_monotone (s : State T) (op : Op T) :
    s.nextSequence ≤ (step s op).1.nextSequence := by
  cases op <;> simp only [step, enqueue, claim, ack, fail, retryNow, reconnect] <;>
    (try split) <;> (try split) <;> (try split) <;> simp_all

/-! ### Acknowledgement watermark -/

/-- A cumulative acknowledgement never moves its projected watermark backward. -/
theorem acknowledgement_monotone (s : State T) (generation through : Nat) :
    watermark s.ackedThrough ≤ watermark (ack s generation through).1.ackedThrough := by
  unfold ack
  split
  · exact Nat.le_refl _
  · split
    · exact Nat.le_refl _
    · split
      · exact Nat.le_refl _
      · rename_i h
        cases hs : s.ackedThrough with
        | none => simp [watermark]
        | some c =>
            simp [ackCovered, hs] at h
            simp [watermark]
            omega

/-- An advancing acknowledgement strictly raises the watermark. -/
theorem ack_advanced_strict (s : State T) (generation through : Nat) (c : Nat)
    (h : (ack s generation through).2.2 = .advanced through) (hs : s.ackedThrough = some c) :
    c < watermark (ack s generation through).1.ackedThrough := by
  unfold ack at *
  by_cases hg : generation = s.generation
  · by_cases hb : s.nextSequence ≤ through
    · simp [hg, hb] at h
    · by_cases hc : ackCovered s.ackedThrough through = true
      · simp [hg, hb, hc] at h
      · have hc' : c < through := by simp [ackCovered, hs] at hc; omega
        simp [hg, hb, hc, watermark, hc']
  · simp [hg] at h

/-- No operation moves the acknowledgement watermark backward. -/
theorem step_watermark_monotone (s : State T) (op : Op T) :
    watermark s.ackedThrough ≤ watermark (step s op).1.ackedThrough := by
  cases op with
  | ack g through => exact acknowledgement_monotone s g through
  | _ =>
      simp only [step, enqueue, claim, fail, retryNow, reconnect] <;>
        (try split) <;> (try split) <;> (try split) <;> simp_all

/-! ### Send-side generation fence -/

/-- A send-side operation, and the generation its attachment supplied. -/
def Op.sendGeneration : Op T → Option Nat
  | .claim g => some g
  | .ack g _ => some g
  | .fail g _ => some g
  | .retryNow g _ => some g
  | _ => none

/-- A stale transport attachment has no write authority: every send-side
transition it issues changes no state and invalidates no reader. -/
theorem stale_generation_preserves_state (s : State T) (op : Op T) (g : Nat)
    (hop : op.sendGeneration = some g) (stale : g ≠ s.generation) :
    (step s op).1 = s ∧ (step s op).2.1 = Change.none := by
  cases op <;> simp [Op.sendGeneration] at hop <;> subst hop <;>
    simp [step, claim, ack, fail, retryNow, stale]

/-- A stale reconnect (older generation) is likewise inert. -/
theorem stale_reconnect_preserves_state (s : State T) (g : Nat) (stale : g < s.generation) :
    (reconnect s g).1 = s ∧ (reconnect s g).2.1 = Change.none := by
  simp [reconnect, stale]

/-- A legitimate reconnect advances the fence, preserves the sequence space and
the ACK watermark, empties the window and the parked set, and rewrites every
retained envelope to the new generation. -/
theorem reconnect_advances_and_preserves_ack (s : State T) (g : Nat)
    (advanced : s.generation < g) :
    (reconnect s g).1.generation = g ∧
      (reconnect s g).1.ackedThrough = s.ackedThrough ∧
      (reconnect s g).1.nextSequence = s.nextSequence ∧
      (reconnect s g).1.inflight = [] ∧
      (reconnect s g).1.failed = [] ∧
      (∀ e ∈ (reconnect s g).1.pending, e.generation = g) := by
  have h1 : ¬ g < s.generation := by omega
  have h2 : g ≠ s.generation := by omega
  simp [reconnect, h1, h2, rewriteGeneration]

/-- Reconnect replays every unacknowledged record: nothing in flight or parked
is lost. -/
theorem reconnect_replays_everything (s : State T) (g : Nat) (advanced : s.generation < g) :
    (reconnect s g).1.pending.length =
      s.pending.length + s.inflight.length + s.failed.length := by
  have h1 : ¬ g < s.generation := by omega
  have h2 : g ≠ s.generation := by omega
  simp [reconnect, h1, h2, insertAll_nil_left]

/-! ### Bounded window -/

private theorem length_insertOrdered (e : Envelope T) (l : List (Envelope T)) :
    (insertOrdered e l).length = l.length + 1 := by
  induction l with
  | nil => simp [insertOrdered]
  | cons x xs ih =>
      simp only [insertOrdered]
      split <;> simp [ih]

/-- The unacknowledged window never exceeds the configured limit. -/
theorem step_window_bounded (s : State T) (op : Op T)
    (h : s.inflight.length ≤ s.policy.inflightLimit) :
    (step s op).1.inflight.length ≤ (step s op).1.policy.inflightLimit := by
  cases op with
  | enqueue p => simpa [step, enqueue] using h
  | claim g =>
      simp only [step, claim]
      split
      · exact h
      · split
        · exact h
        · rename_i _ hlt
          split
          · exact h
          · simp [length_insertOrdered]; omega
  | ack g t =>
      simp only [step, ack]
      split
      · exact h
      · split
        · exact h
        · split
          · exact h
          · exact Nat.le_trans (List.length_filter_le _ _) h
  | fail g q =>
      simp only [step, fail]
      split
      · exact h
      · split
        · exact h
        · exact Nat.le_trans (List.length_filter_le _ _) h
  | retryNow g q =>
      simp only [step, retryNow]
      split
      · exact h
      · split <;> exact h
  | reconnect g =>
      simp only [step, reconnect]
      split
      · exact h
      · split
        · exact h
        · simp

/-! ### Bounded retry -/

/-- `retryBudget` counts retries after the first send attempt. -/
def retryPermitted (retryBudget attempt : Nat) : Prop :=
  1 ≤ attempt ∧ attempt ≤ retryBudget + 1

/-- The number of permitted send attempts is bounded by first-attempt + budget. -/
theorem retry_attempts_bounded
    (retryBudget attempt : Nat)
    (permitted : retryPermitted retryBudget attempt) :
    attempt ≤ retryBudget + 1 :=
  permitted.2

/-- Exponential retry delay is always capped by the configured ceiling. -/
theorem retry_backoff_bounded (base ceiling attempt : Nat) :
    retryBackoff base ceiling attempt ≤ ceiling := by
  simp [retryBackoff, Nat.min_le_left]

/-- A failure is scheduled for retry only while the attempt is within budget. -/
theorem fail_retrying_within_budget (s : State T) (g q : Nat) (r : Retry)
    (h : (fail s g q).2.2 = .retrying r) :
    r.attempt ≤ s.policy.retryBudget ∧ r.exhausted = false := by
  unfold fail at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i rec _
      by_cases hx : s.policy.retryBudget < rec.attempt
      · simp [hx] at h
      · simp [hx] at h
        subst h
        simp; omega

/-- An exhausted failure is terminal: the record is no longer in flight or
parked, so `retry_now` can never schedule it again. -/
theorem fail_exhausted_is_terminal (s : State T) (g q : Nat) (r : Retry)
    (h : (fail s g q).2.2 = .exhausted r)
    (notParked : ∀ e ∈ s.failed, e.sequence ≠ q) :
    s.policy.retryBudget < r.attempt ∧
      (∀ e ∈ (fail s g q).1.inflight, e.sequence ≠ q) ∧
      (retryNow (fail s g q).1 g q).2.2 = .unknownSequence := by
  unfold fail at h ⊢
  split at h
  · simp at h
  · rename_i hg
    split at h
    · simp at h
    · rename_i rec hfind
      by_cases hx : s.policy.retryBudget < rec.attempt
      · simp [hx] at h
        subst h
        simp only [hg, if_false, hx, decide_true]
        have hnone : List.find? (hasSeq q) s.failed = none := by
          rw [List.find?_eq_none]
          intro e he
          simp [hasSeq]
          exact notParked e he
        refine ⟨by simp, ?_, ?_⟩
        · intro e he
          simp [List.mem_filter, hasSeq] at he
          exact he.2
        · simp [retryNow, hg, hnone]
      · simp [hx] at h

/-! ### No duplicated retained record

Every operation either permutes the retained records (claim, retry scheduling,
non-exhausted failure, reconnect replay), appends exactly one fresh sequence
(enqueue), or drops records (cumulative ACK pruning, exhaustion). Hence retained
sequences stay pairwise distinct and below the sequence boundary. -/

/-- Every retained record: pending, in flight, and retry-parked. -/
def all (s : State T) : List (Envelope T) := s.pending ++ s.inflight ++ s.failed

/-- The sequences of every retained record. -/
def seqs (s : State T) : List Nat := (all s).map Envelope.sequence

/-- Retained-record integrity. -/
structure Inv (s : State T) : Prop where
  nodup : (seqs s).Nodup
  below : ∀ n ∈ seqs s, n < s.nextSequence

theorem inv_empty (policy : Policy) (generation : Nat) :
    Inv (State.empty policy generation : State T) :=
  ⟨by simp [seqs, all, State.empty], by simp [seqs, all, State.empty]⟩

private theorem perm_insertOrdered (e : Envelope T) (l : List (Envelope T)) :
    (insertOrdered e l).Perm (e :: l) := by
  induction l with
  | nil => simp [insertOrdered]
  | cons x xs ih =>
      simp only [insertOrdered]
      split
      · exact List.Perm.refl _
      · exact (ih.cons x).trans (List.Perm.swap e x xs)

private theorem perm_insertAll (rs : List (Envelope T)) :
    ∀ acc : List (Envelope T), (insertAll acc rs).Perm (acc ++ rs) := by
  induction rs with
  | nil => intro acc; simp [insertAll]
  | cons r rs ih =>
      intro acc
      have h1 := ih (insertOrdered r acc)
      simp only [insertAll, List.foldl_cons] at h1 ⊢
      refine h1.trans ?_
      refine ((perm_insertOrdered r acc).append_right rs).trans ?_
      exact (List.perm_middle).symm

/-- In a list whose sequences are distinct, removing every record with the
sequence of a member `r` leaves exactly the rest. -/
private theorem perm_filter_seq (r : Envelope T) :
    ∀ (l : List (Envelope T)), (l.map Envelope.sequence).Nodup → r ∈ l →
      l.Perm (r :: l.filter (fun e => !hasSeq r.sequence e)) := by
  intro l
  induction l with
  | nil => intro _ hr; simp at hr
  | cons x xs ih =>
      intro hnd hr
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
      obtain ⟨hx, hnd⟩ := hnd
      by_cases hxs : x.sequence = r.sequence
      · have hxr : x = r := by
          rcases List.mem_cons.mp hr with h | h
          · exact h.symm
          · exact absurd ⟨r, h, hxs.symm⟩ hx
        subst hxr
        have hf : xs.filter (fun e => !hasSeq x.sequence e) = xs := by
          rw [List.filter_eq_self]
          intro a ha
          simp [hasSeq]
          intro heq
          exact hx ⟨a, ha, heq⟩
        have hx' : (!hasSeq x.sequence x) = false := by simp [hasSeq]
        simp only [List.filter_cons, hx', Bool.false_eq_true, if_false, hf]
        exact List.Perm.refl _
      · have hr' : r ∈ xs := by
          rcases List.mem_cons.mp hr with h | h
          · exact absurd (h ▸ rfl) hxs
          · exact h
        have hfx : (!hasSeq r.sequence x) = true := by simp [hasSeq, hxs]
        simp only [List.filter_cons, hfx, if_true]
        exact ((ih hnd hr').cons x).trans (List.Perm.swap r x _)

private theorem inv_of_perm_sublist {s s' : State T} (h : Inv s) (l : List Nat)
    (hp : (seqs s').Perm l) (hl : l.Sublist (seqs s)) (hn : s.nextSequence ≤ s'.nextSequence) :
    Inv s' :=
  ⟨hp.nodup_iff.mpr (h.nodup.sublist hl),
   fun n hn' => Nat.lt_of_lt_of_le (h.below n (hl.subset (hp.mem_iff.mp hn'))) hn⟩

private theorem inv_of_perm {s s' : State T} (h : Inv s)
    (hp : (all s').Perm (all s)) (hn : s.nextSequence ≤ s'.nextSequence) : Inv s' :=
  inv_of_perm_sublist h (seqs s) (hp.map _) (List.Sublist.refl _) hn

private theorem inflight_nodup {s : State T} (h : Inv s) :
    (s.inflight.map Envelope.sequence).Nodup := by
  refine h.nodup.sublist ?_
  simp only [seqs, all, List.map_append]
  exact (List.sublist_append_right _ _).trans (List.sublist_append_left _ _)

private theorem failed_nodup {s : State T} (h : Inv s) :
    (s.failed.map Envelope.sequence).Nodup := by
  refine h.nodup.sublist ?_
  simp only [seqs, all, List.map_append]
  exact List.sublist_append_right _ _

/-- The retained sequences after a step are a permutation of a sub-list of the
retained sequences before it. -/
def SeqRel (s s' : State T) : Prop := ∃ l, (seqs s').Perm l ∧ l.Sublist (seqs s)

private theorem seqRel_refl (s : State T) : SeqRel s s :=
  ⟨seqs s, List.Perm.refl _, List.Sublist.refl _⟩

private theorem seqRel_of_perm {s s' : State T} (hp : (all s').Perm (all s)) : SeqRel s s' :=
  ⟨seqs s, hp.map _, List.Sublist.refl _⟩

/-- Every operation except `enqueue` only permutes or drops retained records. -/
theorem step_seqRel (s : State T) (op : Op T) (h : Inv s) (hop : ∀ p, op ≠ .enqueue p) :
    SeqRel s (step s op).1 := by
  cases op with
  | enqueue p => exact absurd rfl (hop p)
  | claim g =>
      simp only [step, claim]
      split
      · exact seqRel_refl s
      · split
        · exact seqRel_refl s
        · split
          · exact seqRel_refl s
          · rename_i r rest hpend
            refine ⟨seqs s, ?_, List.Sublist.refl _⟩
            have hi := (perm_insertOrdered
              ({ r with generation := s.generation, attempt := r.attempt + 1 } : Envelope T)
              s.inflight).map Envelope.sequence
            simp only [List.map_cons] at hi
            simp only [seqs, all, hpend, List.map_append, List.map_cons, List.cons_append]
            refine ((hi.append_left _).append_right _).trans ?_
            simp only [List.append_assoc, List.cons_append]
            exact List.perm_middle
  | ack g t =>
      simp only [step, ack]
      split
      · exact seqRel_refl s
      · split
        · exact seqRel_refl s
        · split
          · exact seqRel_refl s
          · refine ⟨_, List.Perm.refl _, ?_⟩
            simp only [seqs, all, List.map_append]
            exact ((List.filter_sublist.map _).append (List.filter_sublist.map _)).append
              (List.filter_sublist.map _)
  | fail g q =>
      simp only [step, fail]
      split
      · exact seqRel_refl s
      · split
        · exact seqRel_refl s
        · rename_i r hfind
          have hr : r ∈ s.inflight := List.mem_of_find?_eq_some hfind
          have hq : r.sequence = q := by
            have := List.find?_some hfind
            simpa [hasSeq] using this
          have hperm := perm_filter_seq r s.inflight (inflight_nodup h) hr
          rw [hq] at hperm
          by_cases hx : s.policy.retryBudget < r.attempt
          · simp only [hx, decide_true, if_true]
            refine ⟨_, List.Perm.refl _, ?_⟩
            simp only [seqs, all, List.map_append]
            exact ((List.Sublist.refl _).append (List.filter_sublist.map _)).append
              (List.Sublist.refl _)
          · simp only [hx, decide_false, Bool.false_eq_true, if_false]
            refine seqRel_of_perm ?_
            simp only [all]
            have lhs : (s.pending ++ s.inflight.filter (fun e => !hasSeq q e) ++
                insertOrdered r s.failed).Perm
                (r :: (s.pending ++ s.inflight.filter (fun e => !hasSeq q e) ++ s.failed)) :=
              ((perm_insertOrdered r s.failed).append_left _).trans List.perm_middle
            have rhs : (s.pending ++ s.inflight ++ s.failed).Perm
                (r :: (s.pending ++ s.inflight.filter (fun e => !hasSeq q e) ++ s.failed)) := by
              refine ((hperm.append_left s.pending).append_right s.failed).trans ?_
              exact List.perm_middle.append_right s.failed
            exact lhs.trans rhs.symm
  | retryNow g q =>
      simp only [step, retryNow]
      split
      · exact seqRel_refl s
      · split
        · exact seqRel_refl s
        · rename_i r hfind
          have hr : r ∈ s.failed := List.mem_of_find?_eq_some hfind
          have hq : r.sequence = q := by
            have := List.find?_some hfind
            simpa [hasSeq] using this
          have hperm := perm_filter_seq r s.failed (failed_nodup h) hr
          rw [hq] at hperm
          refine seqRel_of_perm ?_
          simp only [all]
          have lhs : (insertOrdered r s.pending ++ s.inflight ++
              s.failed.filter (fun e => !hasSeq q e)).Perm
              (r :: (s.pending ++ s.inflight ++ s.failed.filter (fun e => !hasSeq q e))) := by
            have := ((perm_insertOrdered r s.pending).append_right s.inflight).append_right
              (s.failed.filter (fun e => !hasSeq q e))
            simpa using this
          have rhs : (s.pending ++ s.inflight ++ s.failed).Perm
              (r :: (s.pending ++ s.inflight ++ s.failed.filter (fun e => !hasSeq q e))) :=
            (hperm.append_left _).trans List.perm_middle
          exact lhs.trans rhs.symm
  | reconnect g =>
      simp only [step, reconnect]
      split
      · exact seqRel_refl s
      · split
        · exact seqRel_refl s
        · refine ⟨seqs s, ?_, List.Sublist.refl _⟩
          have hseq : (Envelope.sequence ∘ rewriteGeneration (T := T) g) = Envelope.sequence := by
            funext e; rfl
          simp only [seqs, all, List.append_nil, List.map_map, hseq]
          refine List.Perm.map _ ?_
          exact (perm_insertAll s.failed _).trans
            ((perm_insertAll s.inflight s.pending).append_right s.failed)


private theorem inv_of_seqRel {s s' : State T} (h : Inv s) (hr : SeqRel s s')
    (hn : s.nextSequence ≤ s'.nextSequence) : Inv s' :=
  let ⟨l, hp, hl⟩ := hr
  inv_of_perm_sublist h l hp hl hn

private theorem enqueue_seqs (s : State T) (p : T) :
    (seqs (step s (.enqueue p)).1).Perm (s.nextSequence :: seqs s) := by
  simp only [step, enqueue, seqs, all, List.map_append, List.map_cons, List.map_nil,
    List.append_assoc]
  exact List.perm_middle

/-- No operation duplicates a retained record or reuses a sequence. -/
theorem step_preserves_inv (s : State T) (op : Op T) (h : Inv s) : Inv (step s op).1 := by
  cases op with
  | enqueue p =>
      have hp := enqueue_seqs s p
      have hn : (step s (.enqueue p)).1.nextSequence = s.nextSequence + 1 := rfl
      refine ⟨hp.nodup_iff.mpr (List.nodup_cons.mpr ⟨fun hm => Nat.lt_irrefl _ (h.below _ hm),
        h.nodup⟩), ?_⟩
      intro n hn'
      rw [hn]
      rcases List.mem_cons.mp (hp.mem_iff.mp hn') with h1 | h1
      · omega
      · exact Nat.lt_succ_of_lt (h.below n h1)
  | claim g =>
      exact inv_of_seqRel h (step_seqRel s _ h (fun _ hc => by cases hc))
        (step_nextSequence_monotone s _)
  | ack g t =>
      exact inv_of_seqRel h (step_seqRel s _ h (fun _ hc => by cases hc))
        (step_nextSequence_monotone s _)
  | fail g q =>
      exact inv_of_seqRel h (step_seqRel s _ h (fun _ hc => by cases hc))
        (step_nextSequence_monotone s _)
  | retryNow g q =>
      exact inv_of_seqRel h (step_seqRel s _ h (fun _ hc => by cases hc))
        (step_nextSequence_monotone s _)
  | reconnect g =>
      exact inv_of_seqRel h (step_seqRel s _ h (fun _ hc => by cases hc))
        (step_nextSequence_monotone s _)

/-! ### Watermark integrity and the beyond-boundary ACK refusal

An `ack(generation, through)` with `through ≥ nextSequence` acknowledges a
sequence that was never assigned. Accepting it would lift the watermark over a
not-yet-enqueued sequence; the next enqueue would retain a record at or below
the watermark, and the receiver's genuine ACK for it would be `unchanged` — the
record would be stranded. The core therefore refuses it
(`ack_beyond_sent_refused`), and the watermark-integrity invariant holds for
every operation unconditionally (`step_preserves_ackInv`); in particular the
formerly stranded trace now advances (`ack_beyond_boundary_does_not_strand`). -/

/-- Every retained record lies strictly above the watermark, and the watermark
lies inside the assigned sequence space. -/
structure AckInv (s : State T) : Prop where
  bound : ∀ c, s.ackedThrough = some c → c < s.nextSequence
  above : ∀ n ∈ seqs s, ∀ c, s.ackedThrough = some c → c < n

private theorem ackInv_of_seqRel {s s' : State T} (ha : AckInv s) (hr : SeqRel s s')
    (hack : s'.ackedThrough = s.ackedThrough) (hn : s.nextSequence ≤ s'.nextSequence) :
    AckInv s' := by
  obtain ⟨l, hp, hl⟩ := hr
  refine ⟨fun c hc => ?_, fun n hn' c hc => ?_⟩
  · rw [hack] at hc
    exact Nat.lt_of_lt_of_le (ha.bound c hc) hn
  · rw [hack] at hc
    exact ha.above n (hl.subset (hp.mem_iff.mp hn')) c hc

theorem ackInv_empty (policy : Policy) (generation : Nat) :
    AckInv (State.empty policy generation : State T) :=
  ⟨by simp [State.empty], by simp [seqs, all, State.empty]⟩

/-- An acknowledgement at or beyond the sequence boundary, from the current
attachment, is refused: no state change, no reader invalidated, and the
refusal names the boundary. -/
theorem ack_beyond_sent_refused (s : State T) (through : Nat)
    (beyond : s.nextSequence ≤ through) :
    ack s s.generation through = (s, Change.none, .beyondSent s.nextSequence) := by
  simp [ack, beyond]

/-- The refusal is exactly the beyond-boundary case: from the current
attachment, `beyondSent` is returned if and only if `through ≥ nextSequence`. -/
theorem ack_beyondSent_iff (s : State T) (through n : Nat) :
    (ack s s.generation through).2.2 = .beyondSent n ↔
      s.nextSequence ≤ through ∧ n = s.nextSequence := by
  unfold ack
  by_cases hb : s.nextSequence ≤ through
  · simp [hb, eq_comm]
  · by_cases hc : ackCovered s.ackedThrough through = true <;> simp [hb, hc]

/-- Watermark integrity is preserved by every operation. -/
theorem step_preserves_ackInv (s : State T) (op : Op T) (h : Inv s) (ha : AckInv s) :
    AckInv (step s op).1 := by
  cases op with
  | enqueue p =>
      have hp := enqueue_seqs s p
      refine ⟨fun c hc => Nat.lt_succ_of_lt (ha.bound c hc), ?_⟩
      intro n hn c hc
      rcases List.mem_cons.mp (hp.mem_iff.mp hn) with h1 | h1
      · subst h1; exact ha.bound c hc
      · exact ha.above n h1 c hc
  | ack g t =>
      simp only [step, ack]
      split
      · exact ha
      · split
        · exact ha
        · rename_i hb
          split
          · exact ha
          · refine ⟨fun c hc => ?_, fun n hn c hc => ?_⟩
            · simp at hc
              show c < s.nextSequence
              omega
            · simp at hc
              subst hc
              simp only [seqs, all, List.map_append, List.mem_append, List.mem_map,
                List.mem_filter, above, decide_eq_true_eq] at hn
              rcases hn with (⟨e, ⟨_, he⟩, rfl⟩ | ⟨e, ⟨_, he⟩, rfl⟩) | ⟨e, ⟨_, he⟩, rfl⟩ <;>
                exact he
  | claim g =>
      refine ackInv_of_seqRel ha (step_seqRel s _ h (fun _ hc => by cases hc)) ?_
        (step_nextSequence_monotone s _)
      simp only [step, claim]; (repeat' split) <;> rfl
  | fail g q =>
      refine ackInv_of_seqRel ha (step_seqRel s _ h (fun _ hc => by cases hc)) ?_
        (step_nextSequence_monotone s _)
      simp only [step, fail]; (repeat' split) <;> rfl
  | retryNow g q =>
      refine ackInv_of_seqRel ha (step_seqRel s _ h (fun _ hc => by cases hc)) ?_
        (step_nextSequence_monotone s _)
      simp only [step, retryNow]; (repeat' split) <;> rfl
  | reconnect g =>
      refine ackInv_of_seqRel ha (step_seqRel s _ h (fun _ hc => by cases hc)) ?_
        (step_nextSequence_monotone s _)
      simp only [step, reconnect]; (repeat' split) <;> rfl

/-- Under watermark integrity no retained record is stranded: a genuine
cumulative ACK for any retained record's sequence, from the current attachment,
advances (it is neither refused nor `unchanged`). -/
theorem retained_record_ack_advances (s : State T) (h : Inv s) (ha : AckInv s)
    (n : Nat) (hn : n ∈ seqs s) :
    (ack s s.generation n).2.2 = .advanced n := by
  have hlt : n < s.nextSequence := h.below n hn
  have hb : ¬ s.nextSequence ≤ n := by omega
  have hc : ackCovered s.ackedThrough n = false := by
    cases hs : s.ackedThrough with
    | none => rfl
    | some c =>
        have := ha.above n hn c hs
        simp [ackCovered]; omega
  simp [ack, hb, hc]

/-- The trace that used to strand a record: an ACK past the sequence boundary
is now refused, so the record later assigned that sequence is acknowledged by
the receiver's genuine ACK. -/
theorem ack_beyond_boundary_does_not_strand :
    let s0 : State Nat := State.empty ⟨1, 0, 1, 1⟩ 0
    let s1 := (step s0 (.ack 0 5)).1
    let s2 := (step s1 (.enqueue 42)).1
    (step s0 (.ack 0 5)).2.2 = .ack (.beyondSent 0) ∧
      s1 = s0 ∧
      s2.pending.map Envelope.sequence = [0] ∧
      (step s2 (.ack 0 0)).2.2 = .ack (.advanced 0) ∧
      (step s2 (.ack 0 0)).1.pending = [] := by
  decide

/-! ### Reader invalidation soundness

The reactive shells invalidate exactly the reader kinds `step` reports. Every
change to a projected reader is reported, so no reader can observe a stale
projection. (The converse — no spurious invalidation — is not claimed: a
reconnect that replays only parked records conservatively reports `inflight`.) -/

/-- Each reader whose projection changed is invalidated. -/
def ChangeSound (s s' : State T) (c : Change) : Prop :=
  (s'.pending ≠ s.pending → c.pending = true) ∧
    (s'.inflight ≠ s.inflight → c.inflight = true) ∧
    (s'.ackedThrough ≠ s.ackedThrough → c.ackedThrough = true) ∧
    (s'.retry ≠ s.retry → c.retry = true)

private theorem filter_eq_of_length {l : List (Envelope T)} {p : Envelope T → Bool}
    (h : (l.filter p).length = l.length) : l.filter p = l :=
  List.filter_eq_self.mpr (List.length_filter_eq_length_iff.mp h)

/-- Every reader whose projection a step changes is reported as invalidated. -/
theorem step_change_sound (s : State T) (op : Op T) :
    ChangeSound s (step s op).1 (step s op).2.1 := by
  cases op with
  | enqueue p => simp [ChangeSound, step, enqueue]
  | claim g =>
      simp only [step, claim]
      split
      · simp [ChangeSound]
      · split
        · simp [ChangeSound]
        · split
          · simp [ChangeSound]
          · refine ⟨fun _ => rfl, fun _ => rfl, fun h => absurd rfl h, ?_⟩
            intro h
            cases hr : retryIs s.retry _ <;> simp_all
  | ack g t =>
      simp only [step, ack]
      split
      · simp [ChangeSound]
      · split
        · simp [ChangeSound]
        · split
          · simp [ChangeSound]
          · refine ⟨?_, ?_, fun _ => rfl, ?_⟩
            · intro h
              simp only [decide_eq_true_eq]
              intro hl
              exact h (filter_eq_of_length hl)
            · intro h
              simp only [decide_eq_true_eq]
              intro hl
              exact h (filter_eq_of_length hl)
            · intro h
              cases hr : retryAtOrBelow s.retry t <;> simp_all
  | fail g q =>
      simp only [step, fail]
      split
      · simp [ChangeSound]
      · split
        · simp [ChangeSound]
        · exact ⟨fun h => absurd rfl h, fun _ => rfl, fun h => absurd rfl h, fun _ => rfl⟩
  | retryNow g q =>
      simp only [step, retryNow]
      split
      · simp [ChangeSound]
      · split
        · simp [ChangeSound]
        · refine ⟨fun _ => rfl, fun h => absurd rfl h, fun h => absurd rfl h, ?_⟩
          intro h
          cases hr : retryIs s.retry q <;> simp_all
  | reconnect g =>
      simp only [step, reconnect]
      split
      · simp [ChangeSound]
      · split
        · simp [ChangeSound]
        · refine ⟨?_, ?_, fun h => absurd rfl h, ?_⟩
          · intro h
            cases hp : s.pending with
            | cons _ _ => simp
            | nil =>
                cases hi : s.inflight with
                | cons _ _ => simp; omega
                | nil =>
                    cases hf : s.failed with
                    | cons _ _ => simp
                    | nil => simp [hp, hi, hf, insertAll] at h
          · intro h
            cases hi : s.inflight with
            | cons _ _ => simp; omega
            | nil => simp [hi] at h
          · intro h
            cases hr : s.retry with
            | some _ => simp
            | none => simp [hr] at h

end LazilyFormal.Egress
