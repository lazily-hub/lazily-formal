/-
! Transport-agnostic reactive egress — formal model (`#lzegress`).

The core, rather than its transport Effect, owns sequence assignment, the
unacknowledged window, the acknowledgement watermark, retry budget, and the
producer-generation fence.
-/

namespace LazilyFormal.Egress

variable {T : Type}

structure Envelope (T : Type) where
  generation : Nat
  sequence : Nat
  attempt : Nat
  payload : T

structure State (T : Type) where
  generation : Nat
  nextSequence : Nat
  ackedThrough : Option Nat
  pending : List (Envelope T)
  inflight : List (Envelope T)

def enqueue (s : State T) (payload : T) : State T × Nat :=
  let sequence := s.nextSequence
  ({ s with
      nextSequence := sequence + 1
      pending := s.pending ++ [{
        generation := s.generation
        sequence := sequence
        attempt := 0
        payload := payload
      }] },
   sequence)

/-- Enqueue allocates exactly one fresh, larger sequence boundary. -/
theorem enqueue_sequence_monotone (s : State T) (payload : T) :
    s.nextSequence < (enqueue s payload).1.nextSequence := by
  simp [enqueue]

def advanceAck (current : Option Nat) (through : Nat) : Option Nat :=
  match current with
  | none => some through
  | some watermark => some (max watermark through)

def watermark : Option Nat → Nat
  | none => 0
  | some through => through

def acknowledge (s : State T) (through : Nat) : State T :=
  { s with ackedThrough := advanceAck s.ackedThrough through }

/-- A cumulative acknowledgement never moves its projected watermark backward. -/
theorem acknowledgement_monotone (s : State T) (through : Nat) :
    watermark s.ackedThrough ≤ watermark (acknowledge s through).ackedThrough := by
  cases h : s.ackedThrough with
  | none =>
      simp [acknowledge, advanceAck, watermark, h]
  | some current =>
      simp [acknowledge, advanceAck, watermark, h, Nat.le_max_left]

/-- Every send-side transition passes through this generation fence. -/
def fenced (s : State T) (suppliedGeneration : Nat) (transition : State T → State T) :
    State T :=
  if suppliedGeneration = s.generation then transition s else s

/-- A stale transport attachment has no write authority and changes no state. -/
theorem stale_generation_preserves_state
    (s : State T)
    (suppliedGeneration : Nat)
    (transition : State T → State T)
    (stale : suppliedGeneration ≠ s.generation) :
    fenced s suppliedGeneration transition = s := by
  simp [fenced, stale]

def rewriteGeneration (generation : Nat) (envelope : Envelope T) : Envelope T :=
  { envelope with generation := generation }

def reconnect (s : State T) (newGeneration : Nat) : State T :=
  if s.generation < newGeneration then
    { s with
      generation := newGeneration
      pending :=
        (s.inflight ++ s.pending).map (rewriteGeneration newGeneration)
      inflight := [] }
  else
    s

/-- A legitimate reconnect advances the fence and preserves ACK progress. -/
theorem reconnect_advances_and_preserves_ack
    (s : State T)
    (newGeneration : Nat)
    (advanced : s.generation < newGeneration) :
    (reconnect s newGeneration).generation = newGeneration ∧
      (reconnect s newGeneration).ackedThrough = s.ackedThrough := by
  simp [reconnect, advanced]

/-- `retryBudget` counts retries after the first send attempt. -/
def retryPermitted (retryBudget attempt : Nat) : Prop :=
  1 ≤ attempt ∧ attempt ≤ retryBudget + 1

/-- The number of permitted send attempts is bounded by first-attempt + budget. -/
theorem retry_attempts_bounded
    (retryBudget attempt : Nat)
    (permitted : retryPermitted retryBudget attempt) :
    attempt ≤ retryBudget + 1 :=
  permitted.2

def retryBackoff (base ceiling attempt : Nat) : Nat :=
  min ceiling (base * 2 ^ (attempt - 1))

/-- Exponential retry delay is always capped by the configured ceiling. -/
theorem retry_backoff_bounded (base ceiling attempt : Nat) :
    retryBackoff base ceiling attempt ≤ ceiling := by
  simp [retryBackoff, Nat.min_le_left]

end LazilyFormal.Egress
