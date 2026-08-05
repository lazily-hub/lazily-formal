/-
! Snapshot-plus-event boundary ingress (`#lzingressadapters`).

This model is the subscription shell around `Ingress`, not a second value
admission primitive. It owns only producer generation, channel cursor, bounded
future-event buffering, membership, validation, and one-shot receipt facts.
-/

namespace LazilyFormal.BoundaryIngress

inductive Phase where
  | detached
  | bootstrapping
  | live
  | replayRequired
  | backpressured
  | invalid
  deriving DecidableEq, Repr

structure State where
  phase : Phase
  generation : Nat
  cursor : Option Nat
  buffered : List Nat
  sourceCount : Nat
  memberCount : Nat
  valid : Bool
  replayFrom : Option Nat
  staleEvents : Nat
  revision : Nat
  deriving DecidableEq, Repr

def initial : State :=
  { phase := .detached
    generation := 0
    cursor := none
    buffered := []
    sourceCount := 0
    memberCount := 0
    valid := true
    replayFrom := none
    staleEvents := 0
    revision := 0 }

def subscribe (s : State) (generation : Nat) : State :=
  if generation < s.generation then s
  else
    { s with
      phase := .bootstrapping
      generation := generation
      cursor := none
      buffered := []
      sourceCount := 0
      memberCount := 0
      replayFrom := none
      revision := s.revision + 1 }

/-- A hot resubscription cannot retain buffered frames from the old producer. -/
theorem restart_during_bootstrap_fences_old_buffer
    (s : State)
    (generation : Nat)
    (fresh : ¬ generation < s.generation) :
    (subscribe s generation).generation = generation ∧
      (subscribe s generation).buffered = [] ∧
      (subscribe s generation).cursor = none := by
  simp [subscribe, fresh]

def staleEvent (s : State) (generation : Nat) : State :=
  if generation < s.generation then
    { s with staleEvents := s.staleEvents + 1, revision := s.revision + 1 }
  else
    s

/-- Stale-generation telemetry cannot move cursor or value membership. -/
theorem stale_generation_preserves_authority
    (s : State)
    (generation : Nat)
    (stale : generation < s.generation) :
    (staleEvent s generation).generation = s.generation ∧
      (staleEvent s generation).cursor = s.cursor ∧
      (staleEvent s generation).sourceCount = s.sourceCount := by
  simp [staleEvent, stale]

def applySnapshot
    (s : State)
    (generation cursor sourceCount memberCount : Nat)
    (valid : Bool) : State :=
  if generation < s.generation then staleEvent s generation
  else
    { s with
      phase := if valid then .live else .invalid
      generation := generation
      cursor := some cursor
      buffered := s.buffered.filter (cursor < ·)
      sourceCount := sourceCount
      memberCount := memberCount
      valid := valid
      replayFrom := none
      revision := s.revision + 1 }

/-- A covering snapshot is one state replacement and advances one revision. -/
theorem snapshot_is_one_atomic_observation
    (s : State)
    (generation cursor sourceCount memberCount : Nat)
    (valid : Bool)
    (fresh : ¬ generation < s.generation) :
    (applySnapshot s generation cursor sourceCount memberCount valid).revision =
      s.revision + 1 := by
  simp [applySnapshot, fresh]

def admitFuture (maxBuffered cursor : Nat) (s : State) : State :=
  if cursor ∈ s.buffered then s
  else if s.buffered.length < maxBuffered then
    { s with buffered := s.buffered ++ [cursor], revision := s.revision + 1 }
  else
    { s with
      phase := .backpressured
      replayFrom := some (s.cursor.map (· + 1) |>.getD 0)
      revision := s.revision + 1 }

/-- A full bounded buffer requests cold replay instead of growing without bound. -/
theorem full_buffer_backpressures
    (s : State)
    (maxBuffered cursor : Nat)
    (novel : cursor ∉ s.buffered)
    (full : ¬ s.buffered.length < maxBuffered) :
    (admitFuture maxBuffered cursor s).phase = .backpressured := by
  simp [admitFuture, novel, full]

def detectGap (s : State) (cursor : Nat) : State :=
  match s.cursor with
  | none => s
  | some current =>
      if cursor = current + 1 then
        { s with
          cursor := some cursor
          replayFrom := none
          phase := .live
          revision := s.revision + 1 }
      else if current < cursor then
        { s with
          phase := .replayRequired
          replayFrom := some (current + 1)
          buffered := s.buffered ++ [cursor]
          revision := s.revision + 1 }
      else
        s

/-- A future cursor derives the exact first missing cursor. -/
theorem cursor_gap_requests_cold_replay
    (s : State)
    (current cursor : Nat)
    (hasCursor : s.cursor = some current)
    (gap : current + 1 < cursor) :
    (detectGap s cursor).phase = .replayRequired ∧
      (detectGap s cursor).replayFrom = some (current + 1) := by
  have notNext : cursor ≠ current + 1 := by omega
  have future : current < cursor := by omega
  simp [detectGap, hasCursor, notNext, future]

structure Receipt where
  targetCount : Nat
  ackedCount : Nat
  deriving DecidableEq, Repr

def Receipt.converged (receipt : Receipt) : Prop :=
  0 < receipt.targetCount ∧ receipt.targetCount ≤ receipt.ackedCount

/-- Reaching zero subscribers is pending, never vacuous convergence. -/
theorem zero_member_delivery_not_converged (acked : Nat) :
    ¬ Receipt.converged { targetCount := 0, ackedCount := acked } := by
  simp [Receipt.converged]

def leaveMember (receipt : Receipt) : Receipt := receipt

/-- Membership departure cannot shrink a captured one-shot frontier. -/
theorem member_leave_preserves_receipt_targets (receipt : Receipt) :
    (leaveMember receipt).targetCount = receipt.targetCount := by
  rfl

def acknowledge (receipt : Receipt) (alreadyAcknowledged : Bool) : Receipt :=
  if alreadyAcknowledged then receipt
  else { receipt with ackedCount := receipt.ackedCount + 1 }

/-- Duplicate acknowledgements are state-idempotent. -/
theorem duplicate_acknowledgement_idempotent (receipt : Receipt) :
    acknowledge receipt true = receipt := by
  simp [acknowledge]

end LazilyFormal.BoundaryIngress
