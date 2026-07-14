/-
! Membership + failure detection (`#lzmemb`) — formal model.

The formal counterpart of `lazily-spec/docs/membership.md`. The Phi-accrual
arithmetic is abstracted away as the `suspectSignal` event; what is proved here
is the **SWIM state-machine safety**: which transitions are reachable, so a peer
never skips a state. The reactive `PeerSet` is exactly the `Alive` peers.
-/

namespace LazilyFormal.Membership

inductive PeerState where
  | alive
  | suspect
  | dead
  | left
  deriving DecidableEq

inductive Event where
  | heartbeat
  | suspectSignal
  | deadTimeout
  | leave

/-- The SWIM per-peer transition. Graceful `leave` always wins; a heartbeat
revives any non-left peer; suspicion only escalates `alive → suspect`; the dead
timeout only escalates `suspect → dead`. -/
def step : PeerState → Event → PeerState
  | _, Event.leave => PeerState.left
  | PeerState.left, Event.heartbeat => PeerState.left
  | _, Event.heartbeat => PeerState.alive
  | PeerState.alive, Event.suspectSignal => PeerState.suspect
  | s, Event.suspectSignal => s
  | PeerState.suspect, Event.deadTimeout => PeerState.dead
  | s, Event.deadTimeout => s

/-- A peer is in the reactive `PeerSet` iff its state is `Alive`. -/
def inAliveSet (s : PeerState) : Bool :=
  match s with
  | PeerState.alive => true
  | _ => false

theorem alive_set_iff (s : PeerState) : inAliveSet s = true ↔ s = PeerState.alive := by
  cases s <;> simp [inAliveSet]

/-! ## Transition safety -/

theorem alive_to_suspect : step PeerState.alive Event.suspectSignal = PeerState.suspect := rfl

theorem suspect_to_dead : step PeerState.suspect Event.deadTimeout = PeerState.dead := rfl

/-- `leave` from any state yields `Left`. -/
theorem any_to_left (s : PeerState) : step s Event.leave = PeerState.left := by
  cases s <;> rfl

/-- A heartbeat revives any non-left peer to `Alive`. -/
theorem heartbeat_revives (s : PeerState) (h : s ≠ PeerState.left) :
    step s Event.heartbeat = PeerState.alive := by
  cases s <;> simp_all [step]

/-- `Left` is terminal under every event. -/
theorem left_terminal (e : Event) : step PeerState.left e = PeerState.left := by
  cases e <;> rfl

/-- Suspicion only arises from `Alive`: a non-alive peer is unchanged by a
suspect signal. -/
theorem suspect_from_alive (s : PeerState) (h : s ≠ PeerState.alive) :
    step s Event.suspectSignal = s := by
  cases s <;> simp_all [step]

/-- Death only arises from `Suspect`: a non-suspect peer is unchanged by a dead
timeout. -/
theorem dead_from_suspect (s : PeerState) (h : s ≠ PeerState.suspect) :
    step s Event.deadTimeout = s := by
  cases s <;> simp_all [step]

end LazilyFormal.Membership
