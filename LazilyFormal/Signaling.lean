/-
! Signaling protocol — per-connection lifecycle FSM + anti-spoof forwarding.

The formal counterpart of `lazily-spec/protocol.md` § "Signaling Protocol
(WebSocket)" (the distributed plane's peer-discovery layer) and its schema
`lazily-spec/schemas/signaling.json`. Two pure cores are fixed here:

- **Connection lifecycle.** A signaling WebSocket connection is
  `Disconnected → Joining → Joined → Closed`: the client `join`s, the server
  `welcome`s it into the room, offer/answer/ice/relay frames flow while
  `Joined`, and `leave`/`socketClose` terminate the connection. Fail-closed: a
  signaling op (offer/answer/ice/relay) before the connection has joined is
  rejected with no lifecycle change; a second `join` on an already-joined
  connection is a no-op; `Closed` is terminal and absorbing.

- **Anti-spoofing** (`protocol.md` § "Anti-spoofing"): "The `from` field on
  every forwarded frame is the sender connection's registered peer id, never
  client-supplied." Client→server directed frames carry a `to` (target) and no
  `from`; the server stamps `from` from the *connection's server-registered
  peer id* when forwarding. `forwarded_from_is_registered` pins that the stamped
  `from` equals the registered id regardless of the client-supplied target —
  the load-bearing property every binding cites.

`step`, `forward`, and `relay` are total functions of their inputs, so these
guarantees hold for *every* input — the universal result no finite fixture
suite can establish.
-/

import LazilyFormal.Primitive

namespace LazilyFormal.Signaling

/-- A peer identifier (abstract; a `Nat` stand-in for the wire integer id). -/
abbrev PeerId := Nat

/-- The lifecycle state of one signaling WebSocket connection. -/
inductive ConnState where
  /-- Socket open, not yet registered with the session. -/
  | disconnected : ConnState
  /-- Client sent `join`; awaiting the server's `welcome`. -/
  | joining : ConnState
  /-- Registered in the room; may send/receive offer/answer/ice/relay. -/
  | joined : ConnState
  /-- Terminal: `leave` or socket close. -/
  | closed : ConnState
  deriving Repr, DecidableEq

/-- An event driving one connection through its lifecycle. Signaling ops
    (`offer`/`answer`/`ice`/`relay`) never change the connection's own lifecycle
    state — they are routing events; whether they are *forwarded* is governed by
    `relay` below. -/
inductive ConnEvent where
  /-- Client registers with the session under a peer id (server-assigned/registered). -/
  | join (peer : PeerId) : ConnEvent
  /-- Server admits the connection into the room (roster delivered). -/
  | welcome : ConnEvent
  | offer : ConnEvent
  | answer : ConnEvent
  | ice : ConnEvent
  | relay : ConnEvent
  /-- Client leaves the session. -/
  | leave : ConnEvent
  /-- Transport-level socket close. -/
  | socketClose : ConnEvent
  deriving Repr

/-- One signaling connection: lifecycle state plus the server-registered peer id
    (set on `join`, cleared on close). The registered id is the identity the
    server stamps onto forwarded frames (`forward`). -/
structure Conn where
  state : ConnState
  registered : Option PeerId
  deriving Repr

/-- One lifecycle transition. `join` is accepted only from `disconnected`
    (a second `join` is a no-op); `welcome` only advances a `joining` connection;
    signaling ops never change lifecycle state; `leave`/`socketClose` go to the
    terminal `closed` state and clear the registered id. -/
def step (c : Conn) : ConnEvent → Conn
  | ConnEvent.join p =>
    match c.state with
    | ConnState.disconnected => { state := ConnState.joining, registered := some p }
    | _ => c
  | ConnEvent.welcome =>
    match c.state with
    | ConnState.joining => { c with state := ConnState.joined }
    | _ => c
  | ConnEvent.offer => c
  | ConnEvent.answer => c
  | ConnEvent.ice => c
  | ConnEvent.relay => c
  | ConnEvent.leave => { state := ConnState.closed, registered := none }
  | ConnEvent.socketClose => { state := ConnState.closed, registered := none }

/-- A connection is well-formed when it holds a server-registered peer id exactly
    while it is in the session (`joining`/`joined`), and none otherwise
    (`disconnected`/`closed`). -/
def Conn.WellFormed (c : Conn) : Prop :=
  match c.state with
  | ConnState.disconnected => c.registered = none
  | ConnState.joining => c.registered ≠ none
  | ConnState.joined => c.registered ≠ none
  | ConnState.closed => c.registered = none

/-! ## Lifecycle theorems -/

/-- Fail-closed: an `offer` before the connection has joined is rejected — the
    connection is unchanged. -/
theorem offer_before_join_rejected (reg : Option PeerId) :
    step ⟨ConnState.disconnected, reg⟩ ConnEvent.offer = ⟨ConnState.disconnected, reg⟩ := rfl

/-- Fail-closed: an `answer` before the connection has joined is rejected. -/
theorem answer_before_join_rejected (reg : Option PeerId) :
    step ⟨ConnState.disconnected, reg⟩ ConnEvent.answer = ⟨ConnState.disconnected, reg⟩ := rfl

/-- Fail-closed: an `ice` candidate before the connection has joined is rejected. -/
theorem ice_before_join_rejected (reg : Option PeerId) :
    step ⟨ConnState.disconnected, reg⟩ ConnEvent.ice = ⟨ConnState.disconnected, reg⟩ := rfl

/-- Fail-closed: a `relay` before the connection has joined is rejected. -/
theorem relay_before_join_rejected (reg : Option PeerId) :
    step ⟨ConnState.disconnected, reg⟩ ConnEvent.relay = ⟨ConnState.disconnected, reg⟩ := rfl

/-- `join` from `disconnected` advances the connection to `joining`. -/
theorem join_from_disconnected_advances (p : PeerId) (reg : Option PeerId) :
    (step ⟨ConnState.disconnected, reg⟩ (ConnEvent.join p)).state = ConnState.joining := rfl

/-- `join` from `disconnected` records the joining peer's id as the connection's
    server-registered identity. -/
theorem join_registers_peer (p : PeerId) (reg : Option PeerId) :
    (step ⟨ConnState.disconnected, reg⟩ (ConnEvent.join p)).registered = some p := rfl

/-- `welcome` admits a `joining` connection into the room. -/
theorem welcome_admits_joining (reg : Option PeerId) :
    (step ⟨ConnState.joining, reg⟩ ConnEvent.welcome).state = ConnState.joined := rfl

/-- A second `join` on an already-`joined` connection is a no-op. -/
theorem already_joined_rejects (p : PeerId) (reg : Option PeerId) :
    step ⟨ConnState.joined, reg⟩ (ConnEvent.join p) = ⟨ConnState.joined, reg⟩ := rfl

/-- `leave` is terminal: from any state it goes to `closed`. -/
theorem leave_terminal (c : Conn) : (step c ConnEvent.leave).state = ConnState.closed := rfl

/-- `socketClose` is absorbing: from any state it goes to `closed`. -/
theorem close_absorbing (c : Conn) :
    (step c ConnEvent.socketClose).state = ConnState.closed := rfl

/-- `closed` is terminal: no event escapes it. -/
theorem closed_terminal (reg : Option PeerId) (e : ConnEvent) :
    (step ⟨ConnState.closed, reg⟩ e).state = ConnState.closed := by
  cases e <;> rfl

/-- `step` preserves well-formedness: the registered-id / lifecycle invariant is
    maintained across every transition. -/
theorem step_preserves_wellFormed (c : Conn) (e : ConnEvent) (wf : c.WellFormed) :
    (step c e).WellFormed := by
  obtain ⟨st, reg⟩ := c
  cases e <;> cases st <;> simp_all [step, Conn.WellFormed]

/-! ## Anti-spoof forwarding -/

/-- A client→server directed signaling frame. It carries a target `toPeer` and
    an opaque body (SDP / ICE candidate / relay payload, elided). Crucially it
    carries **no** client-supplied `from` field — the client cannot name the
    sender. -/
structure DirectedFrame where
  toPeer : PeerId
  deriving Repr

/-- A server→client forwarded signaling frame. The `fromPeer` field is
    server-stamped from the sender connection's registered id. -/
structure ForwardedFrame where
  fromPeer : PeerId
  toPeer : PeerId
  deriving Repr

/-- Forward a directed frame: stamp the sender connection's **registered** peer
    id as `fromPeer`, preserving the client-supplied target. The registered id is
    the only source of `fromPeer`; no client-supplied value can influence it. -/
def forward (registered : PeerId) (f : DirectedFrame) : ForwardedFrame :=
  { fromPeer := registered, toPeer := f.toPeer }

/-- **Anti-spoof invariant** (`protocol.md` § "Anti-spoofing"): the forwarded
    frame's `from` equals the sender connection's server-registered peer id,
    regardless of the client-supplied target (or any other frame content). -/
theorem forwarded_from_is_registered (registered : PeerId) (f : DirectedFrame) :
    (forward registered f).fromPeer = registered := rfl

/-- Forwarding routes to the client-supplied target: the delivery `to` is
    preserved. -/
theorem forwarded_to_preserved (registered : PeerId) (f : DirectedFrame) :
    (forward registered f).toPeer = f.toPeer := rfl

/-- Server-side handling of a directed frame from a connection: it is forwarded
    (with the server-stamped `from`) only when the connection is `joined` and
    holds a registered id; otherwise it is dropped (fail-closed). -/
def relay (c : Conn) (f : DirectedFrame) : Option ForwardedFrame :=
  match c.state with
  | ConnState.joined =>
    match c.registered with
    | some p => some (forward p f)
    | none => none
  | _ => none

/-- Fail-closed routing: a directed frame from a connection that has not joined
    is dropped (never forwarded). -/
theorem relay_before_join_dropped (c : Conn) (f : DirectedFrame)
    (h : c.state ≠ ConnState.joined) : relay c f = none := by
  cases hs : c.state <;> simp only [relay, hs] <;> first | rfl | exact absurd hs h

/-- A frame relayed from a `joined`, registered connection carries the
    server-stamped registered id as its `from` — spoofing is impossible even
    though the client chose the target `f`. -/
theorem relayed_from_is_registered (p : PeerId) (f : DirectedFrame) (ff : ForwardedFrame)
    (h : relay ⟨ConnState.joined, some p⟩ f = some ff) : ff.fromPeer = p := by
  simp only [relay] at h
  injection h with h
  subst h
  rfl

end LazilyFormal.Signaling
