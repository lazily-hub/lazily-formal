/-
! Signaling roster — room peer membership.

The formal counterpart of the roster the signaling server maintains per session
(`lazily-spec/protocol.md` § "Signaling Protocol (WebSocket)", the `welcome` /
`peer-joined` / `peer-left` server frames and their `peers` roster). The room
membership is modeled as a duplicate-free list of registered peer ids, with
`join` / `leave` operations and the `welcome` roster projection.

Fixed here:

- `join_adds_peer` / `leave_removes_peer`: `join` makes a peer present, `leave`
  makes it absent.
- `duplicate_join_rejected`: joining an id already in the room is a no-op — the
  roster never accumulates duplicates.
- `welcome_roster_excludes_self`: the `peers` roster delivered to a joining peer
  never contains that peer's own id (a peer is not told it is its own neighbor).

All operations are total functions, so these guarantees hold for every roster.
-/

import LazilyFormal.Primitive

namespace LazilyFormal.SignalingRoster

/-- A peer identifier (abstract; a `Nat` stand-in for the wire integer id). -/
abbrev PeerId := Nat

/-- A room roster: the peer ids currently registered in a session. -/
abbrev Roster := List PeerId

/-- Add a peer to the roster. Idempotent: joining an already-present id is a
    no-op, so the roster never accumulates duplicates. -/
def join (r : Roster) (p : PeerId) : Roster :=
  if p ∈ r then r else p :: r

/-- Remove a peer from the roster (all occurrences). -/
def leave (r : Roster) (p : PeerId) : Roster :=
  r.filter (· != p)

/-- The `peers` roster delivered to a joining peer `p`: every current member
    except `p` itself. -/
def welcomeRoster (r : Roster) (p : PeerId) : Roster :=
  r.filter (· != p)

/-! ## Theorems -/

/-- `join` makes the peer present in the roster. -/
theorem join_adds_peer (r : Roster) (p : PeerId) : p ∈ join r p := by
  unfold join
  split <;> simp_all

/-- `leave` makes the peer absent from the roster. -/
theorem leave_removes_peer (r : Roster) (p : PeerId) : p ∉ leave r p := by
  simp [leave, List.mem_filter]

/-- Joining an id already in the roster is a no-op — no duplicate is added. -/
theorem duplicate_join_rejected (r : Roster) (p : PeerId) (h : p ∈ r) :
    join r p = r := by
  simp only [join, if_pos h]

/-- The `welcome` roster delivered to a joining peer never contains that peer's
    own id. -/
theorem welcome_roster_excludes_self (r : Roster) (p : PeerId) :
    p ∉ welcomeRoster r p := by
  simp [welcomeRoster, List.mem_filter]

/-- The `welcome` roster preserves every *other* member: a peer `q ≠ p` present
    in the room appears in the roster delivered to `p`. -/
theorem welcome_roster_keeps_others (r : Roster) (p q : PeerId)
    (hq : q ∈ r) (hne : q ≠ p) : q ∈ welcomeRoster r p := by
  simp [welcomeRoster, List.mem_filter, hq, hne]

end LazilyFormal.SignalingRoster
