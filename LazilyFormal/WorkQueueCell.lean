/-
! WorkQueueCell (competing consumers) — formal model stub.

The formal counterpart of `lazily-spec/cell-model.md` § "Future queue primitives →
WorkQueueCell". A work queue where N consumers compete for elements from a shared
FIFO. Each element is delivered to exactly one consumer (exclusive handoff).

Exclusive handoff requires an authority (designated leader peer) to serialize
pop-assignment — pure CRDT cannot provide it (concurrent pops both survive merge
→ duplicate delivery). This is why production distributed queues use consensus.

**Status:** stub — structure and key invariants declared, proofs deferred. Full
formal model lands with the distributed-queue PRD Phase 2 (consensus core).
-/

import LazilyFormal.Primitive

namespace LazilyFormal.WorkQueueCell

abbrev Value := Nat

/-- Delivery state for one element. -/
inductive DeliveryState where
  /-- Element is in the queue, not yet claimed. -/
  | pending : DeliveryState
  /-- Element claimed by consumer `c`; awaiting ack. -/
  | claimed : Nat → DeliveryState
  /-- Element acknowledged (consumed); collectable. -/
  | acked : DeliveryState

/-- The state of a work queue (`WorkQueueCell`). -/
structure WorkQueueCell where
  /-- Elements with delivery state (FIFO order). -/
  entries : List (Value × DeliveryState)

/- Key invariants (stated, not yet proven):

- **Exclusive handoff**: at most one consumer holds a `claimed` state for any
  given element (serialized by the leader).
- **At-least-once delivery**: an unacked element (`claimed` but not `acked`) is
  redelivered after a timeout (visibility-timeout / lease).
- **Exactly-once processing**: requires consumer-side dedup via delivery IDs
  assigned by the leader.
- **Dead-letter**: poison messages (repeatedly nacked) are moved to a dead-letter
  queue after a threshold.

Full proofs deferred to PRD Phase 2 (consensus core required for the leader
authority that makes exclusive handoff possible). -/

end LazilyFormal.WorkQueueCell
