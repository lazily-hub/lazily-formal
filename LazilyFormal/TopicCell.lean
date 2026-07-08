/-
! TopicCell (broadcast) — formal model stub.

The formal counterpart of `lazily-spec/cell-model.md` § "Future queue primitives →
TopicCell". A broadcast topic where every subscriber receives every pushed
element. Each subscriber maintains its own cursor; the topic retains elements
until all cursors have advanced past them (or a TTL expires).

**Status:** stub — structure and key invariants declared, proofs deferred. Full
formal model lands with the distributed-queue PRD Phase 3.
-/

import LazilyFormal.Primitive

namespace LazilyFormal.TopicCell

abbrev Value := Nat

/-- A subscriber cursor: the index of the next element to receive. -/
abbrev Cursor := Nat

/-- The state of a broadcast topic (`TopicCell`). -/
structure TopicCell where
  /-- The append-only element log (oldest first). -/
  elements : List Value
  /-- Per-subscriber cursors (each subscriber reads independently). -/
  cursors : List Cursor

/- Key invariants (stated, not yet proven):

- **Independent cursors**: each subscriber advances its own cursor independently;
  a slow subscriber does not block others.
- **Retention bound**: elements below all cursors are collectable (GC frontier =
  minimum cursor).
- **Broadcast**: every subscriber eventually sees every element.

Full proofs deferred to PRD Phase 3. -/

end LazilyFormal.TopicCell
