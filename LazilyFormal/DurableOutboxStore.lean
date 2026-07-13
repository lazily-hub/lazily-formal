import LazilyFormal.ReliableSync

/-!
Storage-independent durable outbox (`#lzdurableoutbox`). `OutboxStore` supplies
ordered bytes; the shared protocol owns monotone cursors, prune safety, and replay.
-/

namespace LazilyFormal.DurableOutboxStore

open LazilyFormal.ReliableSync

structure Store where
  frames : OutboxQueue
  cursor : Nat

def saveCursor (store : Store) (ack : Nat) : Store :=
  { store with cursor := max store.cursor ack }

theorem cursor_monotone (store : Store) (ack : Nat) :
    store.cursor ≤ (saveCursor store ack).cursor := by
  simp [saveCursor, Nat.le_max_left]

def prune (store : Store) : Store :=
  { store with frames := ackThrough store.frames store.cursor }

def replay (store : Store) : OutboxQueue :=
  ackThrough store.frames store.cursor

/-- Every replayed row is above the durable cursor; acknowledged rows never resurrect. -/
theorem replay_prune_safe (store : Store) (epoch : Nat) (delta : Delta)
    (member : (epoch, delta) ∈ replay store) : store.cursor < epoch := by
  unfold replay ackThrough at member
  exact of_decide_eq_true (List.mem_filter.mp member).2

/-- Appending an unacknowledged row makes it replayable. -/
theorem append_before_ack_replays (store : Store) (epoch : Nat) (delta : Delta)
    (fresh : store.cursor < epoch) :
    (epoch, delta) ∈ replay { store with frames := enqueue store.frames epoch delta } := by
  simp [replay, ackThrough, enqueue, fresh]

end LazilyFormal.DurableOutboxStore
