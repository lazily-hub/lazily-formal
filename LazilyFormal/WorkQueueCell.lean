/-
! WorkQueueCell (competing consumers) — formal model.

The formal counterpart of `lazily-spec/cell-model.md` § "The queue family — two axes"
and § "Future queue primitives → WorkQueueCell". A **work queue**: N consumers compete
for elements from a shared FIFO; each element is delivered to **exactly one** consumer
(exclusive, destructive handoff).

Why pure CRDT cannot do this: a queue pop is not idempotent-commutative — two consumers
concurrently popping the same head both survive a CRDT merge → duplicate delivery, and
there is no "un-pop". Exclusive handoff therefore needs a **single serialization point**
for the assignment decision: a consensus-committed assignment log. With consensus,
"element X → worker W" is a majority-committed entry, and because any two majorities of
an `n`-voter set intersect (`ReliableSync.majorities_intersect`), two conflicting
assignments of the same element can never both commit.

Results fixed here:

- **Exclusive handoff / no double-delivery** (`no_double_delivery`,
  `commit_preserves_atmostone`): a committed assignment log built by `commit` (which
  refuses to re-assign an already-assigned element) holds **at most one** assignment per
  element — no element is ever delivered to two workers. The consensus backstop that
  makes a single commit authoritative is `quorum_commit_exclusive`
  (= `ReliableSync.majorities_intersect`).
- **Lease expiry ⇒ at-least-once redelivery** (`expired_lease_redelivers`,
  `leaseExpire_preserves_value`, `redelivery_preserves_item`): an assigned-but-unacked
  element past its lease TTL becomes re-assignable (returns to `pending`), and
  redelivery preserves the item's value — eventually delivered, never lost. A **live**
  lease stays `claimed` (`live_lease_stays_claimed`), so no premature double-delivery.
- **Ack removes / nack requeues** (`ack_not_pending`, `nack_pending`,
  `queue_ack_removes_pending`, `queue_nack_requeues_pending`): `ack` moves a claimed
  assignment to `acked` (removed from the pending set); `nack` returns it to `pending`
  (re-assignable).

Assignment-FIFO is not processing-FIFO, and dead-letter / fairness are further deferred
lifecycle features (see the spec); the safety core is proven here.
-/

import LazilyFormal.Primitive
import LazilyFormal.ReliableSync

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

/-! ## Exclusive handoff: the consensus-committed assignment log

Each element's assignment ("element `e` → worker `w`") is a committed log entry.
`commit` refuses to add a second assignment for an already-assigned element — the model
of a consensus-serialized single-assignment decision — so a log built from `[]` holds at
most one assignment per element: no double-delivery. -/

/-- An abstract worker/consumer id. -/
abbrev Worker := Nat

/-- One committed assignment: element `element` handed to worker `worker`. -/
structure Assignment where
  element : Value
  worker : Worker

/-- The committed assignment log (append-only, oldest first). -/
abbrev AssignLog := List Assignment

/-- How many assignments the log already holds for element `e`. -/
def assignedCount (log : AssignLog) (e : Value) : Nat :=
  (log.filter (fun a => decide (a.element = e))).length

/-- Commit an assignment `e → w`, but only if `e` is not already assigned (the
serialization point: a consensus commit is authoritative and exclusive). -/
def commit (log : AssignLog) (e : Value) (w : Worker) : AssignLog :=
  if 0 < assignedCount log e then log else log ++ [{ element := e, worker := w }]

/-- Build a committed log by folding `commit` over a sequence of assignment requests. -/
def committedFrom (reqs : List (Value × Worker)) : AssignLog :=
  reqs.foldl (fun l p => commit l p.1 p.2) []

theorem assignedCount_append (a b : AssignLog) (e : Value) :
    assignedCount (a ++ b) e = assignedCount a e + assignedCount b e := by
  simp only [assignedCount, List.filter_append, List.length_append]

theorem assignedCount_singleton (e w x : Nat) :
    assignedCount [{ element := e, worker := w }] x = if e = x then 1 else 0 := by
  by_cases h : e = x
  · simp [assignedCount, h]
  · simp [assignedCount, h]

/-- **Commit preserves the at-most-one-assignment invariant.** If every element has `≤ 1`
assignment, so does the log after any `commit` — because `commit` refuses to add a second
assignment for an already-assigned element. -/
theorem commit_preserves_atmostone (log : AssignLog) (e : Value) (w : Worker)
    (hinv : ∀ x, assignedCount log x ≤ 1) :
    ∀ x, assignedCount (commit log e w) x ≤ 1 := by
  intro x
  unfold commit
  by_cases hass : 0 < assignedCount log e
  · rw [if_pos hass]; exact hinv x
  · rw [if_neg hass, assignedCount_append, assignedCount_singleton]
    by_cases hx : e = x
    · rw [if_pos hx]
      have h0 : assignedCount log e = 0 := Nat.le_zero.mp (Nat.not_lt.mp hass)
      have hx0 : assignedCount log x = 0 := by rw [← hx]; exact h0
      omega
    · rw [if_neg hx]; have := hinv x; omega

/-- Fold `commit` from any log that already satisfies the invariant keeps it. -/
theorem foldl_commit_preserves (reqs : List (Value × Worker)) (log : AssignLog)
    (hinv : ∀ x, assignedCount log x ≤ 1) :
    ∀ x, assignedCount (reqs.foldl (fun l p => commit l p.1 p.2) log) x ≤ 1 := by
  induction reqs generalizing log with
  | nil => exact hinv
  | cons p rest ih =>
    simp only [List.foldl_cons]
    exact ih (commit log p.1 p.2) (commit_preserves_atmostone log p.1 p.2 hinv)

/-- **No double-delivery.** A committed log built from `[]` assigns every element to at
most one worker — exclusive handoff, no element delivered twice. -/
theorem no_double_delivery (reqs : List (Value × Worker)) :
    ∀ x, assignedCount (committedFrom reqs) x ≤ 1 :=
  foldl_commit_preserves reqs [] (by intro x; simp [assignedCount])

/-- **Quorum commit is exclusive (consensus backstop).** Two majorities of an `n`-voter
set share a voter, so two conflicting assignments of the same element cannot both commit.
This is `ReliableSync.majorities_intersect` — the arithmetic reason a single committed
assignment is authoritative, and why competing consumers need consensus, not CRDT. -/
theorem quorum_commit_exclusive (n a b : Nat)
    (ha : n / 2 + 1 ≤ a) (hb : n / 2 + 1 ≤ b) (han : a ≤ n) (hbn : b ≤ n) :
    1 ≤ a + b - n :=
  LazilyFormal.ReliableSync.majorities_intersect n a b ha hb han hbn

/-! ## Delivery lifecycle: ack removes, nack requeues

Per-element delivery-state transitions. `ack` moves a claimed element to `acked`
(removed from the pending set); `nack` returns it to `pending` (re-assignable); `claim`
takes a pending element for a worker. -/

/-- Is this delivery state pending (still awaiting a worker)? -/
def isPending : DeliveryState → Bool
  | DeliveryState.pending => true
  | _ => false

/-- Ack a claimed element → `acked` (a no-op on any other state). -/
def ackSt : DeliveryState → DeliveryState
  | DeliveryState.claimed _ => DeliveryState.acked
  | s => s

/-- Nack a claimed element → back to `pending` (a no-op on any other state). -/
def nackSt : DeliveryState → DeliveryState
  | DeliveryState.claimed _ => DeliveryState.pending
  | s => s

/-- Claim a pending element for worker `w` → `claimed w` (a no-op on any other state). -/
def claimSt (w : Nat) : DeliveryState → DeliveryState
  | DeliveryState.pending => DeliveryState.claimed w
  | s => s

/-- **Ack removes from pending.** An acked element is no longer pending. -/
theorem ack_not_pending (w : Nat) :
    isPending (ackSt (DeliveryState.claimed w)) = false := rfl

/-- **Nack requeues to pending.** A nacked element is pending again (re-assignable). -/
theorem nack_pending (w : Nat) :
    isPending (nackSt (DeliveryState.claimed w)) = true := rfl

/-- Claiming a pending element hands it to the worker. -/
theorem claim_of_pending (w : Nat) :
    claimSt w DeliveryState.pending = DeliveryState.claimed w := rfl

/-- Ack is terminal / idempotent: re-acking an acked element is a no-op. -/
theorem ack_idempotent : ackSt (ackSt (DeliveryState.claimed 0)) = ackSt (DeliveryState.claimed 0) := rfl

/-- The pending set size of a queue. -/
def pendingCount (q : WorkQueueCell) : Nat :=
  (q.entries.filter (fun p => isPending p.2)).length

/-- **Ack removes the assignment from the queue's pending set.** -/
theorem queue_ack_removes_pending (v : Value) (w : Nat) :
    pendingCount { entries := [(v, ackSt (DeliveryState.claimed w))] } = 0 := by
  simp [pendingCount, ackSt, isPending]

/-- **Nack returns the assignment to the queue's pending set.** -/
theorem queue_nack_requeues_pending (v : Value) (w : Nat) :
    pendingCount { entries := [(v, nackSt (DeliveryState.claimed w))] } = 1 := by
  simp [pendingCount, nackSt, isPending]

/-! ## Visibility-timeout / lease: at-least-once redelivery

An assigned element is leased with a TTL (a `deadline`). Past the deadline the worker is
presumed dead and the element is reassigned (returns to `pending`); before it, the lease
holds (`claimed`). Redelivery preserves the element's value — the item is eventually
delivered, never lost. -/

/-- An in-flight lease: element `value` claimed by `worker`, valid until `deadline`. -/
structure Lease where
  value : Value
  worker : Worker
  deadline : Nat

/-- The lease has expired at time `now` (past its deadline). -/
def expired (l : Lease) (now : Nat) : Bool := decide (l.deadline < now)

/-- Evaluate a lease at time `now`: an expired lease returns the element to `pending`
(re-assignable); a live lease keeps it `claimed`. The value is carried through either way. -/
def leaseExpireEntry (l : Lease) (now : Nat) : Value × DeliveryState :=
  if l.deadline < now then (l.value, DeliveryState.pending)
  else (l.value, DeliveryState.claimed l.worker)

theorem expired_iff (l : Lease) (now : Nat) : expired l now = true ↔ l.deadline < now := by
  simp [expired]

/-- **Live lease stays claimed.** Before the deadline the element remains claimed — no
premature redelivery, hence no spurious double-delivery. -/
theorem live_lease_stays_claimed (l : Lease) (now : Nat) (h : ¬ l.deadline < now) :
    leaseExpireEntry l now = (l.value, DeliveryState.claimed l.worker) := by
  simp [leaseExpireEntry, h]

/-- **Lease expiry ⇒ redelivery.** Past the TTL the unacked element becomes pending
(re-assignable) — the at-least-once redelivery path. -/
theorem expired_lease_redelivers (l : Lease) (now : Nat) (h : l.deadline < now) :
    leaseExpireEntry l now = (l.value, DeliveryState.pending) := by
  simp [leaseExpireEntry, h]

/-- **Redelivery preserves the item.** However the lease resolves, the element's value is
carried through — an unacked element is redelivered, never lost. -/
theorem leaseExpire_preserves_value (l : Lease) (now : Nat) :
    (leaseExpireEntry l now).1 = l.value := by
  simp only [leaseExpireEntry]
  split <;> rfl

/-- **At-least-once, never lost.** An expired lease's element returns to `pending` and is
re-claimed by a fresh worker `w'` with its value intact — the redelivery cycle preserves
the item and hands it to exactly one (new) worker. -/
theorem redelivery_preserves_item (l : Lease) (now : Nat) (w' : Nat)
    (_h : l.deadline < now) :
    let e := leaseExpireEntry l now
    (e.1, claimSt w' e.2) = (l.value, DeliveryState.claimed w') := by
  simp only [leaseExpireEntry, if_pos _h, claimSt]

/-! ## Closure of the lifecycle

Bundled safety statement mirroring `QueueCell.Closed_then_stays_Closed`: exclusive
handoff (no double-delivery), ack-removes / nack-requeues, and lease-expiry redelivery
with value preservation all hold together. -/

theorem workqueue_delivery_safe :
    (∀ (reqs : List (Value × Worker)) x, assignedCount (committedFrom reqs) x ≤ 1) ∧
    (∀ (v : Value) (w : Nat),
      pendingCount { entries := [(v, ackSt (DeliveryState.claimed w))] } = 0) ∧
    (∀ (v : Value) (w : Nat),
      pendingCount { entries := [(v, nackSt (DeliveryState.claimed w))] } = 1) ∧
    (∀ (l : Lease) (now : Nat), l.deadline < now →
      leaseExpireEntry l now = (l.value, DeliveryState.pending)) ∧
    (∀ (l : Lease) (now : Nat), (leaseExpireEntry l now).1 = l.value) :=
  ⟨no_double_delivery, queue_ack_removes_pending, queue_nack_requeues_pending,
    expired_lease_redelivers, leaseExpire_preserves_value⟩

end LazilyFormal.WorkQueueCell
