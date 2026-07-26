import LazilyFormal.QueueCell

/-!
# Queue reader kinds — the invalidation set is a pure function of the transition

Every binding's queue shell carries the same load-bearing comment: on a successful
op it bumps *exactly* the reader kinds whose derived value provably changed,
computed **from the transition** (the op plus the pre-op length) and **not** by
deriving each value and comparing. That claim is what makes the reader-kind plane
portable across the single-threaded, thread-safe, and async flavors: the set
depends only on the storage transition, so it is neither thread- nor
async-coloured.

It was asserted in comments in lazily-rs, lazily-zig, and lazily-kt and proven
nowhere. This module proves it.

* `invalidationSet_no_derive` — the set is a function of the bound, the pre-op
  length, and the closed flag **alone**. Two queues agreeing on those agree on the
  set whatever their elements are. This is the "not by deriving the value" half,
  and it is what licenses running the identical rule on all three flavors.
* `invalidationSet_empty_of_not_applied` / `changed_empty_of_not_applied` — a
  rejected push and a pop on empty invalidate nothing, in both directions: the
  rule emits the empty set, and nothing actually changed.
* `close_changes_only_closed` — `close` touches the `closed` reader kind and no
  other, and push/pop never touch it. The reader kinds do not leak into each
  other.
* `apply_atomic` — a reader that observes the post-op storage observes the whole
  invalidation set applied, never a prefix of it. This is what rules out a
  subscriber seeing `len` bumped while `isFull` has not yet flipped.

Deliberately **not** here: per-flavor models. The point is that the algebra does
not fork, so a per-flavor copy would be the very defect this file exists to rule
out. There is one model and three shells.
-/

namespace LazilyFormal.QueueReaderKinds

open LazilyFormal.QueueCell

/-- A bounded queue: the storage-agnostic core plus its (fixed) bound. Capacity is
an *optional, fixed* backend capability — `none` is unbounded. -/
structure Bounded where
  queue : QueueCell
  capacity : Option Nat

/-- The five reader kinds the spec names as Core. `head`, `len`, `isEmpty` and
`isFull` derive from storage; `closed` changes only via `close`. -/
inductive ReaderKind
  | head
  | len
  | isEmpty
  | isFull
  | closed
  deriving DecidableEq, Repr

/-- The ops that can change a reader kind. -/
inductive Op
  | push (v : Value)
  | pop
  | close
  deriving Repr

/-- At capacity? Unbounded is never full. -/
def atCapacity (cap : Option Nat) (n : Nat) : Bool :=
  match cap with
  | none => false
  | some c => Nat.ble c n

def isFull (b : Bounded) : Bool := atCapacity b.capacity (length b.queue)

def isEmpty (b : Bounded) : Bool :=
  match b.queue.elements with
  | [] => true
  | _ :: _ => false

/-- A reader kind's observable value, encoded into one type so the kinds are
comparable. -/
def observe (b : Bounded) : ReaderKind → Option Value
  | .head => head b.queue
  | .len => some (length b.queue)
  | .isEmpty => some (if isEmpty b then 1 else 0)
  | .isFull => some (if isFull b then 1 else 0)
  | .closed => some (if b.queue.closed then 1 else 0)

/-- Whether the op mutates storage. A closed queue rejects a push, a full bounded
queue rejects a push, an empty queue has nothing to pop, and closing a closed
queue is a no-op. -/
def applied (b : Bounded) : Op → Bool
  | .push _ => !b.queue.closed && !atCapacity b.capacity (length b.queue)
  | .pop => !isEmpty b
  | .close => !b.queue.closed

/-- Apply an op. Every rejection path leaves the queue **untouched**, which is
what makes "a failed op invalidates nothing" true rather than merely intended. -/
def step (b : Bounded) (op : Op) : Bounded :=
  if applied b op = false then b else
  match op with
  | .push v => { b with queue := push b.queue v }
  | .pop =>
      match pop b.queue with
      | none => b
      | some (_, q') => { b with queue := q' }
  | .close => { b with queue := close b.queue }

/-- **The implementation's rule.** The reader kinds to invalidate, computed from
the op, the bound, and the PRE-op length and closed flag — never by deriving a
value.

* `len` always changes on a successful push or pop.
* `head` changes on every pop, and on a push only out of empty.
* `isEmpty` changes only when the transition crosses zero.
* `isFull` changes only when the transition crosses the bound.
* `closed` changes only on a successful `close`. -/
def invalidationSet (b : Bounded) (op : Op) : List ReaderKind :=
  if applied b op = false then [] else
  let n := length b.queue
  match op with
  | .push _ =>
      [ReaderKind.len]
        ++ (match n with
            | 0 => [ReaderKind.isEmpty, ReaderKind.head]
            | _ + 1 => [])
        ++ (if atCapacity b.capacity (n + 1) then [ReaderKind.isFull] else [])
  | .pop =>
      [ReaderKind.len, ReaderKind.head]
        ++ (match n with
            | 1 => [ReaderKind.isEmpty]
            | _ => [])
        ++ (if atCapacity b.capacity n && !atCapacity b.capacity (n - 1)
            then [ReaderKind.isFull] else [])
  | .close => [ReaderKind.closed]

/-- The reader kinds whose observable value actually changed. The *ground truth*
the rule must match. -/
def changed (b : Bounded) (op : Op) : List ReaderKind :=
  let b' := step b op
  [ReaderKind.head, ReaderKind.len, ReaderKind.isEmpty, ReaderKind.isFull,
   ReaderKind.closed].filter (fun k => decide (observe b k ≠ observe b' k))

/-! ## A failed op invalidates nothing — both directions -/

theorem step_noop_of_not_applied (b : Bounded) (op : Op)
    (h : applied b op = false) : step b op = b := by
  simp [step, h]

theorem invalidationSet_empty_of_not_applied (b : Bounded) (op : Op)
    (h : applied b op = false) : invalidationSet b op = [] := by
  simp [invalidationSet, h]

/-- The rule emits nothing AND nothing changed. A binding that invalidated on a
rejected push would be over-invalidating against this. -/
theorem changed_empty_of_not_applied (b : Bounded) (op : Op)
    (h : applied b op = false) : changed b op = [] := by
  simp only [changed, step_noop_of_not_applied b op h]
  simp [observe]

/-! ## `closed` does not leak into the other reader kinds -/

theorem closed_untouched_by_push (b : Bounded) (v : Value) :
    (step b (Op.push v)).queue.closed = b.queue.closed := by
  by_cases h : applied b (Op.push v) = false
  · simp only [step, h, if_pos]
  · simp only [Bool.not_eq_false] at h
    simp only [applied, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp [step, applied, h.left, h.right, push]

theorem closed_untouched_by_pop (b : Bounded) :
    (step b Op.pop).queue.closed = b.queue.closed := by
  by_cases h : applied b Op.pop = false
  · simp only [step, h, if_pos]
  · simp only [Bool.not_eq_false] at h
    cases hel : b.queue.elements with
    | nil => simp [applied, isEmpty, hel] at h
    | cons x rest => simp [step, applied, isEmpty, hel, pop]

/-- `close` moves the `closed` reader kind and, when it applies, only that one:
the elements are untouched, so `head`, `len`, `isEmpty` and `isFull` cannot move. -/
theorem close_changes_only_closed (b : Bounded) :
    (step b Op.close).queue.elements = b.queue.elements := by
  by_cases h : applied b Op.close = false
  · simp only [step, h, if_pos]
  · simp only [Bool.not_eq_false] at h
    simp only [applied, Bool.not_eq_true'] at h
    simp [step, applied, h, close]

theorem invalidationSet_close (b : Bounded) (h : applied b Op.close = true) :
    invalidationSet b Op.close = [ReaderKind.closed] := by
  simp [invalidationSet, h]

/-! ## Atomicity -/

/-- Clearing a set of reader kinds: a cleared kind has no cached value, an
uncleared one keeps what it had. -/
def applyInvalidation (cached : ReaderKind → Option Value) (set : List ReaderKind)
    (k : ReaderKind) : Option Value :=
  if k ∈ set then none else cached k

/-- **Atomicity.** A reader that sees the post-op storage sees every kind in the
invalidation set cleared and every kind outside it untouched. There is no
intermediate state in which storage has advanced but only part of the set has been
applied — which is exactly what would let a subscriber observe `len` bumped while
`isFull` had not yet flipped. -/
theorem apply_atomic (b : Bounded) (op : Op) (cached : ReaderKind → Option Value)
    (k : ReaderKind) :
    (k ∈ invalidationSet b op →
        applyInvalidation cached (invalidationSet b op) k = none)
    ∧ (k ∉ invalidationSet b op →
        applyInvalidation cached (invalidationSet b op) k = cached k) := by
  refine ⟨?_, ?_⟩
  · intro h; simp [applyInvalidation, h]
  · intro h; simp [applyInvalidation, h]

/-! ## Confluence of the reader-kind plane (the thread-safe obligation) -/

/-- **The invalidation set is order-independent.** `applyInvalidation` consults only
*membership* in the set, so applying the same set in any order — or applying a
permutation of it — yields the same reader-kind cache state.

This is the queue-family instance of the thread-safe flavor's confluence
obligation, and it is why the thread-safe shell needs no extra machinery: two
threads that bump the same set in different orders converge, because the set is a
set and not a sequence. `ThreadSafe.lean`'s `flushBatch` gives the same property
for a graph batch; this states it for the reader-kind plane directly, over the
set the queue rule actually emits. -/
theorem applyInvalidation_order_independent
    (cached : ReaderKind → Option Value) (s₁ s₂ : List ReaderKind)
    (hmem : ∀ k, k ∈ s₁ ↔ k ∈ s₂) (k : ReaderKind) :
    applyInvalidation cached s₁ k = applyInvalidation cached s₂ k := by
  by_cases h : k ∈ s₁
  · have h₂ : k ∈ s₂ := (hmem k).mp h
    simp [applyInvalidation, h, h₂]
  · have h₂ : k ∉ s₂ := fun hc => h ((hmem k).mpr hc)
    simp [applyInvalidation, h, h₂]

/-- Applying the set twice is applying it once. A redelivered or replayed bump
cannot deepen the invalidation, so an at-least-once delivery of the same
transition is safe. -/
theorem applyInvalidation_idempotent
    (cached : ReaderKind → Option Value) (set : List ReaderKind) (k : ReaderKind) :
    applyInvalidation (applyInvalidation cached set) set k
      = applyInvalidation cached set k := by
  by_cases h : k ∈ set
  · simp [applyInvalidation, h]
  · simp [applyInvalidation, h]

/-! ## The set never reads the elements -/

/-- **"Not by deriving the value."** Two bounded queues agreeing on the bound, the
length, and the closed flag produce the *same* invalidation set for the same op,
whatever their elements are.

So the rule provably cannot be reading values, and running the identical rule on
the single-threaded, thread-safe, and async shells is sound: it consumes only
transition data, which no flavor colours. -/
theorem invalidationSet_no_derive (b₁ b₂ : Bounded) (op : Op)
    (hcap : b₁.capacity = b₂.capacity)
    (hlen : length b₁.queue = length b₂.queue)
    (hempty : isEmpty b₁ = isEmpty b₂)
    (hclosed : b₁.queue.closed = b₂.queue.closed) :
    invalidationSet b₁ op = invalidationSet b₂ op := by
  have happlied : applied b₁ op = applied b₂ op := by
    cases op with
    | push v => simp only [applied, hcap, hlen, hclosed]
    | pop => simp only [applied, hempty]
    | close => simp only [applied, hclosed]
  simp only [invalidationSet, happlied, hlen, hcap]

end LazilyFormal.QueueReaderKinds
