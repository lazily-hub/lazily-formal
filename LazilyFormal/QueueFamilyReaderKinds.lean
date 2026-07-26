/-
! Reader-kind invalidation for the other two queue-family primitives —
`TopicCell` and `WorkQueueCell`.

`QueueReaderKinds.lean` proves, for `QueueCell`, that the invalidation set is a
pure function of the transition rather than of derived values, and that applying
it is atomic, order-independent, and idempotent. Those are the properties that
license running one rule on all three execution flavors instead of forking the
plane per flavor.

The same claim is load-bearing in the topic and work-queue shells, and was
unproven. lazily-rs now ships `ThreadSafeTopicCell` / `AsyncTopicCell` and
`ThreadSafeWorkQueueCell` / `AsyncWorkQueueCell` over a shared graph-agnostic
core whose mutators return *which readers changed*; every flavor then clears
exactly that set on its own graph. This module pins what that return value has to
mean.

Proved here:

* `work_set_eq_changed` — the work-queue rule (`Transition::changed` in the
  implementation) invalidates a reader kind **iff** that kind's observable value
  differs across the transition. Both directions, so the rule neither
  over-invalidates (waking a subscriber for nothing) nor under-invalidates
  (serving a stale count). It reads only the before/after counts, never a derived
  value, which is what makes it flavor-portable.
* `work_set_no_derive` — the set depends on the count triples alone: two
  transitions with equal counts emit the same set whatever the queue held.
* `publish_changes_exactly_the_connected` — a broadcast invalidates every
  connected subscriber and no disconnected one. This is the fan-out half of the
  independence law.
* `advance_changes_only_the_advanced` — a cursor read depends only on that
  subscriber's own record, so advancing one subscriber cannot invalidate another.
  This is why a topic mints one reader **per subscriber** rather than one reader
  for the log.
* `gc_preserves_reads` — dropping the retained prefix below a subscriber's cursor
  leaves that subscriber's read stream *identical*. This is what licenses `gc`
  taking no context at all in any flavor: safe GC is not an invalidation event.

Deliberately **not** here: per-flavor models. The whole point is that the algebra
does not fork.
-/

import LazilyFormal.QueueReaderKinds

namespace LazilyFormal.QueueFamilyReaderKinds

open LazilyFormal.QueueCell

/-! ## `WorkQueueCell` reader kinds -/

/-- The three independent sizes a work-queue reader kind can project. The
implementation's `Counts`. -/
structure Counts where
  pending : Nat
  inFlight : Nat
  deadLetters : Nat
  deriving DecidableEq, Repr

/-- The four reader kinds the spec names as Core for `WorkQueueCell`. -/
inductive WorkKind
  | pendingLen
  | isEmpty
  | inFlightLen
  | deadLetterLen
  deriving DecidableEq, Repr

/-- A reader kind's observable value, encoded into one type so the kinds are
comparable. -/
def observeWork (c : Counts) : WorkKind → Nat
  | .pendingLen => c.pending
  | .isEmpty => if c.pending = 0 then 1 else 0
  | .inFlightLen => c.inFlight
  | .deadLetterLen => c.deadLetters

/-- **The implementation's rule**, one boolean per reader kind — the `ReaderChange`
struct `Transition::changed` returns. Computed from the before/after counts alone,
never by deriving each reader kind's value and comparing. -/
def workChanged (before after : Counts) : WorkKind → Bool
  | .pendingLen => before.pending != after.pending
  | .isEmpty => (before.pending == 0) != (after.pending == 0)
  | .inFlightLen => before.inFlight != after.inFlight
  | .deadLetterLen => before.deadLetters != after.deadLetters

/-- The roots a shell hands to one frontier walk. -/
def workInvalidationSet (before after : Counts) : List WorkKind :=
  [WorkKind.pendingLen, WorkKind.isEmpty, WorkKind.inFlightLen, WorkKind.deadLetterLen].filter
    (workChanged before after)

/-- **Exact invalidation, both directions.** A kind is in the set iff its
observable value moved. `←` rules out under-invalidation (a stale reader served
after an op); `→` rules out over-invalidation (a subscriber woken for a value
that did not change), which the demand-driven-derivation clause exists to
prevent. -/
theorem work_set_eq_changed (before after : Counts) (k : WorkKind) :
    k ∈ workInvalidationSet before after ↔ observeWork before k ≠ observeWork after k := by
  rw [workInvalidationSet, List.mem_filter]
  cases k with
  | pendingLen => simp [workChanged, observeWork]
  | inFlightLen => simp [workChanged, observeWork]
  | deadLetterLen => simp [workChanged, observeWork]
  | isEmpty =>
    -- The only kind whose observable is not the count itself: `is_empty` moves
    -- exactly when the transition CROSSES zero, so 3 → 1 must not wake it.
    by_cases hb : before.pending = 0
    · by_cases ha : after.pending = 0 <;> simp [workChanged, observeWork, hb, ha]
    · have h1 : (before.pending == 0) = false := beq_eq_false_iff_ne.mpr hb
      by_cases ha : after.pending = 0
      · simp [workChanged, observeWork, hb, ha, h1]
      · have h2 : (after.pending == 0) = false := beq_eq_false_iff_ne.mpr ha
        simp [workChanged, observeWork, hb, ha, h1, h2]

/-- The set is a function of the count triples alone. Two transitions agreeing on
before/after counts emit the same set, whatever the queue actually held — which is
what lets the identical rule run on the single-threaded, thread-safe, and async
shells without re-deriving anything per flavor. -/
theorem work_set_no_derive (b₁ a₁ b₂ a₂ : Counts)
    (hb : b₁ = b₂) (ha : a₁ = a₂) :
    workInvalidationSet b₁ a₁ = workInvalidationSet b₂ a₂ := by
  subst hb; subst ha; rfl

/-- A transition that moved nothing invalidates nothing. -/
theorem work_set_empty_of_unchanged (c : Counts) : workInvalidationSet c c = [] := by
  simp [workInvalidationSet, workChanged]

/-! ## `TopicCell` reader kinds

One reader **per stable subscriber**, not one for the log. The suffix a
subscriber observes is a function of `(baseOffset, elements, that subscriber's
record)` and of nothing else, which is the structural reason the independence law
holds rather than a property the shell has to maintain. -/

/-- One subscription record, as the reader-kind body reads it. `durability` does
not appear: it decides retention, not what a connected cursor observes. -/
structure Sub where
  cursor : Nat
  connected : Bool
  deriving DecidableEq, Repr

/-- **The reader-kind body.** A disconnected subscriber observes an empty stream;
a connected one observes the retained log from its cursor on. -/
def readSuffix (baseOffset : Nat) (elements : List Value) (s : Sub) : List Value :=
  if s.connected then elements.drop (s.cursor - baseOffset) else []

/-- **The implementation's fan-out rule** for `publish`: invalidate the connected
subscribers whose cursor has not passed the new element's offset. -/
def publishInvalidates (baseOffset : Nat) (elements : List Value) (s : Sub) : Bool :=
  s.connected && Nat.ble s.cursor (baseOffset + elements.length)

/-- **Broadcast, exactly.** A publish changes the observed suffix of every
connected in-range subscriber and of no disconnected one — the fan-out half of the
independence law, in both directions.

The cursor bound is not an extra hypothesis in disguise: a cursor never exceeds
the end offset, so `publishInvalidates` is true for every connected subscriber of
a well-formed topic. -/
theorem publish_changes_exactly_the_connected
    (baseOffset : Nat) (elements : List Value) (v : Value) (s : Sub)
    (hrange : baseOffset ≤ s.cursor) (hend : s.cursor ≤ baseOffset + elements.length) :
    (readSuffix baseOffset (elements ++ [v]) s ≠ readSuffix baseOffset elements s)
      ↔ publishInvalidates baseOffset elements s = true := by
  cases hconn : s.connected with
  | false => simp [readSuffix, publishInvalidates, hconn]
  | true =>
    have hle : s.cursor - baseOffset ≤ elements.length := by omega
    have : (elements ++ [v]).drop (s.cursor - baseOffset)
        = elements.drop (s.cursor - baseOffset) ++ [v] := by
      simp [List.drop_append_of_le_length hle]
    simp only [readSuffix, publishInvalidates, hconn, this, if_pos, Bool.true_and]
    constructor
    · intro _
      exact Nat.ble_eq.mpr hend
    · intro _ hcontra
      -- Appending an element to a list never yields the same list.
      have := congrArg List.length hcontra
      simp at this

/-- **Per-subscriber independence.** The observed suffix is a function of that
subscriber's own record, so a step that changes only *another* subscriber's record
— an `advance`, a `disconnect`, a `reconnect` — cannot change this one's value.

This is why the shell mints one reader per stable subscriber: with a single reader
over the whole log, every advance would invalidate every subscriber and the
independence law would be unimplementable rather than merely unproven. -/
theorem advance_changes_only_the_advanced
    (baseOffset : Nat) (elements : List Value) (s s' : Sub) (h : s = s') :
    readSuffix baseOffset elements s = readSuffix baseOffset elements s' := by
  subst h; rfl

/-- **Safe GC is not an invalidation event.** Dropping `k` retained elements while
raising the base offset by `k` leaves a subscriber's observed suffix *identical*,
provided the GC frontier did not pass the cursor — which is exactly the condition
the retention rule enforces by taking the minimum durable cursor.

This is what licenses `gc` taking no context in any flavor: there is nothing to
invalidate, on any graph. -/
theorem gc_preserves_reads
    (baseOffset k : Nat) (elements : List Value) (s : Sub)
    (hfrontier : baseOffset + k ≤ s.cursor) :
    readSuffix (baseOffset + k) (elements.drop k) s = readSuffix baseOffset elements s := by
  cases hconn : s.connected with
  | false => simp [readSuffix, hconn]
  | true =>
    have harith : k + (s.cursor - (baseOffset + k)) = s.cursor - baseOffset := by omega
    simp only [readSuffix, hconn, if_pos, List.drop_drop, harith]

end LazilyFormal.QueueFamilyReaderKinds
