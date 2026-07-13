/-
! TopicCell (broadcast) — formal model.

The formal counterpart of `lazily-spec/cell-model.md` § "The queue family — two axes"
and § "Future queue primitives → TopicCell". A **broadcast topic**: every subscriber
receives every pushed element. Each subscriber holds its **own cursor** and reads
**non-destructively** — one subscriber advancing removes nothing for the others. The
topic retains an element until every durable cursor has passed it (GC frontier = the
minimum cursor).

Universal properties fixed here:

- **Broadcast delivery**: a subscriber reading from cursor `0` observes the full
  published sequence (its read-stream = `elements`); every subscriber sees the same
  full sequence independently (`broadcast_delivery`, `readStreamFrom_zero`).
- **Non-destructive read**: advancing one subscriber's cursor changes neither
  `elements` nor any other subscriber's cursor or read-stream
  (`advance_preserves_elements`, `advance_preserves_other_cursor`,
  `advance_preserves_other_readStream`).
- **Slowest-subscriber retention**: elements below the minimum cursor are GC-safe —
  dropping them (and shifting cursors) leaves every subscriber's future reads
  unchanged (`gc_preserves_readStream`, `gc_at_min_preserves_readStream`, with the
  frontier `minCursor_le_cursor`).
- **State-topic conflation is effect-lossless**: for value/state semantics a
subscriber that jumps its cursor to the latest element observes the same final
value as one that read every element — the LWW last-write, analogous to
`ReliableSync.joinReg` (`state_conflation_effect_lossless`).
- **Durable lifecycle**: a newly-created durable subscription starts at the
current tail, cursors never advance beyond the tail, and snapshot/restore preserves
every durable cursor across subscriber restart (`subscribeDurable_cursor_at_tail`,
`advance_at_end_noop`, `restore_snapshot`, `restart_preserves_cursor`). Ephemeral
cursors are caller-owned and therefore do not participate in the retention frontier.

Unlike `QueueCell` (destructive pop, one consumer) a topic distributes with **no
assignment consensus**: N independent per-subscriber cursor-queues. Total-order
broadcast (atomic broadcast ≡ consensus) is out of scope here.
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
  /-- Per-durable-subscriber cursors (each subscriber reads independently). Ephemeral
  session cursors are intentionally caller-owned and absent from this retention set. -/
  cursors : List Cursor

/-! ## Publish, read, advance -/

/-- Publish (broadcast) a value: append it to the log. Cursors are untouched — a
publish makes an element available to every subscriber without moving any cursor. -/
def publish (t : TopicCell) (v : Value) : TopicCell :=
  { t with elements := t.elements ++ [v] }

/-- Subscriber `i`'s cursor (an unsubscribed / out-of-range index reads from `0`). -/
def cursorOf (t : TopicCell) (i : Nat) : Cursor := t.cursors.getD i 0

/-- The read-stream from a raw cursor: the not-yet-consumed suffix of the log. -/
def readStreamFrom (t : TopicCell) (c : Cursor) : List Value := t.elements.drop c

/-- Subscriber `i`'s read-stream — everything it has not yet read. -/
def readStream (t : TopicCell) (i : Nat) : List Value := readStreamFrom t (cursorOf t i)

/-- Advance subscriber `i` by one available read (consume one element for that
subscriber only). At the tail this is a no-op, so a cursor can never be advanced by
polling an empty topic. -/
def advance (t : TopicCell) (i : Nat) : TopicCell :=
if cursorOf t i < t.elements.length then
  { t with cursors := t.cursors.set i (cursorOf t i + 1) }
else
  t

/-! ## Subscription lifecycle -/

/-- The stable id allocated to the next durable subscriber. Subscriber ids are list
indices in the pure model; bindings may use any stable external key. -/
def nextSubscriberId (t : TopicCell) : Nat := t.cursors.length

/-- Register a durable subscriber at the current tail. It receives future publishes,
and its cursor is retained in topic state while it is offline. -/
def subscribeDurable (t : TopicCell) : TopicCell :=
{ t with cursors := t.cursors ++ [t.elements.length] }

/-- An ephemeral subscription owns only a connected-session cursor. It starts at the
current tail, is not stored in `TopicCell`, and therefore never holds back GC. -/
def subscribeEphemeral (t : TopicCell) : Cursor := t.elements.length

/-- Persisted state required to recover durable subscriptions after process restart. -/
structure DurableSnapshot where
elements : List Value
cursors : List Cursor

/-- Capture the append log and every durable cursor atomically. -/
def snapshot (t : TopicCell) : DurableSnapshot :=
{ elements := t.elements, cursors := t.cursors }

/-- Restore a topic from its durable snapshot. -/
def restore (s : DurableSnapshot) : TopicCell :=
{ elements := s.elements, cursors := s.cursors }

theorem publish_appends (t : TopicCell) (v : Value) :
    (publish t v).elements = t.elements ++ [v] := rfl

/-- **Publish does not move any cursor.** Availability of a new element is independent
of consumption progress — every subscriber decides when to advance. -/
theorem publish_preserves_cursors (t : TopicCell) (v : Value) :
(publish t v).cursors = t.cursors := rfl

/-- A durable subscriber is created at the current tail, so historical elements are
not replayed merely by creating a new subscription. -/
theorem subscribeDurable_cursor_at_tail (t : TopicCell) :
cursorOf (subscribeDurable t) (nextSubscriberId t) = t.elements.length := by
  simp [subscribeDurable, nextSubscriberId, cursorOf]

/-- The first publish after subscribing is visible to the new durable subscriber. -/
theorem publish_visible_to_new_durable (t : TopicCell) (v : Value) :
readStream (publish (subscribeDurable t) v) (nextSubscriberId t) = [v] := by
  simp [readStream, readStreamFrom, publish, subscribeDurable, nextSubscriberId,
    cursorOf]

/-- A new ephemeral session also starts at the current tail. Because this cursor is
returned to the caller rather than inserted in `t.cursors`, it does not participate in
`minCursor`. -/
theorem subscribeEphemeral_cursor_at_tail (t : TopicCell) :
subscribeEphemeral t = t.elements.length := rfl

/-- Snapshot followed by restore is byte-for-byte topic recovery. -/
theorem restore_snapshot (t : TopicCell) : restore (snapshot t) = t := by
  cases t
  rfl

/-- **Cursor persistence.** Restarting from an atomic snapshot preserves every durable
subscriber cursor. -/
theorem restart_preserves_cursor (t : TopicCell) (i : Nat) :
cursorOf (restore (snapshot t)) i = cursorOf t i := by
  rw [restore_snapshot]

/-! ## Broadcast delivery

Reading from cursor `0` yields the whole published sequence, and any two subscribers
both at `0` observe the identical full sequence — the defining broadcast property
(every subscriber receives every element, independently). -/

/-- The read-stream from cursor `0` is exactly the full published log. -/
theorem readStreamFrom_zero (t : TopicCell) : readStreamFrom t 0 = t.elements := rfl

/-- **Broadcast delivery.** Any subscriber whose cursor is at `0` observes the full
published sequence, and two such subscribers observe the *same* sequence — each sees
every element, independently of the other. -/
theorem broadcast_delivery (t : TopicCell) (i j : Nat)
    (hi : cursorOf t i = 0) (hj : cursorOf t j = 0) :
    readStream t i = t.elements ∧
    readStream t j = t.elements ∧
    readStream t i = readStream t j := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [readStream, readStreamFrom, hi, List.drop_zero]
  · simp only [readStream, readStreamFrom, hj, List.drop_zero]
  · simp only [readStream, readStreamFrom, hi, hj]

/-! ## Non-destructive read

A `TopicCell` subscriber reads by cursor and removes nothing: advancing subscriber `i`
changes neither the shared `elements` log nor any *other* subscriber's cursor or
read-stream. This is the sharp contrast with `QueueCell`'s destructive pop. -/

/-- **Advance is non-destructive on the log.** One subscriber consuming an element
leaves the shared element log intact for everyone else. -/
theorem advance_preserves_elements (t : TopicCell) (i : Nat) :
(advance t i).elements = t.elements := by
  unfold advance
  split <;> rfl

/-- Polling at (or beyond) the tail cannot manufacture progress. -/
theorem advance_at_end_noop (t : TopicCell) (i : Nat)
    (h : t.elements.length ≤ cursorOf t i) :
    advance t i = t := by
  simp only [advance, Nat.not_lt.mpr h, ↓reduceIte]

/-- **Advance is local to subscriber `i`.** Advancing subscriber `i`'s cursor does not
touch any other subscriber `j`'s cursor. -/
theorem advance_preserves_other_cursor (t : TopicCell) (i j : Nat) (h : i ≠ j) :
cursorOf (advance t i) j = cursorOf t j := by
  unfold advance
  split
  · simp only [cursorOf, List.getD_eq_getElem?_getD, List.getElem?_set_ne h]
  · rfl

/-- **Advance preserves other subscribers' reads.** A slow subscriber advancing does
not change any other subscriber's read-stream — failure / lag is isolated per
subscription. -/
theorem advance_preserves_other_readStream (t : TopicCell) (i j : Nat) (h : i ≠ j) :
    readStream (advance t i) j = readStream t j := by
  simp only [readStream, readStreamFrom, advance_preserves_elements,
    advance_preserves_other_cursor t i j h]

/-! ## Slowest-subscriber retention (GC frontier = min cursor)

The topic retains an element until every cursor has passed it. Elements strictly below
the minimum cursor are collectable: dropping the first `k ≤ min` elements and shifting
every cursor down by `k` leaves each subscriber's future read-stream identical. -/

/-- Garbage-collect the first `k` elements: drop them from the log and shift every
cursor down by `k` (the retained log re-based at the new origin). -/
def gc (t : TopicCell) (k : Nat) : TopicCell :=
  { elements := t.elements.drop k,
    cursors := t.cursors.map (· - k) }

/-- The retention identity: dropping a GC prefix of size `k ≤ c` and reading from the
shifted cursor `c - k` yields the same suffix as reading from `c` on the full log —
GC below a cursor is invisible to that cursor's reads. -/
theorem gc_preserves_readStream_core (l : List Value) (c k : Nat) (h : k ≤ c) :
    (l.drop k).drop (c - k) = l.drop c := by
  rw [List.drop_drop]
  congr 1
  omega

/-- After GC of `k`, subscriber `i` (in range) sits at `cursorOf t i - k`. -/
theorem cursorOf_gc (t : TopicCell) (i k : Nat) (h : i < t.cursors.length) :
    cursorOf (gc t k) i = cursorOf t i - k := by
  simp only [cursorOf, gc, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem h, Option.map_some, Option.getD_some]

/-- **Retention is read-preserving below a cursor.** GC of any `k ≤ cursorOf t i`
leaves subscriber `i`'s read-stream unchanged. -/
theorem gc_preserves_readStream (t : TopicCell) (i k : Nat)
    (hi : i < t.cursors.length) (hk : k ≤ cursorOf t i) :
    readStream (gc t k) i = readStream t i := by
  simp only [readStream, readStreamFrom, cursorOf_gc t i k hi]
  show (t.elements.drop k).drop (cursorOf t i - k) = t.elements.drop (cursorOf t i)
  exact gc_preserves_readStream_core t.elements (cursorOf t i) k hk

/-- `foldl min` never exceeds its seed. -/
theorem foldl_min_le_start (a : Nat) (l : List Nat) : l.foldl min a ≤ a := by
  induction l generalizing a with
  | nil => exact Nat.le_refl a
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (ih (min a x)) (Nat.min_le_left a x)

/-- `foldl min` is a lower bound of every element it folds over. -/
theorem foldl_min_le_of_mem : ∀ (a x : Nat) (l : List Nat), x ∈ l → l.foldl min a ≤ x := by
  intro a x l
  induction l generalizing a with
  | nil => intro h; cases h
  | cons y ys ih =>
    intro h
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with he | hm
    · subst he
      exact Nat.le_trans (foldl_min_le_start (min a x) ys) (Nat.min_le_right a x)
    · exact ih (min a y) hm

/-- The GC frontier: the minimum cursor over all durable subscribers (seeded at the log
length, so a topic with no durable subscribers may collect everything). Below this
frontier no durable cursor has any un-read element, so those elements are
retention-collectable. -/
def minCursor (t : TopicCell) : Cursor := t.cursors.foldl min (t.elements.length)

/-- Subscriber `i`'s cursor is a member of the cursor list (in range). -/
theorem cursorOf_mem (t : TopicCell) (i : Nat) (h : i < t.cursors.length) :
    cursorOf t i ∈ t.cursors := by
  have he : cursorOf t i = t.cursors[i] := by
    simp only [cursorOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h,
      Option.getD_some]
  rw [he]
  exact List.getElem_mem h

/-- **The frontier bounds every subscriber.** `minCursor` is `≤` every in-range
subscriber's cursor — so GC at `minCursor` is safe for all of them at once. -/
theorem minCursor_le_cursor (t : TopicCell) (i : Nat) (h : i < t.cursors.length) :
    minCursor t ≤ cursorOf t i :=
  foldl_min_le_of_mem (t.elements.length) (cursorOf t i) t.cursors (cursorOf_mem t i h)

/-- **Slowest-subscriber retention.** GC at the minimum cursor preserves *every*
subscriber's read-stream: the slowest cursor sets the GC frontier and nothing any
subscriber can still read is dropped. -/
theorem gc_at_min_preserves_readStream (t : TopicCell) (i : Nat)
    (hi : i < t.cursors.length) :
    readStream (gc t (minCursor t)) i = readStream t i :=
  gc_preserves_readStream t i (minCursor t) hi (minCursor_le_cursor t i hi)

/-! ## State-topic conflation is effect-lossless

For a **state topic** (each element is a fresh value that supersedes the last) old
elements are worthless once superseded, so a lagging subscriber may **conflate to
latest** — jump its cursor over the intermediates straight to the newest element — and
observe the identical final value as a subscriber that read every element. This is the
LWW last-write / fold-to-last, the per-subscriber analog of `ReliableSync.joinReg`. -/

/-- The observed value of a state topic: fold keep-last from `init` (the newest element,
or `init` for an empty stream). -/
def lastValue (init : Value) (l : List Value) : Value := l.foldl (fun _ v => v) init

/-- Folding keep-last over any prefix then one more element is that element. -/
theorem lastValue_append_singleton (init : Value) (l : List Value) (v : Value) :
    lastValue init (l ++ [v]) = v := by
  simp only [lastValue, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- **State-topic conflation is effect-lossless.** A subscriber that reads the whole
stream (fold keep-last from cursor `0`) and one that jumps its cursor to the latest
element (reading only `[v]`) observe the same final value — the skipped intermediates
`front` are effect-lossless for value/state semantics. -/
theorem state_conflation_effect_lossless (init : Value) (front : List Value) (v : Value) :
    lastValue init (front ++ [v]) = lastValue init [v] := by
  rw [lastValue_append_singleton]
  simp only [lastValue, List.foldl_cons, List.foldl_nil]

end LazilyFormal.TopicCell
