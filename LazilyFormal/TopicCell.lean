/-
! TopicCell (broadcast) — absolute-offset formal model.

The executable counterpart of `lazily-spec/cell-model.md` § "TopicCell
(broadcast)". A topic is a retained append log with an absolute `baseOffset`
and one stable subscription slot per subscriber id. Every connected subscriber
reads non-destructively from its own absolute cursor.

This model pins the v1 semantic core:

- publish appends exactly one value and moves no cursor;
- new subscriptions start at the current absolute tail;
- disconnected durable cursors are retained and frozen until reconnect;
- disconnected ephemeral subscriptions are removed;
- reads and advances are available only while connected, and advancing at the
  tail is a no-op;
- the GC frontier is the slowest durable cursor (or the tail when none exist),
  GC changes `baseOffset` and the retained prefix but never rebases a cursor;
- snapshot/restore preserves the complete absolute-offset state.

Subscriber ids are list indices in this pure model. `Option.none` is a removed
ephemeral slot, so later ids remain stable; bindings may use any stable external
map key.
-/

import LazilyFormal.Primitive

namespace LazilyFormal.TopicCell

abbrev Value := Nat
abbrev Cursor := Nat
abbrev SubscriberId := Nat

inductive Durability where
  | durable
  | ephemeral
  deriving DecidableEq, Repr

structure Subscription where
  cursor : Cursor
  durability : Durability
  connected : Bool
  deriving DecidableEq, Repr

/-- A retained broadcast log with stable absolute subscriber cursors. -/
structure TopicCell where
  baseOffset : Cursor
  elements : List Value
  subscriptions : List (Option Subscription)
  deriving DecidableEq, Repr

/-- Absolute offset immediately after the retained log. -/
def endOffset (t : TopicCell) : Cursor := t.baseOffset + t.elements.length

/-- Stable lookup; removed or out-of-range ids are absent. -/
def subscriptionOf (t : TopicCell) (i : SubscriberId) : Option Subscription :=
  t.subscriptions.getD i none

def cursorOf (t : TopicCell) (i : SubscriberId) : Option Cursor :=
  (subscriptionOf t i).map (·.cursor)

/-- Read an absolute cursor as an index into the retained suffix. -/
def readStreamFrom (t : TopicCell) (cursor : Cursor) : List Value :=
  t.elements.drop (cursor - t.baseOffset)

/-- Unknown and disconnected subscribers have no readable session stream. -/
def readStream (t : TopicCell) (i : SubscriberId) : List Value :=
  match subscriptionOf t i with
  | some sub => if sub.connected then readStreamFrom t sub.cursor else []
  | none => []

def setSubscription
    (t : TopicCell) (i : SubscriberId) (sub : Option Subscription) : TopicCell :=
  { t with subscriptions := t.subscriptions.set i sub }

/-! ## Publish and subscription lifecycle -/

/-- Publish exactly one value without changing the absolute origin or cursors. -/
def publish (t : TopicCell) (value : Value) : TopicCell :=
  { t with elements := t.elements ++ [value] }

def nextSubscriberId (t : TopicCell) : SubscriberId := t.subscriptions.length

/-- Allocate a new stable id at the current tail. -/
def subscribe (t : TopicCell) (durability : Durability) : TopicCell :=
  { t with subscriptions := t.subscriptions ++ [some {
      cursor := endOffset t
      durability := durability
      connected := true
    }] }

def subscribeDurable (t : TopicCell) : TopicCell := subscribe t .durable
def subscribeEphemeral (t : TopicCell) : TopicCell := subscribe t .ephemeral

/-- Reconnect only an existing durable id, preserving its cursor. -/
def reconnect (t : TopicCell) (i : SubscriberId) : TopicCell :=
  match subscriptionOf t i with
  | some sub =>
      match sub.durability with
      | .durable =>
          if sub.connected then t
          else setSubscription t i (some { sub with connected := true })
      | .ephemeral => t
  | none => t

/-- Durable disconnect persists an offline cursor; ephemeral disconnect removes
the record while retaining the stable id slot. -/
def disconnect (t : TopicCell) (i : SubscriberId) : TopicCell :=
  match subscriptionOf t i with
  | some sub =>
      match sub.durability with
      | .durable => setSubscription t i (some { sub with connected := false })
      | .ephemeral => setSubscription t i none
  | none => t

/-- Move only a connected cursor by one available element. Unknown ids,
disconnected ids, and cursors at the tail are no-ops. -/
def advance (t : TopicCell) (i : SubscriberId) : TopicCell :=
  match subscriptionOf t i with
  | some sub =>
      if sub.connected then
        if sub.cursor < endOffset t then
          setSubscription t i (some { sub with cursor := sub.cursor + 1 })
        else t
      else t
  | none => t

/-- Atomic state used for process restart. -/
structure Snapshot where
  baseOffset : Cursor
  elements : List Value
  subscriptions : List (Option Subscription)
  deriving DecidableEq, Repr

def snapshot (t : TopicCell) : Snapshot :=
  { baseOffset := t.baseOffset, elements := t.elements,
    subscriptions := t.subscriptions }

def restore (saved : Snapshot) : TopicCell :=
  { baseOffset := saved.baseOffset, elements := saved.elements,
    subscriptions := saved.subscriptions }

theorem publish_appends (t : TopicCell) (value : Value) :
    (publish t value).elements = t.elements ++ [value] := rfl

theorem publish_preserves_baseOffset (t : TopicCell) (value : Value) :
    (publish t value).baseOffset = t.baseOffset := rfl

theorem publish_preserves_subscriptions (t : TopicCell) (value : Value) :
    (publish t value).subscriptions = t.subscriptions := rfl

theorem subscribe_cursor_at_tail (t : TopicCell) (durability : Durability) :
    cursorOf (subscribe t durability) (nextSubscriberId t) = some (endOffset t) := by
  simp [cursorOf, subscriptionOf, subscribe, nextSubscriberId,
    List.getD_eq_getElem?_getD]

theorem subscribeDurable_cursor_at_tail (t : TopicCell) :
    cursorOf (subscribeDurable t) (nextSubscriberId t) = some (endOffset t) := by
  simpa [subscribeDurable] using subscribe_cursor_at_tail t Durability.durable

theorem subscribeEphemeral_cursor_at_tail (t : TopicCell) :
    cursorOf (subscribeEphemeral t) (nextSubscriberId t) = some (endOffset t) := by
  simpa [subscribeEphemeral] using subscribe_cursor_at_tail t Durability.ephemeral

theorem reconnect_durable_offline (t : TopicCell) (i : SubscriberId)
    (sub : Subscription) (hsub : subscriptionOf t i = some sub)
    (hdur : sub.durability = .durable) (hoffline : sub.connected = false) :
    reconnect t i = setSubscription t i (some { sub with connected := true }) := by
  simp [reconnect, hsub, hdur, hoffline]

theorem disconnect_durable_persists (t : TopicCell) (i : SubscriberId)
    (sub : Subscription) (hsub : subscriptionOf t i = some sub)
    (hdur : sub.durability = .durable) :
    disconnect t i = setSubscription t i (some { sub with connected := false }) := by
  simp [disconnect, hsub, hdur]

theorem disconnect_ephemeral_removes (t : TopicCell) (i : SubscriberId)
    (sub : Subscription) (hsub : subscriptionOf t i = some sub)
    (hdur : sub.durability = .ephemeral) :
    disconnect t i = setSubscription t i none := by
  simp [disconnect, hsub, hdur]

theorem restore_snapshot (t : TopicCell) : restore (snapshot t) = t := by
  cases t
  rfl

theorem restart_preserves_cursor (t : TopicCell) (i : SubscriberId) :
    cursorOf (restore (snapshot t)) i = cursorOf t i := by
  rw [restore_snapshot]

/-! ## Connected reads, bounded advance, and cursor isolation -/

theorem readStreamFrom_base (t : TopicCell) :
    readStreamFrom t t.baseOffset = t.elements := by
  simp [readStreamFrom]

theorem disconnected_read_empty (t : TopicCell) (i : SubscriberId)
    (sub : Subscription) (hsub : subscriptionOf t i = some sub)
    (hoffline : sub.connected = false) :
    readStream t i = [] := by
  simp [readStream, hsub, hoffline]

theorem connected_read_at_base (t : TopicCell) (i : SubscriberId)
    (sub : Subscription) (hsub : subscriptionOf t i = some sub)
    (hconnected : sub.connected = true) (hcursor : sub.cursor = t.baseOffset) :
    readStream t i = t.elements := by
  simp [readStream, hsub, hconnected, readStreamFrom, hcursor]

theorem broadcast_delivery (t : TopicCell) (i j : SubscriberId)
    (si sj : Subscription)
    (hsi : subscriptionOf t i = some si) (hsj : subscriptionOf t j = some sj)
    (hci : si.connected = true) (hcj : sj.connected = true)
    (hcursorI : si.cursor = t.baseOffset) (hcursorJ : sj.cursor = t.baseOffset) :
    readStream t i = t.elements ∧ readStream t j = t.elements ∧
      readStream t i = readStream t j := by
  have hi := connected_read_at_base t i si hsi hci hcursorI
  have hj := connected_read_at_base t j sj hsj hcj hcursorJ
  exact ⟨hi, hj, hi.trans hj.symm⟩

theorem advance_preserves_elements (t : TopicCell) (i : SubscriberId) :
    (advance t i).elements = t.elements := by
  cases hsub : subscriptionOf t i with
  | none => simp [advance, hsub]
  | some sub =>
      cases hconnected : sub.connected with
      | false => simp [advance, hsub, hconnected]
      | true =>
          by_cases htail : sub.cursor < endOffset t
          · simp [advance, hsub, hconnected, htail, setSubscription]
          · simp [advance, hsub, hconnected, htail]

theorem advance_preserves_baseOffset (t : TopicCell) (i : SubscriberId) :
    (advance t i).baseOffset = t.baseOffset := by
  cases hsub : subscriptionOf t i with
  | none => simp [advance, hsub]
  | some sub =>
      cases hconnected : sub.connected with
      | false => simp [advance, hsub, hconnected]
      | true =>
          by_cases htail : sub.cursor < endOffset t
          · simp [advance, hsub, hconnected, htail, setSubscription]
          · simp [advance, hsub, hconnected, htail]

theorem advance_disconnected_noop (t : TopicCell) (i : SubscriberId)
    (sub : Subscription) (hsub : subscriptionOf t i = some sub)
    (hoffline : sub.connected = false) :
    advance t i = t := by
  simp [advance, hsub, hoffline]

theorem advance_at_end_noop (t : TopicCell) (i : SubscriberId)
    (sub : Subscription) (hsub : subscriptionOf t i = some sub)
    (hend : sub.cursor = endOffset t) :
    advance t i = t := by
  cases hconnected : sub.connected <;> simp [advance, hsub, hconnected, hend]

theorem subscriptionOf_set_ne (t : TopicCell) (i j : SubscriberId)
    (sub : Option Subscription) (h : i ≠ j) :
    subscriptionOf (setSubscription t i sub) j = subscriptionOf t j := by
  simp [subscriptionOf, setSubscription, List.getD_eq_getElem?_getD,
    List.getElem?_set_ne h]

theorem advance_preserves_other_subscription (t : TopicCell) (i j : SubscriberId)
    (h : i ≠ j) : subscriptionOf (advance t i) j = subscriptionOf t j := by
  cases hsub : subscriptionOf t i with
  | none => simp [advance, hsub]
  | some sub =>
      cases hconnected : sub.connected with
      | false => simp [advance, hsub, hconnected]
      | true =>
          by_cases htail : sub.cursor < endOffset t
          · simpa [advance, hsub, hconnected, htail] using
              subscriptionOf_set_ne t i j
                (some { sub with cursor := sub.cursor + 1 }) h
          · simp [advance, hsub, hconnected, htail]

theorem advance_preserves_other_cursor (t : TopicCell) (i j : SubscriberId)
    (h : i ≠ j) : cursorOf (advance t i) j = cursorOf t j := by
  simp [cursorOf, advance_preserves_other_subscription t i j h]

theorem advance_preserves_other_readStream (t : TopicCell) (i j : SubscriberId)
    (h : i ≠ j) : readStream (advance t i) j = readStream t j := by
  simp [readStream, advance_preserves_other_subscription t i j h,
    advance_preserves_elements, advance_preserves_baseOffset, readStreamFrom]

/-! ## Durable retention and absolute-offset GC -/

def durableCursors (t : TopicCell) : List Cursor :=
  t.subscriptions.filterMap fun slot =>
    match slot with
    | some sub =>
        match sub.durability with
        | .durable => some sub.cursor
        | .ephemeral => none
    | none => none

/-- Slowest durable absolute cursor, or the tail when no durable cursor exists. -/
def retentionFrontier (t : TopicCell) : Cursor :=
  (durableCursors t).foldl min (endOffset t)

/-- Safe GC drops the prefix below the durable frontier, advances the absolute
origin, and leaves every subscription record byte-for-byte unchanged. -/
def gc (t : TopicCell) : TopicCell :=
  let frontier := retentionFrontier t
  let remove := frontier - t.baseOffset
  { t with baseOffset := frontier, elements := t.elements.drop remove }

theorem gc_preserves_subscriptions (t : TopicCell) :
    (gc t).subscriptions = t.subscriptions := rfl

theorem gc_preserves_subscription (t : TopicCell) (i : SubscriberId) :
    subscriptionOf (gc t) i = subscriptionOf t i := rfl

theorem gc_preserves_absolute_cursor (t : TopicCell) (i : SubscriberId) :
    cursorOf (gc t) i = cursorOf t i := rfl

theorem foldl_min_le_start (a : Nat) (values : List Nat) :
    values.foldl min a ≤ a := by
  induction values generalizing a with
  | nil => exact Nat.le_refl a
  | cons value rest ih =>
      exact Nat.le_trans (ih (min a value)) (Nat.min_le_left a value)

theorem foldl_min_le_of_mem : ∀ (a value : Nat) (values : List Nat),
    value ∈ values → values.foldl min a ≤ value := by
  intro a value values
  induction values generalizing a with
  | nil => intro h; cases h
  | cons head tail ih =>
      intro h
      rcases List.mem_cons.mp h with he | hm
      · subst he
        exact Nat.le_trans (foldl_min_le_start (min a value) tail)
          (Nat.min_le_right a value)
      · exact ih (min a head) hm

theorem retentionFrontier_le_durableCursor (t : TopicCell) (cursor : Cursor)
    (h : cursor ∈ durableCursors t) : retentionFrontier t ≤ cursor :=
  foldl_min_le_of_mem (endOffset t) cursor (durableCursors t) h

theorem no_durable_frontier_is_tail (t : TopicCell)
    (h : durableCursors t = []) : retentionFrontier t = endOffset t := by
  simp [retentionFrontier, h]

theorem ephemeral_head_does_not_hold_frontier (t : TopicCell) (sub : Subscription)
    (h : sub.durability = .ephemeral) :
    durableCursors { t with subscriptions := some sub :: t.subscriptions } =
      durableCursors t := by
  simp [durableCursors, h]

/-- Dropping an absolute prefix below `cursor` and reading relative to the new
origin yields the same suffix as before GC. -/
theorem gc_preserves_readStream_core
    (elements : List Value) (base frontier cursor : Cursor)
    (hbase : base ≤ frontier) (hcursor : frontier ≤ cursor) :
    (elements.drop (frontier - base)).drop (cursor - frontier) =
      elements.drop (cursor - base) := by
  have hoffsets : (frontier - base) + (cursor - frontier) = cursor - base := by
    have hfrontier : frontier - base + base = frontier := Nat.sub_add_cancel hbase
    have hcursorFrontier : cursor - frontier + frontier = cursor :=
      Nat.sub_add_cancel hcursor
    have hcursorBase : cursor - base + base = cursor :=
      Nat.sub_add_cancel (Nat.le_trans hbase hcursor)
    exact Nat.add_right_cancel (by
      calc
        ((frontier - base) + (cursor - frontier)) + base =
            (cursor - frontier) + ((frontier - base) + base) := by ac_rfl
        _ = (cursor - frontier) + frontier := by rw [hfrontier]
        _ = cursor := hcursorFrontier
        _ = (cursor - base) + base := hcursorBase.symm)
  rw [List.drop_drop, hoffsets]

theorem gc_preserves_readStream (t : TopicCell) (cursor : Cursor)
    (hbase : t.baseOffset ≤ retentionFrontier t)
    (hcursor : retentionFrontier t ≤ cursor) :
    readStreamFrom (gc t) cursor = readStreamFrom t cursor := by
  simpa [gc, readStreamFrom] using
    gc_preserves_readStream_core t.elements t.baseOffset
      (retentionFrontier t) cursor hbase hcursor

theorem gc_at_min_preserves_readStream (t : TopicCell) (i : SubscriberId)
    (sub : Subscription) (hsub : subscriptionOf t i = some sub)
    (hconnected : sub.connected = true)
    (hbase : t.baseOffset ≤ retentionFrontier t)
    (hcursor : retentionFrontier t ≤ sub.cursor) :
    readStream (gc t) i = readStream t i := by
  simp [readStream, gc_preserves_subscription t i, hsub, hconnected]
  exact gc_preserves_readStream t sub.cursor hbase hcursor

/-! ## State-topic conflation -/

def lastValue (initial : Value) (values : List Value) : Value :=
  values.foldl (fun _ value => value) initial

theorem lastValue_append_singleton (initial : Value) (values : List Value)
    (value : Value) : lastValue initial (values ++ [value]) = value := by
  simp [lastValue, List.foldl_append]

/-- For state/value topics, skipping superseded intermediates preserves the
final observed value. Event/log topics do not use this policy. -/
theorem state_conflation_effect_lossless
    (initial : Value) (front : List Value) (value : Value) :
    lastValue initial (front ++ [value]) = lastValue initial [value] := by
  simp [lastValue, List.foldl_append]

end LazilyFormal.TopicCell
