/-
! Presence + ephemeral plane (`#lzpresence`) — formal model.

The formal counterpart of `lazily-spec/docs/presence.md`. Proves the ephemeral
value clears exactly at expiry, awareness is last-writer-per-peer, and — the
structural invariant — the **ephemeral plane never writes to the durable
outbox**: the durable projection of any all-ephemeral op stream is empty.
-/

namespace LazilyFormal.Presence

/-! ## Ephemeral single value -/

structure Ephemeral (α : Type) where
  value : Option α
  expiry : Nat

def Ephemeral.set (e : Ephemeral α) (v : α) (now ttl : Nat) : Ephemeral α :=
  { e with value := some v, expiry := now + ttl }

def Ephemeral.tick (e : Ephemeral α) (now : Nat) : Ephemeral α :=
  if e.expiry ≤ now then { e with value := none } else e

/-- The value clears once the TTL lapses. -/
theorem ephemeral_clears_at_expiry (e : Ephemeral α) (v : α) (now ttl now' : Nat)
    (h : now + ttl ≤ now') :
    ((e.set v now ttl).tick now').value = none := by
  simp [Ephemeral.set, Ephemeral.tick, h]

/-- The value is live before the TTL lapses. -/
theorem ephemeral_live_before_expiry (e : Ephemeral α) (v : α) (now ttl now' : Nat)
    (h : now' < now + ttl) :
    ((e.set v now ttl).tick now').value = some v := by
  have hnle : ¬ (now + ttl ≤ now') := Nat.not_le.mpr h
  simp [Ephemeral.set, Ephemeral.tick, hnle]

/-! ## Awareness (last-writer-per-peer) -/

/-- A peer → (value, expiry) map. -/
def AwarenessMap (α : Type) := Nat → Option (α × Nat)

def setPeer (m : AwarenessMap α) (peer : Nat) (v : α) (exp : Nat) : AwarenessMap α :=
  fun p => if p = peer then some (v, exp) else m p

/-- Setting a peer overwrites its prior value (no merge). -/
theorem awareness_last_writer (m : AwarenessMap α) (peer : Nat) (v : α) (exp : Nat) :
    (setPeer m peer v exp) peer = some (v, exp) := by
  simp [setPeer]

/-- Setting one peer never touches another. -/
theorem awareness_isolates (m : AwarenessMap α) (peer other : Nat) (v : α) (exp : Nat)
    (h : other ≠ peer) : (setPeer m peer v exp) other = m other := by
  simp [setPeer, h]

/-! ## Ephemeral plane never persists -/

inductive Plane where
  | ephemeral
  | durable

structure Tagged (α : Type) where
  plane : Plane
  value : α

/-- The durable outbox persists only `durable`-tagged values. -/
def persist : List (Tagged α) → List α
  | [] => []
  | t :: rest =>
      match t.plane with
      | Plane.durable => t.value :: persist rest
      | Plane.ephemeral => persist rest

/-- An all-ephemeral op stream produces no durable records. -/
theorem ephemeral_never_durable (items : List (Tagged α))
    (h : ∀ t ∈ items, t.plane = Plane.ephemeral) : persist items = [] := by
  induction items with
  | nil => rfl
  | cons t rest ih =>
      have ht : t.plane = Plane.ephemeral := h t List.mem_cons_self
      have hrest : ∀ x ∈ rest, x.plane = Plane.ephemeral :=
        fun x hx => h x (List.mem_cons_of_mem t hx)
      simp only [persist, ht]
      exact ih hrest

end LazilyFormal.Presence
