/-
! Latest-durable per-key projection egress (`#lzlatestdurableprojection`).

The formal counterpart of the lazily-spec `LatestDurableProjectionCore` contract.
Unlike ordinary FIFO egress, this primitive owes only the latest desired value
for each key.  A key has at most one delivery in flight; a newer desired epoch
supersedes pending state without rewriting that flight.  Successful receipts
advance a monotone `durable_through` frontier, while retryable failure keeps the
desired projection pending.

Generation and epoch form the receipt fence.  A reconnect invalidates the old
generation's flight, and an acknowledgement must exactly match the current
flight before it has any authority.  Even a valid acknowledgement for an older
flight cannot clear a newer desired epoch.
-/

namespace LazilyFormal.LatestDurableProjection

variable {K V : Type}

/-- The latest live projection desired for one key. -/
structure Desired (V : Type) where
  epoch : Nat
  value : V
  deriving Repr, DecidableEq

/-- The single transport attempt currently in flight for one key. -/
structure InFlight (V : Type) where
  generation : Nat
  epoch : Nat
  value : V
  deriving Repr, DecidableEq

/-- Observable delivery status.  `retrying` means the last matching attempt
failed but the desired projection remains owed. -/
inductive Status
  | idle
  | pending
  | inFlight
  | retrying
  deriving Repr, DecidableEq

/-- Pure per-key state for `LatestDurableProjectionCore`. -/
structure Core (V : Type) where
  generation : Nat
  durableThrough : Option Nat
  desired : Option (Desired V)
  inFlight : Option (InFlight V)
  retryPending : Bool
  deriving Repr, DecidableEq

/-- Empty core attached to a transport generation. -/
def Core.empty (generation : Nat) : Core V :=
  { generation := generation
    durableThrough := none
    desired := none
    inFlight := none
    retryPending := false }

/-- Projection of an optional durable frontier used by monotonicity theorems. -/
def durableWatermark : Option Nat → Nat
  | none => 0
  | some epoch => epoch

/-- Monotone acknowledgement join. -/
def advanceDurable (current : Option Nat) (epoch : Nat) : Option Nat :=
  match current with
  | none => some epoch
  | some through => some (max through epoch)

/-- Maximum of two optional epochs. -/
def maxEpoch : Option Nat → Option Nat → Option Nat
  | none, right => right
  | left, none => left
  | some left, some right => some (max left right)

/-- Highest epoch still represented anywhere in the entry.  Moving a projection
between desired, in-flight, and durable state therefore never loses the caller's
monotone epoch fence. -/
def newestKnownEpoch (s : Core V) : Option Nat :=
  maxEpoch s.durableThrough
    (maxEpoch (s.desired.map Desired.epoch) (s.inFlight.map InFlight.epoch))

/-- Status is derived from delivery state; it is never a second authority. -/
def status (s : Core V) : Status :=
  match s.inFlight with
  | some _ => .inFlight
  | none =>
      match s.desired with
      | none => .idle
      | some _ => if s.retryPending then .retrying else .pending

/-- `upsert_desired(epoch, value)`: retain only the newest still-owed epoch.
Equal or older writes are idempotent no-ops.  The existing flight is deliberately
untouched, so supersession never mutates an already-issued command. -/
def upsertDesired (s : Core V) (epoch : Nat) (value : V) : Core V :=
  match newestKnownEpoch s with
  | none => { s with desired := some { epoch := epoch, value := value }, retryPending := false }
  | some current =>
      if current < epoch then
        { s with desired := some { epoch := epoch, value := value }, retryPending := false }
      else
        s

/-- `claim(generation)`: issue the current latest desire only when the per-key
lane is empty and the caller owns the current transport generation. -/
def claim (s : Core V) (generation : Nat) : Core V :=
  if generation = s.generation then
    match s.inFlight, s.desired with
    | none, some desired =>
        { s with
          desired := none
          inFlight := some {
            generation := generation
            epoch := desired.epoch
            value := desired.value }
          retryPending := false }
    | _, _ => s
  else
    s

/-- Restore a failed or disconnected flight unless a newer desired epoch already
supersedes it. -/
def restoreFlight (desired : Option (Desired V)) (flight : InFlight V) : Option (Desired V) :=
  match desired with
  | none => some { epoch := flight.epoch, value := flight.value }
  | some current =>
      if flight.epoch < current.epoch then some current
      else some { epoch := flight.epoch, value := flight.value }

/-- `ack_applied(generation, epoch)`: only an exact receipt for the one current
flight may advance durability.  Any `desired` value is necessarily a newer
projection that arrived after the claim and is left pending. -/
def ackApplied (s : Core V) (generation epoch : Nat) : Core V :=
  match s.inFlight with
  | none => s
  | some flight =>
      if flight.generation = generation ∧ flight.epoch = epoch then
        { s with
          durableThrough := advanceDurable s.durableThrough epoch
          inFlight := none
          retryPending := false }
      else
        s

/-- `fail_retryable(generation, epoch)`: a matching failure frees the single
flight while retaining the latest desire for a later claim.  Stale failures are
fenced exactly like stale acknowledgements. -/
def failRetryable (s : Core V) (generation epoch : Nat) : Core V :=
  match s.inFlight with
  | none => s
  | some flight =>
      if flight.generation = generation ∧ flight.epoch = epoch then
        { s with
          desired := restoreFlight s.desired flight
          inFlight := none
          retryPending := true }
      else
        s

/-- `reconnect(new_generation)`: a strictly newer attachment invalidates the old
flight and restores it to pending unless a newer desired epoch supersedes it. -/
def reconnect (s : Core V) (newGeneration : Nat) : Core V :=
  if s.generation < newGeneration then
    match s.inFlight with
    | none => { s with generation := newGeneration }
    | some flight =>
        { s with
          generation := newGeneration
          desired := restoreFlight s.desired flight
          inFlight := none
          retryPending := true }
  else
    s

/-! ### Core safety and progress-compatible laws -/

/-- `durable_through` never decreases under a successful receipt. -/
theorem advance_durable_monotone (through : Option Nat) (epoch : Nat) :
    durableWatermark through ≤ durableWatermark (advanceDurable through epoch) := by
  cases through with
  | none => simp [durableWatermark, advanceDurable]
  | some current => simp [durableWatermark, advanceDurable, Nat.le_max_left]

/-- A newer desired epoch replaces pending state. -/
theorem upsert_desired_newer_wins
    (s : Core V) (current epoch : Nat) (value : V)
    (known : newestKnownEpoch s = some current)
    (newer : current < epoch) :
    (upsertDesired s epoch value).desired = some { epoch := epoch, value := value } := by
  simp [upsertDesired, known, newer]

/-- An equal or stale epoch cannot alter state.  This is the pure-state safety
half shared by `Unchanged`, `AlreadyDurable`, `StaleEpoch`, and `EpochConflict`;
the API result distinguishes those observations without changing the reducer. -/
theorem upsert_desired_stale_noop
    (s : Core V) (current epoch : Nat) (value : V)
    (known : newestKnownEpoch s = some current)
    (stale : epoch ≤ current) :
    upsertDesired s epoch value = s := by
  simp [upsertDesired, known, Nat.not_lt.mpr stale]

/-- Superseding pending state never rewrites the single in-flight command. -/
theorem upsert_desired_preserves_inflight
    (s : Core V) (epoch : Nat) (value : V) :
    (upsertDesired s epoch value).inFlight = s.inFlight := by
  simp only [upsertDesired]
  split <;> try rfl
  split <;> rfl

/-- At most one delivery can be in flight: claiming an occupied lane is a no-op. -/
theorem claim_single_flight
    (s : Core V) (flight : InFlight V) (generation : Nat)
    (occupied : s.inFlight = some flight) :
    claim s generation = s := by
  simp [claim, occupied]

/-- A claim from the current generation snapshots the latest desired value. -/
theorem claim_uses_latest_desired
    (s : Core V) (desired : Desired V)
    (empty : s.inFlight = none) (owed : s.desired = some desired) :
    (claim s s.generation).inFlight = some {
      generation := s.generation
      epoch := desired.epoch
      value := desired.value } := by
  simp [claim, empty, owed]

/-- Claim is a move, not a copy: the claimed desired slot becomes empty. -/
theorem claim_moves_desired_to_inflight
    (s : Core V) (desired : Desired V)
    (empty : s.inFlight = none) (owed : s.desired = some desired) :
    (claim s s.generation).desired = none := by
  simp [claim, empty, owed]

/-- An acknowledgement with a stale generation is byte-for-byte inert. -/
theorem stale_generation_ack_noop
    (s : Core V) (flight : InFlight V) (generation epoch : Nat)
    (current : s.inFlight = some flight)
    (stale : flight.generation ≠ generation) :
    ackApplied s generation epoch = s := by
  simp [ackApplied, current, stale]

/-- An acknowledgement with a stale epoch is byte-for-byte inert. -/
theorem stale_epoch_ack_noop
    (s : Core V) (flight : InFlight V) (generation epoch : Nat)
    (current : s.inFlight = some flight)
    (stale : flight.epoch ≠ epoch) :
    ackApplied s generation epoch = s := by
  simp [ackApplied, current, stale]

/-- Every acknowledgement transition preserves or advances `durable_through`. -/
theorem ack_applied_durable_through_monotone
    (s : Core V) (generation epoch : Nat) :
    durableWatermark s.durableThrough ≤
      durableWatermark (ackApplied s generation epoch).durableThrough := by
  simp only [ackApplied]
  split
  · exact Nat.le_refl _
  · split
    · exact advance_durable_monotone s.durableThrough epoch
    · exact Nat.le_refl _

/-- A valid acknowledgement for an older flight cannot clear a newer desire. -/
theorem ack_does_not_clear_newer_desired
    (s : Core V) (flight : InFlight V) (desired : Desired V)
    (currentFlight : s.inFlight = some flight)
    (currentDesired : s.desired = some desired)
    (_newer : flight.epoch < desired.epoch) :
    (ackApplied s flight.generation flight.epoch).desired = some desired := by
  simp [ackApplied, currentFlight, currentDesired]

/-- A matching retryable failure retains the desired projection and frees the
lane, making another claim possible without reconstructing intent. -/
theorem fail_retryable_retains_desired
    (s : Core V) (flight : InFlight V) (desired : Desired V)
    (current : s.inFlight = some flight)
    (newerPending : s.desired = some desired)
    (newer : flight.epoch < desired.epoch) :
    (failRetryable s flight.generation flight.epoch).desired = some desired ∧
      (failRetryable s flight.generation flight.epoch).inFlight = none := by
  simp [failRetryable, current, newerPending, restoreFlight, newer]

/-- A matching retryable failure with outstanding intent derives `retrying`
status rather than dropping into `idle`. -/
theorem fail_retryable_reports_retrying
    (s : Core V) (flight : InFlight V)
    (current : s.inFlight = some flight) :
    status (failRetryable s flight.generation flight.epoch) = Status.retrying := by
  cases desired : s.desired with
  | none => simp [failRetryable, current, status, restoreFlight, desired]
  | some pending =>
      by_cases newer : flight.epoch < pending.epoch <;>
        simp [failRetryable, current, status, restoreFlight, desired, newer]

/-- After a matching retryable failure, the same latest desire can be claimed
again.  This is the state-machine side of retry liveness; transport fairness is
an environmental assumption, not a pure-state theorem. -/
theorem claim_available_after_retryable_failure
    (s : Core V) (flight : InFlight V)
    (generation : s.generation = flight.generation)
    (current : s.inFlight = some flight)
    (noNewer : s.desired = none) :
    (claim (failRetryable s flight.generation flight.epoch) s.generation).inFlight =
      some {
        generation := s.generation
        epoch := flight.epoch
        value := flight.value } := by
  simp [failRetryable, current, claim, noNewer, generation, restoreFlight]

/-- A newer reconnect preserves the durable frontier and frees the per-key lane. -/
theorem reconnect_preserves_durability_and_frees_lane
    (s : Core V) (newGeneration : Nat) (newer : s.generation < newGeneration) :
    (reconnect s newGeneration).durableThrough = s.durableThrough ∧
      (reconnect s newGeneration).inFlight = none := by
  cases current : s.inFlight <;> simp [reconnect, newer, current]

/-- With no newer pending value, reconnect requeues the disconnected flight. -/
theorem reconnect_requeues_unsuperseded_flight
    (s : Core V) (flight : InFlight V) (newGeneration : Nat)
    (newer : s.generation < newGeneration)
    (current : s.inFlight = some flight) (noNewer : s.desired = none) :
    (reconnect s newGeneration).desired =
      some { epoch := flight.epoch, value := flight.value } := by
  simp [reconnect, newer, current, noNewer, restoreFlight]

/-- Receipts from the pre-reconnect generation cannot affect the new attachment. -/
theorem stale_ack_after_reconnect_noop
    (s : Core V) (newGeneration generation epoch : Nat)
    (newer : s.generation < newGeneration) :
    ackApplied (reconnect s newGeneration) generation epoch = reconnect s newGeneration := by
  cases current : s.inFlight <;> simp [reconnect, newer, ackApplied, current]

/-! ### Per-key lifting -/

/-- A projection family is a total map of independent per-key cores. -/
structure State (K V : Type) where
  core : K → Core V

/-- Replace exactly one key's core. -/
def alter [DecidableEq K] (s : State K V) (key : K) (f : Core V → Core V) : State K V :=
  { core := fun candidate => if candidate = key then f (s.core candidate) else s.core candidate }

/-- Keyed `upsert_desired`. -/
def upsertDesiredAt [DecidableEq K]
    (s : State K V) (key : K) (epoch : Nat) (value : V) : State K V :=
  alter s key (fun core => upsertDesired core epoch value)

/-- Keyed `claim`. -/
def claimAt [DecidableEq K]
    (s : State K V) (key : K) (generation : Nat) : State K V :=
  alter s key (fun core => claim core generation)

/-- Keyed `ack_applied`. -/
def ackAppliedAt [DecidableEq K]
    (s : State K V) (key : K) (generation epoch : Nat) : State K V :=
  alter s key (fun core => ackApplied core generation epoch)

/-- Keyed `fail_retryable`. -/
def failRetryableAt [DecidableEq K]
    (s : State K V) (key : K) (generation epoch : Nat) : State K V :=
  alter s key (fun core => failRetryable core generation epoch)

/-- Keyed `reconnect`. -/
def reconnectAt [DecidableEq K]
    (s : State K V) (key : K) (newGeneration : Nat) : State K V :=
  alter s key (fun core => reconnect core newGeneration)

/-- A transition for one key cannot disturb another key. -/
theorem alter_preserves_other_key [DecidableEq K]
    (s : State K V) (key other : K) (f : Core V → Core V)
    (different : other ≠ key) :
    (alter s key f).core other = s.core other := by
  simp [alter, different]

end LazilyFormal.LatestDurableProjection

/-- Canonical cross-repository name used by lazily-spec and the implementations. -/
abbrev LazilyFormal.LatestDurableProjectionCore :=
  LazilyFormal.LatestDurableProjection.Core
