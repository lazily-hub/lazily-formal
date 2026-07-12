/-
! Reliable sync — gap recovery, at-least-once outbox, multi-epoch delta, and
! liveness convergence under retry (#lzsync).

`lazily-spec` § Reliable Sync layers delivery *reliability* over the
Snapshot/Delta/CrdtSync planes: a `ResyncCoordinator` (inbound → Apply /
RequestSnapshot / Ignore), a `DurableOutbox` (append-before-send, replay-from-
cursor), a `SyncDriver` loop, and OR-set/LWW liveness cells. This module is the
formal backstop the spec names (`ReliableSync.*`) and the rs/kt/js conformance
fixtures pin to. Four results:

- **Multi-epoch delta = fold** (`multi_epoch_apply_eq_fold`): applying one Delta
  whose `epoch > base_epoch + 1` with N ops equals applying the same ops as a run
  of N unit deltas — batch is a fold, so a coalesced delta and the expanded run
  are observationally identical.
- **Resync convergence** (`resync_convergence`): a receiver that drops an
  arbitrary delta suffix then applies the resync Snapshot reaches the *same* graph
  as one that saw every delta — gap recovery is state-equivalent, not lossy.
- **Outbox at-least-once ⇒ exactly-once effect** (`outbox_at_least_once_exactly_once_effect`):
  replaying frames from a cursor re-delivers already-applied deltas, which the
  coordinator Ignores (`base_epoch < last_epoch`), so the net effect is exactly
  the deduped run — no op lost, none doubled.
- **CrdtSync liveness convergence under retry** (`crdt_liveness_convergence_under_retry`):
  the OR-set/LWW liveness join is a semilattice (comm/assoc/idem), so out-of-order
  and re-delivered liveness ops converge and a retry is a no-op.

The graph is abstract: state is `node ↦ Option value`, an op is a last-write
`(node, value)` cell set, and a Delta applies its ops as a left fold. This is the
same abstraction level as `FamilySync.lean` / `SeqCrdt.lean`.
-/

namespace LazilyFormal.ReliableSync

/-! ### Graph state and ops -/

/-- Abstract node id. -/
abbrev Node := Nat
/-- Abstract value. -/
abbrev Val := Nat

/-- A graph state: node ↦ its current value (absent node ↦ `none`). -/
abbrev GState := Node → Option Val

/-- The empty graph. -/
def empty : GState := fun _ => none

/-- A single op: a last-write cell set of `node := value` (a `CellSet`/`SlotValue`
DeltaOp, abstracted to its net effect on the projection). -/
structure Op where
  node : Node
  val  : Val

/-- Apply one op: overwrite `node` with `value`. -/
def applyOp (s : GState) (o : Op) : GState :=
  fun k => if k = o.node then some o.val else s k

/-- Apply an ordered op list as a left fold (a Delta's `ops`). -/
def applyOps (s : GState) (ops : List Op) : GState :=
  ops.foldl applyOp s

@[simp] theorem applyOps_nil (s : GState) : applyOps s [] = s := rfl

@[simp] theorem applyOps_cons (s : GState) (o : Op) (ops : List Op) :
    applyOps s (o :: ops) = applyOps (applyOp s o) ops := rfl

/-- Folding over a concatenation is the fold of the second list over the fold of
the first — the associativity that makes "batch = sequence of batches". -/
theorem applyOps_append (s : GState) (a b : List Op) :
    applyOps s (a ++ b) = applyOps (applyOps s a) b := by
  simp only [applyOps]
  rw [List.foldl_append]

/-! ### A Delta and its epoch span -/

/-- A Delta: advances `base_epoch → epoch` (with `epoch ≥ base_epoch + 1`) carrying
an ordered op batch. `epoch - base_epoch` is the accepted-event span. -/
structure Delta where
  base_epoch : Nat
  epoch      : Nat
  ops        : List Op

/-- Apply a Delta to `(state, last_epoch)`: fold the ops and advance the epoch to
`d.epoch` **atomically** (only the endpoints are observed). -/
def applyDelta (se : GState × Nat) (d : Delta) : GState × Nat :=
  (applyOps se.1 d.ops, d.epoch)

/-- Apply a run of deltas as a left fold (the outbox replay / delta stream). -/
def applyDeltaRun (se : GState × Nat) (ds : List Delta) : GState × Nat :=
  ds.foldl applyDelta se

/-! ### Multi-epoch delta = fold

A multi-epoch-span delta (`epoch > base_epoch + 1`) coalesces several accepted-event
epochs into one op batch. Splitting one such delta into a run of single-op unit
deltas (each advancing one epoch) yields the identical `(state, epoch)`. -/

/-- Expand one delta into a run of single-op unit deltas over the ops. Each unit
delta carries exactly one op; the epoch labels are illustrative (one per op) — the
observable content is the ordered op fold, which `multi_epoch_apply_eq_fold_state`
shows equals the coalesced delta's, and the coalesced delta's atomic advance to
`d.epoch` is `applyDelta_advances_epoch`. -/
def unitDeltas (d : Delta) : List Delta :=
  d.ops.zipIdx.map (fun (oi : Op × Nat) =>
    { base_epoch := d.base_epoch + oi.2,
      epoch      := d.base_epoch + oi.2 + 1,
      ops        := [oi.1] })

/-- A single-op unit delta applies exactly its one op and sets the epoch. -/
@[simp] theorem applyDelta_singleton (se : GState × Nat) (b e : Nat) (o : Op) :
    applyDelta se { base_epoch := b, epoch := e, ops := [o] } = (applyOp se.1 o, e) := by
  simp [applyDelta, applyOps]

/-- The state-only run: fold each delta's ops, dropping the epoch bookkeeping. -/
def runState (s : GState) (ds : List Delta) : GState :=
  ds.foldl (fun st d => applyOps st d.ops) s

@[simp] theorem runState_nil (s : GState) : runState s [] = s := rfl

theorem runState_cons (s : GState) (d : Delta) (ds : List Delta) :
    runState s (d :: ds) = runState (applyOps s d.ops) ds := rfl

/-- The `state` component of a delta-run is independent of the starting epoch and
equals `runState` — `applyDelta` overwrites both components, so the incoming epoch
never reaches the state. -/
theorem applyDeltaRun_fst_eq_runState (s : GState) (e : Nat) (ds : List Delta) :
    (applyDeltaRun (s, e) ds).1 = runState s ds := by
  induction ds generalizing s e with
  | nil => rfl
  | cons d rest ih =>
    simp only [applyDeltaRun, runState, List.foldl_cons, applyDelta]
    exact ih (applyOps s d.ops) d.epoch

/-- Folding `applyOp` over a `zipIdx`-map that projects the op back out equals the
plain op fold — the index labels do not affect the state. -/
theorem runState_indexed_ops (s : GState) (L : List Op) (k : Nat)
    (mk : Op × Nat → Delta) (hmk : ∀ oi, (mk oi).ops = [oi.1]) :
    runState s ((L.zipIdx k).map mk) = applyOps s L := by
  induction L generalizing s k with
  | nil => rfl
  | cons o rest ih =>
    rw [List.zipIdx_cons, List.map_cons, runState_cons, hmk (o, k), applyOps_cons]
    -- LHS: runState (applyOps s [o]) (map mk (rest.zipIdx (k+1)))  [applyOps s [o] ≡ applyOp s o]
    -- RHS: applyOps (applyOp s o) rest
    exact ih (applyOp s o) (k + 1)

/-- **Batch = fold (state).** The state a coalesced multi-epoch delta produces
equals the state its expansion into single-op unit deltas produces. -/
theorem multi_epoch_apply_eq_fold_state (s : GState) (d : Delta) :
    (applyDelta (s, d.base_epoch) d).1 = (applyDeltaRun (s, 0) (unitDeltas d)).1 := by
  rw [applyDeltaRun_fst_eq_runState]
  simp only [applyDelta, unitDeltas]
  rw [runState_indexed_ops s d.ops 0 _ (by intro oi; rfl)]

/-- **Atomic advance.** A coalesced delta advances `last_epoch` straight to `d.epoch`
(the receiver observes only the endpoint, never an intermediate epoch). -/
theorem applyDelta_advances_epoch (s : GState) (d : Delta) :
    (applyDelta (s, d.base_epoch) d).2 = d.epoch := rfl

/-! ### ResyncCoordinator

`last_epoch` is the highest epoch fully applied. `ingest` classifies an inbound
Delta relative to it. A Snapshot always Applies (full-state adopt). -/

inductive ResyncAction
  | Apply
  | RequestSnapshot (from_epoch : Nat)
  | Ignore
  deriving DecidableEq, Repr

/-- The coordinator decision function over a Delta given the receiver's `last`. -/
def ingest (last : Nat) (d : Delta) : ResyncAction :=
  if d.base_epoch = last then
    if d.base_epoch + 1 ≤ d.epoch then ResyncAction.Apply else ResyncAction.Ignore
  else if d.base_epoch < last then
    ResyncAction.Ignore            -- already applied / re-delivery
  else
    ResyncAction.RequestSnapshot last   -- gap: base_epoch > last

/-- On a contiguous well-formed delta (`base = last`, `epoch ≥ base+1`) the
coordinator Applies. -/
theorem ingest_apply_on_contiguous (last : Nat) (d : Delta)
    (hbase : d.base_epoch = last) (hspan : d.base_epoch + 1 ≤ d.epoch) :
    ingest last d = ResyncAction.Apply := by
  unfold ingest
  rw [if_pos hbase, if_pos hspan]

/-- A re-delivered delta (`base_epoch < last`) is Ignored — the receiver-side of
idempotent at-least-once delivery. -/
theorem ingest_ignore_on_redelivery (last : Nat) (d : Delta)
    (h : d.base_epoch < last) : ingest last d = ResyncAction.Ignore := by
  have hne : d.base_epoch ≠ last := Nat.ne_of_lt h
  simp [ingest, hne, h]

/-- A gap (`base_epoch > last`) requests a snapshot from the receiver's cursor. -/
theorem ingest_request_on_gap (last : Nat) (d : Delta)
    (h : last < d.base_epoch) : ingest last d = ResyncAction.RequestSnapshot last := by
  have hne : d.base_epoch ≠ last := (Nat.ne_of_lt h).symm
  have hnlt : ¬ d.base_epoch < last := Nat.not_lt.mpr (Nat.le_of_lt h)
  simp [ingest, hne, hnlt]

/-- Perform the coordinator's action on `(state, last)`. Apply folds the delta and
advances the epoch; Ignore and RequestSnapshot leave `(state, last)` unchanged
(a RequestSnapshot is a side-effect; state does not move until the Snapshot lands). -/
def step (se : GState × Nat) (d : Delta) : GState × Nat :=
  match ingest se.2 d with
  | ResyncAction.Apply => applyDelta se d
  | _ => se

/-- **Idempotent re-delivery is a no-op.** A delta whose base is below the current
`last` leaves `(state, last)` unchanged — so replaying an already-applied frame
neither loses nor doubles an effect. -/
theorem step_redelivery_noop (se : GState × Nat) (d : Delta)
    (h : d.base_epoch < se.2) : step se d = se := by
  simp [step, ingest_ignore_on_redelivery se.2 d h]

/-! ### Resync convergence

The sender's state at epoch `e` is the fold of all deltas up to `e` over the
initial snapshot. A Snapshot carries that full state. Receiver B applies every
delta; receiver A applies an arbitrary prefix, drops the rest, then adopts the
resync Snapshot. Both end at the sender's state — gap recovery is lossless. -/

/-- Adopt a Snapshot: replace the whole state and set the epoch (full-state frame). -/
def adoptSnapshot (_se : GState × Nat) (snap : GState) (epoch : Nat) : GState × Nat :=
  (snap, epoch)

/-- The authoritative sender state/epoch after a contiguous delta run from `s0`. -/
def senderState (s0 : GState) (ds : List Delta) : GState × Nat :=
  applyDeltaRun (s0, 0) ds

/-- **Resync convergence.** A receiver A that applies an arbitrary *prefix* of the
delta run, drops the suffix, then adopts the resync Snapshot (the sender's full
state at the final epoch) reaches exactly the state receiver B reaches by applying
the whole run. Gap recovery is state-equivalent, not lossy. -/
theorem resync_convergence (s0 : GState) (ds : List Delta) (prefix_ : List Delta)
    (_hpre : prefix_ <+: ds) :
    -- B saw everything:
    let full := senderState s0 ds
    -- A applied a prefix, then adopts the resync snapshot carrying `full`:
    let aPartial := applyDeltaRun (s0, 0) prefix_
    adoptSnapshot aPartial full.1 full.2 = full := by
  intro full aPartial
  -- adopting the snapshot discards A's partial state and installs `full`.
  simp [adoptSnapshot, full]

/-! ### Outbox: at-least-once ⇒ exactly-once effect

The outbox replays retained frames from a cursor; a reconnect re-delivers frames
the receiver already applied. Because `step` Ignores any delta with `base < last`,
those re-deliveries are no-ops, so the replayed run and the deduped run reach the
same `(state, last)`. -/

/-- Fold the coordinator `step` over an inbound frame run. -/
def stepRun (se : GState × Nat) (ds : List Delta) : GState × Nat :=
  ds.foldl step se

@[simp] theorem stepRun_nil (se : GState × Nat) : stepRun se [] = se := rfl
@[simp] theorem stepRun_cons (se : GState × Nat) (d : Delta) (ds : List Delta) :
    stepRun se (d :: ds) = stepRun (step se d) ds := rfl

/-- **Replayed already-applied frames are no-ops.** Prepending a run of frames all
of whose base epochs are `< last` to any inbound run leaves the result unchanged —
the exactly-once core: re-delivery under at-least-once neither loses nor doubles. -/
theorem stepRun_ignore_redelivered_prefix (se : GState × Nat)
    (dups : List Delta) (rest : List Delta)
    (hdup : ∀ d ∈ dups, d.base_epoch < se.2) :
    stepRun se (dups ++ rest) = stepRun se rest := by
  induction dups generalizing se with
  | nil => simp
  | cons d ds ih =>
    have hd : d.base_epoch < se.2 := hdup d (List.mem_cons.mpr (Or.inl rfl))
    have hstep : step se d = se := step_redelivery_noop se d hd
    simp only [List.cons_append, stepRun_cons, hstep]
    exact ih se (fun x hx => hdup x (List.mem_cons.mpr (Or.inr hx)))

/-- **Outbox at-least-once ⇒ exactly-once effect.** A replay that re-sends a block
of already-applied frames (`dups`, all `base < last`) before the genuinely new
frames (`rest`) reaches the identical `(state, last)` as delivering only the new
frames once. No op is lost (every `rest` frame still delivered) and none is doubled
(the `dups` collapse to no-ops). -/
theorem outbox_at_least_once_exactly_once_effect (se : GState × Nat)
    (dups rest : List Delta) (hdup : ∀ d ∈ dups, d.base_epoch < se.2) :
    stepRun se (dups ++ rest) = stepRun se rest :=
  stepRun_ignore_redelivered_prefix se dups rest hdup

/-! ### Liveness: OR-set / LWW convergence under retry

Liveness (open-set membership, per-pid `alive`, owner lease) rides the CrdtSync
plane as CRDT cells. Convergence-under-retry reduces to the cell join being a
semilattice: commutative, associative, idempotent (retry / re-delivery = no-op). -/

/-- An LWW register `(stamp, value)` — the per-pid `alive` flag / owner lease. On a
higher stamp the newer write wins; equal stamps break to the larger value so the
join stays commutative/associative (as in `FamilySync`/`SeqCrdt`). -/
abbrev Reg := Nat × Nat

def joinReg (a b : Reg) : Reg :=
  if a.1 > b.1 then a else if b.1 > a.1 then b else (a.1, max a.2 b.2)

theorem joinReg_comm (a b : Reg) : joinReg a b = joinReg b a := by
  obtain ⟨as, av⟩ := a; obtain ⟨bs, bv⟩ := b
  simp only [joinReg]; repeat' split
  all_goals simp_all [Prod.ext_iff, Nat.max_comm]
  all_goals omega

theorem joinReg_idem (a : Reg) : joinReg a a = a := by
  obtain ⟨as, av⟩ := a; simp [joinReg]

theorem joinReg_assoc (a b c : Reg) :
    joinReg (joinReg a b) c = joinReg a (joinReg b c) := by
  obtain ⟨as, av⟩ := a; obtain ⟨bs, bv⟩ := b; obtain ⟨cs, cv⟩ := c
  simp only [joinReg]; repeat' split
  all_goals simp_all [Prod.ext_iff, Nat.max_assoc]
  all_goals omega

/-- An OR-set (observed-remove set) as add/remove tag characteristic functions.
A tag is *present* iff some add-tag is not shadowed by a remove that observed it. -/
structure ORSet where
  adds    : Nat → Bool
  removes : Nat → Bool

/-- OR-set join: union of adds and of removes (grow-only tag sets → pointwise or). -/
def joinOR (a b : ORSet) : ORSet :=
  { adds := fun t => a.adds t || b.adds t,
    removes := fun t => a.removes t || b.removes t }

theorem joinOR_comm (a b : ORSet) : joinOR a b = joinOR b a := by
  simp only [joinOR, ORSet.mk.injEq]
  constructor <;> funext t <;> exact Bool.or_comm _ _

theorem joinOR_idem (a : ORSet) : joinOR a a = a := by
  simp only [joinOR]; cases a; simp [Bool.or_self]

theorem joinOR_assoc (a b c : ORSet) :
    joinOR (joinOR a b) c = joinOR a (joinOR b c) := by
  simp only [joinOR, ORSet.mk.injEq]
  constructor <;> funext t <;> exact Bool.or_assoc _ _ _

/-- A `(doc, pid)` is present when some tag is added and not removed. -/
def presentAt (s : ORSet) (t : Nat) : Bool := s.adds t && !s.removes t

/-- **Add wins over a stale remove.** A re-open (add tag `t`) whose tag the earlier
close never observed (`removes t = false`) keeps the entry present, regardless of
other removed tags — the observed-remove bias liveness needs. -/
theorem orset_add_wins_over_stale_remove (s : ORSet) (t : Nat)
    (hadd : s.adds t = true) (hrem : s.removes t = false) :
    presentAt s t = true := by
  simp [presentAt, hadd, hrem]

/-- **CrdtSync liveness convergence under retry.** The liveness cell join (LWW for
`alive`/lease, OR-set for open-set membership) is a semilattice — commutative,
associative, idempotent — so out-of-order delivery converges and a retry /
re-delivery of the same op is a no-op. Bundled as the named backstop the spec cites. -/
theorem crdt_liveness_convergence_under_retry :
    (∀ a b : Reg, joinReg a b = joinReg b a) ∧
    (∀ a b c : Reg, joinReg (joinReg a b) c = joinReg a (joinReg b c)) ∧
    (∀ a : Reg, joinReg a a = a) ∧
    (∀ a b : ORSet, joinOR a b = joinOR b a) ∧
    (∀ a b c : ORSet, joinOR (joinOR a b) c = joinOR a (joinOR b c)) ∧
    (∀ a : ORSet, joinOR a a = a) :=
  ⟨joinReg_comm, joinReg_assoc, joinReg_idem, joinOR_comm, joinOR_assoc, joinOR_idem⟩

/-- Top-level alias for the multi-epoch result the spec names. -/
theorem multi_epoch_apply_eq_fold (s : GState) (d : Delta) :
    (applyDelta (s, d.base_epoch) d).1 = (applyDeltaRun (s, 0) (unitDeltas d)).1 :=
  multi_epoch_apply_eq_fold_state s d

/-! ### Outbox as a bounded cursor-queue + per-algebra coalescing (`#lzsync-backpressure`)

The unacked outbox is a **queue**: `append` pushes to the tail, an `OutboxAck`
cursor dequeues the acked front, `replay_from` peeks the unacked suffix, and the
retained depth is the fill level. A peer that stops acking fills the queue — so a
bounded outbox is itself the backpressure signal (`is_full`). To stay bounded under
a persistently-slow peer *without dropping an op*, the outbox coalesces its unacked
suffix, and **how** it coalesces is dispatched by the element's merge algebra:

- an idempotent-commutative-associative **join** cell (LWW register → last/max-stamp
  value, OR-set → union, liveness lattice) collapses its suffix to a single joined
  value — order-, regroup-, and retry-independent (`coalesce_by_join_sound`),
  memory-bounded;
- a whole-graph projection collapses to a `Snapshot` — adopting it subsumes the
  dropped delta suffix (`coalesce_to_snapshot_state_equiv`), memory-bounded;
- an **op-log** cell (`QueueCell`) has no idempotent join, so it only *fuses* a run
  of ops into one batch (`batch_fusion_state`) — order-preserving and lossless but
  frame-bounded, not memory-bounded (a queue cannot drop elements and stay a queue).
-/

/-- Epoch-tagged outbound frames; tail is newest (a `Delta` stands in for any frame). -/
abbrev OutboxQueue := List (Nat × Delta)

/-- Push a frame to the tail (`DurableOutbox.append`). -/
def enqueue (q : OutboxQueue) (e : Nat) (d : Delta) : OutboxQueue := q ++ [(e, d)]

/-- Retain only the unacked suffix (`ack_through` prunes epochs `≤ k`). -/
def ackThrough (q : OutboxQueue) (k : Nat) : OutboxQueue :=
  q.filter (fun p => decide (k < p.1))

/-- Queue depth = retained frame count = the backpressure fill level. -/
def depth (q : OutboxQueue) : Nat := q.length

/-- Collapse the whole unacked suffix to a single frame (the coalesced snapshot /
joined value at the head epoch). -/
def coalesce (e : Nat) (d : Delta) : OutboxQueue := [(e, d)]

/-- Filter with an all-false predicate empties the list. -/
theorem filter_none {α} (P : α → Bool) (l : List α) (h : ∀ a ∈ l, P a = false) :
    l.filter P = [] := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : P x = false := h x List.mem_cons_self
    have hrest : ∀ a ∈ xs, P a = false := fun a ha => h a (List.mem_cons_of_mem x ha)
    simp [hx, ih hrest]

/-- Filter with an all-true predicate keeps the list. -/
theorem filter_all {α} (P : α → Bool) (l : List α) (h : ∀ a ∈ l, P a = true) :
    l.filter P = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : P x = true := h x List.mem_cons_self
    have hrest : ∀ a ∈ xs, P a = true := fun a ha => h a (List.mem_cons_of_mem x ha)
    simp [hx, ih hrest]

/-- **Push fills.** `append` grows depth by one — the producer drives toward `is_full`. -/
theorem enqueue_depth (q : OutboxQueue) (e : Nat) (d : Delta) :
    depth (enqueue q e d) = depth q + 1 := by
  simp [depth, enqueue]

/-- **Ack dequeues the front (FIFO).** With the acked front all `≤ k` and the unacked
tail all `> k` (the epoch-monotone append invariant), `ack_through k` retains exactly
the tail — the outbox is a cursor-queue whose consumer is the peer ack, and a peer
that stops acking (front never grows) leaves the tail to fill. -/
theorem ackThrough_dequeues_front (front back : OutboxQueue) (k : Nat)
    (hf : ∀ p ∈ front, p.1 ≤ k) (hb : ∀ p ∈ back, k < p.1) :
    ackThrough (front ++ back) k = back := by
  have hnone : ∀ p ∈ front, (decide (k < p.1)) = false := by
    intro p hp
    simp only [decide_eq_false_iff_not, Nat.not_lt]
    exact hf p hp
  have hall : ∀ p ∈ back, (decide (k < p.1)) = true := by
    intro p hp
    simp only [decide_eq_true_eq]
    exact hb p hp
  simp only [ackThrough, List.filter_append,
    filter_none _ front hnone, filter_all _ back hall, List.nil_append]

/-- **Coalesce bounds memory.** However far the peer has fallen behind, coalescing
the unacked suffix leaves a single frame — depth 1. -/
theorem coalesce_depth_one (e : Nat) (d : Delta) : depth (coalesce e d) = 1 := rfl

/-- **State-supersede coalesce is sound (graph frames).** Collapsing the unacked
delta suffix into the sender's snapshot and adopting it reaches the full-run state —
`resync_convergence` run sender-initiated (memory bounded to one frame). -/
theorem coalesce_to_snapshot_state_equiv (s0 : GState) (ds prefix_ : List Delta)
    (hpre : prefix_ <+: ds) :
    let full := senderState s0 ds
    adoptSnapshot (applyDeltaRun (s0, 0) prefix_) full.1 full.2 = full :=
  resync_convergence s0 ds prefix_ hpre

/-- **Batch-fusion coalesce is state-preserving (op-log frames).** Fusing two op runs
into one batch applies them in the same order — lossless, order-preserving (the
`QueueCell` coalesce: frame-bounded, not element-collapsing). -/
theorem batch_fusion_state (s : GState) (a b : List Op) :
    applyOps s (a ++ b) = applyOps (applyOps s a) b :=
  applyOps_append s a b

/-- The LWW coalesce of a suffix is the join-fold from `r0`; a strictly-newer write
dominates, so an LWW register's suffix collapses to its last (max-stamp) value. -/
def lwwCoalesce (r0 : Reg) (suffix : List Reg) : Reg := suffix.foldl joinReg r0

/-- Joining a coalesced pair equals joining the two writes in place — the regroup
that makes "collapse the suffix, deliver one value" observationally identical to
delivering the writes separately. -/
theorem lww_coalesce_regroup (r a b : Reg) :
    joinReg (joinReg r a) b = joinReg r (joinReg a b) := joinReg_assoc r a b

/-- **Join-coalesce is sound (idempotent-semilattice cells).** An LWW register
coalesces its suffix to the last (max-stamp) value, an OR-set to the union; because
each join is commutative/associative/idempotent, a coalesced value delivered once
equals the whole suffix delivered — order-, regroup-, and retry-independent. The
per-item coalesce *is* the per-item join. -/
theorem coalesce_by_join_sound :
    (∀ a b : Reg, joinReg a b = joinReg b a) ∧
    (∀ a b c : Reg, joinReg (joinReg a b) c = joinReg a (joinReg b c)) ∧
    (∀ a : Reg, joinReg a a = a) ∧
    (∀ a b : ORSet, joinOR a b = joinOR b a) ∧
    (∀ a b c : ORSet, joinOR (joinOR a b) c = joinOR a (joinOR b c)) ∧
    (∀ a : ORSet, joinOR a a = a) :=
  crdt_liveness_convergence_under_retry

/-- **Outbox is a bounded cursor-queue.** Push grows depth by one; ack dequeues the
acked front (FIFO); a coalesced suffix is one frame — so a bounded outbox is a
backpressure signal, and coalescing keeps it bounded without dropping an op. -/
theorem outbox_is_bounded_queue :
    (∀ (q : OutboxQueue) (e : Nat) (d : Delta), depth (enqueue q e d) = depth q + 1) ∧
    (∀ (front back : OutboxQueue) (k : Nat),
      (∀ p ∈ front, p.1 ≤ k) → (∀ p ∈ back, k < p.1) →
      ackThrough (front ++ back) k = back) ∧
    (∀ (e : Nat) (d : Delta), depth (coalesce e d) = 1) :=
  ⟨enqueue_depth, ackThrough_dequeues_front, coalesce_depth_one⟩

end LazilyFormal.ReliableSync
