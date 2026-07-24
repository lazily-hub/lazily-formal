/-
! Durable effect sinks (`#lzdurablesink`).

The formal counterpart of `lazily-spec/docs/durable-sinks.md`. It pins the
authority rule that separates *live* Lazily state from *durable* storage: while a
runtime is live, transitions are decided from live state, and durable storage is
a write-only effect sink. A sink MUST NOT reload storage to arbitrate the
transition it is currently persisting.

This module proves the load-bearing invariants the spec's proof matrix names:

- **`durable_through` is monotone** and cannot regress (`durable_through_monotone`,
  `durable_through_no_regress`).
- **Projection persistence is coherent**: an idempotent latest-epoch upsert
  coalesces a batch to its settled value — delivering the settled epoch once
  equals delivering the whole run (`upsert_latest_newer_dominates`,
  `upsert_latest_idem`, `projection_coalesces_to_settled`).
- **Retry is safe**: re-writing an already-acknowledged epoch is a no-op
  (`upsert_latest_older_noop`).
- **History persistence is lossless**: replay covers every epoch past the durable
  cursor, and an advancing cursor never resurrects an acknowledged epoch
  (`history_replay_covers_unacked`, `history_replay_excludes_acked`,
  `history_replay_advances_with_cursor`).
- **A sink failure never rolls live authority backward**: the post-transition
  live state is exactly the pure reducer's output, regardless of sink success or
  failure; only the live status absorbs the failure
  (`transition_authority_is_live`, `persist_failure_no_ack_regress`).
- **Restart is safe**: cold hydration reconstructs the last acknowledged state
  and the live acknowledgement resumes at the durable frontier
  (`hydrate_reconstructs_state`, `hydrate_resumes_at_last_acked`).

The `Ephemeral`-never-`Durable` separation (an ephemeral value must not enter a
durable sink) is already proven in `Presence.ephemeral_never_durable` and is not
re-proved here.

The model is the same abstraction level as `ReliableSync.lean`: the graph is
abstract, the store is a write-only trait, and the live world is a small tuple.
-/

import LazilyFormal.ReliableSync

namespace LazilyFormal.DurableSink

open LazilyFormal.ReliableSync

/-! ### Authority: live state is the decision seam

A transition is decided **purely** from live state. The reducer has no I/O and no
storage-read parameter — the absence of a store argument *is* the invariant that
there is no rehydrate-at-the-decision-seam. -/

abbrev LiveVal := Nat

/-- A pure transition: a function of live state only. -/

abbrev Decide := LiveVal → LiveVal

/-- Live status absorbs a sink failure without moving authority. -/
inductive Status
  | pending
  | retrying
  | applied
  deriving Repr, DecidableEq

/-- The live actor world: authoritative state, the durable acknowledgement
frontier (`ack` = `durable_through`), and a live status. -/
structure LiveWorld where
  state  : LiveVal
  ack    : Nat
  status : Status

/-! ### Monotone `durable_through` acknowledgement -/

/-- Advance the frontier to at least `epoch` (a monotone max). -/
def advanceAck (ack : Nat) (epoch : Nat) : Nat := max ack epoch

theorem durable_through_monotone (ack : Nat) (epoch : Nat) :
    ack ≤ advanceAck ack epoch :=
  Nat.le_max_left _ _

/-- A stale (lower) acknowledgement cannot regress an already-advanced frontier. -/
theorem durable_through_no_regress (ack : Nat) {newer older : Nat}
    (stale : older ≤ newer) :
    advanceAck (advanceAck ack newer) older = advanceAck ack newer := by
  simp only [advanceAck]
  exact Nat.max_eq_left (Nat.le_trans stale (Nat.le_max_right _ _))

/-! ### Projection sink: latest-epoch upsert (idempotent semilattice)

A projection persists the *settled* value of a batch. The sink keeps the
max-epoch value — exactly the LWW join that `ReliableSync.coalesce_by_join_sound`
pins for the outbox — so an intermediate `A → B → C` collapses to `C`. -/

structure ProjStore where
  epoch : Nat
  val   : LiveVal

/-- Latest-epoch wins; an equal epoch rewrites the same value (idempotent). -/
def upsertLatest (st : ProjStore) (e : Nat) (v : LiveVal) : ProjStore :=
  if st.epoch ≤ e then { epoch := e, val := v } else st

/-- A newer-or-equal epoch dominates any preceding write, so delivering the
settled value once equals delivering the whole batch in order. -/
theorem upsert_latest_newer_dominates (st : ProjStore) (e0 e1 : Nat) (v0 v1 : LiveVal)
    (h : e0 ≤ e1) :
    upsertLatest (upsertLatest st e0 v0) e1 v1 = upsertLatest st e1 v1 := by
  dsimp only [upsertLatest]
  by_cases h0 : st.epoch ≤ e0
  · have hse : st.epoch ≤ e1 := Nat.le_trans h0 h
    simp [h0, h, hse]
  · simp [h0]

/-- Re-writing the same epoch/value is an idempotent no-op (retry is safe). -/
theorem upsert_latest_idem (e : Nat) (v : LiveVal) :
    upsertLatest { epoch := e, val := v } e v = { epoch := e, val := v } := by
  simp [upsertLatest]

/-- Re-writing an older epoch is a no-op: an acknowledged frontier never moves
backward under re-delivery. -/
theorem upsert_latest_older_noop (st : ProjStore) (e0 : Nat) (v0 : LiveVal)
    (h : e0 < st.epoch) :
    upsertLatest st e0 v0 = st := by
  have : ¬ st.epoch ≤ e0 := Nat.not_le.mpr h
  simp [upsertLatest, this]

/-- The frontier after a write is `≤ e1` whenever both the prior frontier and the
written epoch are (used by the batch-coalescing induction). -/
theorem upsert_latest_epoch_le (st : ProjStore) (e0 v0 e1 : Nat)
    (hbase : st.epoch ≤ e1) (h01 : e0 ≤ e1) :
    (upsertLatest st e0 v0).epoch ≤ e1 := by
  by_cases h : st.epoch ≤ e0
  · simp [upsertLatest, h]; exact h01
  · simp [upsertLatest, h]; exact hbase

/-- Folding the upsert over a batch (left fold). -/
def foldBatch (st : ProjStore) : List (Nat × LiveVal) → ProjStore
  | [] => st
  | (e, v) :: rest => foldBatch (upsertLatest st e v) rest

/-- **A batch persists only the settled value.** Folding the projection sink over
any prefix whose epochs are all `≤ e1`, then the settled `(e1, v1)`, equals a
single upsert of the settled value — intermediate values are coalesced away. -/
theorem projection_coalesces_to_settled (st : ProjStore)
    (pre : List (Nat × LiveVal)) (e1 : Nat) (v1 : LiveVal)
    (hpre : ∀ p ∈ pre, p.1 ≤ e1) (hbase : st.epoch ≤ e1) :
    foldBatch st (pre ++ [(e1, v1)]) = upsertLatest st e1 v1 := by
  induction pre generalizing st with
  | nil => rfl
  | cons h rest ih =>
    obtain ⟨e0, v0⟩ := h
    simp only [List.cons_append, foldBatch]
    have h01 : e0 ≤ e1 := hpre (e0, v0) List.mem_cons_self
    have hrest : ∀ p ∈ rest, p.1 ≤ e1 :=
      fun p hp => hpre p (List.mem_cons_of_mem _ hp)
    have hfrontier : (upsertLatest st e0 v0).epoch ≤ e1 :=
      upsert_latest_epoch_le st e0 v0 e1 hbase h01
    rw [ih (upsertLatest st e0 v0) hrest hfrontier]
    exact upsert_latest_newer_dominates st e0 e1 v0 v1 h01

/-! ### History sink: ordered, lossless, cursor-resumable

Every accepted fact must survive and stay ordered. The sink appends; an
`ack_through(cursor)` retains the suffix strictly above the cursor; replay
re-reads that suffix. -/

abbrev History := List (Nat × LiveVal)

/-- Replay the unacked suffix: every fact with epoch strictly above the cursor. -/
def replayAfter (h : History) (cursor : Nat) : History :=
  h.filter (fun p => decide (cursor < p.1))

/-- **Replay is lossless.** Every unacked fact (epoch above the cursor) is in the
replay. -/
theorem history_replay_covers_unacked (h : History) (cursor : Nat)
    (p : Nat × LiveVal) (hp : p ∈ h) (hgt : cursor < p.1) :
    p ∈ replayAfter h cursor := by
  simp only [replayAfter, List.mem_filter, hp, decide_eq_true_eq, hgt, and_self]

/-- **No resurrection.** An acknowledged fact (epoch at or below the cursor) is
never replayed. -/
theorem history_replay_excludes_acked (h : History) (cursor : Nat)
    (p : Nat × LiveVal) (hle : p.1 ≤ cursor) :
    p ∉ replayAfter h cursor := by
  intro hm
  simp only [replayAfter, List.mem_filter, decide_eq_true_eq] at hm
  exact Nat.lt_irrefl cursor (Nat.lt_of_lt_of_le hm.2 hle)

/-- **A monotone cursor yields a monotone replay.** Advancing the cursor from `c1`
to `c2 ≥ c1` only narrows the replay — every fact still owed at `c2` (epoch `> c2`)
was already owed at `c1` (since `c1 ≤ c2 < p.1`). An advancing cursor never
resurrects an acknowledged epoch. -/
theorem history_replay_monotone_in_cursor (h : History) (c1 c2 : Nat) (h12 : c1 ≤ c2)
    (p : Nat × LiveVal) (hp : p ∈ replayAfter h c2) :
    p ∈ replayAfter h c1 := by
  simp only [replayAfter, List.mem_filter, decide_eq_true_eq] at hp ⊢
  refine ⟨hp.1, ?_⟩
  exact Nat.lt_of_le_of_lt h12 hp.2

/-! ### Live authority survives sink failure

A transition applies the pure reducer to live state, then persists. A sink
failure flips the live status to `retrying` but leaves the authoritative state
and the durable frontier unchanged — authority never moves to storage. -/

/-- Persist the projection: success advances `durable_through` and marks the
transition applied; failure only marks it retrying. -/
def persistProjection (w : LiveWorld) (sinkOk : Bool) (epoch : Nat) : LiveWorld :=
  if sinkOk then { w with ack := advanceAck w.ack epoch, status := Status.applied }
  else { w with status := Status.retrying }

/-- One transition step: apply the pure reducer, then persist. -/
def stepTransition (w : LiveWorld) (f : Decide) (sinkOk : Bool) (epoch : Nat) : LiveWorld :=
  persistProjection { w with state := f w.state } sinkOk epoch

/-- **Authority is live.** Regardless of sink success or failure, the
post-transition live state is exactly the pure reducer's output — the sink never
arbitrates the transition it is persisting. -/
theorem transition_authority_is_live (w : LiveWorld) (f : Decide) (sinkOk : Bool)
    (epoch : Nat) :
    (stepTransition w f sinkOk epoch).state = f w.state := by
  cases sinkOk <;> simp [stepTransition, persistProjection]

/-- A failed persist leaves the durable frontier unchanged. -/
theorem persist_failure_no_ack_regress (w : LiveWorld) (epoch : Nat) :
    (persistProjection w false epoch).ack = w.ack := by
  simp [persistProjection]

/-- A failed persist does not change live state. -/
theorem persist_failure_preserves_state (w : LiveWorld) (epoch : Nat) :
    (persistProjection w false epoch).state = w.state := by
  simp [persistProjection]

/-- A successful persist advances the frontier monotonically. -/
theorem persist_success_monotone_ack (w : LiveWorld) (epoch : Nat) :
    w.ack ≤ (persistProjection w true epoch).ack := by
  simp [persistProjection, advanceAck, Nat.le_max_left]

/-! ### Cold restart: hydrate once, then resume

Restart recovery is the hydrator's job, run once before the runtime is live: load
the last acknowledged projection into live state and set the live frontier to the
durable cursor. After hydration, authority is live-only. -/

/-- Hydrate live state from the last acknowledged projection. -/
def hydrate (stored : ProjStore) : LiveWorld :=
  { state := stored.val, ack := stored.epoch, status := Status.pending }

theorem hydrate_reconstructs_state (stored : ProjStore) :
    (hydrate stored).state = stored.val := rfl

theorem hydrate_resumes_at_last_acked (stored : ProjStore) :
    (hydrate stored).ack = stored.epoch := rfl

end LazilyFormal.DurableSink
