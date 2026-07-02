/-
! Async effect lifecycle — formal model.

The formal counterpart of `lazily-spec/docs/async.md` § "Async effects" and
§ "Batch support". It models the pure scheduling core of an async reactive
effect — the part of the async context that is *not* the in-flight slot state
machine already covered by `AsyncSlotState.lean`.

Two async conformance points (`async.md` § Conformance) have clean pure-machine
cores and are fixed here:

- **Point 6 — async effect reruns are serialized, cleanup-before-body ordered,
  and executor-scheduled rather than inline.** `fire_blocked_during_cleanup`
  fixes the cleanup-before-body contract: a body rerun cannot start while a
  cleanup future is pending. `cleanupDone_resumes_deferred` fixes the serialized
  resumption: when a cleanup completes and a rerun was queued during it, that
  rerun becomes runnable (it does not run concurrently with the cleanup).
- **Point 7 — batching is synchronous at the mutation boundary; async reruns
  fire only after the outermost batch exits.** `invalidate_from_idle_schedules`
  and `invalidate_yields_pending_or_disposed` fix that a dependency invalidation
  only ever *queues* a rerun (`scheduled` / `cleanupRunningScheduled`), never
  starts one inline; the body runs only when the executor fires it (`fire`).

Disposal (conformance point 3's disposal clause) is also fixed:
`dispose_absorbing` / `disposed_terminal` capture that disposal removes pending
reruns and is terminal — no event revives a disposed effect.

The genuinely concurrency-specific properties — waiter cancellation (point 3's
waiter clause), the two benign `get_async` races (point 4), and compute-context
dependency registration across `.await` (point 5) — are, like the slot-machine
concurrency properties in `AsyncSlotState.lean`, out of scope for a pure total-
function model: the spec itself pins them "by targeted deterministic tests
rather than exhaustive interleaving exploration" (`async.md:236`).

`step` is a total function of `(state, event)`, so the serialization and
scheduling guarantees hold for *every* input — the universal result no finite
deterministic test suite can establish.
-/

import LazilyFormal.Primitive

namespace LazilyFormal.AsyncEffect

/-- The lifecycle state of an async effect. Five states track whether a rerun
    is queued and/or a cleanup future is in flight; `disposed` is terminal. -/
inductive EffectState where
  /-- No body running, no cleanup pending, no rerun queued. -/
  | idle : EffectState
  /-- A rerun is queued, waiting for the executor / outermost-batch exit. -/
  | scheduled : EffectState
  /-- A previous body's cleanup future is in flight; no rerun queued. -/
  | cleanupRunning : EffectState
  /-- A cleanup future is in flight AND a rerun was queued during it (deferred
      until the cleanup completes). -/
  | cleanupRunningScheduled : EffectState
  /-- Terminal: disposed. Pending reruns were removed on disposal. -/
  | disposed : EffectState
  deriving Repr

/-- An event that drives the effect through its lifecycle. -/
inductive EffectEvent where
  /-- A tracked dependency was invalidated; queues a rerun (never starts one). -/
  | invalidate : EffectEvent
  /-- The executor / outermost-batch exit fires a queued rerun. `hasCleanup`
      records whether the body returned an async cleanup future. -/
  | fire (hasCleanup : Bool) : EffectEvent
  /-- The in-flight cleanup future completed. -/
  | cleanupDone : EffectEvent
  /-- Context disposal: remove pending reruns and go terminal. -/
  | dispose : EffectEvent
  deriving Repr

/-- One transition of the effect lifecycle. `fire` from a cleanup-pending state
    is a no-op (cleanup-before-body); `invalidate` only ever queues, never fires;
    `dispose` is absorbing. -/
def step (s : EffectState) : EffectEvent → EffectState
  | EffectEvent.invalidate =>
    match s with
    | .idle => .scheduled
    | .scheduled => .scheduled
    | .cleanupRunning => .cleanupRunningScheduled
    | .cleanupRunningScheduled => .cleanupRunningScheduled
    | .disposed => .disposed
  | EffectEvent.fire hasCleanup =>
    match s, hasCleanup with
    | .scheduled, true => .cleanupRunning
    | .scheduled, false => .idle
    | .disposed, _ => .disposed
    | _, _ => s
  | EffectEvent.cleanupDone =>
    match s with
    | .cleanupRunning => .idle
    | .cleanupRunningScheduled => .scheduled
    | .disposed => .disposed
    | _ => s
  | EffectEvent.dispose => .disposed

/-! ## Theorems -/

/-- Cleanup-before-body (conformance point 6): a body rerun cannot start while a
    cleanup future is pending. From either cleanup-pending state, `fire` is a
    no-op — the state is unchanged, the body is blocked until `cleanupDone`. -/
theorem fire_blocked_during_cleanup (s : EffectState) (hc : Bool)
    (h : s = .cleanupRunning ∨ s = .cleanupRunningScheduled) :
    step s (EffectEvent.fire hc) = s := by
  rcases h with rfl | rfl
  · simp only [step]
  · simp only [step]

/-- Batch-boundary scheduling (conformance point 7): a dependency invalidation
    from an idle effect queues a rerun (`scheduled`); it never starts one inline. -/
theorem invalidate_from_idle_schedules :
    step .idle .invalidate = .scheduled := by
  simp only [step]

/-- Batch-boundary scheduling (conformance point 7): a dependency invalidation
    only ever yields a state with a *queued* rerun (`scheduled` or
    `cleanupRunningScheduled`) or `disposed` — never a state that runs a body
    inline. The body runs only when the executor fires it (`fire`), i.e. after
    the outermost batch exits. -/
theorem invalidate_yields_pending_or_disposed (s : EffectState) :
    step s .invalidate = .scheduled ∨
    step s .invalidate = .cleanupRunningScheduled ∨
    step s .invalidate = .disposed := by
  cases s with
  | idle                  => exact Or.inl (by simp only [step])
  | scheduled             => exact Or.inl (by simp only [step])
  | cleanupRunning        => exact Or.inr (Or.inl (by simp only [step]))
  | cleanupRunningScheduled => exact Or.inr (Or.inl (by simp only [step]))
  | disposed              => exact Or.inr (Or.inr (by simp only [step]))

/-- Serialized resumption (conformance point 6): when a cleanup completes and a
    rerun was queued during it, the deferred rerun becomes runnable
    (`scheduled`) — it does not run concurrently with the just-finished cleanup;
    it fires on the next executor tick. -/
theorem cleanupDone_resumes_deferred :
    step .cleanupRunningScheduled .cleanupDone = .scheduled := by
  simp only [step]

/-- Disposal (conformance point 3): `dispose` is absorbing — from any state it
    transitions to `disposed` (pending reruns removed). -/
theorem dispose_absorbing (s : EffectState) :
    step s .dispose = .disposed := by
  cases s <;> rfl

/-- Disposal is terminal (conformance point 3): once `disposed`, every event
    leaves the effect `disposed`. No event revives a disposed effect. -/
theorem disposed_terminal (e : EffectEvent) :
    step .disposed e = .disposed := by
  cases e <;> first | rfl | (simp only [step])

end LazilyFormal.AsyncEffect
