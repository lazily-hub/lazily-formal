/-
! Signal — the derived eager construct (`Signal ≡ Slot.eager`).

`lazily-spec/docs/reactive-graph.md` demotes `Signal` from the core primitive
set: it is **not** a kind of node. It is a memo `Slot` plus a puller `Effect`
that reads the slot on creation and after every invalidation, so the value is
materialized by the time the invalidating `set_cell` / `batch` returns.

`LazilyFormal.Reactive` already fixes the *graph* half of that claim — the
backing slot carries a concrete value after the puller runs
(`signal_materialized_after_recompute`). What it cannot state is the part the
spec actually leans on, because its `recomputeSlot` receives the new value from
the caller and the graph has no notion of *running a computation*:

- that adding the puller changes **when** compute runs and never **what** a
  reader observes (the claim "Signal is not a primitive" reduces to), and
- that the puller runs **once per flush, not once per write** — the property a
  binding can violate while still passing every value-level fixture, because
  the values it serves are all correct and only the compute count is wrong.

So this module re-models the signal at the resolution where compute is an
event. The graph is collapsed to what these theorems need — a source
environment, one derived node over it, and a counter — and `compute` is a real
function of the sources, invoked by `recompute` and by nothing else. The
counter is the whole point: `World.computes` is the only field here that has no
counterpart in the runtime, and it exists so that "how many times did the memo
run" is a statement the model can make.

Proved here:

- `signal_read_equiv_lazy_memo` — **the demotion theorem.** For every program
  (any interleaving of writes, reads, batches, and disposal), a signal and a
  bare lazy memo over the same compute emit the *same sequence of read values*.
  Both equal `specRun`, the pure spec that just re-evaluates `compute` against
  the current sources at each read. Adding the puller is observationally
  invisible to a reader; it is a scheduling decision, not a semantic one.
- `signal_fresh_after_set_cell` / `signal_fresh_after_batch_exit` — **what
  eager means.** With the puller live, the backing value equals
  `compute sources` the instant the mutator returns, with no intervening read.
- `lazy_memo_not_fresh_after_set_cell` — and the bare memo does not: after the
  same write it is dirty and has run compute zero times. This is the *only*
  observable difference between the two, and it is not visible through a read
  (which is exactly `signal_read_equiv_lazy_memo`).
- `batch_pull_runs_at_most_once` / `batch_pull_runs_exactly_once` — **N writes
  inside a batch cost one compute, not N.** Contrast
  `unbatched_writes_compute_once_per_write`: the same three writes outside a
  batch cost three. A binding that recomputes per write inside a batch serves
  correct values and violates this.
- `disposed_signal_*` — disposing the puller keeps the backing slot readable
  and correct, and reverts it to lazy: a write no longer materializes anything,
  and the next read is what pays for the compute.

Values are abstract `Nat` stand-ins, as everywhere in `LazilyFormal`.
-/

namespace LazilyFormal.Signal

/-- Abstract source-cell identifier. -/
abbrev SrcId := Nat

/-- Abstract node payload — the model exercises equality of values, never their
    type, so a `Nat` stand-in suffices. -/
abbrev Value := Nat

/-- The signal's recipe: a pure computation over the source environment. This is
    the memo body (`signal(compute)` / `ctx.memo`). Purity is the modelling
    assumption that makes "the value a reader observes" well-defined
    independently of *when* the body runs — which is the whole subject here. -/
structure Config where
  compute : (SrcId → Value) → Value

/-- The observable state of a signal: the source environment it reads, the
    backing memo slot (`cache` + `dirty`), the puller effect (`puller`), the
    batch nesting depth, and the deferred-invalidation flag that a batch
    accumulates and its exit drains.

    `computes` counts invocations of `Config.compute`. It has no runtime
    counterpart — it is the instrument, present so that the theorems can talk
    about compute *events* rather than only about values. -/
structure World where
  /-- Current value of every source cell. -/
  src : SrcId → Value
  /-- The memo slot's cached value; `none` before its first computation. -/
  cache : Option Value
  /-- The memo slot needs recomputation before its next observed read. -/
  dirty : Bool
  /-- Number of times `Config.compute` has been invoked. Instrumentation. -/
  computes : Nat
  /-- The puller effect is live. `false` ⇒ a bare lazy memo. -/
  puller : Bool
  /-- Batch nesting depth; `0` ⇒ not inside a batch. -/
  depth : Nat
  /-- An invalidation is waiting for the next flush. -/
  pending : Bool

/-! ## Operations

Everything below is a total function of the world. `recompute` is the only
function that invokes `Config.compute` in a way that bumps the counter — reads
that serve a cache do not, which is what makes the counter meaningful. -/

/-- Run the memo body and cache the result. The single compute event. -/
def recompute (cfg : Config) (w : World) : World :=
  { w with cache := some (cfg.compute w.src), dirty := false,
           computes := w.computes + 1 }

/-- A lazy-pull read of the backing slot: serve the cache when it is present and
    clean, otherwise recompute. This is the *same* read path for a signal and
    for a bare memo — the puller does not change how reading works, it only
    changes whether the read finds the slot already clean. -/
def readSlot (cfg : Config) (w : World) : Value × World :=
  if w.dirty then (cfg.compute w.src, recompute cfg w)
  else
    match w.cache with
    | some v => (v, w)
    | none => (cfg.compute w.src, recompute cfg w)

/-- Drain a pending invalidation. The puller effect *is* this branch: when it is
    live the flush re-materializes the memo, and when it is disposed the flush
    only clears the flag and the slot stays dirty until someone reads it. -/
def flush (cfg : Config) (w : World) : World :=
  if w.pending then
    if w.puller then { recompute cfg w with pending := false }
    else { w with pending := false }
  else w

/-- The `PartialEq`-guarded source write (`LazilyFormal.Reactive.setCell`). An
    equal write is a no-op. A strictly different write updates the source, marks
    the memo dirty, and raises the pending flag — which flushes immediately at
    depth `0` and is deferred to the batch boundary inside a batch. -/
def setCell (cfg : Config) (w : World) (k : SrcId) (v : Value) : World :=
  if w.src k = v then w
  else
    let w' : World :=
      { w with src := fun n => if n = k then v else w.src n,
               dirty := true, pending := true }
    if w.depth = 0 then flush cfg w' else w'

/-- Enter a batch. -/
def beginBatch (w : World) : World := { w with depth := w.depth + 1 }

/-- Leave a batch. Only the *outermost* exit flushes: inner exits just decrement,
    which is what makes the batch accumulate its invalidation roots. -/
def endBatch (cfg : Config) (w : World) : World :=
  if w.depth ≤ 1 then flush cfg { w with depth := 0 }
  else { w with depth := w.depth - 1 }

/-- Dispose the puller effect. The backing slot is untouched — this is a
    *reversion to lazy*, not a teardown (contrast
    `LazilyFormal.Reactive.disposeNode`, which clears the arena entry). -/
def disposePuller (w : World) : World := { w with puller := false }

/-- A freshly created signal: the puller reads the slot on creation, so the
    value is materialized from the start and compute has run exactly once. -/
def initSignal (cfg : Config) (s : SrcId → Value) : World :=
  { src := s, cache := some (cfg.compute s), dirty := false, computes := 1,
    puller := true, depth := 0, pending := false }

/-- A bare lazy memo over the same recipe: nothing computed, nothing cached, no
    puller. The comparison baseline for `signal_read_equiv_lazy_memo`. -/
def initMemo (s : SrcId → Value) : World :=
  { src := s, cache := none, dirty := true, computes := 0,
    puller := false, depth := 0, pending := false }

/-! ## Invariants -/

/-- **Coherence** — a clean cache is the right answer. The invariant every
    operation preserves, and the reason a read never needs to know whether a
    puller exists. -/
def Coherent (cfg : Config) (w : World) : Prop :=
  w.dirty = false → ∀ v, w.cache = some v → v = cfg.compute w.src

/-- **Materialization** — the value is *already* `compute src`, with no read
    required to make it so. This is the property that distinguishes a signal
    from a memo, and it is strictly stronger than `Coherent` (which a dirty
    memo satisfies vacuously). -/
def Materialized (cfg : Config) (w : World) : Prop :=
  w.cache = some (cfg.compute w.src) ∧ w.dirty = false

theorem Materialized.coherent {cfg : Config} {w : World}
    (h : Materialized cfg w) : Coherent cfg w := by
  intro _ v hv
  rw [h.1] at hv
  exact (Option.some.inj hv).symm

/-! ## Reads are canonical

The load-bearing lemma: under `Coherent`, a read returns `compute src` — the
value a fresh evaluation against the current sources would give — whatever the
cache and dirty flag happen to be. -/

theorem readSlot_canonical (cfg : Config) (w : World) (hc : Coherent cfg w) :
    (readSlot cfg w).1 = cfg.compute w.src := by
  unfold readSlot
  cases hdb : w.dirty with
  | true => simp
  | false =>
    cases hcv : w.cache with
    | none => simp
    | some v =>
      simp only [Bool.false_eq_true, if_false]
      exact hc hdb v hcv

theorem readSlot_src (cfg : Config) (w : World) :
    (readSlot cfg w).2.src = w.src := by
  unfold readSlot
  cases hdb : w.dirty with
  | true => simp [recompute]
  | false =>
    cases hcv : w.cache with
    | none => simp [recompute]
    | some v => simp

theorem recompute_materialized (cfg : Config) (w : World) :
    Materialized cfg (recompute cfg w) := ⟨rfl, rfl⟩

theorem readSlot_coherent (cfg : Config) (w : World) (hc : Coherent cfg w) :
    Coherent cfg (readSlot cfg w).2 := by
  unfold readSlot
  cases hdb : w.dirty with
  | true => exact (recompute_materialized cfg w).coherent
  | false =>
    cases hcv : w.cache with
    | none => exact (recompute_materialized cfg w).coherent
    | some v => simpa [hdb, hcv] using hc

/-! ## Flush and write preserve coherence -/

theorem flush_src (cfg : Config) (w : World) : (flush cfg w).src = w.src := by
  unfold flush
  cases hp : w.pending with
  | false => simp
  | true => cases hpl : w.puller <;> simp [recompute]

theorem flush_coherent (cfg : Config) (w : World) (hc : Coherent cfg w) :
    Coherent cfg (flush cfg w) := by
  unfold flush
  cases hp : w.pending with
  | false => simpa [hp] using hc
  | true =>
    cases hpl : w.puller with
    | false => simpa [hp, hpl] using hc
    | true =>
      simp only [if_true]
      intro _ v hv
      exact (Option.some.inj hv).symm

theorem setCell_coherent (cfg : Config) (w : World) (k : SrcId) (v : Value)
    (hc : Coherent cfg w) : Coherent cfg (setCell cfg w k v) := by
  unfold setCell
  by_cases hEq : w.src k = v
  · simpa [hEq] using hc
  · simp only [hEq, if_false]
    by_cases hd : w.depth = 0
    · simp only [hd, if_true]
      refine flush_coherent cfg _ ?_
      intro hdirty
      exact absurd hdirty (by simp)
    · simp only [hd, if_false]
      intro hdirty
      exact absurd hdirty (by simp)

/-- A strictly different write moves the source environment to the pointwise
    update, and an equal write leaves it there too (it was already equal). -/
theorem setCell_src (cfg : Config) (w : World) (k : SrcId) (v : Value) :
    (setCell cfg w k v).src = fun n => if n = k then v else w.src n := by
  unfold setCell
  by_cases hEq : w.src k = v
  · simp only [hEq, if_true]
    funext n
    by_cases hn : n = k
    · rw [hn]; simp [hEq]
    · simp [hn]
  · simp only [hEq, if_false]
    by_cases hd : w.depth = 0
    · simp [hd, flush_src]
    · simp [hd]

theorem endBatch_src (cfg : Config) (w : World) :
    (endBatch cfg w).src = w.src := by
  unfold endBatch
  by_cases h : w.depth ≤ 1
  · simp [h, flush_src]
  · simp [h]

theorem endBatch_coherent (cfg : Config) (w : World) (hc : Coherent cfg w) :
    Coherent cfg (endBatch cfg w) := by
  unfold endBatch
  by_cases h : w.depth ≤ 1
  · simp only [h, if_true]
    exact flush_coherent cfg _ (by simpa using hc)
  · simp only [h, if_false]
    simpa using hc

/-! ## Programs

A program is any interleaving of the operations. `run` executes it against a
world and collects the values the reads observed; `specRun` is the pure
specification — it carries only the sources and answers every read with a fresh
`compute`, having no cache, no puller, and no notion of a batch. -/

/-- One step of a program. -/
inductive Op where
  | write (k : SrcId) (v : Value)
  | read
  | batchBegin
  | batchEnd
  | disposePuller
  deriving Repr

/-- Execute a program, collecting the observed read values in order. -/
def run (cfg : Config) (w : World) : List Op → World × List Value
  | [] => (w, [])
  | .write k v :: os => run cfg (setCell cfg w k v) os
  | .read :: os =>
    let r := readSlot cfg w
    let rest := run cfg r.2 os
    (rest.1, r.1 :: rest.2)
  | .batchBegin :: os => run cfg (beginBatch w) os
  | .batchEnd :: os => run cfg (endBatch cfg w) os
  | .disposePuller :: os => run cfg (disposePuller w) os

/-- The specification: sources only, and every read is a fresh evaluation. No
    cache, no puller, no batch — the reference a reader is entitled to. -/
def specRun (cfg : Config) (s : SrcId → Value) : List Op → List Value
  | [] => []
  | .write k v :: os => specRun cfg (fun n => if n = k then v else s n) os
  | .read :: os => cfg.compute s :: specRun cfg s os
  | .batchBegin :: os => specRun cfg s os
  | .batchEnd :: os => specRun cfg s os
  | .disposePuller :: os => specRun cfg s os

/-- **Every read observes the specification value.** Any coherent world — signal,
    bare memo, mid-batch, puller disposed — emits exactly the read sequence of
    `specRun`. Caching, eagerness, and batching are invisible to a reader. -/
theorem run_reads_canonical (cfg : Config) :
    ∀ (ops : List Op) (w : World), Coherent cfg w →
      (run cfg w ops).2 = specRun cfg w.src ops := by
  intro ops
  induction ops with
  | nil => intro w _; rfl
  | cons o os ih =>
    intro w hc
    cases o with
    | write k v =>
      show (run cfg (setCell cfg w k v) os).2 = specRun cfg w.src (.write k v :: os)
      rw [ih _ (setCell_coherent cfg w k v hc), setCell_src]
      rfl
    | read =>
      show (readSlot cfg w).1 :: (run cfg (readSlot cfg w).2 os).2
             = cfg.compute w.src :: specRun cfg w.src os
      rw [readSlot_canonical cfg w hc, ih _ (readSlot_coherent cfg w hc), readSlot_src]
    | batchBegin =>
      show (run cfg (beginBatch w) os).2 = specRun cfg w.src os
      exact ih _ (by simpa [beginBatch] using hc)
    | batchEnd =>
      show (run cfg (endBatch cfg w) os).2 = specRun cfg w.src os
      rw [ih _ (endBatch_coherent cfg w hc), endBatch_src]
    | disposePuller =>
      show (run cfg (disposePuller w) os).2 = specRun cfg w.src os
      exact ih _ (by simpa [disposePuller] using hc)

/-- **The demotion theorem: `Signal ≡ Slot.eager` on reads.**

    A signal (memo slot + puller effect) and a bare lazy memo over the same
    recipe return *the same value for every read*, under every program — any
    interleaving of writes, reads, batch entry and exit, and puller disposal.

    This is what makes "Signal is not a core primitive" a proof rather than a
    slogan. Adding the puller changes **when** `compute` runs (and therefore how
    many times: see `batch_pull_runs_exactly_once`) and never **what** a reader
    observes. A binding is free to implement `signal(f)` as `slot(f)` plus an
    effect, because there is no read-shaped experiment that can tell the two
    apart.

    Cited by name from `lazily-spec/docs/reactive-graph.md` § "Signal eagerness". -/
theorem signal_read_equiv_lazy_memo
    (cfg : Config) (s : SrcId → Value) (ops : List Op) :
    (run cfg (initSignal cfg s) ops).2 = (run cfg (initMemo s) ops).2 := by
  have hsig : Coherent cfg (initSignal cfg s) := by
    intro _ v hv
    exact (Option.some.inj hv).symm
  have hmemo : Coherent cfg (initMemo s) := by
    intro hd
    exact absurd hd (by simp [initMemo])
  rw [run_reads_canonical cfg ops _ hsig, run_reads_canonical cfg ops _ hmemo]
  rfl

/-! ## Freshness at mutator return

What "eager" means operationally: the value is materialized by the time the
mutator returns, with no intervening read. This is the property a bare lazy memo
does **not** have — and, by `signal_read_equiv_lazy_memo`, the *only* way to
tell the two apart. -/

theorem flush_materialized (cfg : Config) (w : World) (hp : w.puller = true)
    (hm : w.pending = false → Materialized cfg w) :
    Materialized cfg (flush cfg w) := by
  unfold flush
  cases hpend : w.pending with
  | false => simpa [hpend] using hm hpend
  | true => simp only [hp, if_true]; exact ⟨rfl, rfl⟩

/-- **Eager freshness at `set_cell` return.** With the puller live and no batch
    open, the backing value equals `compute` of the *current* sources the moment
    `set_cell` returns — no read required to make it so.

    Materialization is preserved, not merely established: the hypothesis and the
    conclusion are the same predicate, so this iterates over any number of
    writes. -/
theorem signal_fresh_after_set_cell (cfg : Config) (w : World) (k : SrcId)
    (v : Value) (hp : w.puller = true) (hd : w.depth = 0)
    (hm : Materialized cfg w) :
    Materialized cfg (setCell cfg w k v) := by
  unfold setCell
  by_cases hEq : w.src k = v
  · simpa [hEq] using hm
  · simp only [hEq, if_false, hd, if_true]
    exact flush_materialized cfg _ (by simpa using hp) (by intro h; exact absurd h (by simp))

/-- A bare lazy memo has no such property: after the same strictly-different
    write it is dirty, and `compute` has still run zero times. The value it will
    eventually serve is correct (`signal_read_equiv_lazy_memo`) — it just is not
    there yet. This is the entire observable difference between the two
    constructs, and it is not a difference any read can detect. -/
theorem lazy_memo_not_fresh_after_set_cell
    (cfg : Config) (s : SrcId → Value) (k : SrcId) (v : Value)
    (hne : s k ≠ v) :
    (setCell cfg (initMemo s) k v).dirty = true ∧
    (setCell cfg (initMemo s) k v).computes = 0 := by
  constructor <;> simp [setCell, initMemo, hne, flush]

/-! ## Batching: one compute per flush, not one per write

The property most at risk in a binding, because violating it serves *correct
values* — only the compute count is wrong, and a value-level fixture suite
cannot see it. -/

/-- Apply a run of writes in order. -/
def applyWrites (cfg : Config) (w : World) (ws : List (SrcId × Value)) : World :=
  ws.foldl (fun acc p => setCell cfg acc p.1 p.2) w

/-- A batch: enter, write `N` times, exit. -/
def batch (cfg : Config) (w : World) (ws : List (SrcId × Value)) : World :=
  endBatch cfg (applyWrites cfg (beginBatch w) ws)

/-- A write **inside** a batch computes nothing. It either changes nothing at all
    (the `PartialEq` guard), or it raises the pending flag and defers — and in
    the deferring case the flag is necessarily up, so the last clause reads: a
    batched write that leaves nothing pending changed nothing whatsoever. -/
theorem setCell_deep (cfg : Config) (w : World) (k : SrcId) (v : Value)
    (hd : ¬ w.depth = 0) :
    (setCell cfg w k v).depth = w.depth ∧
    (setCell cfg w k v).computes = w.computes ∧
    (setCell cfg w k v).puller = w.puller ∧
    (w.pending = true → (setCell cfg w k v).pending = true) ∧
    ((setCell cfg w k v).pending = false → setCell cfg w k v = w) := by
  unfold setCell
  by_cases hEq : w.src k = v
  · simp [hEq]
  · simp [hEq, hd]

/-- The whole run of batched writes computes nothing, and if it leaves nothing
    pending it changed nothing. -/
theorem applyWrites_deep (cfg : Config) (ws : List (SrcId × Value)) :
    ∀ w : World, ¬ w.depth = 0 →
      (applyWrites cfg w ws).depth = w.depth ∧
      (applyWrites cfg w ws).computes = w.computes ∧
      (applyWrites cfg w ws).puller = w.puller ∧
      (w.pending = true → (applyWrites cfg w ws).pending = true) ∧
      ((applyWrites cfg w ws).pending = false → applyWrites cfg w ws = w) := by
  induction ws with
  | nil => intro w _; exact ⟨rfl, rfl, rfl, fun h => h, fun _ => rfl⟩
  | cons p ps ih =>
    intro w hd
    obtain ⟨sd, sc, sp, spend, schg⟩ := setCell_deep cfg w p.1 p.2 hd
    have hd' : ¬ (setCell cfg w p.1 p.2).depth = 0 := by rw [sd]; exact hd
    obtain ⟨rd, rc, rp, rpend, rchg⟩ := ih (setCell cfg w p.1 p.2) hd'
    have hstep : applyWrites cfg w (p :: ps)
        = applyWrites cfg (setCell cfg w p.1 p.2) ps := rfl
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hstep, rd, sd]
    · rw [hstep, rc, sc]
    · rw [hstep, rp, sp]
    · intro h; rw [hstep]; exact rpend (spend h)
    · intro h
      rw [hstep] at h ⊢
      have hs : (setCell cfg w p.1 p.2).pending = false := by
        cases hsp : (setCell cfg w p.1 p.2).pending with
        | false => rfl
        | true => exact absurd (rpend hsp) (by rw [h]; simp)
      rw [rchg h, schg hs]

/-- **A batch of `N` writes runs the puller at most once.** Not once per write:
    the writes defer, and the single flush at the outermost batch exit is the
    only place `compute` can run.

    This is the statement a binding can fail while every value-level fixture
    still passes — the values are right either way, and only the compute count
    distinguishes a correct implementation from one that pulls per write.

    The `depth = 0` hypothesis is carried for spec fidelity (this is the
    *outermost* batch) but is not used: the bound holds at any nesting depth,
    since an inner exit does not flush at all. -/
theorem flush_computes_le (cfg : Config) (w : World) :
    (flush cfg w).computes ≤ w.computes + 1 := by
  unfold flush
  cases hp : w.pending with
  | false => simp
  | true => cases hpl : w.puller <;> simp [recompute]

theorem endBatch_computes_le (cfg : Config) (w : World) :
    (endBatch cfg w).computes ≤ w.computes + 1 := by
  unfold endBatch
  by_cases h : w.depth ≤ 1
  · simpa [h] using flush_computes_le cfg { w with depth := 0 }
  · simp [h]

theorem batch_pull_runs_at_most_once (cfg : Config) (w : World)
    (ws : List (SrcId × Value)) (_hd : w.depth = 0) :
    (batch cfg w ws).computes ≤ w.computes + 1 := by
  have hb : ¬ (beginBatch w).depth = 0 := by simp [beginBatch]
  obtain ⟨_, ac, _, _, _⟩ := applyWrites_deep cfg ws (beginBatch w) hb
  have hac : (applyWrites cfg (beginBatch w) ws).computes = w.computes := by
    rw [ac]; rfl
  have := endBatch_computes_le cfg (applyWrites cfg (beginBatch w) ws)
  rw [hac] at this
  exact this

/-- **Exactly once.** A batch whose first write actually changes a source runs
    the puller precisely one time, regardless of how many further writes follow
    it. `1`, not `N`, and not `0`. -/
theorem batch_pull_runs_exactly_once (cfg : Config) (w : World)
    (k : SrcId) (v : Value) (ws : List (SrcId × Value))
    (hd : w.depth = 0) (hp : w.puller = true) (hne : ¬ w.src k = v) :
    (batch cfg w ((k, v) :: ws)).computes = w.computes + 1 := by
  have hb : ¬ (beginBatch w).depth = 0 := by simp [beginBatch]
  -- the first write defers, raising the pending flag and computing nothing
  have hfirst : setCell cfg (beginBatch w) k v
      = { beginBatch w with
            src := fun n => if n = k then v else (beginBatch w).src n,
            dirty := true, pending := true } := by
    simp [setCell, beginBatch, hne, hd]
  have hd1 : ¬ (setCell cfg (beginBatch w) k v).depth = 0 := by
    rw [hfirst]; simp [beginBatch]
  obtain ⟨ad, ac, ap, apend, _⟩ :=
    applyWrites_deep cfg ws (setCell cfg (beginBatch w) k v) hd1
  have hstep : applyWrites cfg (beginBatch w) ((k, v) :: ws)
      = applyWrites cfg (setCell cfg (beginBatch w) k v) ws := rfl
  have hpend : (applyWrites cfg (beginBatch w) ((k, v) :: ws)).pending = true := by
    rw [hstep]; exact apend (by rw [hfirst])
  have hpul : (applyWrites cfg (beginBatch w) ((k, v) :: ws)).puller = true := by
    rw [hstep, ap, hfirst]; simpa [beginBatch] using hp
  have hcomp : (applyWrites cfg (beginBatch w) ((k, v) :: ws)).computes = w.computes := by
    rw [hstep, ac, hfirst]; rfl
  have hdep : (applyWrites cfg (beginBatch w) ((k, v) :: ws)).depth = 1 := by
    rw [hstep, ad, hfirst]; simp [beginBatch, hd]
  unfold batch endBatch flush
  simp only [hdep, Nat.le_refl, if_true, hpend, hpul]
  simp only [recompute]
  rw [hcomp]

/-- **The contrast.** The same three writes performed *outside* a batch cost
    three computes: one per write, each flushing at its own mutator boundary.
    Batched, they cost one (`batch_pull_runs_exactly_once`). Both are correct;
    the difference is entirely in the compute count, which is why the count has
    to be normative. -/
theorem unbatched_writes_compute_once_per_write
    (cfg : Config) (w : World) (k : SrcId) (a b c : Value)
    (hd : w.depth = 0) (hp : w.puller = true)
    (h0 : ¬ w.src k = a) (h1 : ¬ a = b) (h2 : ¬ b = c) :
    (setCell cfg (setCell cfg (setCell cfg w k a) k b) k c).computes
      = w.computes + 3 := by
  have step : ∀ (u : World) (x y : Value), u.depth = 0 → u.puller = true →
      ¬ u.src x = y →
      (setCell cfg u x y).computes = u.computes + 1 ∧
      (setCell cfg u x y).depth = 0 ∧
      (setCell cfg u x y).puller = true ∧
      (setCell cfg u x y).src x = y := by
    intro u x y hud hup hne
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp [setCell, hne, hud, flush, recompute, hup]
  obtain ⟨c1, d1, p1, s1⟩ := step w k a hd hp h0
  obtain ⟨c2, d2, p2, s2⟩ := step (setCell cfg w k a) k b d1 p1 (by rw [s1]; exact h1)
  obtain ⟨c3, _, _, _⟩ :=
    step (setCell cfg (setCell cfg w k a) k b) k c d2 p2 (by rw [s2]; exact h2)
  rw [c3, c2, c1]

/-- **Freshness survives the batch boundary.** A signal that was materialized
    before the batch is materialized again the instant the outermost `batch`
    returns — for any number of writes inside, including zero. Together with
    `batch_pull_runs_at_most_once`: fresh at exit, and it cost one compute to
    get there. -/
theorem signal_fresh_after_batch_exit (cfg : Config) (w : World)
    (ws : List (SrcId × Value)) (hd : w.depth = 0) (hp : w.puller = true)
    (hm : Materialized cfg w) :
    Materialized cfg (batch cfg w ws) := by
  have hb : ¬ (beginBatch w).depth = 0 := by simp [beginBatch]
  obtain ⟨ad, _, ap, _, achg⟩ := applyWrites_deep cfg ws (beginBatch w) hb
  have hpul : (applyWrites cfg (beginBatch w) ws).puller = true := by
    rw [ap]; simpa [beginBatch] using hp
  have hdep : (applyWrites cfg (beginBatch w) ws).depth ≤ 1 := by
    rw [ad]; simp [beginBatch, hd]
  unfold batch endBatch
  simp only [hdep, if_true]
  refine flush_materialized cfg _ (by simpa using hpul) ?_
  intro hpend
  have hw : applyWrites cfg (beginBatch w) ws = beginBatch w := achg (by simpa using hpend)
  refine ⟨?_, ?_⟩
  · show ({ applyWrites cfg (beginBatch w) ws with depth := 0 } : World).cache = _
    rw [hw]; exact hm.1
  · show ({ applyWrites cfg (beginBatch w) ws with depth := 0 } : World).dirty = false
    rw [hw]; exact hm.2

/-! ## Disposing the puller reverts to lazy

`reactive-graph.md`: "Disposing the puller effect reverts the signal to lazy
behavior (the backing value stays readable but is no longer eagerly kept
fresh)." Three separable claims, one theorem each. -/

/-- The backing value stays readable: disposal touches the effect, not the slot.
    Contrast `LazilyFormal.Reactive.disposeNode`, which clears the arena entry —
    disposing a *puller* is not disposing the signal. -/
theorem disposed_signal_value_stays_readable (w : World) :
    (disposePuller w).cache = w.cache ∧
    (disposePuller w).dirty = w.dirty ∧
    (disposePuller w).src = w.src := ⟨rfl, rfl, rfl⟩

/-- And it still reads *correctly*: the value a read serves after disposal is
    the value a fresh evaluation of the recipe against current sources gives.
    Reverting to lazy costs freshness, never correctness. -/
theorem disposed_signal_reads_correctly (cfg : Config) (w : World)
    (hc : Coherent cfg w) :
    (readSlot cfg (disposePuller w)).1 = cfg.compute w.src :=
  readSlot_canonical cfg (disposePuller w) (by simpa [disposePuller] using hc)

/-- **It is lazy again.** After disposal a write no longer materializes anything:
    `compute` does not run, and the slot is left dirty for the next reader — the
    exact behavior of the bare memo in `lazy_memo_not_fresh_after_set_cell`. -/
theorem disposed_signal_does_not_materialize_on_write
    (cfg : Config) (w : World) (k : SrcId) (v : Value)
    (hd : w.depth = 0) (hne : ¬ w.src k = v) :
    (setCell cfg (disposePuller w) k v).computes = w.computes ∧
    (setCell cfg (disposePuller w) k v).dirty = true := by
  constructor <;> simp [setCell, disposePuller, hne, hd, flush]

/-- The compute the write no longer performs is paid by the next read instead —
    the timing shift is the whole content of "reverts to lazy". -/
theorem disposed_signal_computes_on_next_read
    (cfg : Config) (w : World) (k : SrcId) (v : Value)
    (hd : w.depth = 0) (hne : ¬ w.src k = v) :
    (readSlot cfg (setCell cfg (disposePuller w) k v)).2.computes
      = w.computes + 1 := by
  have hdirty : (setCell cfg (disposePuller w) k v).dirty = true :=
    (disposed_signal_does_not_materialize_on_write cfg w k v hd hne).2
  have hcomp : (setCell cfg (disposePuller w) k v).computes = w.computes :=
    (disposed_signal_does_not_materialize_on_write cfg w k v hd hne).1
  unfold readSlot
  simp only [hdirty, if_true, recompute]
  rw [hcomp]

end LazilyFormal.Signal
