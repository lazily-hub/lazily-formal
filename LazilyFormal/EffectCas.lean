/-
! Generic keyed effect compare-and-swap — formal model (`#lzeffectcas`).

The formal counterpart of the lazily-spec `EffectCasCore<K, A, P, R>` contract
(`lazily-spec/docs/durable-sinks.md` § "Generic effect compare-and-swap").
Lazily owns stable effect identity and the immutable intent, the authority
token expected by each exact attempt, one in-flight attempt per key, actor-
generation fencing, latest-wins supersession, logical-clock retry, exact
attempt/receipt matching, the monotone `applied_through` frontier, and the
cursor and receipt lineage of an ordered multi-step plan. The application
adapter owns only `observe` and one atomic `compare_and_apply` boundary.

The model is parametric in the key `K`, effect identity `I`, opaque authority
token `A`, plan-step payload `P`, and adapter receipt `R`; it compares them only
for equality. Adapter error values are opaque evidence and are not modeled.
`LazilyFormal.Conformance.EffectCasCorpus` replays every scenario of
`lazily-spec/conformance/egress/effect_cas.json` through `step` inside the
kernel, so the model and the canonical corpus cannot drift.

Universal results (spec invariants 1–6):

* `claim_busy_noop` / `claim_stale_generation_noop` / `claim_waiting_noop` —
  keyed single flight, generation fence, logical-clock eligibility (inv. 1).
* `step_stale_generation_noop`, `step_unknown_attempt_noop` — a stale
  generation, unknown attempt, or non-matching receipt changes no state (inv. 2).
* `step_appliedThrough_monotone` and
  `appliedThrough_advances_only_by_exact_completion` — the frontier is monotone
  and advances only from an exact terminal apply; in particular a superseded,
  retryable, or rejected attempt never advances it (inv. 3, 4).
* `retryable_preserves_identity_cursor`, `reconnect_requeues_same_identity` —
  retry and reconnect preserve effect identity, plan cursor, and completed-step
  receipts (inv. 5).
* `rejected_is_terminal` — rejection is terminal and distinct from retry
  (inv. 6).
* `duplicate_receipt_idempotent`, `completed_retains_receipt`, and the
  receipt-lineage invariant `step_preserves_wf` — every retained intent and
  terminal carries exactly one receipt per completed plan step, in order: no
  terminal receipt is lost or duplicated.
* `step_other_key_unchanged` — independent keys progress independently.
* `completed_terminal_lineage`, `completed_then_duplicate`,
  `superseded_never_advances`, `reconnect_fences_old_generation`,
  `upsert_supersedes_pending` — the per-outcome forms of the above.
-/

namespace LazilyFormal.EffectCas

/-- An immutable desired effect: identity, epoch, key, initial expected
authority, and a (non-empty) ordered plan. -/
structure Intent (K I A P : Type) where
  identity : I
  epoch : Nat
  key : K
  expected : A
  plan : List P
  deriving Repr, DecidableEq

/-- Exact identity of one adapter call. -/
structure AttemptId (I : Type) where
  effect : I
  generation : Nat
  epoch : Nat
  step : Nat
  attempt : Nat
  deriving Repr, DecidableEq

/-- A successful step receipt, retained as lineage for later plan steps. -/
structure Receipt (I A R : Type) where
  attempt : AttemptId I
  receipt : R
  authority : A
  deriving Repr, DecidableEq

/-- The exact compare-and-apply call handed to the adapter. -/
structure Attempt (K I A P R : Type) where
  id : AttemptId I
  key : K
  expected : A
  payload : P
  priorReceipts : List (Receipt I A R)
  deriving Repr, DecidableEq

/-- Retained (pending) work: the intent plus its plan cursor, the authority the
next step expects, completed-step receipts, retry counter, and logical
eligibility time. -/
structure Pending (K I A P R : Type) where
  intent : Intent K I A P
  nextStep : Nat
  expected : A
  receipts : List (Receipt I A R)
  nextAttempt : Nat
  readyAt : Option Nat
  deriving Repr, DecidableEq

/-- The one in-flight attempt of a key and the work it was claimed from. -/
structure Inflight (K I A P R : Type) where
  attempt : Attempt K I A P R
  retained : Pending K I A P R
  deriving Repr, DecidableEq

/-- Retry evidence (the opaque adapter error is not modeled). -/
structure RetryEvidence (I : Type) where
  attempt : AttemptId I
  retryAt : Nat
  deriving Repr, DecidableEq

inductive TerminalKind where
  | applied
  | superseded
  | rejected
  deriving Repr, DecidableEq

/-- The most recent terminal outcome of a key and its receipt lineage. -/
structure Terminal (I A R : Type) where
  kind : TerminalKind
  identity : I
  epoch : Nat
  receipts : List (Receipt I A R)
  deriving Repr, DecidableEq

/-- Per-key state. -/
structure Entry (K I A P R : Type) where
  pending : Option (Pending K I A P R)
  inflight : Option (Inflight K I A P R)
  retry : Option (RetryEvidence I)
  appliedThrough : Option Nat
  terminal : Option (Terminal I A R)
  terminalIntent : Option (Intent K I A P)
  deriving Repr, DecidableEq

/-- The pure core: the actor generation and one entry per key. -/
structure Core (K I A P R : Type) where
  generation : Nat
  entries : List (K × Entry K I A P R)
  deriving Repr, DecidableEq

inductive UpsertResult where
  | accepted
  | unchanged
  | epochConflict
  | staleEpoch (current : Nat)
  | alreadyApplied (appliedThrough : Nat)
  deriving Repr, DecidableEq

inductive ClaimResult (K I A P R : Type) where
  | claimed (attempt : Attempt K I A P R)
  | busy
  | empty
  | waiting (retryAt : Nat)
  | staleGeneration (current : Nat)
  deriving Repr, DecidableEq

inductive AppliedResult where
  | completed (appliedThrough : Nat)
  | stepApplied (nextStep : Nat)
  | duplicate
  | superseded
  | unknownAttempt
  | staleGeneration (current : Nat)
  deriving Repr, DecidableEq

inductive FailureResult where
  | superseded
  | retrying (retryAt : Nat)
  | rejected
  | unknownAttempt
  | staleGeneration (current : Nat)
  deriving Repr, DecidableEq

inductive ReconnectResult where
  | advanced (generation requeued superseded : Nat)
  | unchanged (generation : Nat)
  | staleGeneration (current : Nat)
  deriving Repr, DecidableEq

/-- The adapter's failure outcomes. -/
inductive Failure (A : Type) where
  | superseded (observed : A)
  | retryable (retryAt : Nat)
  | rejected
  deriving Repr, DecidableEq

/-- Every core operation. -/
inductive Op (K I A P R : Type) where
  | upsert (intent : Intent K I A P)
  | claim (key : K) (generation now : Nat)
  | applied (key : K) (attempt : AttemptId I) (receipt : R) (authority : A)
  | failed (key : K) (attempt : AttemptId I) (failure : Failure A)
  | reconnect (generation : Nat)
  deriving Repr, DecidableEq

inductive Outcome (K I A P R : Type) where
  | upsert (result : UpsertResult)
  | claim (result : ClaimResult K I A P R)
  | applied (result : AppliedResult)
  | failure (result : FailureResult)
  | reconnect (result : ReconnectResult)
  deriving Repr, DecidableEq

variable {K I A P R : Type}

/-! ### Keyed storage -/

def Entry.empty : Entry K I A P R :=
  { pending := none, inflight := none, retry := none, appliedThrough := none,
    terminal := none, terminalIntent := none }

def lookup [DecidableEq K] : List (K × Entry K I A P R) → K → Option (Entry K I A P R)
  | [], _ => none
  | (k', e) :: rest, k => if k' = k then some e else lookup rest k

def store [DecidableEq K] :
    List (K × Entry K I A P R) → K → Entry K I A P R → List (K × Entry K I A P R)
  | [], k, e => [(k, e)]
  | (k', e') :: rest, k, e => if k' = k then (k, e) :: rest else (k', e') :: store rest k e

theorem lookup_store_same [DecidableEq K] (es : List (K × Entry K I A P R)) (k : K)
    (e : Entry K I A P R) : lookup (store es k e) k = some e := by
  induction es with
  | nil => simp [store, lookup]
  | cons x rest ih =>
      obtain ⟨k', e'⟩ := x
      by_cases h : k' = k <;> simp [store, lookup, h, ih]

theorem lookup_store_other [DecidableEq K] (es : List (K × Entry K I A P R)) (k k' : K)
    (e : Entry K I A P R) (hne : k' ≠ k) : lookup (store es k e) k' = lookup es k' := by
  induction es with
  | nil => simp [store, lookup, Ne.symm hne]
  | cons x rest ih =>
      obtain ⟨k₀, e₀⟩ := x
      by_cases h : k₀ = k
      · subst h; simp [store, lookup, Ne.symm hne]
      · by_cases h' : k₀ = k'
        · subst h'; simp [store, lookup, h]
        · simp [store, lookup, h, h', ih]

/-- The entry of a key (a fresh key has an empty entry). -/
def Core.entry [DecidableEq K] (c : Core K I A P R) (k : K) : Entry K I A P R :=
  (lookup c.entries k).getD Entry.empty

/-! ### Operations

Each operation is split into small named pieces with no nested `let`, so every
branch of the reducer is a distinct, inspectable definition. -/

def maxOpt : Option Nat → Option Nat → Option Nat
  | none, b => b
  | a, none => a
  | some a, some b => some (max a b)

/-- The newest epoch the entry still represents (pending, in flight, or the
last terminal intent). -/
def currentEpoch (e : Entry K I A P R) : Option Nat :=
  maxOpt (e.pending.map (·.intent.epoch))
    (maxOpt (e.inflight.map (·.retained.intent.epoch)) (e.terminalIntent.map (·.epoch)))

/-- A pending intent strictly newer than `epoch` exists. -/
def newerPending (e : Entry K I A P R) (epoch : Nat) : Bool :=
  match e.pending with
  | none => false
  | some p => decide (epoch < p.intent.epoch)

/-- The terminal recording supersession of retained work. -/
def supersededTerminal (p : Pending K I A P R) : Terminal I A R :=
  { kind := .superseded, identity := p.intent.identity, epoch := p.intent.epoch,
    receipts := p.receipts }

def freshPending (intent : Intent K I A P) : Pending K I A P R :=
  { intent := intent, nextStep := 0, expected := intent.expected, receipts := [],
    nextAttempt := 1, readyAt := none }

/-- Does the entry already hold this exact immutable intent at its epoch? -/
def sameIntent [DecidableEq K] [DecidableEq I] [DecidableEq A] [DecidableEq P]
    (e : Entry K I A P R) (intent : Intent K I A P) : Bool :=
  decide (e.pending.map (·.intent) = some intent) ||
    decide (e.inflight.map (·.retained.intent) = some intent) ||
    decide (e.terminalIntent = some intent)

/-- Replacing pending work records its explicit supersession, retaining any
completed-step receipts. -/
def supersedePending (e : Entry K I A P R) : Entry K I A P R :=
  match e.pending with
  | none => e
  | some p => { e with terminal := some (supersededTerminal p), terminalIntent := some p.intent }

def replaceEntry (e : Entry K I A P R) (intent : Intent K I A P) : Entry K I A P R :=
  { supersedePending e with pending := some (freshPending intent), retry := none }

def upsertFresh [DecidableEq K] [DecidableEq I] [DecidableEq A] [DecidableEq P]
    (e : Entry K I A P R) (intent : Intent K I A P) :
    Option (Entry K I A P R) × UpsertResult :=
  match currentEpoch e with
  | some current =>
      if intent.epoch < current then (none, .staleEpoch current)
      else if intent.epoch = current then
        (none, if sameIntent e intent then .unchanged else .epochConflict)
      else (some (replaceEntry e intent), .accepted)
  | none => (some (replaceEntry e intent), .accepted)

/-- `upsert_desired(intent)`: accept only a strictly newer epoch. -/
def upsertEntry [DecidableEq K] [DecidableEq I] [DecidableEq A] [DecidableEq P]
    (e : Entry K I A P R) (intent : Intent K I A P) :
    Option (Entry K I A P R) × UpsertResult :=
  match e.appliedThrough with
  | some applied =>
      if intent.epoch ≤ applied then (none, .alreadyApplied applied) else upsertFresh e intent
  | none => upsertFresh e intent

/-- The exact adapter call for the retained work's current plan step. -/
def mkAttempt (p : Pending K I A P R) (generation : Nat) (payload : P) : Attempt K I A P R :=
  { id := { effect := p.intent.identity, generation := generation, epoch := p.intent.epoch,
            step := p.nextStep, attempt := p.nextAttempt }
    key := p.intent.key
    expected := p.expected
    payload := payload
    priorReceipts := p.receipts }

/-- Move eligible pending work into the sole in-flight slot. -/
def claimReady (e : Entry K I A P R) (p : Pending K I A P R) (generation : Nat) :
    Option (Entry K I A P R) × ClaimResult K I A P R :=
  match p.intent.plan[p.nextStep]? with
  | none => (none, .empty)
  | some payload =>
      (some { e with pending := none,
                     inflight := some { attempt := mkAttempt p generation payload, retained := p } },
       .claimed (mkAttempt p generation payload))

/-- `claim(key, generation, now)` for the current generation. -/
def claimEntry (e : Entry K I A P R) (generation now : Nat) :
    Option (Entry K I A P R) × ClaimResult K I A P R :=
  match e.inflight with
  | some _ => (none, .busy)
  | none =>
      match e.pending with
      | none => (none, .empty)
      | some p =>
          match p.readyAt with
          | some r => if now < r then (none, .waiting r) else claimReady e p generation
          | none => claimReady e p generation

/-- Does the terminal already hold exactly this receipt for this attempt? -/
def knownReceipt [DecidableEq I] [DecidableEq R] (e : Entry K I A P R) (id : AttemptId I)
    (receipt : R) : Bool :=
  match e.terminal with
  | none => false
  | some t => t.receipts.any (fun r => decide (r.attempt = id) && decide (r.receipt = receipt))

/-- Is `id` exactly the in-flight attempt? -/
def isInflight [DecidableEq I] (e : Entry K I A P R) (id : AttemptId I) : Bool :=
  match e.inflight with
  | none => false
  | some f => decide (f.attempt.id = id)

/-- Monotone frontier join. -/
def advanceFrontier : Option Nat → Nat → Nat
  | none, epoch => epoch
  | some old, epoch => max old epoch

/-- Retained work with one more completed-step receipt. -/
def Pending.withReceipt (p : Pending K I A P R) (r : Receipt I A R) : Pending K I A P R :=
  { p with receipts := p.receipts ++ [r] }

/-- Terminal supersession of retained work; the in-flight slot is released. -/
def supersedeEntry (e : Entry K I A P R) (retained : Pending K I A P R) : Entry K I A P R :=
  { e with inflight := none, retry := none, terminal := some (supersededTerminal retained),
           terminalIntent := some retained.intent }

/-- An exact apply of the in-flight attempt, given the retained work with the
new receipt appended. -/
def appliedMatched (e : Entry K I A P R) (retained : Pending K I A P R) (authority : A) :
    Option (Entry K I A P R) × AppliedResult :=
  if newerPending e retained.intent.epoch then
    (some (supersedeEntry e retained), .superseded)
  else if retained.nextStep + 1 < retained.intent.plan.length then
    (some { e with inflight := none, retry := none,
                   pending := some { retained with nextStep := retained.nextStep + 1,
                                                   expected := authority, readyAt := none,
                                                   nextAttempt := 1 } },
     .stepApplied (retained.nextStep + 1))
  else
    (some { e with inflight := none, retry := none,
                   appliedThrough := some (advanceFrontier e.appliedThrough retained.intent.epoch),
                   terminal := some { kind := .applied, identity := retained.intent.identity,
                                      epoch := retained.intent.epoch,
                                      receipts := retained.receipts },
                   terminalIntent := some retained.intent },
     .completed (advanceFrontier e.appliedThrough retained.intent.epoch))

/-- `record_applied(attempt, receipt, authority)` for the current generation. -/
def appliedEntry [DecidableEq I] [DecidableEq R] (e : Entry K I A P R) (id : AttemptId I)
    (receipt : R) (authority : A) : Option (Entry K I A P R) × AppliedResult :=
  if knownReceipt e id receipt then (none, .duplicate)
  else
    match e.inflight with
    | none => (none, .unknownAttempt)
    | some f =>
        if f.attempt.id = id then
          appliedMatched e
            (f.retained.withReceipt { attempt := id, receipt := receipt, authority := authority })
            authority
        else (none, .unknownAttempt)

/-- A matched adapter failure. -/
def failedMatched (e : Entry K I A P R) (retained : Pending K I A P R) (id : AttemptId I) :
    Failure A → Option (Entry K I A P R) × FailureResult
  | .superseded _ => (some (supersedeEntry e retained), .superseded)
  | .retryable retryAt =>
      if newerPending e retained.intent.epoch then (some (supersedeEntry e retained), .superseded)
      else
        (some { e with inflight := none, retry := some { attempt := id, retryAt := retryAt },
                       pending := some { retained with nextAttempt := retained.nextAttempt + 1,
                                                       readyAt := some retryAt } },
         .retrying retryAt)
  | .rejected =>
      (some { e with inflight := none, retry := none,
                     terminal := some { kind := .rejected, identity := retained.intent.identity,
                                        epoch := retained.intent.epoch,
                                        receipts := retained.receipts },
                     terminalIntent := some retained.intent },
       .rejected)

/-- `record_superseded` / `record_retryable` / `record_rejected` for the
current generation. -/
def failedEntry [DecidableEq I] (e : Entry K I A P R) (id : AttemptId I) (failure : Failure A) :
    Option (Entry K I A P R) × FailureResult :=
  match e.inflight with
  | none => (none, .unknownAttempt)
  | some f => if f.attempt.id = id then failedMatched e f.retained id failure else (none, .unknownAttempt)

/-- Reconnect one entry: requeue its in-flight cursor (same identity, cursor,
and receipts) unless a newer desired intent supersedes it. Returns the new entry
and whether it requeued (`some true`), superseded (`some false`), or had nothing
in flight (`none`). -/
def reconnectEntry (e : Entry K I A P R) : Entry K I A P R × Option Bool :=
  match e.inflight with
  | none => (e, none)
  | some f =>
      if newerPending e f.retained.intent.epoch then
        ({ e with inflight := none, terminal := some (supersededTerminal f.retained),
                  terminalIntent := some f.retained.intent }, some false)
      else
        ({ e with inflight := none,
                  pending := some { f.retained with
                    nextAttempt := f.retained.nextAttempt + 1, readyAt := none } }, some true)

def countRequeued : List (K × (Entry K I A P R × Option Bool)) → Nat × Nat
  | [] => (0, 0)
  | (_, (_, r)) :: rest =>
      match r with
      | some true => ((countRequeued rest).1 + 1, (countRequeued rest).2)
      | some false => ((countRequeued rest).1, (countRequeued rest).2 + 1)
      | none => countRequeued rest

/-- Apply a per-entry result at `k`, or leave the core unchanged. -/
def commit [DecidableEq K] (c : Core K I A P R) (k : K) : Option (Entry K I A P R) → Core K I A P R
  | none => c
  | some e => { c with entries := store c.entries k e }

/-- The total reducer: next core and the outcome. -/
def step [DecidableEq K] [DecidableEq I] [DecidableEq A] [DecidableEq P] [DecidableEq R]
    (c : Core K I A P R) : Op K I A P R → Core K I A P R × Outcome K I A P R
  | .upsert intent =>
      (commit c intent.key (upsertEntry (c.entry intent.key) intent).1,
       .upsert (upsertEntry (c.entry intent.key) intent).2)
  | .claim k g now =>
      if g = c.generation then
        match lookup c.entries k with
        | none => (c, .claim .empty)
        | some e => (commit c k (claimEntry e g now).1, .claim (claimEntry e g now).2)
      else (c, .claim (.staleGeneration c.generation))
  | .applied k id receipt authority =>
      if id.generation = c.generation then
        match lookup c.entries k with
        | none => (c, .applied .unknownAttempt)
        | some e =>
            (commit c k (appliedEntry e id receipt authority).1,
             .applied (appliedEntry e id receipt authority).2)
      else (c, .applied (.staleGeneration c.generation))
  | .failed k id failure =>
      if id.generation = c.generation then
        match lookup c.entries k with
        | none => (c, .failure .unknownAttempt)
        | some e => (commit c k (failedEntry e id failure).1, .failure (failedEntry e id failure).2)
      else (c, .failure (.staleGeneration c.generation))
  | .reconnect g =>
      if g < c.generation then (c, .reconnect (.staleGeneration c.generation))
      else if g = c.generation then (c, .reconnect (.unchanged c.generation))
      else
        ({ generation := g,
           entries := c.entries.map (fun x => (x.1, (reconnectEntry x.2).1)) },
         .reconnect (.advanced g
           (countRequeued (c.entries.map (fun x => (x.1, reconnectEntry x.2)))).1
           (countRequeued (c.entries.map (fun x => (x.1, reconnectEntry x.2)))).2))

/-! ### Conformance replay

The corpus is transcribed with every opaque type instantiated at `Nat`. A trace
operation names attempts by the slot a prior claim saved them in, exactly like
the fixture's `save` / `attempt` references. -/

abbrev NCore := Core Nat Nat Nat Nat Nat

inductive TraceOp where
  | upsert (intent : Intent Nat Nat Nat Nat)
  | claim (key generation now : Nat) (save : Option Nat)
  | applied (key slot receipt authority : Nat)
  /-- `backendBefore`/`backendAfter` are the adapter's zero-mutation evidence. -/
  | superseded (key slot observed backendBefore backendAfter : Nat)
  | retryable (key slot retryAt : Nat)
  | rejected (key slot : Nat)
  | reconnect (generation : Nat)
  deriving Repr, DecidableEq

/-- The fields of a claimed attempt the corpus asserts. -/
structure ClaimView where
  identity : Nat
  step : Nat
  attempt : Nat
  expected : Nat
  payload : Nat
  deriving Repr, DecidableEq

inductive ClaimReturn where
  | claimed (view : ClaimView)
  | busy
  | empty
  | waiting (retryAt : Nat)
  | staleGeneration (current : Nat)
  deriving Repr, DecidableEq

inductive Returns where
  | upsert (result : UpsertResult)
  | claim (result : ClaimReturn)
  | applied (result : AppliedResult)
  | failure (result : FailureResult)
  | reconnect (result : ReconnectResult)
  deriving Repr, DecidableEq

def Outcome.view : Outcome Nat Nat Nat Nat Nat → Returns
  | .upsert r => .upsert r
  | .claim (.claimed a) => .claim (.claimed
      { identity := a.id.effect, step := a.id.step, attempt := a.id.attempt,
        expected := a.expected, payload := a.payload })
  | .claim .busy => .claim .busy
  | .claim .empty => .claim .empty
  | .claim (.waiting r) => .claim (.waiting r)
  | .claim (.staleGeneration g) => .claim (.staleGeneration g)
  | .applied r => .applied r
  | .failure r => .failure r
  | .reconnect r => .reconnect r

/-- The per-key projection every binding runner asserts at the end of a
scenario. -/
structure KeyView where
  pendingIdentity : Option Nat
  inflightIdentity : Option Nat
  appliedThrough : Option Nat
  terminal : Option TerminalKind
  receiptCount : Nat
  retryAt : Option Nat
  deriving Repr, DecidableEq

def Entry.view (e : Entry Nat Nat Nat Nat Nat) : KeyView :=
  { pendingIdentity := e.pending.map (·.intent.identity)
    inflightIdentity := e.inflight.map (·.attempt.id.effect)
    appliedThrough := e.appliedThrough
    terminal := e.terminal.map (·.kind)
    receiptCount := (e.terminal.map (·.receipts.length)).getD 0
    retryAt := e.retry.map (·.retryAt) }

structure Scenario where
  generation : Nat
  steps : List (TraceOp × Returns)
  final : List (Nat × KeyView)
  deriving Repr, DecidableEq

def slotLookup : List (Nat × AttemptId Nat) → Nat → Option (AttemptId Nat)
  | [], _ => none
  | (n, a) :: rest, k => if n = k then some a else slotLookup rest k

/-- Run one trace operation; `none` when it names an unsaved attempt or its
zero-mutation evidence is violated. -/
def runOp (c : NCore) (env : List (Nat × AttemptId Nat)) :
    TraceOp → Option (NCore × List (Nat × AttemptId Nat) × Returns)
  | .upsert intent =>
      let (c', o) := step c (.upsert intent)
      some (c', env, o.view)
  | .claim k g now save =>
      let (c', o) := step c (.claim k g now)
      let env' := match save, o with
        | some n, .claim (.claimed a) => (n, a.id) :: env
        | _, _ => env
      some (c', env', o.view)
  | .applied k slot receipt authority => do
      let id ← slotLookup env slot
      let (c', o) := step c (.applied k id receipt authority)
      some (c', env, o.view)
  | .superseded k slot observed before after => do
      let id ← slotLookup env slot
      if before ≠ after then none
      else
        let (c', o) := step c (.failed k id (.superseded observed))
        some (c', env, o.view)
  | .retryable k slot retryAt => do
      let id ← slotLookup env slot
      let (c', o) := step c (.failed k id (.retryable retryAt))
      some (c', env, o.view)
  | .rejected k slot => do
      let id ← slotLookup env slot
      let (c', o) := step c (.failed k id .rejected)
      some (c', env, o.view)
  | .reconnect g =>
      let (c', o) := step c (.reconnect g)
      some (c', env, o.view)

def runSteps : NCore → List (Nat × AttemptId Nat) → List (TraceOp × Returns) → Option NCore
  | c, _, [] => some c
  | c, env, (op, expected) :: rest =>
      match runOp c env op with
      | none => none
      | some (c', env', got) => if got = expected then runSteps c' env' rest else none

/-- Does the model replay the scenario: every step's outcome and the final
per-key projection, over exactly the keys the scenario lists? -/
def Scenario.replays (sc : Scenario) : Bool :=
  match runSteps { generation := sc.generation, entries := [] } [] sc.steps with
  | none => false
  | some c =>
      decide (c.entries.length = sc.final.length) &&
        sc.final.all (fun (k, v) =>
          match lookup c.entries k with
          | none => false
          | some e => decide (e.view = v))

/-! ### Safety theorems -/

section Theorems

set_option linter.unusedSectionVars false

variable [DecidableEq K] [DecidableEq I] [DecidableEq A] [DecidableEq P] [DecidableEq R]

/-! #### Keyed storage facts -/

theorem entry_of_lookup {c : Core K I A P R} {k : K} {e : Entry K I A P R}
    (h : lookup c.entries k = some e) : c.entry k = e := by
  simp [Core.entry, h]

theorem commit_generation (c : Core K I A P R) (k : K) (o : Option (Entry K I A P R)) :
    (commit c k o).generation = c.generation := by
  cases o <;> rfl

theorem lookup_commit_same (c : Core K I A P R) (k : K) (e : Entry K I A P R) :
    lookup (commit c k (some e)).entries k = some e :=
  lookup_store_same _ _ _

theorem lookup_commit_other (c : Core K I A P R) (k k' : K) (o : Option (Entry K I A P R))
    (hne : k' ≠ k) : lookup (commit c k o).entries k' = lookup c.entries k' := by
  cases o with
  | none => rfl
  | some e => exact lookup_store_other _ _ _ _ hne

theorem entry_commit_same (c : Core K I A P R) (k : K) (e : Entry K I A P R) :
    (commit c k (some e)).entry k = e := by
  simp [Core.entry, lookup_commit_same]

theorem entry_commit_other (c : Core K I A P R) (k k' : K) (o : Option (Entry K I A P R))
    (hne : k' ≠ k) : (commit c k o).entry k' = c.entry k' := by
  simp [Core.entry, lookup_commit_other _ _ _ _ hne]

theorem lookup_reconnect (es : List (K × Entry K I A P R)) (k : K) :
    lookup (es.map (fun x => (x.1, (reconnectEntry x.2).1))) k =
      (lookup es k).map (fun e => (reconnectEntry e).1) := by
  induction es with
  | nil => rfl
  | cons x rest ih =>
      obtain ⟨k', e⟩ := x
      simp only [List.map_cons, lookup]
      by_cases h : k' = k
      · simp [h]
      · simp only [h, if_false]; exact ih

/-! #### Single flight, fencing, logical clock (invariants 1, 2) -/

/-- Keyed single flight: a key with an attempt in flight refuses a second claim
and changes nothing. -/
theorem claim_busy_noop (c : Core K I A P R) (k : K) (now : Nat) (e : Entry K I A P R)
    (f : Inflight K I A P R) (he : lookup c.entries k = some e) (hf : e.inflight = some f) :
    step c (.claim k c.generation now) = (c, .claim .busy) := by
  simp [step, he, claimEntry, hf, commit]

/-- A claim from a stale actor generation changes nothing. -/
theorem claim_stale_generation_noop (c : Core K I A P R) (k : K) (g now : Nat)
    (hg : g ≠ c.generation) :
    step c (.claim k g now) = (c, .claim (.staleGeneration c.generation)) := by
  simp [step, hg]

/-- Logical-clock retry: pending work is not eligible before its retry time. -/
theorem claim_waiting_noop (c : Core K I A P R) (k : K) (now r : Nat) (e : Entry K I A P R)
    (p : Pending K I A P R) (he : lookup c.entries k = some e) (hi : e.inflight = none)
    (hp : e.pending = some p) (hr : p.readyAt = some r) (early : now < r) :
    step c (.claim k c.generation now) = (c, .claim (.waiting r)) := by
  simp [step, he, claimEntry, hi, hp, hr, early, commit]

/-- The actor generation an attempt-receipt operation supplies. -/
def Op.receiptGeneration : Op K I A P R → Option Nat
  | .applied _ id _ _ => some id.generation
  | .failed _ id _ => some id.generation
  | _ => none

/-- A receipt from a stale actor generation changes no state (inv. 2). -/
theorem step_stale_generation_noop (c : Core K I A P R) (op : Op K I A P R) (g : Nat)
    (hop : op.receiptGeneration = some g) (stale : g ≠ c.generation) : (step c op).1 = c := by
  cases op <;> simp [Op.receiptGeneration] at hop <;> subst hop <;> simp [step, stale]

theorem appliedEntry_none (e : Entry K I A P R) (id : AttemptId I) (receipt : R)
    (authority : A) (hne : isInflight e id = false) :
    (appliedEntry e id receipt authority).1 = none := by
  unfold appliedEntry
  split
  · rfl
  · cases hf : e.inflight with
    | none => rfl
    | some f =>
        have : f.attempt.id ≠ id := by simpa [isInflight, hf] using hne
        simp [this]

theorem failedEntry_none (e : Entry K I A P R) (id : AttemptId I) (failure : Failure A)
    (hne : isInflight e id = false) : (failedEntry e id failure).1 = none := by
  unfold failedEntry
  cases hf : e.inflight with
  | none => rfl
  | some f =>
      have : f.attempt.id ≠ id := by simpa [isInflight, hf] using hne
      simp [this]

/-- An attempt that is not exactly the key's in-flight attempt (unknown,
already finished, or with any mismatched identity field) changes no state
(inv. 2) — including an exact duplicate of a terminal receipt. -/
theorem step_unknown_attempt_noop (c : Core K I A P R) (k : K) (id : AttemptId I)
    (hne : isInflight (c.entry k) id = false) :
    (∀ receipt authority, (step c (.applied k id receipt authority)).1 = c) ∧
      (∀ failure, (step c (.failed k id failure)).1 = c) := by
  constructor
  · intro receipt authority
    simp only [step]
    split
    · split
      · rfl
      · rename_i e he
        rw [entry_of_lookup he] at hne
        simp only [appliedEntry_none e id receipt authority hne, commit]
    · rfl
  · intro failure
    simp only [step]
    split
    · split
      · rfl
      · rename_i e he
        rw [entry_of_lookup he] at hne
        simp only [failedEntry_none e id failure hne, commit]
    · rfl

/-! #### The applied frontier (invariants 3, 4) -/

/-- Projection of an optional frontier. -/
def watermark : Option Nat → Nat
  | none => 0
  | some n => n

theorem replaceEntry_appliedThrough (e : Entry K I A P R) (intent : Intent K I A P) :
    (replaceEntry e intent).appliedThrough = e.appliedThrough := by
  unfold replaceEntry supersedePending; split <;> rfl

theorem upsertEntry_shape (e : Entry K I A P R) (intent : Intent K I A P)
    (e' : Entry K I A P R) (r : UpsertResult) (h : upsertEntry e intent = (some e', r)) :
    e' = replaceEntry e intent ∧ r = .accepted := by
  unfold upsertEntry upsertFresh at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [Prod.mk.injEq, Option.some.injEq] at h; exact ⟨h.1.symm, h.2.symm⟩)

theorem claimEntry_shape (e : Entry K I A P R) (g now : Nat) (e' : Entry K I A P R)
    (r : ClaimResult K I A P R) (h : claimEntry e g now = (some e', r)) :
    e.inflight = none ∧ ∃ p payload, e.pending = some p ∧ p.intent.plan[p.nextStep]? = some payload ∧
      e' = { e with pending := none,
                    inflight := some { attempt := mkAttempt p g payload, retained := p } } ∧
      r = .claimed (mkAttempt p g payload) := by
  unfold claimEntry at h
  split at h
  · simp at h
  · rename_i hi
    split at h
    · simp at h
    · rename_i p hp
      have ready : ∀ (h' : claimReady e p g = (some e', r)), e.inflight = none ∧ ∃ p' payload,
          e.pending = some p' ∧ p'.intent.plan[p'.nextStep]? = some payload ∧
          e' = { e with pending := none,
                        inflight := some { attempt := mkAttempt p' g payload, retained := p' } } ∧
          r = .claimed (mkAttempt p' g payload) := by
        intro h'
        unfold claimReady at h'
        split at h'
        · simp at h'
        · rename_i payload hpl
          simp only [Prod.mk.injEq, Option.some.injEq] at h'
          exact ⟨hi, p, payload, hp, hpl, h'.1.symm, h'.2.symm⟩
      split at h
      · split at h
        · simp at h
        · exact ready h
      · exact ready h

theorem supersedeEntry_appliedThrough (e : Entry K I A P R) (p : Pending K I A P R) :
    (supersedeEntry e p).appliedThrough = e.appliedThrough := rfl

/-- Shape of an exact apply. -/
theorem appliedEntry_shape (e : Entry K I A P R) (id : AttemptId I) (receipt : R)
    (authority : A) (e' : Entry K I A P R) (r : AppliedResult)
    (h : appliedEntry e id receipt authority = (some e', r)) :
    ∃ f, e.inflight = some f ∧ f.attempt.id = id ∧ knownReceipt e id receipt = false ∧
      appliedMatched e
        (f.retained.withReceipt { attempt := id, receipt := receipt, authority := authority })
        authority = (some e', r) := by
  unfold appliedEntry at h
  split at h
  · simp at h
  · rename_i hk
    split at h
    · simp at h
    · rename_i f hf
      split at h
      · rename_i hid
        exact ⟨f, hf, hid, by simpa using hk, h⟩
      · simp at h

theorem appliedMatched_cases (e : Entry K I A P R) (p : Pending K I A P R) (authority : A)
    (e' : Entry K I A P R) (r : AppliedResult) (h : appliedMatched e p authority = (some e', r)) :
    (newerPending e p.intent.epoch = true ∧ e' = supersedeEntry e p ∧ r = .superseded) ∨
      (newerPending e p.intent.epoch = false ∧ p.nextStep + 1 < p.intent.plan.length ∧
        e' = { e with inflight := none, retry := none,
                      pending := some { p with nextStep := p.nextStep + 1, expected := authority,
                                               readyAt := none, nextAttempt := 1 } } ∧
        r = .stepApplied (p.nextStep + 1)) ∨
      (newerPending e p.intent.epoch = false ∧ ¬ p.nextStep + 1 < p.intent.plan.length ∧
        e' = { e with inflight := none, retry := none,
                      appliedThrough := some (advanceFrontier e.appliedThrough p.intent.epoch),
                      terminal := some { kind := .applied, identity := p.intent.identity,
                                         epoch := p.intent.epoch, receipts := p.receipts },
                      terminalIntent := some p.intent } ∧
        r = .completed (advanceFrontier e.appliedThrough p.intent.epoch)) := by
  unfold appliedMatched at h
  split at h
  · rename_i hn
    simp only [Prod.mk.injEq, Option.some.injEq] at h
    exact Or.inl ⟨hn, h.1.symm, h.2.symm⟩
  · rename_i hn
    split at h
    · rename_i hs
      simp only [Prod.mk.injEq, Option.some.injEq] at h
      exact Or.inr (Or.inl ⟨by simpa using hn, hs, h.1.symm, h.2.symm⟩)
    · rename_i hs
      simp only [Prod.mk.injEq, Option.some.injEq] at h
      exact Or.inr (Or.inr ⟨by simpa using hn, hs, h.1.symm, h.2.symm⟩)

theorem failedEntry_shape (e : Entry K I A P R) (id : AttemptId I) (failure : Failure A)
    (e' : Entry K I A P R) (r : FailureResult) (h : failedEntry e id failure = (some e', r)) :
    ∃ f, e.inflight = some f ∧ f.attempt.id = id ∧
      failedMatched e f.retained id failure = (some e', r) := by
  unfold failedEntry at h
  split at h
  · simp at h
  · rename_i f hf
    split at h
    · rename_i hid
      exact ⟨f, hf, hid, h⟩
    · simp at h

theorem failedMatched_appliedThrough (e : Entry K I A P R) (p : Pending K I A P R)
    (id : AttemptId I) (failure : Failure A) (e' : Entry K I A P R) (r : FailureResult)
    (h : failedMatched e p id failure = (some e', r)) : e'.appliedThrough = e.appliedThrough := by
  unfold failedMatched at h
  repeat' split at h
  all_goals (simp only [Prod.mk.injEq, Option.some.injEq] at h; rw [← h.1]; try rfl)

theorem reconnectEntry_appliedThrough (e : Entry K I A P R) :
    (reconnectEntry e).1.appliedThrough = e.appliedThrough := by
  unfold reconnectEntry
  split
  · rfl
  · split <;> rfl

theorem advanceFrontier_ge (o : Option Nat) (n : Nat) : watermark o ≤ advanceFrontier o n := by
  cases o <;> simp [watermark, advanceFrontier] <;> omega

/-- Every step either leaves a key's frontier unchanged or is an exact
completion of that key's in-flight attempt, which raises the frontier. -/
theorem step_frontier (c : Core K I A P R) (op : Op K I A P R) (k : K) :
    ((step c op).1.entry k).appliedThrough = (c.entry k).appliedThrough ∨
      ∃ id receipt authority n, op = .applied k id receipt authority ∧
        isInflight (c.entry k) id = true ∧ (step c op).2 = .applied (.completed n) ∧
        ((step c op).1.entry k).appliedThrough = some n ∧
        watermark (c.entry k).appliedThrough ≤ n := by
  cases op with
  | upsert i =>
      left
      by_cases hk : k = i.key
      · rw [hk]
        cases hU : upsertEntry (c.entry i.key) i with
        | mk o r =>
            cases o with
            | none => simp [step, hU, commit]
            | some e' =>
                obtain ⟨rfl, -⟩ := upsertEntry_shape _ _ _ _ hU
                simp only [step, hU, entry_commit_same, replaceEntry_appliedThrough]
      · simp only [step]; rw [entry_commit_other _ _ _ _ hk]
  | claim k0 g now =>
      left
      simp only [step]
      split
      · split
        · rfl
        · rename_i e he
          by_cases hk : k = k0
          · rw [hk]
            cases hC : claimEntry e g now with
            | mk o r =>
                cases o with
                | none => simp [commit]
                | some e' =>
                    obtain ⟨-, p, payload, -, -, rfl, -⟩ := claimEntry_shape _ _ _ _ _ hC
                    simp only [entry_commit_same, entry_of_lookup he]
          · rw [entry_commit_other _ _ _ _ hk]
      · rfl
  | applied k0 id receipt authority =>
      simp only [step]
      split
      · split
        · left; rfl
        · rename_i e he
          by_cases hk : k = k0
          · rw [hk]
            cases hA : appliedEntry e id receipt authority with
            | mk o r =>
                cases o with
                | none => left; simp [commit]
                | some e' =>
                    obtain ⟨f, hf, hid, -, hM⟩ := appliedEntry_shape _ _ _ _ _ _ hA
                    rcases appliedMatched_cases _ _ _ _ _ hM with
                      ⟨-, rfl, -⟩ | ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, rfl⟩
                    · left
                      simp only [entry_commit_same, entry_of_lookup he, supersedeEntry_appliedThrough]
                    · left; simp only [entry_commit_same, entry_of_lookup he]
                    · right
                      refine ⟨id, receipt, authority, _, rfl, ?_, rfl, ?_, ?_⟩
                      · simp [entry_of_lookup he, isInflight, hf, hid]
                      · simp only [entry_commit_same]
                      · rw [entry_of_lookup he]; exact advanceFrontier_ge _ _
          · left; rw [entry_commit_other _ _ _ _ hk]
      · left; rfl
  | failed k0 id failure =>
      left
      simp only [step]
      split
      · split
        · rfl
        · rename_i e he
          by_cases hk : k = k0
          · rw [hk]
            cases hF : failedEntry e id failure with
            | mk o r =>
                cases o with
                | none => simp [commit]
                | some e' =>
                    obtain ⟨f, -, -, hM⟩ := failedEntry_shape _ _ _ _ _ hF
                    simp only [entry_commit_same, entry_of_lookup he]
                    exact failedMatched_appliedThrough _ _ _ _ _ _ hM
          · rw [entry_commit_other _ _ _ _ hk]
      · rfl
  | reconnect g =>
      left
      simp only [step]
      split
      · rfl
      · split
        · rfl
        · simp only [Core.entry, lookup_reconnect]
          cases lookup c.entries k <;> simp [reconnectEntry_appliedThrough]

/-- The frontier of every key is monotone under every operation (inv. 3). -/
theorem step_appliedThrough_monotone (c : Core K I A P R) (op : Op K I A P R) (k : K) :
    watermark (c.entry k).appliedThrough ≤ watermark ((step c op).1.entry k).appliedThrough := by
  rcases step_frontier c op k with h | ⟨_, _, _, n, _, _, _, h, hle⟩
  · rw [h]; exact Nat.le_refl _
  · rw [h]; exact hle

/-- The frontier advances only from an exact terminal apply (inv. 3, 4): if a
step changes a key's `applied_through`, the step was `record_applied` for that
key, its attempt was exactly the key's in-flight attempt, and the outcome was
`completed`. So a superseded, retryable, or rejected attempt — and an applied
receipt that a newer intent superseded — never advances the frontier. -/
theorem appliedThrough_advances_only_by_exact_completion (c : Core K I A P R)
    (op : Op K I A P R) (k : K)
    (hchg : ((step c op).1.entry k).appliedThrough ≠ (c.entry k).appliedThrough) :
    ∃ id receipt authority n, op = .applied k id receipt authority ∧
      isInflight (c.entry k) id = true ∧ (step c op).2 = .applied (.completed n) := by
  rcases step_frontier c op k with h | ⟨id, receipt, authority, n, hop, hin, hout, _, _⟩
  · exact absurd h hchg
  · exact ⟨id, receipt, authority, n, hop, hin, hout⟩

/-- Keyed operations leave every other key's entry untouched (independent keys
progress independently). -/
theorem step_other_key_unchanged (c : Core K I A P R) (op : Op K I A P R) (k : K)
    (hother : match op with
      | .upsert intent => k ≠ intent.key
      | .claim k₀ _ _ => k ≠ k₀
      | .applied k₀ _ _ _ => k ≠ k₀
      | .failed k₀ _ _ => k ≠ k₀
      | .reconnect _ => False) :
    lookup (step c op).1.entries k = lookup c.entries k := by
  cases op with
  | upsert intent => exact lookup_commit_other _ _ _ _ hother
  | claim k₀ g now =>
      simp only [step]; split
      · split
        · rfl
        · exact lookup_commit_other _ _ _ _ hother
      · rfl
  | applied k₀ id receipt authority =>
      simp only [step]; split
      · split
        · rfl
        · exact lookup_commit_other _ _ _ _ hother
      · rfl
  | failed k₀ id failure =>
      simp only [step]; split
      · split
        · rfl
        · exact lookup_commit_other _ _ _ _ hother
      · rfl
  | reconnect g => exact absurd hother id

/-! #### Terminal receipts -/

/-- An exact terminal receipt is retained: completing the final plan step
records exactly this attempt's receipt at the end of the terminal lineage. -/
theorem completed_retains_receipt (e : Entry K I A P R) (id : AttemptId I) (receipt : R)
    (authority : A) (e' : Entry K I A P R) (n : Nat)
    (h : appliedEntry e id receipt authority = (some e', .completed n)) :
    ∃ f, e.inflight = some f ∧ f.attempt.id = id ∧
      e'.terminal = some { kind := .applied, identity := f.retained.intent.identity,
                           epoch := f.retained.intent.epoch,
                           receipts := f.retained.receipts ++
                             [{ attempt := id, receipt := receipt, authority := authority }] } := by
  obtain ⟨f, hf, hid, -, hM⟩ := appliedEntry_shape _ _ _ _ _ _ h
  rcases appliedMatched_cases _ _ _ _ _ hM with ⟨-, -, hr⟩ | ⟨-, -, -, hr⟩ | ⟨-, -, rfl, -⟩
  · cases hr
  · cases hr
  · exact ⟨f, hf, hid, rfl⟩

/-- A duplicate of a terminal receipt is idempotent: reported `duplicate`, no
state change — a redelivered receipt is never recorded twice. -/
theorem duplicate_receipt_idempotent (c : Core K I A P R) (k : K) (id : AttemptId I)
    (receipt : R) (authority : A) (e : Entry K I A P R) (he : lookup c.entries k = some e)
    (hg : id.generation = c.generation) (hdup : knownReceipt e id receipt = true) :
    step c (.applied k id receipt authority) = (c, .applied .duplicate) := by
  simp [step, hg, he, appliedEntry, hdup, commit]

theorem appliedMatched_some (e : Entry K I A P R) (p : Pending K I A P R) (authority : A) :
    (appliedMatched e p authority).1.isSome = true := by
  unfold appliedMatched; split
  · rfl
  · split <;> rfl

/-- Completing an effect and then redelivering the same receipt: the second
delivery is a `duplicate` no-op. -/
theorem completed_then_duplicate (c : Core K I A P R) (k : K) (id : AttemptId I) (receipt : R)
    (authority : A) (n : Nat) (hg : id.generation = c.generation)
    (hc : (step c (.applied k id receipt authority)).2 = .applied (.completed n)) :
    step (step c (.applied k id receipt authority)).1 (.applied k id receipt authority) =
      ((step c (.applied k id receipt authority)).1, .applied .duplicate) := by
  cases hl : lookup c.entries k with
  | none => simp [step, hg, hl] at hc
  | some e =>
      cases hA : appliedEntry e id receipt authority with
      | mk o r =>
          have hr : r = .completed n := by simpa [step, hg, hl, hA] using hc
          subst hr
          cases o with
          | none =>
              exfalso
              have hsome : (appliedEntry e id receipt authority).1.isSome = true := by
                obtain ⟨f, hf, hid, -⟩ : ∃ f, e.inflight = some f ∧ f.attempt.id = id ∧ True := by
                  unfold appliedEntry at hA
                  split at hA
                  · simp at hA
                  · split at hA
                    · simp at hA
                    · rename_i f hf
                      split at hA
                      · rename_i hid; exact ⟨f, hf, hid, trivial⟩
                      · simp at hA
                unfold appliedEntry
                have hk : knownReceipt e id receipt = false := by
                  unfold appliedEntry at hA; split at hA
                  · simp at hA
                  · simpa using ‹¬knownReceipt e id receipt = true›
                simp only [hk, Bool.false_eq_true, if_false, hf, hid, if_true]
                exact appliedMatched_some _ _ _
              rw [hA] at hsome; simp at hsome
          | some e' =>
              obtain ⟨f, _, _, ht⟩ := completed_retains_receipt e id receipt authority e' n hA
              have hstep : (step c (.applied k id receipt authority)).1 = commit c k (some e') := by
                simp [step, hg, hl, hA]
              rw [hstep]
              refine duplicate_receipt_idempotent _ k id receipt authority e'
                (lookup_commit_same _ _ _) (by rw [commit_generation]; exact hg) ?_
              simp [knownReceipt, ht]

/-! #### Retry, reconnect, rejection, supersession (invariants 4–6) -/

/-- A retryable failure restores the same effect identity, plan cursor, expected
authority, and completed-step receipts, with the next attempt number and the
caller's logical retry time (inv. 5). -/
theorem retryable_preserves_identity_cursor (e : Entry K I A P R) (id : AttemptId I)
    (t : Nat) (e' : Entry K I A P R) (r : Nat)
    (h : failedEntry e id (.retryable t) = (some e', .retrying r)) :
    ∃ f, e.inflight = some f ∧ f.attempt.id = id ∧ r = t ∧ e'.inflight = none ∧
      e'.pending = some { f.retained with nextAttempt := f.retained.nextAttempt + 1,
                                          readyAt := some t } := by
  obtain ⟨f, hf, hid, hM⟩ := failedEntry_shape _ _ _ _ _ h
  simp only [failedMatched] at hM
  split at hM
  · simp at hM
  · simp only [Prod.mk.injEq, Option.some.injEq, FailureResult.retrying.injEq] at hM
    obtain ⟨rfl, rfl⟩ := hM
    exact ⟨f, hf, hid, rfl, rfl, rfl⟩

/-- A compare mismatch (`Superseded`) terminally supersedes the attempt with
zero frontier movement; the adapter mutated nothing (inv. 4). -/
theorem superseded_never_advances (e : Entry K I A P R) (id : AttemptId I) (observed : A)
    (e' : Entry K I A P R) (r : FailureResult)
    (h : failedEntry e id (.superseded observed) = (some e', r)) :
    r = .superseded ∧ e'.appliedThrough = e.appliedThrough ∧
      (e'.terminal.map (·.kind)) = some .superseded ∧ e'.inflight = none := by
  obtain ⟨f, -, -, hM⟩ := failedEntry_shape _ _ _ _ _ h
  simp only [failedMatched, Prod.mk.injEq, Option.some.injEq] at hM
  obtain ⟨rfl, rfl⟩ := hM
  simp [supersedeEntry, supersededTerminal]

/-- Rejection is terminal and observably distinct from retry (inv. 6): the
terminal records `rejected`, no retry is scheduled, nothing is in flight, and
the rejected intent is not requeued (pending is whatever newer intent already
existed). -/
theorem rejected_is_terminal (e : Entry K I A P R) (id : AttemptId I) (e' : Entry K I A P R)
    (r : FailureResult) (h : failedEntry e id .rejected = (some e', r)) :
    r = .rejected ∧ (e'.terminal.map (·.kind)) = some .rejected ∧ e'.retry = none ∧
      e'.inflight = none ∧ e'.pending = e.pending := by
  obtain ⟨f, -, -, hM⟩ := failedEntry_shape _ _ _ _ _ h
  simp only [failedMatched, Prod.mk.injEq, Option.some.injEq] at hM
  obtain ⟨rfl, rfl⟩ := hM
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Reconnect requeues an in-flight cursor with the same identity, cursor,
expected authority, and receipts unless a newer intent supersedes it (inv. 5);
a superseded cursor is terminally recorded with its receipt lineage. -/
theorem reconnect_requeues_same_identity (e : Entry K I A P R) (f : Inflight K I A P R)
    (hf : e.inflight = some f) :
    (reconnectEntry e).1.inflight = none ∧
      ((newerPending e f.retained.intent.epoch = false ∧
          (reconnectEntry e).1.pending = some { f.retained with
            nextAttempt := f.retained.nextAttempt + 1, readyAt := none }) ∨
        (newerPending e f.retained.intent.epoch = true ∧
          (reconnectEntry e).1.pending = e.pending ∧
          (reconnectEntry e).1.terminal = some (supersededTerminal f.retained))) := by
  unfold reconnectEntry
  rw [hf]
  cases hn : newerPending e f.retained.intent.epoch <;> simp [hn]

/-- A legitimate reconnect advances the actor generation and empties every
in-flight slot, so every receipt from the old generation is fenced. -/
theorem reconnect_fences_old_generation (c : Core K I A P R) (g : Nat) (hg : c.generation < g) :
    (step c (.reconnect g)).1.generation = g ∧
      ∀ k e, lookup (step c (.reconnect g)).1.entries k = some e → e.inflight = none := by
  have h1 : ¬ g < c.generation := by omega
  have h2 : g ≠ c.generation := by omega
  simp only [step, h1, h2, if_false]
  refine ⟨trivial, ?_⟩
  intro k e he
  rw [lookup_reconnect] at he
  cases hl : lookup c.entries k with
  | none => simp [hl] at he
  | some e₀ =>
      simp only [hl, Option.map_some, Option.some.injEq] at he
      subst he
      unfold reconnectEntry
      split
      · assumption
      · split <;> rfl

/-- Latest-wins supersession: accepting a newer intent over pending work
terminally supersedes that work while retaining its completed-step receipts. -/
theorem upsert_supersedes_pending (e : Entry K I A P R) (intent : Intent K I A P)
    (p : Pending K I A P R) (hp : e.pending = some p) (e' : Entry K I A P R) (r : UpsertResult)
    (h : upsertEntry e intent = (some e', r)) :
    r = .accepted ∧ e'.pending = some (freshPending intent) ∧
      e'.terminal = some (supersededTerminal p) ∧ e'.retry = none := by
  obtain ⟨rfl, rfl⟩ := upsertEntry_shape _ _ _ _ h
  simp [replaceEntry, supersedePending, hp]

/-! #### Receipt lineage: no lost or duplicated terminal receipt

Every retained intent carries exactly one receipt per completed plan step, in
step order, and its cursor stays inside its plan; every terminal records such a
lineage. Hence a completed effect's terminal holds exactly one receipt for each
step of its plan (`completed_terminal_lineage`). -/

/-- Exactly one receipt per step `0 … n-1`, in order. -/
def Lineage (rs : List (Receipt I A R)) (n : Nat) : Prop :=
  rs.map (·.attempt.step) = List.range n

structure PendingWF (p : Pending K I A P R) : Prop where
  lineage : Lineage p.receipts p.nextStep
  cursor : p.nextStep < p.intent.plan.length

structure EntryWF (e : Entry K I A P R) : Prop where
  pending : ∀ p, e.pending = some p → PendingWF p
  inflight : ∀ f, e.inflight = some f →
    PendingWF f.retained ∧ f.attempt.id.step = f.retained.nextStep
  terminal : ∀ t, e.terminal = some t → ∃ n, Lineage t.receipts n

/-- Every key's entry is well formed. -/
def CoreWF (c : Core K I A P R) : Prop :=
  ∀ k e, lookup c.entries k = some e → EntryWF e

/-- Plans are non-empty (the spec's `EffectPlan` refuses an empty plan). -/
def Op.plansNonEmpty : Op K I A P R → Prop
  | .upsert intent => intent.plan ≠ []
  | _ => True

theorem coreWF_empty (g : Nat) : CoreWF ({ generation := g, entries := [] } : Core K I A P R) := by
  intro k e h; simp [lookup] at h

private theorem lineage_withReceipt (p : Pending K I A P R) (rec : Receipt I A R)
    (h : Lineage p.receipts p.nextStep) (hs : rec.attempt.step = p.nextStep) :
    Lineage (p.withReceipt rec).receipts (p.nextStep + 1) := by
  simp only [Lineage, Pending.withReceipt, List.map_append, List.map_cons, List.map_nil] at h ⊢
  rw [h, hs, List.range_succ]

private theorem replaceEntry_wf (e : Entry K I A P R) (intent : Intent K I A P)
    (h : EntryWF e) (hp : intent.plan ≠ []) : EntryWF (replaceEntry e intent) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp'
    simp only [replaceEntry, Option.some.injEq] at hp'
    subst hp'
    refine ⟨by simp [Lineage, freshPending], ?_⟩
    simp only [freshPending]
    exact List.length_pos_iff.mpr hp
  · intro f hf
    have : (replaceEntry e intent).inflight = e.inflight := by
      unfold replaceEntry supersedePending; split <;> rfl
    exact h.inflight f (this ▸ hf)
  · intro t ht
    unfold replaceEntry supersedePending at ht
    split at ht
    · exact h.terminal t ht
    · rename_i p hpe
      simp only [Option.some.injEq] at ht
      subst ht
      exact ⟨p.nextStep, (h.pending p hpe).lineage⟩

private theorem claimEntry_wf (e : Entry K I A P R) (g now : Nat) (e' : Entry K I A P R)
    (r : ClaimResult K I A P R) (h : EntryWF e) (hc : claimEntry e g now = (some e', r)) :
    EntryWF e' := by
  obtain ⟨-, p, payload, hp, -, rfl, -⟩ := claimEntry_shape _ _ _ _ _ hc
  refine ⟨fun p' hp' => by simp at hp', fun f hf => ?_, fun t ht => h.terminal t ht⟩
  simp only [Option.some.injEq] at hf
  subst hf
  exact ⟨h.pending p hp, rfl⟩

private theorem appliedEntry_wf (e : Entry K I A P R) (id : AttemptId I) (receipt : R)
    (authority : A) (e' : Entry K I A P R) (r : AppliedResult) (h : EntryWF e)
    (ha : appliedEntry e id receipt authority = (some e', r)) : EntryWF e' := by
  obtain ⟨f, hf, hid, -, hM⟩ := appliedEntry_shape _ _ _ _ _ _ ha
  obtain ⟨hwf, hstep⟩ := h.inflight f hf
  have hlin := lineage_withReceipt f.retained
    { attempt := id, receipt := receipt, authority := authority } hwf.lineage
    (by rw [← hid]; exact hstep)
  rcases appliedMatched_cases _ _ _ _ _ hM with ⟨-, rfl, -⟩ | ⟨-, hs, rfl, -⟩ | ⟨-, -, rfl, -⟩
  · refine ⟨h.pending, fun f' hf' => by simp [supersedeEntry] at hf', fun t ht => ?_⟩
    simp only [supersedeEntry, Option.some.injEq] at ht
    subst ht
    exact ⟨_, hlin⟩
  · refine ⟨fun p hp => ?_, fun f' hf' => by simp at hf', fun t ht => h.terminal t ht⟩
    simp only [Option.some.injEq] at hp
    subst hp
    exact ⟨hlin, hs⟩
  · refine ⟨h.pending, fun f' hf' => by simp at hf', fun t ht => ?_⟩
    simp only [Option.some.injEq] at ht
    subst ht
    exact ⟨_, hlin⟩

private theorem failedEntry_wf (e : Entry K I A P R) (id : AttemptId I) (failure : Failure A)
    (e' : Entry K I A P R) (r : FailureResult) (h : EntryWF e)
    (hfl : failedEntry e id failure = (some e', r)) : EntryWF e' := by
  obtain ⟨f, hf, -, hM⟩ := failedEntry_shape _ _ _ _ _ hfl
  obtain ⟨hwf, -⟩ := h.inflight f hf
  have sup : EntryWF (supersedeEntry e f.retained) :=
    ⟨h.pending, fun f' hf' => by simp [supersedeEntry] at hf', fun t ht => by
      simp only [supersedeEntry, Option.some.injEq] at ht
      subst ht
      exact ⟨_, hwf.lineage⟩⟩
  unfold failedMatched at hM
  split at hM
  · simp only [Prod.mk.injEq, Option.some.injEq] at hM; rw [← hM.1]; exact sup
  · split at hM
    · simp only [Prod.mk.injEq, Option.some.injEq] at hM; rw [← hM.1]; exact sup
    · simp only [Prod.mk.injEq, Option.some.injEq] at hM
      rw [← hM.1]
      refine ⟨fun p hp => ?_, fun f' hf' => by simp at hf', fun t ht => h.terminal t ht⟩
      simp only [Option.some.injEq] at hp
      subst hp
      exact ⟨hwf.lineage, hwf.cursor⟩
  · simp only [Prod.mk.injEq, Option.some.injEq] at hM
    rw [← hM.1]
    refine ⟨h.pending, fun f' hf' => by simp at hf', fun t ht => ?_⟩
    simp only [Option.some.injEq] at ht
    subst ht
    exact ⟨_, hwf.lineage⟩

private theorem reconnectEntry_wf (e : Entry K I A P R) (h : EntryWF e) :
    EntryWF (reconnectEntry e).1 := by
  unfold reconnectEntry
  split
  · exact h
  · rename_i f hf
    obtain ⟨hwf, -⟩ := h.inflight f hf
    split
    · refine ⟨h.pending, fun f' hf' => by simp at hf', fun t ht => ?_⟩
      simp only [Option.some.injEq] at ht
      subst ht
      exact ⟨_, hwf.lineage⟩
    · refine ⟨fun p hp => ?_, fun f' hf' => by simp at hf', fun t ht => h.terminal t ht⟩
      simp only [Option.some.injEq] at hp
      subst hp
      exact ⟨hwf.lineage, hwf.cursor⟩

private theorem coreWF_commit (c : Core K I A P R) (k : K) (e' : Entry K I A P R)
    (h : CoreWF c) (he' : EntryWF e') : CoreWF (commit c k (some e')) := by
  intro k' e hl
  by_cases hk : k' = k
  · subst hk
    rw [lookup_commit_same] at hl
    simp only [Option.some.injEq] at hl
    exact hl ▸ he'
  · rw [lookup_commit_other _ _ _ _ hk] at hl
    exact h k' e hl

private theorem entryWF_of (c : Core K I A P R) (k : K) (h : CoreWF c) : EntryWF (c.entry k) := by
  cases hl : lookup c.entries k with
  | none =>
      simp only [Core.entry, hl, Option.getD_none]
      exact ⟨fun p hp => by simp [Entry.empty] at hp, fun f hf => by simp [Entry.empty] at hf,
        fun t ht => by simp [Entry.empty] at ht⟩
  | some e => rw [entry_of_lookup hl]; exact h k e hl

/-- Receipt lineage is preserved by every operation over non-empty plans. -/
theorem step_preserves_wf (c : Core K I A P R) (op : Op K I A P R) (h : CoreWF c)
    (hp : op.plansNonEmpty) : CoreWF (step c op).1 := by
  cases op with
  | upsert intent =>
      simp only [step]
      cases hU : upsertEntry (c.entry intent.key) intent with
      | mk o r =>
          cases o with
          | none => exact h
          | some e' =>
              obtain ⟨rfl, -⟩ := upsertEntry_shape _ _ _ _ hU
              exact coreWF_commit _ _ _ h (replaceEntry_wf _ _ (entryWF_of c _ h) hp)
  | claim k g now =>
      simp only [step]
      split
      · split
        · exact h
        · rename_i e he
          cases hC : claimEntry e g now with
          | mk o r =>
              cases o with
              | none => exact h
              | some e' => exact coreWF_commit _ _ _ h (claimEntry_wf _ _ _ _ _ (h k e he) hC)
      · exact h
  | applied k id receipt authority =>
      simp only [step]
      split
      · split
        · exact h
        · rename_i e he
          cases hA : appliedEntry e id receipt authority with
          | mk o r =>
              cases o with
              | none => exact h
              | some e' => exact coreWF_commit _ _ _ h (appliedEntry_wf _ _ _ _ _ _ (h k e he) hA)
      · exact h
  | failed k id failure =>
      simp only [step]
      split
      · split
        · exact h
        · rename_i e he
          cases hF : failedEntry e id failure with
          | mk o r =>
              cases o with
              | none => exact h
              | some e' => exact coreWF_commit _ _ _ h (failedEntry_wf _ _ _ _ _ (h k e he) hF)
      · exact h
  | reconnect g =>
      simp only [step]
      split
      · exact h
      · split
        · exact h
        · intro k e hl
          simp only [lookup_reconnect] at hl
          cases hl' : lookup c.entries k with
          | none => simp [hl'] at hl
          | some e₀ =>
              simp only [hl', Option.map_some, Option.some.injEq] at hl
              subst hl
              exact reconnectEntry_wf _ (h k e₀ hl')

/-- A completed effect's terminal holds exactly one receipt for each step of
its plan, in step order — none lost, none duplicated. -/
theorem completed_terminal_lineage (e : Entry K I A P R) (id : AttemptId I) (receipt : R)
    (authority : A) (e' : Entry K I A P R) (n : Nat) (h : EntryWF e)
    (ha : appliedEntry e id receipt authority = (some e', .completed n)) :
    ∃ f t, e.inflight = some f ∧ e'.terminal = some t ∧ t.kind = .applied ∧
      Lineage t.receipts f.retained.intent.plan.length := by
  obtain ⟨f, hf, hid, -, hM⟩ := appliedEntry_shape _ _ _ _ _ _ ha
  obtain ⟨hwf, hstep⟩ := h.inflight f hf
  have hlin := lineage_withReceipt f.retained
    { attempt := id, receipt := receipt, authority := authority } hwf.lineage
    (by rw [← hid]; exact hstep)
  rcases appliedMatched_cases _ _ _ _ _ hM with ⟨-, -, hr⟩ | ⟨-, -, -, hr⟩ | ⟨-, hs, rfl, -⟩
  · cases hr
  · cases hr
  · refine ⟨f, _, hf, rfl, rfl, ?_⟩
    have hlen : f.retained.nextStep + 1 = f.retained.intent.plan.length := by
      have := hwf.cursor
      simp only [Pending.withReceipt] at hs
      omega
    rw [← hlen]
    exact hlin

end Theorems

end LazilyFormal.EffectCas
