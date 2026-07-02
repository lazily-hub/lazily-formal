/-
! Formal safety proof for the agent-doc local-process state chart (`#adstatechart`).

This instantiates the general Harel `StateChart` model at the concrete
`agent-doc-state-backbone::adstatechart` closeout region and proves the
**load-bearing rung-1 invariant**: a `commit` while the editor buffer is ahead
of disk (`editor_synced` resolves `false`) is a **rejected `send` edge**, so the
`committed` state is never entered — the invariant is the guard doing real work,
not an ad-hoc check re-verified at N call sites.

Scope (matching the PRD, `tasks/agent-doc/prd-adstatechart-local-process-statechart.md`):
this is **per-process safety** over the finite closeout config space. It proves
the chart cannot *take* the illegal edge; it does NOT (and cannot) prove
production wedge-freedom, because a live wedge is "the unblocking event never
fires" — a distributed-liveness property outside a per-process chart (root cause
B). The `commit`-edge guard here is exactly what the Rust `#adstatechart1` unit
test `commit_while_editor_ahead_is_rejected_edge` checks by example; this proves
it holds on every path through the modeled region, not just the sampled ones.
-/

import LazilyFormal.Primitive
import LazilyFormal.StateChart

namespace LazilyFormal.AdStateChart

open LazilyFormal.Primitive
open LazilyFormal.StateChart

-- State ids of the closeout region.
def closeout : StateId := 0
def written : StateId := 1
def committed : StateId := 2

-- The named guard and event that gate the load-bearing edge.
def editorSynced : GuardId := 0
def commitEv : EventId := 0

/-- The only transition on `commit`: `written --commit[editor_synced]--> committed`. -/
def commitTrans : Transition :=
  { target := committed, guard := some editorSynced, action := [], internal := false }

/-- The closeout region of the adstatechart as a concrete Harel chart: a compound
`closeout` with initial `written`, whose sole event is the guarded `commit` edge
into the `final` state `committed`. -/
def adChart : Chart :=
  { states := [closeout, written, committed]
    parent := fun s =>
      if s = written then some closeout
      else if s = committed then some closeout
      else none
    kind := fun s =>
      if s = closeout then Kind.compound
      else if s = committed then Kind.final
      else Kind.atomic
    initial := fun s => if s = closeout then some written else none
    default := fun _ => none
    on := fun s ev =>
      if s = written then (if ev = commitEv then some commitTrans else none) else none
    entry := fun _ => []
    exit := fun _ => [] }

/-- Active configuration with `written` active (leaf plus its ancestor). -/
def writtenCfg : Configuration := [closeout, written]

/-- The empty history (no region has been exited). -/
def noHistory : History := fun _ => none

/-- Guard resolver for "editor buffer is ahead of disk": `editor_synced = false`. -/
def gAhead : GuardResolver := fun _ => false

/-- Guard resolver for "editor synced": `editor_synced = true`. -/
def gSynced : GuardResolver := fun n => n == editorSynced

/-- **Rejected-edge safety (one macrostep, all paths).** When the editor buffer
is ahead of disk (`editor_synced` resolves `false`), the `commit` event is
rejected: `send` leaves the configuration unchanged. Proved by evaluation over
the concrete finite chart, so it holds for *every* `commit` from `written`, not
just sampled cases. -/
theorem commit_rejected_when_editor_ahead :
    (send adChart writtenCfg noHistory gAhead commitEv).cfg = writtenCfg := by
  decide

/-- Corollary: the `committed` state is never entered while the editor is ahead. -/
theorem committed_not_entered_when_editor_ahead :
    committed ∉ (send adChart writtenCfg noHistory gAhead commitEv).cfg := by
  decide

/-- **The guard is the gate (liveness of the legal edge).** When the editor is
synced, the *same* `commit` event IS taken and `committed` is entered — so the
safety theorem above is the guard doing real work, not `commit` being
structurally unreachable. -/
theorem commit_taken_when_editor_synced :
    committed ∈ (send adChart writtenCfg noHistory gSynced commitEv).cfg := by
  decide

end LazilyFormal.AdStateChart
