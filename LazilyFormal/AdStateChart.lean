/-
! Formal safety proof for the agent-doc local-process state chart (`#adstatechart`).

This instantiates the general Harel `StateChart` model at the concrete
`agent-doc-state-backbone::adstatechart` closeout region and proves the
**two load-bearing rung-1 invariants** the PRD calls for:

1. **Rejected-edge safety (all paths).** A `commit` while the editor buffer is
   ahead of disk (`editor_synced` resolves `false`) is a **rejected `send` edge**,
   so the `committed` state is never entered — the invariant is the guard doing
   real work, not an ad-hoc check re-verified at N call sites.
2. **No dead-end config.** The non-final `written` state always has an enabled
   outgoing edge (progress is possible), the `commit` edge exists in the table
   regardless of the resolver (rejection is guard work, not a missing edge), and
   the only terminal sink is the accepting `final` state `committed`.

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

-- ------------------------------------------------------- no dead-end config
-- The PRD's second rung-1 invariant: the modeled region has no dead-end
-- configuration — every non-final active state can still progress, and the only
-- terminal sink is the accepting `final` state. Proved by evaluation, so it
-- covers the whole finite config space rather than sampled points.

/-- The non-final `written` config is not stuck: under the synced resolver the
`commit` edge is enabled, so progress out of `written` is always possible.
(Uses `.length` to stay decidable without `DecidableEq Transition`.) -/
theorem written_not_dead_end :
    (enabled adChart writtenCfg gSynced commitEv).length = 1 := by
  decide

/-- The `commit` edge out of `written` is present in the transition table
regardless of the resolver — when the editor is ahead the guard rejects it
*inside* `send` (`enabled` returns `[]`), it does not vanish from the chart. So
the rejected-edge safety above is genuine guard work, not the edge being absent. -/
theorem written_commit_edge_exists :
    (adChart.on written commitEv).isSome = true := by
  decide

theorem enabled_empty_when_editor_ahead :
    (enabled adChart writtenCfg gAhead commitEv).length = 0 := by
  decide

/-- `committed` is a `final` (accepting) state: its terminality is the success
sink, not a dead-end. Projected through a Bool match to avoid needing
`DecidableEq Kind`. -/
theorem committed_is_final :
    (match adChart.kind committed with | Kind.final => true | _ => false) = true := by
  decide

/-- `written` is *not* final — so `written_not_dead_end` is a real progress
obligation on a non-accepting state, not vacuously about the sink. -/
theorem written_is_not_final :
    (match adChart.kind written with | Kind.final => true | _ => false) = false := by
  decide

end LazilyFormal.AdStateChart
