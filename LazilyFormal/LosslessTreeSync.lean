/-
! Lossless tree CRDT — op-based delta sync over a dotted, non-contiguous frontier.

The formal counterpart of `lazily-rs` `lossless_tree_crdt`'s `diff` /
`apply_update` / `TreeVersionFrontier`, behind
`lazily-spec/conformance/lossless-tree/non_contiguous_anti_entropy.json`.

Tree anti-entropy is **op-based**: a replica holds a set of dotted op ids, and the
delta it owes a partner is the ops it holds that the partner lacks. The frontier
that summarizes "which ops do I hold" must be a **dot set** (a contiguous prefix
plus out-of-order holes), not a per-peer *max* counter. This file proves:

- **`delta_complete`** — delivering the delta gives the partner exactly the union
  of both op sets, so bidirectional exchange converges;
- **`frontier_no_skip`** — every op the sender holds and the receiver lacks is in
  the delta (the dotted set difference omits nothing);
- **`perPeerMax_skips`** — a per-peer-max frontier provably skips a
  non-contiguous hole: after a higher dot is delivered it believes the missing
  lower dot is already held, so its delta omits an op the receiver genuinely
  lacks. This is the version-vector shortcut the design forbids.

The op set is modelled as `OpId → Bool` (its characteristic function), so the whole
argument stays in decidable `Bool` algebra with no external library.
-/

namespace LazilyFormal.LosslessTreeSync

/-- A dotted operation id: `(peer, counter)`. -/
abbrev OpId := Nat × Nat

/-- The set of op ids a replica holds, as a characteristic function — the exact,
non-contiguous frontier (each dot independently present or not). -/
abbrev Dots := OpId → Bool

/-- Membership. -/
def has (d : Dots) (o : OpId) : Bool := d o

/-- The delta `mine` owes a partner holding `theirs`: the ops `mine` holds that
`theirs` lacks (dotted set difference). Models `LosslessTreeCrdt::diff`. -/
def delta (mine theirs : Dots) : Dots := fun o => mine o && !theirs o

/-- Union of two op sets (the partner's state after applying a delta). -/
def union (a b : Dots) : Dots := fun o => a o || b o

/-- **Delta completeness.** After the partner (`theirs`) applies the delta `mine`
owes it, it holds exactly `theirs ∪ mine` — nothing `mine` held is lost, so a
bidirectional exchange converges both replicas to the same union. -/
theorem delta_complete (mine theirs : Dots) :
    union theirs (delta mine theirs) = union theirs mine := by
  funext o
  simp only [union, delta]
  cases theirs o <;> cases mine o <;> rfl

/-- **Bidirectional convergence.** Each replica applies the delta the other owes it;
both then hold the same union `theirs ∪ mine`. -/
theorem sync_converges (mine theirs : Dots) :
    union theirs (delta mine theirs) = union mine (delta theirs mine) := by
  rw [delta_complete, delta_complete]
  funext o
  simp only [union]
  cases mine o <;> cases theirs o <;> rfl

/-- **The frontier cannot skip a missing non-contiguous op.** For any op the sender
holds (`mine o`) that the receiver lacks (`¬ theirs o`), the delta contains it. The
dotted set difference omits nothing the receiver is genuinely missing. -/
theorem frontier_no_skip (mine theirs : Dots) (o : OpId)
    (hHave : mine o = true) (hLack : theirs o = false) :
    delta mine theirs o = true := by
  simp [delta, hHave, hLack]

/-! ### A per-peer-max frontier provably skips holes -/

/-- A per-peer-max frontier: for each peer, the greatest counter believed held. -/
abbrev PeerMax := Nat → Nat

/-- The op set a per-peer-max frontier *believes* it holds: every dot at or below
the peer's max — including holes below a delivered higher dot. -/
def believed (m : PeerMax) : Dots := fun o => decide (o.2 ≤ m o.1)

/-- **A per-peer-max frontier skips a non-contiguous hole.** Concretely: the
receiver has delivered dots `(0,1)` and `(0,3)` but not `(0,2)` (a hole). Its
per-peer-max is `3`, so the max frontier believes it holds `(0,2)`. The sender
holds `(0,2)`; the correct dotted delta re-sends it, but the max-based delta omits
it — the receiver never converges. This is why the dotted frontier is mandatory. -/
theorem perPeerMax_skips :
    ∃ (mine recv : Dots) (m : PeerMax) (o : OpId),
      mine o = true ∧
      recv o = false ∧
      delta mine recv o = true ∧            -- dotted frontier re-sends the hole
      delta mine (believed m) o = false := by  -- per-peer-max frontier skips it
  refine ⟨fun _ => true,
          fun p => decide (p = (0, 1) ∨ p = (0, 3)),
          fun _ => 3,
          (0, 2),
          ?_, ?_, ?_, ?_⟩
  · rfl
  · decide
  · decide
  · decide

end LazilyFormal.LosslessTreeSync
