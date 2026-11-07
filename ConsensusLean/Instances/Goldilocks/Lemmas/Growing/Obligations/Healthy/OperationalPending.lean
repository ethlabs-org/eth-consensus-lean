module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetSource
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Seed

public section

/-! # Pending growing Healing interface of operational persistence

The growing forms of the Healing lemmas that `operational_proposal_below_later_parent` consumes,
under their agreed names (static name + `_at`). Each node is honest at its own cut, a reader of a
held state at an observation time after the state's cuts, and the slot-`u` proposer through
`t_u + hold`:

* `ResetPremisesUpTo.operational_unanimous_at`;
* `report_cover_of_unanimous_at` (`Obligations.UpTo.report_cover_of_unanimous`).

It re-exports the proved `ResetPremisesUpTo.cutZ_lt_reset_at` (`Kernel/ResetSource`) and
`ResetPremisesUpTo.reset_seed_before_slot_at` (`Kernel/Seed`). Each theorem here is an open
`sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)
open Regimes.Growing (hold)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a : Time}

namespace ResetPremisesUpTo

variable {b : Time}

/-- Every vote of slot `u` by a node honest at its cut, by `b`, is for the post-drain operational
proposal `P` of slot `u`, whose proposer is honest through `t_u + hold`. -/
theorem operational_unanimous_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {p : Fin sp.n} {k u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H (sp.ts u + hold sp)) (hdesignated : p = proposer u)
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u) (hR : drainTime sp a ≤ sp.ts u)
    (hub : sp.ts u ≤ b) :
    ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → e.msg.slot = u →
      tr.time j ≤ b → e.msg.head = P.root := by
  sorry

end ResetPremisesUpTo

variable {b : Time}

/-- Reports above a unanimous post-drain proposal `P` of slot `u` by `t_u + 6Δ`: every node
honest at `t_u + 6Δ` reports a descendant of `P`, or a node honest at its report reports a strict
height increase above `P`. -/
theorem report_cover_of_unanimous_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {u : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : P ∈ tr.HonestBlocksAt H) (hslot : P.slot = u) (hu : 0 < u)
    (hPg : P.root ≠ sp.genesisRoot)
    (hun : ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → tr.time j ≤ b →
      e.msg.slot = u → e.msg.head = P.root)
    (hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts u) (hR : drainTime sp a ≤ sp.ts (u + 1 : Nat))
    (hTb : sp.ts u + 6 * sp.Δ ≤ b) :
    (∀ y, y ∈ H (sp.ts u + 6 * sp.Δ) → ∃ r e R, SA.ToFGAt tr.projAC y r e R ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocksAt H) P R) ∨
    (∃ x r e C, x ∈ H (tr.time r) ∧ SA.ToFGAt tr.projAC x r e C ∧
      tr.time r ≤ sp.ts u + 6 * sp.Δ ∧ Anc (tr.HonestBlocksAt H) P C ∧
      ((tr.state x r).fg.σ P.root).h < ((tr.state x r).fg.σ C.root).h) := by
  sorry

end Consensus.Goldilocks.Healing.Growing

end
