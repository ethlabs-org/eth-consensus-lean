module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Restart

public section

/-! # Pending growing interface of the operational reports

The growing forms of the Healing and AC lemmas that the operational report lemmas consume, under
their agreed names (static name + `_at`), with each node honest at its own cut (the proved
`ResetPremisesUpTo.restart_le_before_at` is re-exported from `Growing/Healing/Restart`):

* `Healing.Growing.ResetPremisesUpTo.high_origin_votes_before_at`
  (`Healing.ResetPremisesUpTo.high_origin_votes_before`, retention R2);
* `Healing.Growing.healthy_base_of_reset_catch_before_at`
  (`Healing.healthy_base_of_reset_catch_before`, in prefix form: the static AC base on the prefix
  through `d` over `H d`).

Each theorem here is an open `sorry`; this module is deleted when the home modules land. -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

namespace ResetPremisesUpTo

/-- High origins written by the horizon retain every later-label vote of a voter honest at its
cast through the horizon. -/
theorem high_origin_votes_before_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) :
    ∀ k, tr.time k ≤ b → ∀ x i j B, HighOrigin tr H g x i j B → tr.time i ≤ b →
      ∀ y ell e, y ∈ H (tr.time k) → SA.CastAt tr.projAC y k ell e → j < e.msg.slot →
        SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
  sorry

end ResetPremisesUpTo

/-- Finite reset health supplies the static AC base on the prefix through every `d ∈ [0, b]`, over
the validators honest at `d`. -/
theorem healthy_base_of_reset_catch_before_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {d : Time} (hd0 : 0 ≤ d) (hdb : d ≤ b) :
    SA.HealthyBaseUpTo (tr.projAC.upTo d) (H d) ((tr.upTo d).HonestBlocks (H d)) proposer g d := by
  sorry

end Consensus.Goldilocks.Healing.Growing

end
