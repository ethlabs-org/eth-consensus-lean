module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.ACWindowDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs

public section

/-! # Pending growing interface of the operational reports

The growing forms of the Healing and AC lemmas that the operational report lemmas consume, under
their agreed names (static name + `_at`), with each node honest at its own cut:

* `Healing.Growing.ResetPremisesUpTo.high_origin_votes_before_at`
  (`Healing.ResetPremisesUpTo.high_origin_votes_before`, retention R2);
* `Healing.Growing.ResetPremisesUpTo.restart_le_before_at` (`Healing.restart_le_before`);
* `Healing.Growing.healthy_base_of_reset_catch_before_at`
  (`Healing.healthy_base_of_reset_catch_before`);
* `SA.Growing.honest_votes_in_slot_before_at` (`SA.honest_votes_in_slot_before`).

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

/-- A restart of a node honest at it, by the horizon, is by the slot after `ḡ`. -/
theorem restart_le_before_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k)) (hk : tr.RestartAt y k)
    (hkb : tr.time k ≤ b) : tr.time k ≤ sp.ts (sp.slot (gbar g) + 1 : Nat) := by
  sorry

end ResetPremisesUpTo

/-- Finite reset health supplies the growing AC base through the horizon. -/
theorem healthy_base_of_reset_catch_before_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) :
    SA.Growing.HealthyBaseUpTo tr.projAC H (tr.HonestBlocksAt H) proposer g b := by
  sorry

end Consensus.Goldilocks.Healing.Growing

namespace Consensus.Goldilocks.SA.Growing

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP}
  {tr : SATrace sp FGP ro} {H : Time → Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}
  {proposer : Nat → Fin sp.n} {g : Time}

/-- Every validator honest at the vote deadline `t_m + Δ` votes in slot `m` by then. -/
theorem honest_votes_in_slot_before_at {b : Time} (hS : HealthyBaseUpTo tr H U proposer g b)
    {m : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts m) (hmb : sp.ts m + sp.Δ ≤ b)
    (hrestart : ∀ x r, x ∈ H (tr.time r) → tr.time r ≤ sp.ts m + sp.Δ → tr.RestartAt x r →
      tr.time r ≤ sp.ts ((m : Int) - 1)) :
    ∀ x, x ∈ H (sp.ts m + sp.Δ) →
      ∃ j e, VoteAt tr x j e ∧ e.msg.slot = m ∧ tr.time j ≤ sp.ts m + sp.Δ := by
  sorry

end Consensus.Goldilocks.SA.Growing

end
