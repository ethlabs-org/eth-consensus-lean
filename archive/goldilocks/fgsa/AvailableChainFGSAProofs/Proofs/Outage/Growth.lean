module
public import AvailableChainFGSAClaims.Statements.Regimes
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthCausal
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowthProposal
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.Shared.OutputGrowth -- shake: keep

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-- ROOT-DIGEST W2b. Plan A1–A6; bp 03 §5 (03:418–458);
DC Generic/Lemmas.lean:60 liveFrom_of_includedFrom.
Unfolded CleanGrowthClaim body. Select one awake honest proposal at the trigger
and use its gate by the original deadline. The recurrence supplies the join guard.
The trigger and deadline readers are independent. Assembly supplies compatibility
with the proposal at the trigger and scoped inclusion at the deadline. -/
theorem clean_growth_body [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G ΔF : Time)
    (hset : CleanSet p c E rho ΔF)
    (hcompatible : ∀ s B, HonestProposal E rho (fgsaInterface p c) s B →
      SA.gateTime p.toParams s ≤ rho.horizon →
      ∀ u x g, 0 ≤ u → u < V2.D.proposalTime (fgsaInterface p c) s →
        confirmedReader p c E rho x u →
        g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] →
        Block.Compatible (V2.D.outputAt E rho g x u) B)
    (hinclusion : ∀ s B, HonestProposal E rho (fgsaInterface p c) s B →
      SA.gateTime p.toParams s ≤ rho.horizon →
      ∀ u x g, SA.gateTime p.toParams s ≤ u → u ≤ rho.horizon →
        confirmedReader p c E rho x u →
        g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed] →
        Block.Preceq B (V2.D.outputAt E rho g x u))
    (hrec : AwakeProposerRecurrenceFrom p c E rho 0 G)
    (_hgap : 4 * p.Δ ≤ G) (t : Time) (ht : 0 ≤ t)
    (hhor : t + G + 6 * p.Δ ≤ rho.horizon) :
    ∃ s B, t < V2.D.proposalTime (fgsaInterface p c) s ∧
      HonestProposal E rho (fgsaInterface p c) s B ∧
      ∀ g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed],
        (∀ x, confirmedReader p c E rho x t → Block.Prec (V2.D.outputAt E rho g x t) B) ∧
        (∀ x, confirmedReader p c E rho x (t + G + 6 * p.Δ) →
          Block.Preceq B (V2.D.outputAt E rho g x (t + G + 6 * p.Δ))) := by
  have hd := p.deltaPos
  have h6 : 0 ≤ 6 * p.Δ := mul_nonneg (by decide) hd.le
  have hwindow : t + G ≤ rho.horizon := (le_add_of_nonneg_right h6).trans hhor
  obtain ⟨s, hfuture, hupper, hh, hjoined⟩ := hrec t ht hwindow
  have hs := hset.pre.base.valid.toScheduleWellFormed
  obtain ⟨B, hprop, hslot⟩ := fgsa_honestProposal_exists_of_awake_slot E rho hs
    hset.pre.base.delta hh hjoined.1 hjoined.2.2 (hupper.trans hwindow)
  have hgate : SA.gateTime p.toParams s ≤ t + G + 6 * p.Δ := by
    change 4 * p.Δ * (s : Time) + 6 * p.Δ ≤ t + G + 6 * p.Δ
    change 4 * p.Δ * (s : Time) ≤ t + G at hupper
    simpa only [add_comm] using add_le_add_left hupper (6 * p.Δ)
  refine ⟨s, B, hfuture, hprop, ?_⟩
  intro g hg
  refine ⟨?_, fun x hx => hinclusion s B hprop (hgate.trans hhor)
    _ x g hgate hhor hx hg⟩
  intro x hx
  have hn := fgsa_output_noFuture_of_slot E rho hs ht hfuture hslot.ge g hg x
  have hc := hcompatible s B hprop (hgate.trans hhor) t x g ht hfuture hx hg
  have hle : Block.Preceq (V2.D.outputAt E rho g x t) B := by
    simp only [Block.Compatible, Block.compatible, Bool.or_eq_true] at hc
    exact hc.elim id (fun hb => (hn hb).elim)
  have hne : V2.D.outputAt E rho g x t ≠ B := by
    intro he
    exact hn (he ▸ Gen.Pure.block_preceq_refl _)
  change (!decide (V2.D.outputAt E rho g x t = B) &&
    Block.preceq (V2.D.outputAt E rho g x t) B) = true
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  exact ⟨hne, hle⟩

end AvailableChain.FGSA.Run
end
