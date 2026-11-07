module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Relay

public section

/-! # The operational proposal in each honest voter's frame -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)
open Regimes.Growing (hold)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- The actual proposal reaches a voter honest at its own cast, above its finalized root. -/
theorem reset_proposal_frame_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {p y : Fin sp.n} {k j u : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hpH : p ∈ H (sp.ts u + hold sp))
    (hdesignated : p = proposer u) (hactual : tr.ProposesAt p k P) (hPs : P.slot = u)
    (hu : 0 < u) (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j ell e)
    (hes : e.msg.slot = u) (hjb : tr.time j ≤ b) (hg : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoin : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j)
    (hF : Anc (tr.HonestBlocksAt H) ell.frame.F P) : P ∈ ell.frame.tree := by
  by_cases hearly : tr.time j < sp.ts u + sp.Δ
  · exact Outcome.proposal_mem_of_early_cast hp.run hp.noColl hpH hdesignated hactual hPs
      hu hy hcy hes hearly
  have hk : tr.time k = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, SAParams.ts] using hactual.2.2
  have ht : 0 ≤ sp.ts u := hk ▸ hp.run.time_nonneg k
  have hp₀ : p ∈ H (sp.ts u) :=
    hp.run.antitone (le_add_of_nonneg_right sp.toParams.hΔ.le) hpH
  have hactual' : (tr.upTo (sp.ts u)).ProposesAt p k P := by
    rcases hactual with ⟨⟨⟨acc, ha⟩, hpos⟩, hprop, htime⟩
    exact ⟨⟨⟨acc, (Trace.upTo_callAt tr).mpr ⟨hk.le, ha⟩⟩, hpos⟩, hprop, htime⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ja, -, hacc, hta⟩ :=
    Healing.honestProposalRun_of_proposesAt (hp.run.upTo ht) (hp.noColl.upTo _)
      hp₀ hdesignated hactual' hPs
  obtain ⟨ell', hacc, hblock⟩ := hacc
  rw [← hdesignated] at hacc
  obtain ⟨q, hq, ha, htime⟩ := Compose.acBlock_prev (hp.run.upTo ht).toLocalRun hp₀
    (Compose.projAC_callAt.mp hacc) hblock
  have haq := (RunTrace.upTo_acceptAt tr).mp ha
  have hqt : tr.time q = sp.ts u := by
    change tr.time ja = sp.ts u at hta
    exact htime.trans hta
  exact Outcome.accept_mem_frame hp hc (hp.run.antitone hqt.le hp₀) hy haq.2 hcy.1 hjb hg
    hjoin (by rw [hqt]; exact not_lt.mp hearly) hF

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
