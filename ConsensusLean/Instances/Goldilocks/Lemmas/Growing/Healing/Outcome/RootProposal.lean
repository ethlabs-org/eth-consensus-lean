module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.RootBound
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalPasses
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Suffix

public section

/-! # An honest cast's root lies below the actual post-drain proposal -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)
open Regimes.Growing (hold)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- Actual bounded proposal and cast evidence bound the voter root by the proposal. -/
theorem reset_vote_root_below_proposal_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ)) {p : Fin sp.n} {k u : Nat}
    {P : SA.Blk sp.n (List (FG.Att sp.n))} (hpH : p ∈ H (sp.ts u + hold sp))
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = u)
    (hR : drainTime sp a ≤ sp.ts u) {i : Nat}
    {ellp : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts u) (hib : tr.time i ≤ b) (hPQ : P.parent = some d.head.root)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j)) {elly : ACLabel (goldilocksNode sp ro)}
    {e : SA.Em sp (List (FG.Att sp.n))} (hcy : SA.CastAt tr.projAC y j elly e)
    (hes : e.msg.slot = u) (hjb : tr.time j ≤ b) :
    Anc (tr.HonestBlocksAt H) elly.frame.fcRoot P := by
  have hpi : p ∈ H (tr.time i) := hp.run.antitone (by
    rw [hti]
    exact le_add_of_nonneg_right sp.toParams.hΔ.le) hpH
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hci' := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hci⟩
  obtain ⟨hPhi, _⟩ := SA.frameIn_of_callAt (hac.localRun.upTo (hp.run.time_nonneg i)) hpi hci'
  obtain ⟨hst, hsQ⟩ := Compose.acProposal_start_anc_head hPhi hd
  have hsub := Outcome.frame_tree_subset hp.run hpi hci
  have hQU := hsub (Compose.mem_of_anc_left hsQ hst)
  have hk : tr.time k = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, SAParams.ts] using hactual.2.2
  have hpk : p ∈ H (tr.time k) := hp.run.antitone (by
    rw [hk]
    exact le_add_of_nonneg_right sp.toParams.hΔ.le) hpH
  have hactual' : (tr.upTo (tr.time k)).ProposesAt p k P := by
    rcases hactual with ⟨⟨⟨acc, hacc⟩, hpos⟩, hprop, htime⟩
    exact ⟨⟨⟨acc, (Trace.upTo_callAt tr).mpr ⟨le_rfl, hacc⟩⟩, hpos⟩, hprop, htime⟩
  have hacc' := Compose.proposal_accepted (hp.run.upTo (hp.run.time_nonneg k))
    (hp.noColl.upTo _) hpk hactual'
  have hacc := ((Trace.upTo_callAt tr).mp hacc').2
  have hPU : P ∈ tr.HonestBlocksAt H := by
    refine ⟨p, k + 1, tr.time k, hp.run.time_nonneg k,
      (fun q hq => hp.run.time_mono (by omega)), hpk, ?_⟩
    rw [tr.state_succ_of_call hacc,
      (Store.tree_grows _ _ _ _ (fg_reachable_at hp.run (hp.run.time_nonneg k)
        (fun q hq => hp.run.time_mono hq.le) hpk)).1 P _ (hp.run.cutLaw p k _ hacc hpk).2.1]
    exact Set.mem_insert _ _
  apply hp.reset_vote_root_below_bound_at hR hPU (fun x r l O ho hrt _ => ?_) hy hcy hes hjb
  exact (hp.reset_proposal_passes_at hc hpi hR hci hcall hd hti hib O ⟨x, r, l, ho, hrt⟩).trans
    (.single ⟨hQU, hPU, hPQ⟩)

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
