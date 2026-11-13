module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesRelay

public section

/-! # Proposal and voter views on the voter's read prefix

The view comparison uses a healthy AC base on that prefix. The proposer is honest through
the vote deadline and the voter at its cast; no static healing invariant is reconstructed.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Finite proposal/vote view agreement, with honesty at the two observation cuts. -/
theorem proposal_views_agree_before_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {s : Nat} (hm : gbar g + 2 * sp.Δ ≤ sp.ts s)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts (s + 1 : Nat) + sp.Δ))
    (hdesignated : z = proposer (s + 1))
    {k : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hactual : tr.ProposesAt z k P) (hPs : P.slot = s + 1)
    {ip : Nat} {ellp : ACLabel (goldilocksNode sp ro)} {pay : Payload sp.n}
    (hp : SA.ProposalAt tr.projAC z ip ellp pay) (hti : tr.time ip = sp.ts (s + 1 : Nat))
    (hpay : P.acPayload = pay)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {elly : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hP : P ∈ elly.frame.tree) (hjb : tr.time j ≤ b) (hstock : sp.committeeSize = sp.n) :
    SA.equivocators (SA.View.ofLists pay).votes =
        SA.equivocators (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)).votes ∧
      SA.voters (SA.View.ofLists pay).votes =
        SA.voters (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)).votes ∧
      ∀ X ∈ ellp.frame.tree, X ∈ elly.frame.tree →
        SA.supporters ellp.frame (SA.View.ofLists pay) s X =
          SA.supporters elly.frame (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s X := by
  have hr := hrun.toLocalRun
  have hd := hr.time_nonneg j
  have hS := healthy_base_of_service_catch_before_at hrun hnc hsvc hawake hf hcatch hd hjb hstock
  have hc' : SA.CastAt (tr.upTo (tr.time j)).projAC y j elly e := by
    refine ⟨?_, hc.2⟩
    rw [RunTrace.upTo_projAC]
    exact (Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩
  have hSr := hS.run.localRun
  rw [← RunTrace.upTo_projAC] at hSr
  have hslot := (SA.castAt_spec hSr hy hc').2.1.symm.trans hes
  change sp.slot (tr.time j) = s + 1 at hslot
  have hlo : sp.ts (s + 1 : Nat) ≤ tr.time j :=
    (SA.ts_le_iff_le_slot sp hd _).2 (by rw [hslot])
  have hhigh : tr.time j ≤ sp.ts (s + 1 : Nat) + sp.Δ := by
    have ht := SA.vote_time_le hSr hy ⟨elly, hc'⟩
    change tr.time j ≤ sp.ts (sp.slot (tr.time j)) + sp.Δ at ht
    rwa [hslot] at ht
  have hz' := hr.antitone hhigh hz
  have hpk : tr.time k = sp.ts (s + 1 : Nat) := by
    simpa only [hPs, sp.slotTime_eq, SAParams.ts] using hactual.2.2
  have hactual' : (tr.upTo (tr.time j)).ProposesAt z k P := by
    rcases hactual with ⟨⟨⟨acc, hk⟩, hpos⟩, hprop, ht⟩
    exact ⟨⟨⟨acc, (Trace.upTo_callAt _).mpr ⟨hpk ▸ hlo, hk⟩⟩, hpos⟩, hprop, ht⟩
  have hp' : SA.ProposalAt (tr.upTo (tr.time j)).projAC z ip ellp pay := by
    obtain ⟨hcp, hcall, d, hp⟩ := hp
    have hs := Trace.upTo_state tr.projAC z (d := tr.time j) (i := ip)
      (fun q hq => (hr.time_mono hq.le).trans (hti ▸ hlo))
    refine ⟨?_, hcall, d, ?_⟩
    · rw [RunTrace.upTo_projAC]
      exact (Trace.upTo_callAt _).mpr ⟨hti ▸ hlo, hcp⟩
    · simpa only [RunTrace.upTo_projAC, hs, Trace.upTo_time] using hp
  have hnr' : Healing.NoRestartAfter (tr.upTo (tr.time j)) (H (tr.time j)) (gbar g) := by
    intro x hx q hq
    obtain ⟨hqd, hq⟩ := (RunTrace.upTo_restartAt _).mp hq
    exact hnr x q (hr.antitone hqd hx) hq
  rw [← RunTrace.upTo_projAC] at hS
  exact Healing.proposal_views_agree_before (hrun.upTo hd) (hnc.upTo _) hS hnr' hm
    hz' hdesignated hactual' hPs hp' hti hpay hy hc' hes hP le_rfl

end Consensus.Goldilocks.Healing.Growing

end
