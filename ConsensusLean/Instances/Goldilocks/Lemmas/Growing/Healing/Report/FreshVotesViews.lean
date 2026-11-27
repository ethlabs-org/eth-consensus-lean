module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesRelay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.CoreStock
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowProposal
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Proposal and voter views on the voter's read prefix

The view comparison uses a healthy AC base on that prefix. The proposer is honest through
the vote deadline and the voter at its cast; no static healing invariant is reconstructed.
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
variable {hold : Time}

namespace Core

variable
  {u : Store sp.toParams (Payload sp.n) → FG.ChainState sp.n → Store sp.toParams (Payload sp.n)}
  {frameOf : NodeState (goldilocksNode sp) → AC.Frm sp.n (List (FG.Att sp.n))}

/-- Finite proposal/vote view agreement, with honesty at the two observation cuts. -/
theorem proposal_views_agree_before_at
    {K : AC.CommitteeDict sp.n}
    (hrun : GoldilocksRunCore u frameOf proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {s : Nat} (hm : gbar g + 2 * sp.Δ ≤ sp.ts s)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts (s + 1 : Nat) + sp.Δ))
    (hdesignated : z = proposer (s + 1))
    {k : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hactual : tr.ProposesAt z k P) (hPs : P.slot = s + 1)
    {ip : Nat} {ellp : ACLabel (goldilocksNode sp)} {pay : Payload sp.n}
    (hp : AC.ProposalAt tr.projAC z ip ellp pay) (hti : tr.time ip = sp.ts (s + 1 : Nat))
    (hpay : P.acPayload = pay)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {elly : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hP : P ∈ elly.frame.tree) (hjb : tr.time j ≤ b) (hK : CommitteeHalfUpTo tr H K g b) :
    AC.equivocators (AC.View.ofLists pay).votes =
        AC.equivocators (AC.mergedVoteView sp e.readPoint elly.frame (s + 1)).votes ∧
      AC.voters (AC.View.ofLists pay).votes =
        AC.voters (AC.mergedVoteView sp e.readPoint elly.frame (s + 1)).votes ∧
      ∀ X ∈ ellp.frame.tree, X ∈ elly.frame.tree →
        AC.supporters ellp.frame (AC.View.ofLists pay) s X =
          AC.supporters elly.frame (AC.mergedVoteView sp e.readPoint elly.frame (s + 1)) s X := by
  have hd := hrun.time_nonneg j
  have hS := hK.healthy_base_before_at_core hrun hnc hsvc hawake hf hcatch hd hjb
  have hc' : AC.CastAt (tr.projAC.upTo (tr.time j)) y j elly e :=
    ⟨(Trace.upTo_callAt _).mpr ⟨le_rfl, hc.1⟩, hc.2⟩
  have hSr := hS.run.localRun
  have hslot := (AC.castAt_specU hSr.toU hy hc').2.1.symm.trans hes
  change sp.slot (tr.time j) = s + 1 at hslot
  have hlo : sp.ts (s + 1 : Nat) ≤ tr.time j :=
    (AC.ts_le_iff_le_slot sp hd _).2 (by rw [hslot])
  have hhigh : tr.time j ≤ sp.ts (s + 1 : Nat) + sp.Δ := by
    have ht := AC.vote_time_leU hSr.toU hy ⟨elly, hc'⟩
    change tr.time j ≤ sp.ts (sp.slot (tr.time j)) + sp.Δ at ht
    rwa [hslot] at ht
  have hz' := hrun.antitone hhigh hz
  have hp' : AC.ProposalAt (tr.projAC.upTo (tr.time j)) z ip ellp pay := by
    obtain ⟨hcp, hcall, d, hp⟩ := hp
    have hs := Trace.upTo_state tr.projAC z (d := tr.time j) (i := ip)
      (fun q hq => (hrun.time_mono hq.le).trans (hti ▸ hlo))
    refine ⟨?_, hcall, d, ?_⟩
    · exact (Trace.upTo_callAt _).mpr ⟨hti ▸ hlo, hcp⟩
    · simpa only [hs, Trace.upTo_time] using hp
  have hPhiY := hrun.frameIn_at hnc hy hc.1
  have hzip : z ∈ H (tr.time ip) :=
    hrun.antitone (by rw [hti]; linarith [sp.toParams.hΔ]) hz
  have hPhiP := hrun.frameIn_at hnc hzip hp.1
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := AC.ts_succ s
  have hnrP : ∀ r ≤ ip, tr.RestartAt z r → tr.time r ≤ gbar g :=
    fun r hr hrs => hnr z r (hrun.antitone (hrun.time_mono hr) hzip) hrs
  have hnrY : ∀ r ≤ j, tr.RestartAt y r → tr.time r ≤ gbar g :=
    fun r hr hrs => hnr y r (hrun.antitone (hrun.time_mono hr) hy) hrs
  apply AC.view_agree_window_before hS.run hS.run.vstart
    hz' hy hdesignated hp' hti hc' hes
    ⟨P, hP, hPs, hpay⟩ (AC.serviceWindowBefore_of_sync hS.sync)
    (by linarith only [hm, hΔ]) (hti ▸ hlo) le_rfl
  · intro B hB _ hstamp hFB
    rw [AC.readPoint_blockStamp_eqU hSr.toU hy hc'] at hstamp
    rcases Healing.stamp_origin hSr hy j elly hc'.1 B hB with
        hg | ⟨q, hqj, ellq, hq, hBq, hsq⟩
    · have hcp' : (tr.projAC.upTo (tr.time ip)).CallAt z ip ellp :=
        (Trace.upTo_callAt _).mpr ⟨le_rfl, hp.1⟩
      obtain ⟨G, hGU, hGr, hGp⟩ := AC.genesis_mem_of_callU sp
        (hrun.acRun_upTo hnc (hrun.time_nonneg ip)).localRun.toU hzip ip ellp hcp'
      obtain rfl : B = G := (hrun.coherent hnc).1 (hPhiY.2 hB)
        (hrun.upTo_subset (hrun.time_nonneg ip) hGU) (hg.trans hGr.symm)
      rcases Relation.ReflTransGen.cases_tail hFB with he | ⟨C, _, hpar⟩
      · exact he ▸ hPhiP.1.rooted.1
      · exact (Option.some_ne_none _ (hpar.2.2.symm.trans hGp)).elim
    have hqt : tr.time q < sp.ts s + 3 * sp.Δ := by
      rw [hsq] at hstamp
      have ht := WithTop.coe_lt_coe.1 (WithBot.coe_lt_coe.1 hstamp)
      change tr.time q < AC.freeze sp (s + 1) at ht
      simpa only [AC.freeze, show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega] using ht
    exact frame_relay_before_at hrun hnc hsvc hcatch
      (hrun.antitone (hrun.time_mono hqj) hy) hzip hnrP
      ((Trace.upTo_callAt _).mp hq).2 hp.1 hBq
      (by rw [hti, hts]; linarith only [hm, hΔ])
      (by rw [hti, hts]; linarith only [hqt])
      (hFB.mono (hrun.upTo_subset hd))
  · intro v hv B hB hBr hFB
    by_cases hearly : tr.time j < sp.ts (s + 1 : Nat) + sp.Δ
    · obtain ⟨⟨P', hP', hPs', hsup⟩, -⟩ :=
        AC.cast_readyU hSr.toU hy hc' (by rw [hes]; exact hearly)
      rw [hes] at hPs' hsup
      obtain rfl := proposal_frame_unique_at hrun hnc hz hdesignated hactual hPs
        (by omega) hy hc.1 hhigh hP' hPs'
      have hvs : v.slot + 1 = s + 1 := by
        obtain ⟨d, hd⟩ := hp.2.2
        have hpayeq : pay = AC.voteViewList (tr.projAC.state z ip) ellp.frame
            ((sp.slot (tr.time ip) : Int) - 1) ⊤ := by
          unfold AC.acProposal at hd
          split_ifs at hd
          simp only [Option.some.injEq, Prod.mk.injEq] at hd
          exact hd.2.symm
        have hsi : sp.slot (tr.time ip) = s + 1 := AC.proposal_slot (tr := tr.projAC) hti
        rw [hpayeq, hsi] at hv
        simp only [show ((s + 1 : Nat) : Int) - 1 = (s : Int) by omega,
          AC.voteViewList, AC.ACState.poolAt, Int.toNat_natCast, List.filter_filter,
          List.mem_filter, List.mem_ite_nil_left, not_lt, Nat.cast_nonneg, true_and,
          Bool.and_eq_true, decide_eq_true_eq] at hv
        have hv' : v ∈ ((tr.projAC.upTo (tr.time j)).state z ip).pool s := by
          simpa only [Trace.upTo_state tr.projAC z
            (fun q hq => (hrun.time_mono hq.le).trans (hti ▸ hlo))] using hv.1
        rw [AC.state_pool_slotU sp hSr.toU hS.run.vstart hz' ip s v hv']
      obtain ⟨B', hB', hBr', -⟩ :=
        hsup v (by rw [AC.declaredSupportVotes, hpay]; exact hv) hvs
      rwa [(hrun.coherent hnc).1 (hPhiP.2 hB) (hPhiY.2 hB') (hBr.trans hBr'.symm)]
    · exact frame_relay_before_at hrun hnc hsvc hcatch hzip hy hnrY hp.1 hc.1 hB
        (by linarith only [hm, hΔ, hts, hlo]) (by rw [hti]; exact not_lt.1 hearly)
        (hFB.mono (hrun.upTo_subset hd))

end Core

/-- Finite proposal/vote view agreement, with honesty at the two observation cuts. -/
theorem proposal_views_agree_before_at
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time}
    (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    {s : Nat} (hm : gbar g + 2 * sp.Δ ≤ sp.ts s)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts (s + 1 : Nat) + sp.Δ))
    (hdesignated : z = proposer (s + 1))
    {k : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hactual : tr.ProposesAt z k P) (hPs : P.slot = s + 1)
    {ip : Nat} {ellp : ACLabel (goldilocksNode sp)} {pay : Payload sp.n}
    (hp : AC.ProposalAt tr.projAC z ip ellp pay) (hti : tr.time ip = sp.ts (s + 1 : Nat))
    (hpay : P.acPayload = pay)
    {y : Fin sp.n} {j : Nat} (hy : y ∈ H (tr.time j))
    {elly : ACLabel (goldilocksNode sp)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hP : P ∈ elly.frame.tree) (hjb : tr.time j ≤ b) (hK : CommitteeHalfUpTo tr H K g b) :
    AC.equivocators (AC.View.ofLists pay).votes =
        AC.equivocators (AC.mergedVoteView sp e.readPoint elly.frame (s + 1)).votes ∧
      AC.voters (AC.View.ofLists pay).votes =
        AC.voters (AC.mergedVoteView sp e.readPoint elly.frame (s + 1)).votes ∧
      ∀ X ∈ ellp.frame.tree, X ∈ elly.frame.tree →
        AC.supporters ellp.frame (AC.View.ofLists pay) s X =
          AC.supporters elly.frame (AC.mergedVoteView sp e.readPoint elly.frame (s + 1)) s X := by
  exact Core.proposal_views_agree_before_at hrun.toCore hnc hsvc hawake hf hcatch hnr hm
    hz hdesignated hactual hPs hp hti hpay hy hc hes hP hjb hK

end Consensus.Goldilocks.Healing.Growing

end
