module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.FrozenFrame
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Relay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResultSupport
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Agree
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Ready
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Head
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The operational proposal's view agrees with the voter's, under growing faults

`reset_views_agree_at`, the growing form of `Healing.ResetPremisesUpTo.reset_views_agree`
(`Healing/Outcome/SupplierFrames`): the proposal's view and a slot-`(s+1)` voter's merged view
agree on common held targets, for a proposer honest through `t_{s+1} + hold` and a voter honest
at its cast. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)
open Regimes.Growing (hold)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- The operational proposal's view and a slot-`(s+1)` voter's merged view agree on common held
targets, for a proposer honest through `t_{s+1} + hold` and a voter honest at its cast. -/
theorem reset_views_agree_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    (hc : CatchRun tr H g (2 * sp.Δ))
    {p y : Fin sp.n} {k i j s : Nat} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hpH : p ∈ H (sp.ts (s + 1 : Nat) + hold sp)) (hdesignated : p = proposer (s + 1))
    (hactual : tr.ProposesAt p k P) (hPs : P.slot = s + 1)
    {ellp elly : ACLabel (goldilocksNode sp ro)}
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hci : tr.projAC.CallAt p i ellp) (hcall : ellp.call = .proposal)
    (hd : (SA.acProposal sp (tr.projAC.state p i) ellp.frame (tr.time i)).2 = some (d, pay))
    (hti : tr.time i = sp.ts (s + 1 : Nat)) (hpay : P.acPayload = pay)
    (hy : y ∈ H (tr.time j)) {e : SA.Em sp (List (FG.Att sp.n))}
    (hcy : SA.CastAt tr.projAC y j elly e) (hes : e.msg.slot = s + 1)
    (hib : tr.time i ≤ b) (hjb : tr.time j ≤ b)
    (hPy : P ∈ elly.frame.tree) (hg : SA.gbar g ≤ sp.ts s)
    (hgi : SA.gbar g + 2 * sp.Δ ≤ tr.time i)
    (hgj : SA.gbar g + 2 * sp.Δ ≤ tr.time j)
    (hjoi : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time i)
    (hjoj : sp.ts (sp.slot (SA.gbar g) + 1 : Nat) + sp.Δ ≤ tr.time j) :
    SA.equivocators (SA.View.ofLists pay).votes =
        SA.equivocators (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)).votes ∧
      SA.voters (SA.View.ofLists pay).votes =
        SA.voters (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)).votes ∧
      ∀ X ∈ ellp.frame.tree, X ∈ elly.frame.tree →
        SA.supporters ellp.frame (SA.View.ofLists pay) s X =
          SA.supporters elly.frame (SA.mergedVoteView sp e.readPoint elly.frame (s + 1)) s X := by
  have hm := hp.run.time_mono
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hr := (hac.upTo (hp.run.time_nonneg j)).localRun
  have hcy' := SA.upTo_castAt.mpr (And.intro le_rfl hcy)
  have htj : tr.time j ≤ sp.ts (s + 1 : Nat) + hold sp := by
    have ht := (Compose.cast_head_fcRoot hr hy hcy').2
    change tr.time j ≤ sp.ts e.msg.slot + sp.Δ at ht
    simpa only [hes, hold] using ht
  have hpi : p ∈ H (tr.time i) := hp.run.antitone
    (by rw [hti]; exact le_add_of_nonneg_right sp.toParams.hΔ.le) hpH
  have hpmax : p ∈ H (max (tr.time i) (tr.time j)) := hp.run.antitone
    (max_le (by rw [hti]; exact le_add_of_nonneg_right sp.toParams.hΔ.le) htj) hpH
  have hrp := (hac.upTo (hp.run.time_nonneg i)).localRun
  have hci' := (Trace.upTo_callAt tr.projAC).mpr (And.intro le_rfl hci)
  have hsync := KernelProof.reset_syncACAt hp (lo := sp.ts s) (hi := sp.ts (s + 1 : Nat))
    ((le_max_left g 0).trans hg)
  apply SA.Growing.view_agree hac hpmax hy hdesignated ⟨hci, hcall, d, hd⟩ hti hcy
    ⟨P, hPy, hPs, hpay⟩ hsync
  · intro B hB _ hstamp hF
    exact hp.reset_frozen_frame_at hc hpi hy hci hti hcy hib hgi hjoi hB hstamp hF
  · intro v hv B hB hBr hF
    by_cases hearly : tr.time j < sp.ts (s + 1 : Nat) + sp.Δ
    · obtain ⟨Q, hQ, hQs, hsup⟩ := SA.cast_ready hr hy hcy' (by rw [hes]; exact hearly)
      rw [hes] at hQs hsup
      obtain rfl := Outcome.proposal_unique_before_hold hp.run hp.noColl hpH hdesignated
        hactual hPs (by omega) hy hcy.1 htj hQ hQs
      have hslot : sp.slot (tr.time i) = s + 1 := by
        rw [hti]
        exact SA.slot_of_mem sp _ le_rfl ((SA.ts_lt_iff sp).mpr (by omega))
      have hpay' : pay = SA.voteViewList (tr.projAC.state p i) ellp.frame (s : Int) ⊤ := by
        unfold SA.acProposal at hd
        split_ifs at hd
        simp only [Option.some.injEq, Prod.mk.injEq] at hd
        rw [← hd.2, hslot]
        congr 1
        push_cast
        ring
      have hsip : (tr.projAC.upTo (tr.time i)).state p i = tr.projAC.state p i :=
        Trace.upTo_state _ p (fun q hq => hm hq.le)
      have hvs : v.slot + 1 = s + 1 := by
        rw [hpay'] at hv
        simp only [SA.voteViewList, SA.SAState.poolAt, Int.toNat_natCast, List.filter_filter,
          List.mem_filter, List.mem_ite_nil_left, not_lt, Nat.cast_nonneg, true_and,
          Bool.and_eq_true, decide_eq_true_eq] at hv
        rw [SA.state_pool_slot sp hrp hpi i s v (hsip.symm ▸ hv.1)]
      obtain ⟨B', hB', hBr', _⟩ := hsup v (by rw [SA.blockSupport, hpay]; exact hv) hvs
      rwa [hac.localRun.coherent.1 ((SA.frameIn_of_callAt hrp hpi hci').2 hB)
        ((SA.frameIn_of_callAt hr hy hcy'.1).2 hB') (hBr.trans hBr'.symm)]
    · have hframe := Outcome.frame_of_call hp.run hpi hci
      have hBt : B ∈ (tr.state p i).fg.tree := by rw [hframe] at hB; exact hB.1
      have hpre := hp.run.upTo (hp.run.time_nonneg i)
      have hBt' : B ∈ ((tr.upTo (tr.time i)).state p i).fg.tree := by
        rwa [Trace.upTo_state tr p (fun q hq => hm hq.le)]
      rcases Healing.tree_accepted hpre.toLocalRun hpi hBt' with hgen | ⟨q, hqi, hacc⟩
      · have hBy := Store.genesis_mem (fg_reachable_at hp.run (hp.run.time_nonneg j)
          (fun q hq => hm hq.le) hy)
        rw [← hgen] at hBy
        rw [Outcome.frame_of_call hp.run hy hcy.1]
        exact ⟨hBy, store_anc_of_honest_anc_at hp.run hp.noColl (hp.run.time_nonneg j)
          (fun q hq => hm hq.le) hy
          (by rwa [Outcome.frame_of_call hp.run hy hcy.1] at hF) hBy⟩
      · obtain ⟨hqt, hacc⟩ := (RunTrace.upTo_acceptAt tr).mp hacc
        exact Outcome.accept_mem_frame hp hc (hp.run.antitone hqt hpi) hy hacc hcy.1 hjb
          hgj hjoj (by have ht := hm hqi.le; rw [hti] at ht; linarith) hF

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
