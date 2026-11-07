module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.WitnessRelay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.WitnessUnanimity
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowFinality
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.QuorumMargin
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Causal next-vote induction from an independently honest early witness -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar)
open Compose.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The lock-specific transfer consumes only earlier honestly signed votes. -/
theorem next_votes_of_early_witness_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b)
    (_hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ))
    {s floor : Nat} {hi : Time} (hm : gbar g ≤ sp.ts s)
    (hnext : sp.ts (s + 1 : Nat) + sp.Δ ≤ hi) (hmb : hi ≤ b)
    {kindJ : Prop} {J X Q : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s) hi floor kindJ J)
    {w : Fin sp.n} {a : Nat} (hw : w ∈ H (tr.time a))
    (hat : tr.time a < sp.ts s + 2 * sp.Δ)
    {ellw : ACLabel (goldilocksNode sp ro)} (hcw : tr.projAC.CallAt w a ellw)
    (hQw : Q ∈ ellw.frame.tree) (hh : floor ≤ ((tr.state w a).fg.σ Q.root).h)
    (hJ : kindJ → Anc (tr.HonestBlocksAt H) J X)
    (hXQ : Anc (tr.HonestBlocksAt H) X Q)
    (htransfer : ∀ y i ell e, y ∈ H (tr.time i) → SA.CastAt tr.projAC y i ell e →
      e.msg.slot = s + 1 → tr.time i ≤ hi →
      Anc (tr.HonestBlocksAt H) (Node.frame (tr.state y i)).F X →
      SA.ViableAtVote ell e (s + 1) X →
      (∀ z k ev, k < i → z ∈ H (tr.time k) → SA.VoteAt tr.projAC z k ev →
        ev.msg.slot = s + 1 → SA.VoteExtends (tr.HonestBlocksAt H) ev.msg X) →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg X) :
    ∀ y i e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e → e.msg.slot = s + 1 →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
  have hU := honestBlocksAt_coherent hrun hnc
  have hQ : Q ∈ (tr.state w a).fg.tree := by
    rw [frame_of_projAC_at hrun hw hcw] at hQw
    exact hQw.1
  suffices hall : ∀ i, ∀ y e, y ∈ H (tr.time i) → SA.VoteAt tr.projAC y i e →
      e.msg.slot = s + 1 → SA.VoteExtends (tr.HonestBlocksAt H) e.msg X from
    fun y i e hy hv hs => hall i y e hy hv hs
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro y e hy ⟨ell, hc, he⟩ hs
    have hcast : SA.CastAt tr.projAC y i ell e := ⟨hc, he⟩
    have ht0 := hrun.time_nonneg i
    have hr := (acRun_upTo hrun hnc ht0).localRun
    have hcast' := sa_castAt_upTo.mpr ⟨le_rfl, hcast⟩
    have hslot : sp.slot (tr.time i) = s + 1 :=
      (castAt_spec_at hrun hnc hy hcast).2.1.symm.trans hs
    have hti : sp.ts (s + 1 : Nat) ≤ tr.time i :=
      (SA.ts_le_iff_le_slot sp ht0 _).2 (by rw [hslot])
    have hts := SA.ts_succ s (sp := sp)
    have hlo : sp.ts s ≤ tr.time i := by linarith only [hti, hts, sp.toParams.hΔ]
    have hhi : tr.time i ≤ hi := by
      have ht := (cast_head_fcRoot_at hrun hnc hy hcast).2
      rw [hs] at ht
      exact ht.trans hnext
    have hmargin : (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n :=
      sp.toParams.fg.faults_lt_quorum_margin (hf _ ht0 (hhi.trans hmb))
    have hFQ := hframe.finalized_below_descendant_at hrun hnc hy hw hw
      (by rw [max_eq_left (show tr.time a ≤ tr.time i by
            linarith only [hat, hti, hts, sp.toParams.hΔ])]; exact hmargin)
      hlo hhi hQ hh (fun hk => (hJ hk).trans hXQ) hQ .refl
    rcases SA.anc_total hU hFQ hXQ with hFX | hXF
    swap
    · obtain ⟨hPhi, hPhiU⟩ := frameIn_at hrun hnc hy hc
      obtain ⟨W, hW, hWr, hFW⟩ := SA.castAt_head_anc hr hy hcast' (Or.inr rfl)
        (fun L hL => (SA.liveLockBlock_candidate hPhi hL).elim
          (fun h => Or.inr h.2.1) Or.inl) hPhi.F_anc_fcRoot
      have hFW := hFW.mono hPhiU
      rw [frame_of_projAC_at hrun hy hc] at hFW
      exact ⟨W, hPhiU hW, hWr, hXF.trans hFW⟩
    have hFQ' : Anc (tr.HonestBlocksAt H) ell.frame.F Q := by
      rw [frame_of_projAC_at hrun hy hc]
      exact hFX.trans hXQ
    have hdom := witness_voterBlockTree_at hrun hnc hsvc hcatch hm hw hy hcw hat hQw
      hcast hs hFQ'
    have hQy : Q ∈ (tr.state y i).fg.tree := by
      have ht := hdom.1
      rw [frame_of_projAC_at hrun hy hc] at ht
      exact ht.1
    have hhy := floor_le_of_honest_ancestor_at hrun hnc hy hw hQ hh hQy
      (Relation.ReflTransGen.refl : Anc (tr.HonestBlocksAt H) Q Q)
    have hpath := witness_frame_at hrun hnc hframe hy hc hlo hhi hmargin hQy hhy hJ hXQ
    rcases hpath with hXF | ⟨-, hXt, hroot, -, hvQ, hXQf⟩
    · obtain ⟨hPhi, hPhiU⟩ := frameIn_at hrun hnc hy hc
      obtain ⟨W, hW, hWr, hFW⟩ := SA.castAt_head_anc hr hy hcast' (Or.inr rfl)
        (fun L hL => (SA.liveLockBlock_candidate hPhi hL).elim
          (fun h => Or.inr h.2.1) Or.inl) hPhi.F_anc_fcRoot
      have hFW := hFW.mono hPhiU
      exact ⟨W, hPhiU hW, hWr, hXF.trans hFW⟩
    have hviab : SA.ViableAtVote ell e (s + 1) X := by
      have hdomA := SA.voterBlockTree_anc hr hy hcast'
      rw [hs] at hdomA
      exact Or.inl ⟨hdomA Q hdom X hXQf, hroot, Q, hdom, hvQ, hXQf⟩
    exact htransfer y i ell e hy hcast hs hhi hFX hviab
      (fun z k ev hki hz hv hes => ih k hki z ev hz hv hes)

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
