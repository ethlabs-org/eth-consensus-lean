module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.CurrentLock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowCast
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowRegularBoundary
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowLaterBoundary
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Passage of an honest cast's live read locks below a warm proposal -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar)
open Compose.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Older read locks pass through their historical writes; only current optimistic writes
remain as a causal alternative. -/
theorem current_lock_passage_of_regular_base_at
    {g ΔF b : Time} {s₀ p floor : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts p + sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hsp : s₀ ≤ p) (hp0 : 0 < p)
    (hpb : sp.ts p + sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts p + sp.Δ)) (hdes : z = proposer p)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = p)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hes : e.msg.slot = p)
    (hmargin : s₀ + 2 * sp.k ≤ p)
    {l : SA.Lock} (hl : l ∈ e.readPoint.locks) (hlive : p ≤ l.slot + sp.k)
    {B : SA.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ell.frame.tree)
    (hBr : B.root = l.block) (hstock : sp.committeeSize = sp.n) :
    P ∈ ell.frame.viableHeads ∧
      P ∈ ell.frame.viableTree (SA.voterBlockTree sp e.readPoint ell.frame p) ∧
      (Anc (tr.HonestBlocksAt H) B P ∨
        (l.slot = p ∧ ∃ a ≤ i, ∃ D CV, y ∈ H (tr.time a) ∧
          SA.OptimisticLockAt tr.projAC y a p D CV ∧ sp.ts p ≤ tr.time a ∧
          Anc (tr.HonestBlocksAt H) B D)) := by
  have hΔ := sp.toParams.hΔ
  have hm₀ : gbar g ≤ sp.ts s₀ := by linarith
  obtain ⟨hvP, hdomP⟩ := proposal_viable_at_cast_at hframe hrun hnc hsvc hawake hf hcatch
    hnr hm₀ hsp hp0 hpb hz hdes hP hPs hy hc hes hstock
  refine ⟨hvP, hdomP, ?_⟩
  have hlabel : s₀ + sp.k ≤ l.slot := by omega
  have hd := hrun.time_nonneg i
  have hr := (acRun_upTo hrun hnc hd).localRun
  have hc' := sa_castAt_upTo.mpr ⟨le_rfl, hc⟩
  have hPhi := frameIn_at hrun hnc hy hc.1
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono hd
  have hslot : sp.slot (tr.time i) = p := ((SA.castAt_spec hr hy hc').2.1).symm.trans hes
  by_cases hcurrent : p ≤ l.slot
  · obtain ⟨hs, a, hai, D, CV, hya, hop, ht, C, hC, hCr, hCD⟩ :=
      current_lock_write_readPoint_at hrun hnc hy hc (hes ▸ hp0) hl (hes ▸ hcurrent)
    have hcoh := Compose.Growing.honest_blocks_coherent hrun hnc
    obtain rfl : C = B := hcoh.1 hC (hPhi.2 hB) (hCr.trans hBr.symm)
    rw [hes] at hs hop ht
    exact Or.inr ⟨hs, a, hai, D, CV, hya, hop, ht, hCD⟩
  have hold : l.slot + 1 ≤ p := by omega
  obtain ⟨l₀, hl₀, hs, B₀, hB₀, hBr₀, C, hC, hCr, hCB⟩ :=
    SA.readPoint_locks_below_stored hr hy hc'
      (by change 0 < sp.slot (tr.time i); rw [hslot]; exact hp0) l hl
      (by change l.slot ≠ sp.slot (tr.time i); rw [hslot]; omega)
  have hCE : C = B := hPhi.1.coherent.1 hC hB (hCr.trans hBr.symm)
  subst C
  obtain ⟨a, hai, ellw, D, ha, hD, ho, M, hM, hMr, hMA⟩ :=
    SA.lock_selection_candidate_provenance hr hy i l₀ hl₀
  obtain rfl : M = B₀ := hr.coherent.1 hM
    ((SA.frameIn_of_callAt hr hy hc'.1).2 hB₀) (hMr.trans hBr₀.symm)
  rw [← hs] at ho
  have hat := hrun.time_mono hai.le
  have hya := hrun.antitone hat hy
  have hsa := Trace.upTo_state tr.projAC y (d := tr.time i) (i := a)
    (fun q hq => (hrun.time_mono hq.le).trans hat)
  have hcall : ∀ ℓ, (tr.projAC.upTo (tr.time i)).CallAt y a ℓ ↔
      tr.projAC.CallAt y a ℓ := fun _ => Trace.upTo_callAt_of_le _ hat
  have ha₀ : tr.projAC.CallAt y a ellw := by
    exact (Trace.upTo_callAt _).mp ha |>.2
  have ho₀ : ((∃ CV, SA.FastUpdateAt tr.projAC y a l.slot D CV) ∨
      SA.SlowLockAt tr.projAC y a l.slot D) ∨
      ∃ CV, SA.OptimisticLockAt tr.projAC y a l.slot D CV := by
    have ho' : (∃ CV, SA.FastUpdateAt (tr.projAC.upTo (tr.time i)) y a l.slot D CV ∨
        SA.OptimisticLockAt (tr.projAC.upTo (tr.time i)) y a l.slot D CV) ∨
        SA.SlowLockAt (tr.projAC.upTo (tr.time i)) y a l.slot D := by
      rcases ho with ⟨_, CV, hfast | hop⟩ | ⟨_, hslow⟩
      · exact Or.inl ⟨CV, Or.inl hfast⟩
      · exact Or.inl ⟨CV, Or.inr hop⟩
      · exact Or.inr hslow
    have ho'' : (∃ CV, SA.FastUpdateAt tr.projAC y a l.slot D CV ∨
        SA.OptimisticLockAt tr.projAC y a l.slot D CV) ∨
        SA.SlowLockAt tr.projAC y a l.slot D := by
      simpa only [RunTrace.upTo_projAC, SA.FastUpdateAt, SA.UpdateAt,
        SA.SlowLockAt, SA.OptimisticLockAt, SA.OptimisticPoint, hcall, hsa,
        Trace.upTo_time] using ho'
    rcases ho'' with ⟨CV, hfast | hop⟩ | hslow
    · exact Or.inl (Or.inl ⟨CV, hfast⟩)
    · exact Or.inr ⟨CV, hop⟩
    · exact Or.inl (Or.inr hslow)
  let A := ellw.frame.viableAncestor D
  have hBA : Anc (tr.HonestBlocksAt H) B A :=
    (Anc.mono hPhi.2 hCB).trans (Anc.mono hsub hMA)
  have hW := frameIn_at hrun hnc hya ha₀
  have hAD : Anc (tr.HonestBlocksAt H) A D :=
    Anc.mono hW.2 (SA.viableAncestor_anc hW.1 hD).2
  have hhigh : tr.time i ≤ sp.ts p + sp.Δ := by
    have ht := SA.vote_time_le hr hy ⟨ell, hc'⟩
    change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at ht
    rwa [hslot] at ht
  have htime : tr.time kP = sp.ts p := by
    simpa only [sp.slotTime_eq, hPs, SAParams.ts] using hP.2.2
  have hzk : z ∈ H (tr.time kP) := hrun.antitone (by rw [htime]; linarith) hz
  have hP' : (tr.upTo (tr.time kP)).ProposesAt z kP P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hP.1⟩, hP.2⟩
  obtain ⟨_, ip, ellp, d, pay, hcp, hcallp, hpay, hti, hparent, _⟩ :=
    Healing.honestProposalRun_of_proposesAt (hrun.upTo (hrun.time_nonneg kP))
      (hnc.upTo _) hzk hdes hP' hPs
  rw [← hdes] at hcp hpay
  have hip : tr.time ip = sp.ts p := hti
  have hcp₀ : tr.projAC.CallAt z ip ellp := by
    rw [RunTrace.upTo_projAC] at hcp
    exact ((Trace.upTo_callAt _).mp hcp).2
  have hzip : z ∈ H (tr.time ip) := hrun.antitone (by rw [hip]; linarith) hz
  have hpay₀ : (SA.acProposal sp (tr.projAC.state z ip) ellp.frame (tr.time ip)).2 =
      some (d, pay) := by
    have hst := Trace.upTo_state tr.projAC z (d := tr.time kP) (i := ip)
      (fun q hq => (hrun.time_mono hq.le).trans (by rw [hip, htime]))
    simp only [RunTrace.upTo_projAC, hst, Trace.upTo_time] at hpay
    exact hpay
  have hHP : Anc (tr.HonestBlocksAt H) d.head P := by
    have hH : d.head ∈ ellp.frame.tree := by
      rw [(SA.acProposal_head hpay₀).2]
      exact SA.getHead_mem (frameIn_at hrun hnc hzip hcp₀).1
        (fun X (hX : X ∈ ellp.frame.viableTree ellp.frame.tree) => hX.1) _ _ _ _
    exact .single ⟨(frameIn_at hrun hnc hzip hcp₀).2 hH, hPhi.2 hdomP.1.1, hparent⟩
  rcases ho₀ with horigin | ⟨CV, hop⟩
  · obtain ⟨ell', hu⟩ : ∃ ell', SA.UpdateAt tr.projAC y a l.slot ell' := by
      rcases horigin with ⟨CV, ell', C, hu, _⟩ | ⟨ell', C, hu, _⟩ <;> exact ⟨ell', hu⟩
    have ht := hu.2.2.1
    change tr.time a = _ at ht
    have hgap : l.slot + 2 ≤ p := by
      by_contra hn
      have he : p = l.slot + 1 := by omega
      rw [he] at hhigh
      simp only [SAParams.ts] at ht hhigh
      push_cast at hhigh
      linarith
    have hDP := (hframe.regular_later_heads_at hrun hnc hsvc hawake hf hcatch hnr
      hlabel (by omega) (by omega) hm hgap hpb hya horigin hstock p (by omega) le_rfl).2
      hgap z ip ellp hzip hcp₀ hcallp hip d pay hpay₀
    exact Or.inl (hBA.trans (hAD.trans (hDP.trans hHP)))
  have hts : sp.ts s₀ ≤ sp.ts l.slot := (SA.ts_le_iff sp).2 (by omega)
  have hlow : sp.ts l.slot ≤ tr.time a := by
    obtain ⟨_, _, _, hs', _⟩ := hop
    change sp.slot (tr.time a) = l.slot at hs'
    exact (SA.ts_le_iff_le_slot sp (hrun.time_nonneg a) _).2 (by rw [hs'])
  have halo := hts.trans hlow
  rcases (SA.viableAncestor_spec hW.1 hD).2.1 with hbelow | hAv
  · have hAw := Anc.mono hW.2 hbelow
    change Anc (tr.HonestBlocksAt H) A ellw.frame.fcRoot at hAw
    rw [frame_of_projAC_at hrun hya ha₀] at hAw
    have hmono := fcRoot_mono_at hframe hrun hy hai.le halo hhigh
    have hrootP := Anc.mono hPhi.2 hdomP.2.1
    rw [frame_of_projAC_at hrun hy hc.1] at hrootP
    exact Or.inl (hBA.trans (hAw.trans (hmono.trans hrootP)))
  obtain ⟨Q, hQ, hvQ, hAQ⟩ := hAv.2.2
  have hvQ' := hvQ
  rw [frame_of_projAC_at hrun hya ha₀] at hvQ'
  have hh : floor ≤ ((tr.state y a).fg.σ Q.root).h := by
    rw [← hframe.floor_eq y a hya halo (hat.trans hhigh)]
    exact hvQ'.2.2.2
  have hJ : kindJ → Anc (tr.HonestBlocksAt H) J A := by
    intro hk
    have hkind := (hframe.kind_iff y a hya halo (hat.trans hhigh)).mpr hk
    have hrootA := Anc.mono hW.2 hAv.2.1
    change Anc (tr.HonestBlocksAt H) ellw.frame.fcRoot A at hrootA
    rw [frame_of_projAC_at hrun hya ha₀] at hrootA
    change Anc (tr.HonestBlocksAt H) (tr.state y a).fg.fcRoot A at hrootA
    rwa [show (tr.state y a).fg.fcRoot = (tr.state y a).fg.J from ite_eq_left hkind,
      hframe.root_eq y a hya halo (hat.trans hhigh) hk] at hrootA
  have hsubframe : FrameWindow tr H (sp.ts l.slot) (sp.ts p + sp.Δ) floor kindJ J :=
    ⟨fun w j hw hlo hhi => hframe.floor_eq w j hw (hts.trans hlo) hhi,
     fun w j hw hlo hhi => hframe.kind_iff w j hw (hts.trans hlo) hhi,
     fun w j hw hlo hhi => hframe.root_eq w j hw (hts.trans hlo) hhi⟩
  have hAP := (optimistic_later_heads_of_witness_at hrun hnc hsvc hawake hf hcatch hnr
    (hm₀.trans hts) hpb hsubframe hya hop hAD ha₀ hQ hh hJ (Anc.mono hW.2 hAQ) hstock
    p hold le_rfl).2 z ip ellp hzip hcp₀ hcallp hip d pay hpay₀
  exact Or.inl (hBA.trans (hAP.trans hHP))

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
