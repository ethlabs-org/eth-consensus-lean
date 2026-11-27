module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ProposalViable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.LockLocal
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RegularLater
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.OptimisticWitness
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.CurrentLock
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Current lock passage over the primed window

Regular origins propagate through the primed regular-later supplier. An optimistic
writer's own viable head supplies the early witness, without a stock contest residue.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {hold : Time}

section Passage

variable
    {g ΔF b : Time} {s₀ p M : Nat} {isTop : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow' tr H (sp.ts s₀) (sp.ts p + sp.Δ) M isTop J)
    {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hsp : s₀ ≤ p) (hp0 : 0 < p)
    (hpb : sp.ts p + sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts p + sp.Δ)) (hdes : z = proposer p)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = p)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hes : e.msg.slot = p)
    (hmargin : s₀ + 2 * sp.k ≤ p)
    {l : AC.Lock} (hl : l ∈ e.readPoint.locks) (hlive : p ≤ l.slot + sp.k)
    {B : AC.Blk sp.n (List (FG.Att sp.n))} (hB : B ∈ ell.frame.tree)
    (hBr : B.root = l.block) (hK : CommitteeHalfUpTo tr H K g b)

include hframe hrun hnc hsvc hawake hf hcatch hnr hm hsp hp0 hpb hz hdes hP hPs
  hy hc hes hmargin hl hlive hB hBr hK

/-- Older lock passage assembled from regular propagation and the writer's viable witness. -/
private theorem older_lock_prefix_transfer_primed (holder : l.slot < p) :
    Anc (tr.HonestBlocksAt H) B P := by
  have rc := hrun.toCore
  have hΔ := sp.toParams.hΔ
  have hlabel : s₀ + sp.k ≤ l.slot := by omega
  have hd := hrun.time_nonneg i
  have hr := (rc.acRun_upTo hnc hd).localRun
  have hc' := AC.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hPhi := rc.frameIn_at hnc hy hc.1
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono hd
  have hslot : sp.slot (tr.time i) = p := ((AC.castAt_specU hr.toU hy hc').2.1).symm.trans hes
  obtain ⟨l₀, hl₀, hs, B₀, hB₀, hBr₀, C, hC, hCr, hCB⟩ :=
    AC.readPoint_locks_below_stored hr hy hc'
      (by change 0 < sp.slot (tr.time i); rw [hslot]; exact hp0) l hl
      (by change l.slot ≠ sp.slot (tr.time i); rw [hslot]; omega)
  have hCE : C = B := hPhi.1.coherent.1 hC hB (hCr.trans hBr.symm)
  subst C
  obtain ⟨a, hai, ellw, D, ha, hD, ho, M, hM, hMr, hMA⟩ :=
    AC.lock_selection_candidate_provenance hr hrun.vstart hy i l₀ hl₀
  obtain rfl : M = B₀ := hr.coherent.1 hM
    ((AC.frameIn_of_callAt hr hy hc'.1).2 hB₀) (hMr.trans hBr₀.symm)
  rw [← hs] at ho
  have hat := hrun.time_mono hai.le
  have hya := hrun.antitone hat hy
  have hsa := Trace.upTo_state tr.projAC y (d := tr.time i) (i := a)
    (fun q hq => (hrun.time_mono hq.le).trans hat)
  have hcall : ∀ ℓ, (tr.projAC.upTo (tr.time i)).CallAt y a ℓ ↔
      tr.projAC.CallAt y a ℓ := fun _ => Trace.upTo_callAt_of_le _ hat
  have ha₀ : tr.projAC.CallAt y a ellw := ((Trace.upTo_callAt _).mp ha).2
  have ho₀ : ((∃ CV, AC.FastUpdateAt tr.projAC y a l.slot D CV) ∨
      AC.SlowLockAt tr.projAC y a l.slot D) ∨
      ∃ CV, AC.OptimisticLockAt tr.projAC y a l.slot D CV := by
    have ho' : (∃ CV, AC.FastUpdateAt (tr.projAC.upTo (tr.time i)) y a l.slot D CV ∨
        AC.OptimisticLockAt (tr.projAC.upTo (tr.time i)) y a l.slot D CV) ∨
        AC.SlowLockAt (tr.projAC.upTo (tr.time i)) y a l.slot D := by
      rcases ho with ⟨_, CV, hfast | hop⟩ | ⟨_, hslow⟩
      · exact Or.inl ⟨CV, Or.inl hfast⟩
      · exact Or.inl ⟨CV, Or.inr hop⟩
      · exact Or.inr hslow
    have ho'' : (∃ CV, AC.FastUpdateAt tr.projAC y a l.slot D CV ∨
        AC.OptimisticLockAt tr.projAC y a l.slot D CV) ∨
        AC.SlowLockAt tr.projAC y a l.slot D := by
      simpa only [AC.FastUpdateAt, AC.UpdateAt, AC.SlowLockAt, AC.OptimisticLockAt,
        AC.OptimisticPoint, hcall, hsa, Trace.upTo_time] using ho'
    rcases ho'' with ⟨CV, hfast | hop⟩ | hslow
    · exact Or.inl (Or.inl ⟨CV, hfast⟩)
    · exact Or.inr ⟨CV, hop⟩
    · exact Or.inl (Or.inr hslow)
  let A := ellw.frame.viableAncestor D
  have hBA : Anc (tr.HonestBlocksAt H) B A :=
    (hCB.mono hPhi.2).trans (hMA.mono hsub)
  have hW := rc.frameIn_at hnc hya ha₀
  have hAD : Anc (tr.HonestBlocksAt H) A D :=
    (AC.viableAncestor_anc hW.1 hD).2.mono hW.2
  have hhigh : tr.time i ≤ sp.ts p + sp.Δ := by
    have ht := AC.vote_time_leU hr.toU hy ⟨ell, hc'⟩
    change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at ht
    rwa [hslot] at ht
  have htime : tr.time kP = sp.ts p := by
    simpa only [sp.slotTime_eq, hPs, ACParams.ts] using hP.2.2
  have hzk : z ∈ H (tr.time kP) := hrun.antitone (by rw [htime]; linarith) hz
  have hP' : (tr.upTo (tr.time kP)).ProposesAt z kP P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hP.1⟩, hP.2⟩
  obtain ⟨_, ip, ellp, d, pay, hcp, hcallp, hpay, hti, hparent, _⟩ :=
    Coherence.honestProposalRun_of_proposesAt (hrun.upTo (hrun.time_nonneg kP))
      (hnc.upTo _) hzk hdes hP' hPs
  rw [← hdes] at hcp hpay
  have hip : tr.time ip = sp.ts p := hti
  have hcp₀ : tr.projAC.CallAt z ip ellp := by
    rw [RunTrace.upTo_projAC] at hcp
    exact ((Trace.upTo_callAt _).mp hcp).2
  have hzip : z ∈ H (tr.time ip) := hrun.antitone (by rw [hip]; linarith) hz
  have hpay₀ : (AC.acProposal sp (tr.projAC.state z ip) ellp.frame (tr.time ip)).2 =
      some (d, pay) := by
    have hst := Trace.upTo_state tr.projAC z (d := tr.time kP) (i := ip)
      (fun q hq => (hrun.time_mono hq.le).trans (by rw [hip, htime]))
    simp only [RunTrace.upTo_projAC, hst, Trace.upTo_time] at hpay
    exact hpay
  have hm₀ : gbar g ≤ sp.ts s₀ := by linarith
  have hdomP := (proposal_viable_at_cast_primed_at' hframe hrun hnc hsvc hf hnr hm₀ hsp hp0
    hpb hz hdes hP hPs hy hc hes).2
  have hHP : Anc (tr.HonestBlocksAt H) d.head P := by
    have hH : d.head ∈ ellp.frame.tree := by
      rw [(AC.acProposal_head hpay₀).2]
      exact AC.getHead_mem (rc.frameIn_at hnc hzip hcp₀).1
        (fun X (hX : X ∈ ellp.frame.viableTree ellp.frame.tree) => hX.1) _ _ _ _
    exact .single ⟨(rc.frameIn_at hnc hzip hcp₀).2 hH, hPhi.2 hdomP.1.1, hparent⟩
  rcases ho₀ with horigin | ⟨CV, hop⟩
  · obtain ⟨ell', hu⟩ : ∃ ell', AC.UpdateAt tr.projAC y a l.slot ell' := by
      rcases horigin with ⟨CV, ell', C, hu, _⟩ | ⟨ell', C, hu, _⟩ <;> exact ⟨ell', hu⟩
    have ht := hu.2.2.1
    change tr.time a = _ at ht
    have hgap : l.slot + 2 ≤ p := by
      by_contra hn
      have he : p = l.slot + 1 := by omega
      rw [he] at hhigh
      simp only [ACParams.ts] at ht hhigh
      push_cast at hhigh
      linarith
    have hDP := (Healing.PU.regular_later_heads_at hframe hrun hnc hsvc hawake
      hf hcatch hnr hlabel (by omega) (by omega) hm hgap hpb hya horigin hK p
      (by omega) le_rfl).2 hgap z ip ellp hzip hcp₀ hcallp hip d pay hpay₀
    exact hBA.trans (hAD.trans (hDP.trans hHP))
  have hts : sp.ts s₀ ≤ sp.ts l.slot := (AC.ts_le_iff sp).2 (by omega)
  have hlow : sp.ts l.slot ≤ tr.time a := by
    obtain ⟨_, _, _, hs', _⟩ := hop
    change sp.slot (tr.time a) = l.slot at hs'
    exact (AC.ts_le_iff_le_slot sp (hrun.time_nonneg a) _).2 (by rw [hs'])
  have halo := hts.trans hlow
  rcases (AC.viableAncestor_spec hW.1 hD).2.1 with hbelow | hAv
  · have hAw := hbelow.mono hW.2
    change Anc (tr.HonestBlocksAt H) A ellw.frame.fcRoot at hAw
    rw [rc.frame_of_projAC_at hya ha₀] at hAw
    have hrootP := hdomP.2.1.mono hPhi.2
    rw [rc.frame_of_projAC_at hy hc.1] at hrootP
    exact hBA.trans (hAw.trans ((fcRoot_mono_at' hrun hy hai.le).trans hrootP))
  obtain ⟨Q, hQ, hvQ, hAQ⟩ := hAv.2.2
  have hearly : tr.time a < sp.ts l.slot + 2 * sp.Δ := by
    obtain ⟨ell', A', hp, hsl, hsel, -⟩ := hop
    unfold AC.optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel with hn
    exact lt_of_not_ge (fun ht => hn (Or.inr (Or.inr (Or.inl (hsl ▸ ht)))))
  have hAP := (Shadow.PU.Growing.optimistic_later_heads_of_early_witness_at hrun hnc hsvc
    hawake hf hcatch hnr (hm₀.trans hts) hpb (hframe.mono hts le_rfl) hya hop hAD
    hya hlow hearly ha₀ hQ hvQ (hAQ.mono hW.2) hK p (by omega) le_rfl).2
    z ip ellp hzip hcp₀ hcallp hip d pay hpay₀
  exact hBA.trans (hAP.trans hHP)

/-- The stock passage conclusion over the shadow run and primed window. -/
theorem current_lock_passage_of_regular_base_primed_at' :
    P ∈ ell.frame.viableHeads ∧
      P ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame p) ∧
      (Anc (tr.HonestBlocksAt H) B P ∨
        (l.slot = p ∧ ∃ a ≤ i, ∃ D CV, y ∈ H (tr.time a) ∧
          AC.OptimisticLockAt tr.projAC y a p D CV ∧ sp.ts p ≤ tr.time a ∧
          Anc (tr.HonestBlocksAt H) B D)) := by
  have hm₀ : gbar g ≤ sp.ts s₀ := by linarith [sp.toParams.hΔ]
  obtain ⟨hvP, hdomP⟩ := proposal_viable_at_cast_primed_at' hframe hrun hnc hsvc hf hnr hm₀ hsp hp0
    hpb hz hdes hP hPs hy hc hes
  refine ⟨hvP, hdomP, ?_⟩
  by_cases hcurrent : p ≤ l.slot
  · obtain ⟨hs, a, hai, D, CV, hya, hop, ht, C, hC, hCr, hCD⟩ :=
      Core.current_lock_write_readPoint_at hrun.toCore hnc hy hc (hes ▸ hp0) hl
        (hes ▸ hcurrent)
    have hPhi := hrun.toCore.frameIn_at hnc hy hc.1
    have hcoh := hrun.toCore.coherent hnc
    obtain rfl : C = B := hcoh.1 hC (hPhi.2 hB) (hCr.trans hBr.symm)
    rw [hes] at hs hop ht
    exact Or.inr ⟨hs, a, hai, D, CV, hya, hop, ht, hCD⟩
  · exact Or.inl (older_lock_prefix_transfer_primed hframe hrun hnc hsvc hawake hf
      hcatch hnr hm hsp hp0 hpb hz hdes hP hPs hy hc hes hmargin hl hlive hB hBr hK
      (Nat.lt_of_not_ge hcurrent))

end Passage

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
