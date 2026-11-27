module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.WitnessFloor
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.WitnessFamily
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.ViableHeadRoute
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesRelay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowProposal
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Warm proposal viability at honest casts over the stock window -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {hold : Time}

/-- The proposed child, rather than its P-U viable parent, reaches the stock window's floor. -/
theorem proposal_viable_at_call_at'
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    {g ΔF b hi : Time} {s₀ p floor : Nat} {kindJ : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) hi floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g ≤ sp.ts s₀) (hsp : s₀ ≤ p) (hphi : sp.ts p + sp.Δ ≤ hi) (hib : hi ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts p + sp.Δ)) (hdes : z = proposer p)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = p)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ell)
    (hpT : sp.ts p ≤ tr.time i) (hhigh : tr.time i ≤ hi)
    (hearly : tr.time i < sp.ts p + sp.Δ → P ∈ ell.frame.tree) :
    P ∈ ell.frame.tree ∧ ell.frame.Anc ell.frame.fcRoot P ∧ P ∈ ell.frame.viableHeads := by
  have rc := hrun.toCore
  have hac := Compose.Growing.goldilocks_ac_projection_from' hrun hnc
  have hts : sp.ts s₀ ≤ sp.ts p := (AC.ts_le_iff sp).2 (by exact_mod_cast hsp)
  have hlow := hts.trans hpT
  have htime : tr.time kP = sp.ts p := by
    simpa only [sp.slotTime_eq, hPs, ACParams.ts] using hP.2.2
  have hzk : z ∈ H (tr.time kP) :=
    hrun.antitone (by rw [htime]; linarith [sp.toParams.hΔ]) hz
  have hP' : (tr.upTo (tr.time kP)).ProposesAt z kP P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hP.1⟩, hP.2⟩
  obtain ⟨_, ip, ellp, d, pay, hcp, hcall, hd, hti, hparent, _, _, _, ja, _, hacc, hta⟩ :=
    Coherence.honestProposalRun_of_proposesAt (hrun.upTo (hrun.time_nonneg kP))
      (hnc.upTo _) hzk hdes hP' hPs
  rw [← hdes] at hacc
  have hja : tr.time ja = sp.ts p := hta
  have hzja : z ∈ H (tr.time ja) := hrun.antitone (by
    rw [hja]; linarith [sp.toParams.hΔ]) hz
  rw [RunTrace.upTo_projAC] at hacc
  obtain ⟨ella, hca, hblock⟩ := hacc
  have hca' := ((Trace.upTo_callAt tr.projAC).mp hca).2
  have hra := hac.upTo (hrun.time_nonneg ja)
  have hca'' := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hca'⟩
  have hPt := (AC.accept_new sp hra.localRun hzja ⟨ella, hca'', hblock⟩).1 ella hca''
  have hfa := Goldilocks.Shadow.PU.Growing.frame_of_projAC_at hrun hzja hca'
  have hfi := Goldilocks.Shadow.PU.Growing.frame_of_projAC_at hrun hy hc
  rw [hfa, Node.frame_eq, Store.toFrame_tree] at hPt
  have hPm := (Coherence.accept_of_proposesAt (hrun.upTo (hrun.time_nonneg kP))
    (hnc.upTo _) hzk hP').2.1
  rw [Trace.upTo_state tr z (fun q hq => hrun.time_mono (by omega))] at hPm
  have hσ := σ_eq_honest_at hrun hnc (hrun.time_nonneg kP)
    (fun q hq => hrun.time_mono (by omega)) hzk (hrun.time_nonneg ja)
    (fun q hq => hrun.time_mono hq.le) hzja hPm hPt.1
  have hmf (t : Time) (ht0 : 0 ≤ t) (htb : t ≤ b) :
      (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hf' := hf t ht0 htb
    have hn := sp.toParams.hn
    change (H t)ᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  have hzp : z ∈ H (sp.ts p) := htime ▸ hzk
  obtain ⟨hh, hstrict⟩ := Goldilocks.Shadow.PU.Witness.warm_proposal_bounds_at
    hrun hnc hframe hzp hdes hP hPs hts (by linarith [sp.toParams.hΔ])
    (hmf _ (by rw [← htime]; exact hrun.time_nonneg kP)
      (by linarith only [hphi.trans hib, sp.toParams.hΔ]))
  rw [hσ] at hh hstrict
  have hreach := Compose.Growing.reachable_at hrun (hrun.time_nonneg i) hy
    (fun q hq => hrun.time_mono hq.le)
  have hj := Store.hj_lt_hmax_of_reachable_with Store.finalitySpec_updateFinality
    hreach.reachableWith
  have hfl := hframe.floor_eq y i hy hlow hhigh
  have hkind := hframe.kind_iff y i hy hlow hhigh
  have hgt : (tr.state y i).fg.hj < ((tr.state z ja).fg.σ P.root).h := by
    by_cases hk : kindJ
    · obtain ⟨hm', hc'⟩ := hkind.mpr hk
      rw [Store.headHeightFloor, ite_eq_right hc', hm'] at hfl
      have := hstrict hk
      omega
    · have hnk := hkind.not.mpr hk
      by_cases hc' : (tr.state y i).fg.Contest
      · rw [Store.headHeightFloor, ite_eq_left hc'] at hfl
        omega
      · rw [Store.headHeightFloor, ite_eq_right hc'] at hfl
        have hne : (tr.state y i).fg.hmax ≠ (tr.state y i).fg.hj + 1 :=
          fun hm' => hnk ⟨hm', hc'⟩
        omega
  have hFP := finalized_below_of_hj_lt_at hrun hnc hy hzja
    (hmf _ ((hrun.time_nonneg i).trans (le_max_left _ _))
      (max_le (hhigh.trans hib) (by rw [hja]; linarith [sp.toParams.hΔ]))) hPt.1 hgt
  have hFP' : Anc (tr.HonestBlocksAt H) ell.frame.F P := by
    rw [hfi, Node.frame_eq, Store.toFrame_F]
    exact hFP
  have hPy : P ∈ ell.frame.tree := by
    by_cases hearly' : tr.time i < sp.ts p + sp.Δ
    · exact hearly hearly'
    · have hri := hac.upTo (hrun.time_nonneg i)
      have hci := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc⟩
      obtain ⟨q, hqi, haq, _⟩ := Core.accepted_relay_before_at rc hsvc hnr hzja
        ⟨ella, hca', hblock⟩ (by rw [hja]; exact hm.trans hts) hy hc
        (by rw [hja]; exact not_lt.mp hearly') hFP'
      have haq' : ACTrace.AcceptAt (tr.projAC.upTo (tr.time i)) y q P := by
        obtain ⟨ellq, hcq, heq⟩ := haq
        exact ⟨ellq, (Trace.upTo_callAt _).mpr ⟨hrun.time_mono hqi, hcq⟩, heq⟩
      exact AC.mem_tree_of_acceptAtU sp hri.localRun.toU hy haq' hqi hci hFP'
  have hPyi : P ∈ (tr.state y i).fg.tree := by
    rw [hfi, Node.frame_eq, Store.toFrame_tree] at hPy
    exact hPy.1
  have hσy := σ_eq_honest_at hrun hnc (hrun.time_nonneg ja)
    (fun q hq => hrun.time_mono hq.le) hzja (hrun.time_nonneg i)
    (fun q hq => hrun.time_mono hq.le) hy hPt.1 hPyi
  rw [hσy] at hh hstrict
  have hv := Store.isViable_of_floor (tr.state y i).fg hj (Q := P) (by rwa [hfl])
    (fun hm' hc' => Or.inl (by rw [hfl]; exact hstrict (hkind.mp ⟨hm', hc'⟩)))
  have hstore := store_anc_of_honest_anc_at hrun hnc (hrun.time_nonneg i)
    (fun q hq => hrun.time_mono hq.le) hy hFP hPyi
  refine ⟨hPy, ?_, ?_⟩
  · rw [hfi, Node.frame_eq, Store.toFrame_fcRoot]
    change Anc (tr.state y i).fg.toFrame.tree _ _
    rw [Store.toFrame_tree]
    exact Anc.restrict .refl hstore
  · rw [hfi, Node.frame_eq, Store.toFrame_viableHeads]
    exact ⟨hPyi, hstore, hv⟩

/-- The actual proposal remains viable at an independently honest cast, with the stock window
and conclusion. No floor bound on its parent is required. -/
theorem proposal_viable_at_cast_at'
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    {g ΔF b : Time} {s₀ p floor : Nat} {kindJ : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts p + sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g ≤ sp.ts s₀) (hsp : s₀ ≤ p) (hp0 : 0 < p)
    (hpb : sp.ts p + sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts p + sp.Δ)) (hdes : z = proposer p)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = p)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {e : AC.Em sp (List (FG.Att sp.n))}
    (hc : AC.CastAt tr.projAC y i ell e) (hes : e.msg.slot = p) :
    P ∈ ell.frame.viableHeads ∧
      P ∈ ell.frame.viableTree (AC.voterBlockTree sp e.readPoint ell.frame p) := by
  have hri := (Compose.Growing.goldilocks_ac_projection_from' hrun hnc).upTo
    (hrun.time_nonneg i)
  have hci := AC.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hslot : e.msg.slot = sp.slot (tr.time i) := (AC.castAt_specU hri.localRun.toU hy hci).2.1
  have hslot' := hslot.symm.trans hes
  have hpT : sp.ts p ≤ tr.time i :=
    (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).2 (by rw [hslot'])
  have hhigh : tr.time i ≤ sp.ts p + sp.Δ := by
    have ht := AC.vote_time_leU hri.localRun.toU hy ⟨ell, hci⟩
    change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at ht
    rwa [hslot'] at ht
  obtain ⟨hPy, hroot, hv⟩ := proposal_viable_at_call_at' hframe hrun hnc hsvc hf hnr hm hsp
    le_rfl hpb hz hdes hP hPs hy hc.1 hpT hhigh (fun hearly => by
      obtain ⟨⟨Q, hQ, hQs, _⟩, -⟩ :=
        AC.cast_readyU hri.localRun.toU hy hci (by rw [hes]; exact hearly)
      rw [hes] at hQs
      exact Core.proposal_frame_unique_at hrun.toCore hnc hz hdes hP hPs hp0 hy hc.1
        hhigh hQ hQs ▸ hQ)
  have hdom : P ∈ AC.voterBlockTree sp e.readPoint ell.frame p :=
    ⟨hPy, Or.inr ⟨P, hPy, hPs, .refl⟩⟩
  exact ⟨hv, hdom, hroot, P, hdom, hv, .refl⟩

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
