module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.WitnessFamily
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.WitnessFloor
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.RunCore
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowProposal
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesRelay
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Proposal viability over the P-U frame window -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {hold : Time}

/-- The viable proposal parent transfers its primed-window witness to its child. -/
theorem proposal_window_witness
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {lo hi : Time} {M u : Nat} {isTop : Prop}
    {J B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hwin : Generic.FrameWindow tr H lo hi M isTop J)
    {z : Fin sp.n} {kB : Nat} (hz : z ∈ H (sp.ts u)) (hdes : z = proposer u)
    (hB : tr.ProposesAt z kB B) (hBs : B.slot = u)
    (hlo : lo ≤ sp.ts u) (hhi : sp.ts u ≤ hi)
    (hf : (H (sp.ts u))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n) :
    M - 1 ≤ ((tr.state z (kB + 1)).fg.σ B.root).h ∧
      (isTop → ((tr.state z (kB + 1)).fg.σ B.root).h = M - 1 →
        Anc (tr.HonestBlocksAt H) J B) := by
  have htime : tr.time kB = sp.ts u := by
    simpa only [sp.slotTime_eq, hBs, ACParams.ts] using hB.2.2
  have hzk : z ∈ H (tr.time kB) := htime ▸ hz
  have ht := hrun.time_nonneg kB
  have hr := hrun.upTo ht
  have hB' : (tr.upTo (tr.time kB)).ProposesAt z kB B :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hB.1⟩, hB.2.1, hB.2.2⟩
  obtain ⟨_, ip, ell, d, pay, hc, hcall, hd, hti, hpar, _⟩ :=
    Coherence.honestProposalRun_of_proposesAt hr (hnc.upTo _) hzk hdes hB' hBs
  rw [← hdes] at hc hd
  have hip : tr.time ip = sp.ts u := hti
  have hzi : z ∈ H (tr.time ip) := hip ▸ hz
  have hleip : ∀ q < ip, tr.time q ≤ tr.time kB := by
    intro q hq
    exact (hrun.time_mono hq.le).trans (by rw [hip, htime])
  have hleB : ∀ q < kB + 1, tr.time q ≤ tr.time kB :=
    fun q hq => hrun.time_mono (by omega)
  have hfr := Node.frame_of_projAC_at hr.toLocalRun hzk hc
  have hfr' : ell.frame = Node.frame (tr.state z ip) := by
    rw [Trace.upTo_state tr z hleip] at hfr
    exact hfr
  obtain ⟨Q, hQ, hv, hroot⟩ := Shadow.full_frame_viable_witness_at hrun hnc hzi (hip ▸ hf)
  rw [← hfr'] at hQ hv hroot
  have hac := (Compose.goldilocks_ac_projection_from hr (hnc.upTo _)).localRun
  have hvd := Healing.proposal_head_viable hac hr.vstart hzk hc hcall
    (by rw [sp.slotTime_eq]; exact hti) hd
    ⟨(AC.frameIn_of_callAt hac hzk hc).1.fcRoot_mem, .refl, Q, hQ, hv, hroot⟩
  rw [hfr, Node.frame_eq, Store.toFrame_viableHeads] at hvd
  obtain ⟨hDm, _, hDv⟩ := hvd
  have hBm : B ∈ ((tr.upTo (tr.time kB)).state z (kB + 1)).fg.tree :=
    (Coherence.accept_of_proposesAt hr (hnc.upTo _) hzk hB').2.1
  have hDhist : d.head ∈ (tr.upTo (tr.time kB)).HonestBlocks (H (tr.time kB)) :=
    ⟨z, hzk, ip, hDm⟩
  have hBhist : B ∈ (tr.upTo (tr.time kB)).HonestBlocks (H (tr.time kB)) :=
    ⟨z, hzk, kB + 1, hBm⟩
  have hDB : Anc ((tr.upTo (tr.time kB)).HonestBlocks (H (tr.time kB))) d.head B :=
    .single ⟨hDhist, hBhist, hpar⟩
  have hDBs := Coherence.honest_held_anc' hr (hnc.upTo _) hzk hDB hBm
  have hDpost : d.head ∈ ((tr.upTo (tr.time kB)).state z (kB + 1)).fg.tree := by
    by_cases he : d.head = B
    · exact he ▸ hBm
    · exact (Anc.mem hDBs he).1
  have hσ := Store.σ_eq_of_mem_with
    (Node.fg_reachable_at hr.toLocalRun hzk ip).reachableWith
    Store.finalitySpec_updateFinality
    (Node.fg_reachable_at hr.toLocalRun hzk (kB + 1)).reachableWith
    (Coherence.honest_blocks_coherent hr.toLocalRun (hnc.upTo _)).1
    (fun _ hm => ⟨z, hzk, ip, hm⟩) (fun _ hm => ⟨z, hzk, kB + 1, hm⟩) hDm hDpost
  have hh := (Coherence.honest_held_height' hr (hnc.upTo _) hzk hDBs).1
  rw [← hσ] at hh
  have hM : ((tr.upTo (tr.time kB)).state z ip).fg.hmax = M := by
    rw [Trace.upTo_state tr z hleip]
    exact hwin.M_eq z ip hzi (hip ▸ hlo) (hip ▸ hhi)
  have hpred : M - 1 ≤
      (((tr.upTo (tr.time kB)).state z ip).fg.σ d.head.root).h := by
    rw [Store.isViable_iff] at hDv
    rcases hDv with hh | ⟨hh, _⟩ <;> omega
  have hheight := hpred.trans hh
  rw [Trace.upTo_state tr z hleB] at hheight
  refine ⟨hheight, ?_⟩
  intro htop heq
  have htop' : ((tr.upTo (tr.time kB)).state z ip).fg.hmax =
      ((tr.upTo (tr.time kB)).state z ip).fg.hj + 1 := by
    rw [Trace.upTo_state tr z hleip]
    exact (hwin.top_iff z ip hzi (hip ▸ hlo) (hip ▸ hhi)).2 htop
  have hJ : ((tr.upTo (tr.time kB)).state z ip).fg.J = J := by
    rw [Trace.upTo_state tr z hleip]
    exact hwin.root_eq z ip hzi (hip ▸ hlo) (hip ▸ hhi) htop
  rw [Trace.upTo_state tr z hleB, heq] at hh
  have hJD : ((tr.upTo (tr.time kB)).state z ip).fg.Anc J d.head := by
    rw [Store.isViable_iff] at hDv
    rcases hDv with hh | ⟨hh, hgap | hJD⟩
    · omega
    · omega
    · exact hJ ▸ hJD
  have hJD' : Anc ((tr.upTo (tr.time kB)).HonestBlocks (H (tr.time kB))) J d.head :=
    Anc.mono (fun _ hm => ⟨z, hzk, ip, hm⟩) hJD
  exact Anc.mono (RunTrace.honestBlocks_upTo_subset hrun.time_mono ht) (hJD'.trans hDB)

/-- Relay or early membership preserves the primed proposal witness at an honest call. -/
theorem proposal_viable_at_call_with_early_at
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    {g ΔF b hi : Time} {u M : Nat} {isTop : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts u) hi M isTop J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hnr : NoRestartAfter tr H (gbar g)) (hgu : gbar g ≤ sp.ts u)
    (hphi : sp.ts u + sp.Δ ≤ hi) (hib : hi ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ell)
    (hlo : sp.ts u ≤ tr.time i) (hhi : tr.time i ≤ hi)
    (hearly : tr.time i < sp.ts u + sp.Δ → P ∈ ell.frame.tree) :
    P ∈ ell.frame.tree ∧ ell.frame.Anc ell.frame.fcRoot P ∧ P ∈ ell.frame.viableHeads := by
  have hac := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  have htime : tr.time kP = sp.ts u := by
    simpa only [sp.slotTime_eq, hPs, ACParams.ts] using hP.2.2
  have hzk : z ∈ H (tr.time kP) :=
    hrun.antitone (by rw [htime]; linarith [sp.toParams.hΔ]) hz
  have hP' : (tr.upTo (tr.time kP)).ProposesAt z kP P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hP.1⟩, hP.2⟩
  obtain ⟨_, ip, ellp, d, pay, hcp, hcall, hd, hti, hparent, _, _, _, ja, _, hacc, hta⟩ :=
    Coherence.honestProposalRun_of_proposesAt (hrun.upTo (hrun.time_nonneg kP))
      (hnc.upTo _) hzk hdes hP' hPs
  rw [← hdes] at hacc
  have hja : tr.time ja = sp.ts u := hta
  have hzja : z ∈ H (tr.time ja) := hja ▸ (htime ▸ hzk)
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
  have hw := proposal_window_witness hrun hnc hframe (htime ▸ hzk) hdes hP hPs le_rfl
    (by linarith [sp.toParams.hΔ])
    (hmf _ (by rw [← htime]; exact hrun.time_nonneg kP)
      (by linarith only [hphi.trans hib, sp.toParams.hΔ]))
  rw [hσ] at hw
  have hlow : sp.ts u ≤ tr.time i := by linarith [sp.toParams.hΔ]
  have hFP := Generic.FrameWindow.finalized_below_descendant_at
    hframe hrun hnc hy hzja hzja
    (hmf _ ((hrun.time_nonneg i).trans (le_max_left _ _))
      (max_le (hhi.trans hib) (by rw [hja]; linarith [sp.toParams.hΔ])))
    hlow hhi hPt.1 hw hPt.1 .refl
  have hFP' : Anc (tr.HonestBlocksAt H) ell.frame.F P := by
    rw [hfi, Node.frame_eq, Store.toFrame_F]
    exact hFP
  have hri := hac.upTo (hrun.time_nonneg i)
  have hci := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc⟩
  have hPy : P ∈ ell.frame.tree := by
    by_cases ht : tr.time i < sp.ts u + sp.Δ
    · exact hearly ht
    obtain ⟨q, hqi, haq, _⟩ := Core.accepted_relay_before_at hrun.toCore hsvc hnr hzja
      ⟨ella, hca', hblock⟩ (by rw [hja]; exact hgu) hy hc
      (by rw [hja]; exact not_lt.mp ht) hFP'
    have haq' : ACTrace.AcceptAt (tr.projAC.upTo (tr.time i)) y q P := by
      obtain ⟨ellq, hcq, heq⟩ := haq
      exact ⟨ellq, (Trace.upTo_callAt _).mpr ⟨hrun.time_mono hqi, hcq⟩, heq⟩
    exact AC.mem_tree_of_acceptAtU sp hri.localRun.toU hy haq' hqi hci hFP'
  have hPyi : P ∈ (tr.state y i).fg.tree := by
    rw [hfi, Node.frame_eq, Store.toFrame_tree] at hPy
    exact hPy.1
  have hv := (windowWitness_of_frameWindow
    hrun hnc hframe hzja hPt.1 hw).held y i hy hlow hhi
      (hmf _ (hrun.time_nonneg i) (hhi.trans hib)) hPyi
  have hstore := store_anc_of_honest_anc_at hrun hnc (hrun.time_nonneg i)
    (fun q hq => hrun.time_mono hq.le) hy hFP hPyi
  refine ⟨hPy, ?_, ?_⟩
  · rw [hfi, Node.frame_eq, Store.toFrame_fcRoot]
    change Anc (tr.state y i).fg.toFrame.tree _ _
    rw [Store.toFrame_tree]
    exact Anc.restrict .refl hstore
  · rw [hfi, Node.frame_eq, Store.toFrame_viableHeads]
    exact ⟨hPyi, hstore, hv.2⟩

/-- Late calls obtain proposal membership from relay. -/
theorem proposal_viable_at_call_primed_at'
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    {g ΔF b hi : Time} {u M : Nat} {isTop : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts u) hi M isTop J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b hold)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hnr : NoRestartAfter tr H (gbar g)) (hgu : gbar g ≤ sp.ts u)
    (hphi : sp.ts u + sp.Δ ≤ hi) (hib : hi ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt y i ell)
    (hlo : sp.ts u + sp.Δ ≤ tr.time i) (hhi : tr.time i ≤ hi) :
    P ∈ ell.frame.tree ∧ ell.frame.Anc ell.frame.fcRoot P ∧ P ∈ ell.frame.viableHeads := by
  exact proposal_viable_at_call_with_early_at hframe hrun hnc hsvc hf hnr hgu hphi hib
    hz hdes hP hPs hy hc (by linarith [sp.toParams.hΔ]) hhi
    (fun h => absurd h (not_lt.mpr hlo))

/-- An honest cast retains the proposal in its voter-domain viable tree. -/
theorem proposal_viable_at_cast_primed_at'
    {ini : Fin sp.n → (goldilocksNode sp ro).State}
    {g ΔF b : Time} {s₀ p M : Nat} {isTop : Prop}
    {J P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hframe : Generic.FrameWindow tr H (sp.ts s₀) (sp.ts p + sp.Δ) M isTop J)
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
  have hri := (Compose.Growing.goldilocks_ac_projection_from hrun hnc).upTo
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
  have hts : sp.ts s₀ ≤ sp.ts p := (AC.ts_le_iff sp).2 (by exact_mod_cast hsp)
  obtain ⟨hPy, hroot, hv⟩ := proposal_viable_at_call_with_early_at
    (hframe.mono hts le_rfl) hrun hnc hsvc hf hnr (hm.trans hts) le_rfl hpb
    hz hdes hP hPs hy hc.1 hpT hhigh (fun hearly => by
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
