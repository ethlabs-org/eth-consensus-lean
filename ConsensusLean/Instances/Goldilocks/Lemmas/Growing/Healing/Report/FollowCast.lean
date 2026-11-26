module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowProposal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowFinality
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshVotesRelay
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Warm proposal viability at independently honest casts -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open AC (ACParams ReplayOrder Payload gbar)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
variable {hold : Time}

/-- The actual proposal is viable at an honest call in the frame window, once it is in the
caller's tree or the call is after its relay deadline, from any vote-permitted start. -/
theorem proposal_viable_at_call_at
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
  have hac := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  have hts : sp.ts s₀ ≤ sp.ts p := (AC.ts_le_iff sp).2 (by exact_mod_cast hsp)
  have hlow := hts.trans hpT
  have hpb : sp.ts p + sp.Δ ≤ b := hphi.trans hib
  have htime : tr.time kP = sp.ts p := by
    simpa only [sp.slotTime_eq, hPs, ACParams.ts] using hP.2.2
  have hzk : z ∈ H (tr.time kP) :=
    hrun.antitone (by rw [htime]; linarith [sp.toParams.hΔ]) hz
  have hP' : (tr.upTo (tr.time kP)).ProposesAt z kP P :=
    ⟨(RunTrace.upTo_ownBlockAt _).mpr ⟨le_rfl, hP.1⟩, hP.2⟩
  obtain ⟨_, ip, ellp, d, pay, hcp, hcall, hd, hti, hparent, _, _, _, ja, _, hacc, hta⟩ :=
    Healing.honestProposalRun_of_proposesAt (hrun.upTo (hrun.time_nonneg kP))
      (hnc.upTo _) hzk hdes hP' hPs
  rw [← hdes] at hcp hd hacc
  have hip : tr.time ip = sp.ts p := hti
  have hja : tr.time ja = sp.ts p := hta
  have hzip : z ∈ H (tr.time ip) := hrun.antitone (show tr.time ip ≤ sp.ts p + sp.Δ by
    rw [hip]; linarith [sp.toParams.hΔ]) hz
  have hzja : z ∈ H (tr.time ja) := hrun.antitone (show tr.time ja ≤ sp.ts p + sp.Δ by
    rw [hja]; linarith [sp.toParams.hΔ]) hz
  rw [RunTrace.upTo_projAC] at hcp hd hacc
  have hcp' := ((Trace.upTo_callAt tr.projAC).mp hcp).2
  have hstate := Trace.upTo_state tr.projAC z (d := tr.time kP) (i := ip)
    (fun q hq => (hrun.time_mono hq.le).trans (by rw [hip, htime]))
  have hd' : (AC.acProposal sp (tr.projAC.state z ip) ellp.frame (tr.time ip)).2 =
      some (d, pay) := by
    have hd'' := hd
    rw [hstate] at hd''
    exact hd''
  have hmf (t : Time) (ht0 : 0 ≤ t) (htb : t ≤ b) :
      (H t)ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hf' := hf t ht0 htb
    have hn := sp.toParams.hn
    change (H t)ᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  have hhead := proposal_parent_viable_full_frame_at hrun hnc hzip
    (hmf _ (hrun.time_nonneg ip) (by rw [hip]; linarith [sp.toParams.hΔ]))
    hcp' hcall (by rw [sp.slotTime_eq]; exact hip) hd'
  obtain ⟨ella, hca, hblock⟩ := hacc
  have hca' := ((Trace.upTo_callAt tr.projAC).mp hca).2
  have hra := hac.upTo (hrun.time_nonneg ja)
  have hca'' := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hca'⟩
  have hPt := (AC.accept_new sp hra.localRun hzja ⟨ella, hca'', hblock⟩).1 ella hca''
  have hfa : ella.frame = Node.frame (tr.state z ja) :=
    (hrun.cutLaw z ja (.ac ella) (Compose.projAC_callAt.mp hca') hzja).1
  have hfp : ellp.frame = Node.frame (tr.state z ip) :=
    (hrun.cutLaw z ip (.ac ellp) (Compose.projAC_callAt.mp hcp') hzip).1
  have hfi : ell.frame = Node.frame (tr.state y i) :=
    (hrun.cutLaw y i (.ac ell) (Compose.projAC_callAt.mp hc) hy).1
  rw [hfa] at hPt
  rw [hfp] at hhead
  have hHP : Anc (tr.HonestBlocksAt H) d.head P := .single
    ⟨⟨z, ip, _, hrun.time_nonneg ip, fun q hq => hrun.time_mono hq.le, hzip, hhead.1⟩,
     ⟨z, ja, _, hrun.time_nonneg ja, fun q hq => hrun.time_mono hq.le, hzja, hPt.1⟩,
     hparent⟩
  have hh : floor ≤ ((tr.state z ja).fg.σ P.root).h :=
    floor_le_of_honest_ancestor_at hrun hnc hzja hzip hhead.1
      (by rw [← hframe.floor_eq z ip hzip (hip ▸ hts)
            (by rw [hip]; linarith [sp.toParams.hΔ])]; exact hhead.2.2.2) hPt.1 hHP
  have hJ : kindJ → Anc (tr.HonestBlocksAt H) J P := by
    intro hk
    have hk' := (hframe.kind_iff z ip hzip (hip ▸ hts)
      (by rw [hip]; linarith [sp.toParams.hΔ])).mpr hk
    have hroot := honest_anc_of_store_anc_at (hrun.time_nonneg ip)
      (fun q hq => hrun.time_mono hq.le) hzip hhead.2.2.1
    change Anc _ (tr.state z ip).fg.fcRoot d.head at hroot
    rw [show (tr.state z ip).fg.fcRoot = (tr.state z ip).fg.J from ite_eq_left hk',
      hframe.root_eq z ip hzip (hip ▸ hts) (by rw [hip]; linarith [sp.toParams.hΔ]) hk] at hroot
    exact hroot.trans hHP
  have hFP : Anc (tr.HonestBlocksAt H) ell.frame.F P := by
    rw [hfi]
    exact hframe.finalized_below_descendant_at hrun hnc hy hzja hzja
      (hmf _ ((hrun.time_nonneg i).trans (le_max_left _ _))
        (max_le (hhigh.trans hib) (by rw [hja]; linarith [sp.toParams.hΔ])))
      hlow hhigh hPt.1 hh hJ hPt.1 .refl
  have hPy : P ∈ ell.frame.tree := by
    by_cases hearly' : tr.time i < sp.ts p + sp.Δ
    · exact hearly hearly'
    · have hri := hac.upTo (hrun.time_nonneg i)
      have hci := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, hc⟩
      obtain ⟨q, hqi, haq, _⟩ := accepted_relay_before_at hrun hsvc hnr hzja ⟨ella, hca', hblock⟩
        (by rw [hja]; exact hm.trans hts) hy hc (by rw [hja]; exact not_lt.mp hearly') hFP
      have haq' : ACTrace.AcceptAt (tr.projAC.upTo (tr.time i)) y q P := by
        obtain ⟨ellq, hcq, heq⟩ := haq
        exact ⟨ellq, (Trace.upTo_callAt _).mpr ⟨hrun.time_mono hqi, hcq⟩, heq⟩
      exact AC.mem_tree_of_acceptAt sp hri.localRun hy haq' hqi hci hFP
  obtain ⟨_, hroot, hv⟩ := floor_ancestor_mem_frame_at hrun hnc hy hzja
    (hmf _ (hrun.time_nonneg i) (hhigh.trans hib)) hPt.1
    (by rw [hframe.floor_eq y i hy hlow hhigh]; exact hh)
    (fun hm' hn => by
      have hk := (hframe.kind_iff y i hy hlow hhigh).mp ⟨hm', hn⟩
      rw [hframe.root_eq y i hy hlow hhigh hk]; exact hJ hk)
    (by rw [hfi] at hPy; exact hPy.1) .refl
  rw [← hfi] at hroot hv
  exact ⟨hPy, hroot, hv⟩

/-- The actual proposal is viable at a cast before its proposer's honesty deadline, from any
vote-permitted start. -/
theorem proposal_viable_at_cast_at
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
  have hri := (Compose.Growing.goldilocks_ac_projection_from hrun hnc).upTo (hrun.time_nonneg i)
  have hci := AC.upTo_castAt.mpr ⟨le_rfl, hc⟩
  have hslot : e.msg.slot = sp.slot (tr.time i) := (AC.castAt_spec hri.localRun hy hci).2.1
  have hslot' := hslot.symm.trans hes
  have hpT : sp.ts p ≤ tr.time i :=
    (AC.ts_le_iff_le_slot sp (hrun.time_nonneg i) _).2 (by rw [hslot'])
  have hhigh : tr.time i ≤ sp.ts p + sp.Δ := by
    have ht := AC.vote_time_le hri.localRun hy ⟨ell, hci⟩
    change tr.time i ≤ sp.ts (sp.slot (tr.time i)) + sp.Δ at ht
    rwa [hslot'] at ht
  obtain ⟨hPy, hroot, hv⟩ := proposal_viable_at_call_at hframe hrun hnc hsvc hf hnr hm hsp
    le_rfl hpb hz hdes hP hPs hy hc.1 hpT hhigh (fun hearly => by
      obtain ⟨⟨Q, hQ, hQs, _⟩, -⟩ :=
        AC.cast_readyU hri.localRun.toU hy hci (by rw [hes]; exact hearly)
      rw [hes] at hQs
      exact proposal_frame_unique_at hrun hnc hz hdes hP hPs hp0 hy hc.1 hhigh hQ hQs ▸ hQ)
  have hdom : P ∈ AC.voterBlockTree sp e.readPoint ell.frame p :=
    ⟨hPy, Or.inr ⟨P, hPy, hPs, .refl⟩⟩
  exact ⟨hv, hdom, hroot, P, hdom, hv, .refl⟩


end Consensus.Goldilocks.Healing.Growing.KernelProof

end
