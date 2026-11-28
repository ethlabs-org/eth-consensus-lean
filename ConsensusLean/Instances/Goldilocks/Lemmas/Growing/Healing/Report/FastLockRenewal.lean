module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Local
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Prot
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PrefixBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshUpdate
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshUnlock
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowLocal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.LockFloorFast
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.ConfirmedBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Update
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.FastExpiry
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Fast-update facts over the concrete growing run -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}
  {ini : Fin sp.n → (goldilocksNode sp).State}
variable {hold : Time}

private theorem vote_extends_upTo
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) {d : Time} (hd : 0 ≤ d) {x : Fin sp.n} (hx : x ∈ H d)
    {k : Nat} {e : AC.Em sp (List (FG.Att sp.n))} (hv : AC.VoteAt (tr.projAC.upTo d) x k e)
    {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hext : AC.VoteExtends (tr.HonestBlocksAt H) e.msg B) :
    AC.VoteExtends ((tr.upTo d).HonestBlocks (H d)) e.msg B := by
  have hr := (Compose.Growing.acRun_upTo hrun hnc hd).localRun
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have subU := Compose.Growing.upTo_subset hrun hd
  obtain ⟨ell, hc⟩ := hv
  obtain ⟨⟨Hd, hHd, hHdr, -⟩, -⟩ := Compose.cast_head_fcRoot hr hrun.vstart hx hc
  have hHdU := (AC.frameIn_of_callAt hr hx hc.1).2 hHd
  obtain ⟨W, hW, hWr, hBW⟩ := hext
  obtain rfl : W = Hd := hU.1 hW (subU hHdU) (hWr.trans hHdr.symm)
  exact ⟨W, hHdU, hWr, RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hd hHdU hBW⟩

/-- The later-slot update selects above a block extended by every honest slot vote,
when the block lies above the honest finalized tips. -/
theorem update_result_extends_of_finalized_at {K : AC.CommitteeDict sp.n}
    {lo hi : Time}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartUpTo tr H (gbar g) b)
    {s : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts (s + 1 : Nat))
    (hjoin : ∀ x, x ∈ H (sp.ts (s + 1 : Nat) + sp.Δ) →
      AC.JoinedAt tr.projAC x (sp.ts (s + 1 : Nat) + sp.Δ))
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hfin : ∀ x q, x ∈ H (tr.time q) → lo ≤ tr.time q → tr.time q ≤ hi → tr.time q ≤ b →
      Anc (tr.HonestBlocksAt H) (tr.state x q).fg.F P) (hPg : P.root ≠ sp.genesisRoot)
    (hext : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e → e.msg.slot = s + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} (hu : AC.UpdateAt tr.projAC y k (s + 1) ell)
    (hklo : lo ≤ tr.time k) (hkhi : tr.time k ≤ hi) (hkb : tr.time k ≤ b)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∃ C, AC.getConfirmation sp (tr.projAC.state y k) ell.frame (s + 1) = some C ∧
      Anc (tr.HonestBlocksAt H) P C ∧
      ∃ D, AC.fastSelect sp (tr.projAC.state y k) ell.frame (s + 1) C = some D ∧
        Anc (tr.HonestBlocksAt H) P D := by
  have hmono := hrun.time_mono
  have hΔ := sp.toParams.hΔ
  have hk0 := hrun.time_nonneg k
  have htime : tr.time k = sp.ts (s + 1 : Nat) + 6 * sp.Δ := hu.2.2.1
  have hS := hK.healthy_base_before_at hrun hnc hsvc hawake hf hcatch hk0 hkb
  have hr := hS.run.localRun
  have hsub := Compose.Growing.upTo_subset hrun hk0
  have hu' : AC.UpdateAt (tr.projAC.upTo (tr.time k)) y k (s + 1) ell :=
    (AC.upTo_updateAt hmono).mpr ⟨le_rfl, hu⟩
  have hst : (tr.projAC.upTo (tr.time k)).state y k = tr.projAC.state y k :=
    Trace.upTo_state _ y fun _ hq => hmono hq.le
  have hrestart : ∀ q, ACTrace.RestartAt (tr.projAC.upTo (tr.time k)) y q →
      tr.time q ≤ gbar g := by
    intro q hq
    obtain ⟨hqD, hq⟩ := (ACTrace.upTo_restartAt (A := AC.goldilocksAC sp _)).mp hq
    exact noRestartUpTo_iff.mp hnr y q (hrun.antitone hqD hy) (Compose.projAC_restartAt.mp hq)
      (hqD.trans hkb)
  have hrs : ∀ q ≤ k, ACTrace.RestartAt (tr.projAC.upTo (tr.time k)) y q →
      (tr.projAC.upTo (tr.time k)).time q < sp.ts (s + 1 : Nat) :=
    fun q _ hq => (hrestart q hq).trans_lt (by linarith)
  have hdl : ∀ q ≤ k, ∀ t, gbar g ≤ t →
      ACTrace.deadline (A := AC.goldilocksAC sp _) (tr.projAC.upTo (tr.time k)) y q t ≤
        max t (sp.ts (s + 1 : Nat)) + sp.Δ :=
    fun _ _ t _ => Compose.ac_deadline_le_of_restarts (a := sp.ts (s + 1 : Nat))
      (fun q _ hq => (hrestart q hq).trans (by linarith)) t
  have hext' : ∀ x ∈ H (tr.time k), ∀ q e, AC.VoteAt (tr.projAC.upTo (tr.time k)) x q e →
      e.msg.slot = s + 1 →
        AC.VoteExtends ((tr.upTo (tr.time k)).HonestBlocks (H (tr.time k))) e.msg P := by
    intro x hx q e hv hes
    obtain ⟨hqD, hv'⟩ := AC.upTo_voteAt.mp hv
    exact vote_extends_upTo hrun hnc hk0 hx hv (hext x q e (hrun.antitone hqD hx) hv' hes)
  have hfr := Compose.Growing.frame_of_projAC_at hrun hy hu.1
  have hFe : ell.frame.F = (tr.state y k).fg.F := by rw [hfr]; rfl
  have hF : ∀ x ∈ H (tr.time k), ∀ q e, AC.VoteAt (tr.projAC.upTo (tr.time k)) x q e →
      e.msg.slot = s + 1 → ∀ B ∈ (tr.upTo (tr.time k)).HonestBlocks (H (tr.time k)),
        B.root = e.msg.head →
          Anc ((tr.upTo (tr.time k)).HonestBlocks (H (tr.time k))) ell.frame.F B := by
    intro x hx q e hv hes B hB hBr
    obtain ⟨hqD, hv'⟩ := AC.upTo_voteAt.mp hv
    obtain ⟨W, hW, hWr, hPW⟩ := hext x q e (hrun.antitone hqD hx) hv' hes
    obtain rfl : B = W :=
      (Compose.Growing.honest_blocks_coherent hrun hnc).1 (hsub hB) hW (hBr.trans hWr.symm)
    rw [hFe]
    exact RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hk0 hB
      ((hfin y k hy hklo hkhi hkb).trans hPW)
  have hPhi := (AC.frameIn_of_callAt hr hy hu'.1).1
  have hlate : sp.ts (s + 1 : Nat) + 2 * sp.Δ ≤ (tr.projAC.upTo (tr.time k)).time k := by
    change _ ≤ tr.time k
    rw [htime]; linarith
  have receipt : ∀ x ∈ H (tr.time k), ∀ q e, AC.VoteAt (tr.projAC.upTo (tr.time k)) x q e →
      e.msg.slot = s + 1 → e.msg ∈ (tr.projAC.state y k).pool (s + 1) ∧
        AC.resolutionTime (tr.projAC.state y k) ell.frame e.msg <
          AC.ETime.of (sp.ts (s + 1 : Nat) + 2 * sp.Δ) := by
    intro x hx q e hv hes
    obtain ⟨E, hE, hEr, hEu, hmem, hvs, hbs⟩ := AC.late_vote_held_of_frame_before hS hy hu'.1
      hm hlate le_rfl hdl hrs hx hv hes (hF x hx q e hv hes)
    rw [hst] at hmem hvs hbs
    exact ⟨hmem, AC.resolutionTime_lt_of hPhi hE hEr (hes ▸ hEu) hvs hbs⟩
  have hres : ∀ v ∈ ((tr.projAC.upTo (tr.time k)).state y k).pool (s + 1),
      v.val ∈ H (tr.time k) →
      AC.resolutionTime ((tr.projAC.upTo (tr.time k)).state y k) ell.frame v <
        AC.ETime.of (sp.ts (s + 1 : Nat) + 2 * sp.Δ) := by
    intro v hv hvH
    obtain ⟨q, _, e, he, rfl⟩ := hS.run.honest.pool_vote y hy k (s + 1) v hv hvH
    rw [hst]
    exact (receipt _ hvH q e he (AC.state_pool_slotU sp hr.toU hS.run.vstart hy k (s + 1) _ hv)).2
  have hdl1 : sp.ts (s + 1 : Nat) + sp.Δ ≤ tr.time k := by rw [htime]; linarith
  have hS0 := hK.healthy_base_before_at hrun hnc hsvc hawake hf hcatch
    (show 0 ≤ sp.ts (s + 1 : Nat) + sp.Δ by linarith [AC.gbar_nonneg g]) (hdl1.trans hkb)
  have hvotes := honest_votes_of_joined_before_at hS0 (by linarith) hjoin
  have hH : K.committee (s + 1) ∩ H (tr.time k) ⊆
      {v | v ∈ H (tr.time k) ∧ ∃ vote ∈ ((tr.projAC.upTo (tr.time k)).state y k).pool
        (s + 1), vote.val = v} := by
    rintro x ⟨hxK, hx⟩
    obtain ⟨q, e, ⟨ellq, hcast⟩, hes, hq⟩ := hvotes x (hrun.antitone hdl1 hx) hxK
    have hv : AC.VoteAt (tr.projAC.upTo (tr.time k)) x q e :=
      AC.upTo_voteAt.mpr ⟨hq.trans hdl1, ellq, hcast⟩
    refine ⟨hx, e.msg, ?_,
      (AC.castAt_specU hr.toU hx (AC.upTo_castAt.mpr ⟨hq.trans hdl1, hcast⟩)).1⟩
    rw [hst]
    exact (receipt x hx q e hv hes).1
  have hcount := Set.ncard_le_ncard hH
  have hcs := hS.cs2 (s + 1) (by linarith) (by linarith)
  have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard
    (K.committee (s + 1)) (H (tr.time k)) (Set.toFinite _)
  rw [hS.hsize, Set.sdiff_eq_compl_inter, Set.inter_comm (H (tr.time k))ᶜ] at hsplit
  obtain ⟨C, hconf, hPC, hD⟩ := AC.update_extends_of_resolved_votes hS.run K
    (fun v hv => hS.hP.1 y hy k (s + 1) v hv) hcs hext' hy hu' (by omega) hres
  obtain ⟨D, hfs, hPD⟩ := hD hPg
  rw [hst] at hconf hfs
  exact ⟨C, hconf, hPC.mono hsub, D, hfs, hPD.mono hsub⟩

/-- Every stored label at the later-slot update is compatible with the common vote floor. -/
theorem update_locks_compatible_of_finalized_at {K : AC.CommitteeDict sp.n}
    {lo hi : Time}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g ΔF b : Time} (hsvc : ResetService tr H g ΔF b hold)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartUpTo tr H (gbar g) b)
    {s : Nat} (hm : gbar g + 4 * sp.Δ ≤ sp.ts (s + 1 : Nat)) (hlo : lo ≤ sp.ts (s + 1 : Nat))
    (hjoin : ∀ x, x ∈ H (sp.ts (s + 1 : Nat) + sp.Δ) →
      AC.JoinedAt tr.projAC x (sp.ts (s + 1 : Nat) + sp.Δ))
    {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hfin : ∀ x q, x ∈ H (tr.time q) → lo ≤ tr.time q → tr.time q ≤ hi → tr.time q ≤ b →
      Anc (tr.HonestBlocksAt H) (tr.state x q).fg.F P) (hPg : P.root ≠ sp.genesisRoot)
    (hext : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e → e.msg.slot = s + 1 →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    (hext₁ : ∀ x i e, x ∈ H (tr.time i) → AC.VoteAt tr.projAC x i e → e.msg.slot = s + 2 →
      AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} (hu : AC.UpdateAt tr.projAC y k (s + 1) ell)
    (hkhi : tr.time k ≤ hi) (hkb : tr.time k ≤ b)
    (hK : CommitteeHalfUpTo tr H K g b) :
    ∀ l ∈ (tr.projAC.state y k).locks, ∀ L ∈ tr.HonestBlocksAt H, L.root = l.block →
      Compatible (tr.HonestBlocksAt H) L P := by
  have hmono := hrun.time_mono
  have hΔ := sp.toParams.hΔ
  have hk0 := hrun.time_nonneg k
  have hstep : sp.ts (s + 2 : Nat) = sp.ts (s + 1 : Nat) + 4 * sp.Δ := by
    simp only [ACParams.ts]; push_cast; ring
  have htime : tr.time k = sp.ts (s + 1 : Nat) + 6 * sp.Δ := hu.2.2.1
  have hgu : gbar g ≤ sp.ts (s + 1 : Nat) := by linarith
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hS := hK.healthy_base_before_at hrun hnc hsvc hawake hf hcatch hk0 hkb
  have hr := hS.run.localRun
  have hsub := Compose.Growing.upTo_subset hrun hk0
  have hst := Trace.upTo_state tr.projAC y (d := tr.time k) (i := k) (fun q hq => hmono hq.le)
  have hslot : sp.slot (tr.time k) = s + 2 := by
    rw [htime]
    apply AC.slot_of_mem sp (s + 2)
    all_goals simp only [ACParams.ts]; push_cast; linarith
  have down : ∀ {X Y}, Anc (tr.HonestBlocksAt H) X Y →
      Compatible (tr.HonestBlocksAt H) Y P → Compatible (tr.HonestBlocksAt H) X P := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact AC.anc_total hU hXY h
  intro l hl L hL hLr
  have hl' : l ∈ ((tr.projAC.upTo (tr.time k)).state y k).locks := by rwa [hst]
  by_cases hlt : l.slot < s + 1
  · have hT2 : sp.ts (s + 2 : Nat) + sp.Δ ≤ tr.time k := by rw [htime]; linarith
    have hslot2 : sp.slot (sp.ts (s + 2 : Nat) + sp.Δ) = s + 2 := by
      apply AC.slot_of_mem sp (s + 2)
      all_goals simp only [ACParams.ts]; push_cast; linarith
    have hjn : ∀ x, x ∈ H (sp.ts (s + 2 : Nat) + sp.Δ) →
        AC.JoinedAt tr.projAC x (sp.ts (s + 2 : Nat) + sp.Δ) := by
      intro x hx q hqs hqt
      change tr.time q ≤ sp.ts ((sp.slot (sp.ts (s + 2 : Nat) + sp.Δ) : Int) - 1)
      rw [hslot2, show ((s + 2 : Nat) : Int) - 1 = ((s + 1 : Nat) : Int) by omega]
      exact (noRestartUpTo_iff.mp hnr x q (hrun.antitone hqt hx) (Compose.projAC_restartAt.mp hqs)
        (hqt.trans (hT2.trans hkb))).trans hgu
    have hS2 := hK.healthy_base_before_at hrun hnc hsvc hawake hf hcatch
      (show 0 ≤ sp.ts (s + 2 : Nat) + sp.Δ by linarith [AC.gbar_nonneg g]) (hT2.trans hkb)
    obtain ⟨j, ellj, R, hb, hjs, hjt⟩ := honest_vote_branches_of_joined_before_at hS2
      (by linarith) hjn y (hrun.antitone hT2 hy)
    replace hjs : sp.slot (tr.time j) = s + 2 := by omega
    have hjk : j < k := by
      by_contra hn
      have := hmono (show k ≤ j by omega)
      linarith
    have hjlo : sp.ts (s + 2 : Nat) ≤ tr.time j :=
      (AC.ts_le_iff_le_slot sp (hrun.time_nonneg j) _).2 (by omega)
    have hj0 := hrun.time_nonneg j
    have hjb := (hmono hjk.le).trans hkb
    have hyj := hrun.antitone (hmono hjk.le) hy
    have hSj := hK.healthy_base_before_at hrun hnc hsvc hawake hf hcatch hj0 hjb
    have hrj := hSj.run.localRun
    have hb' : AC.VoteBranchAt (tr.projAC.upTo (tr.time j)) y j ellj R :=
      (voteBranchAt_upTo_iff hmono).2 ⟨le_rfl, hb⟩
    have hPhij := AC.frameIn_of_callAt hrj hyj hb'.callAt
    have hrestart : ∀ q, ACTrace.RestartAt (tr.projAC.upTo (tr.time j)) y q →
        tr.time q ≤ gbar g := by
      intro q hq
      obtain ⟨hqD, hq⟩ := (ACTrace.upTo_restartAt (A := AC.goldilocksAC sp _)).mp hq
      exact noRestartUpTo_iff.mp hnr y q (hrun.antitone hqD hyj) (Compose.projAC_restartAt.mp hq)
        (hqD.trans hjb)
    have hrs : ∀ q ≤ j, ACTrace.RestartAt (tr.projAC.upTo (tr.time j)) y q →
        (tr.projAC.upTo (tr.time j)).time q < sp.ts (s + 1 : Nat) :=
      fun q _ hq => (hrestart q hq).trans_lt (by linarith)
    have hdl : ∀ q ≤ j, ∀ t, gbar g ≤ t →
        ACTrace.deadline (A := AC.goldilocksAC sp _) (tr.projAC.upTo (tr.time j)) y q t ≤
          max t (sp.ts (s + 1 : Nat)) + sp.Δ :=
      fun _ _ t _ => Compose.ac_deadline_le_of_restarts (a := sp.ts (s + 1 : Nat))
        (fun q _ hq => (hrestart q hq).trans hgu) t
    have hfr := Compose.Growing.frame_of_projAC_at hrun hyj hb.callAt
    have hFe : ellj.frame.F = (tr.state y j).fg.F := by rw [hfr]; rfl
    have hFP : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F P :=
      hfin y j hyj (by linarith) ((hmono hjk.le).trans hkhi) hjb
    have hdl1 : sp.ts (s + 1 : Nat) + sp.Δ ≤ tr.time j := by linarith
    have hS0 := hK.healthy_base_before_at hrun hnc hsvc hawake hf hcatch
      (show 0 ≤ sp.ts (s + 1 : Nat) + sp.Δ by linarith [AC.gbar_nonneg g]) (hdl1.trans hjb)
    have hvotes := honest_votes_of_joined_before_at hS0 hgu hjoin
    have hlate : sp.ts (s + 1 : Nat) + 2 * sp.Δ ≤ (tr.projAC.upTo (tr.time j)).time j := by
      change _ ≤ tr.time j
      linarith
    have hsupp : ∀ x ∈ K.committee (s + 1) ∩ H (tr.time j),
        x ∈ AC.supporters ellj.frame (AC.mergedVoteView sp R ellj.frame (s + 1 + 1))
          ((s + 1 : Nat) : Int) P ∧ P ∈ ellj.frame.tree := by
      rintro x ⟨hxK, hx⟩
      obtain ⟨q, e, ⟨ellq, hcast⟩, hes, hq⟩ := hvotes x (hrun.antitone hdl1 hx) hxK
      have hqj : tr.time q ≤ tr.time j := hq.trans hdl1
      have hv : AC.VoteAt (tr.projAC.upTo (tr.time j)) x q e :=
        AC.upTo_voteAt.mpr ⟨hqj, ellq, hcast⟩
      have hxq := hrun.antitone hqj hx
      obtain ⟨W, hW, hWr, hPW⟩ :=
        vote_extends_upTo hrun hnc hj0 hx hv (hext x q e hxq ⟨ellq, hcast⟩ hes)
      have hPU : P ∈ (tr.upTo (tr.time j)).HonestBlocks (H (tr.time j)) := by
        by_cases hPW' : P = W
        · exact hPW' ▸ hW
        · exact (Anc.mem hPW hPW').1
      have hFPj : Anc ((tr.upTo (tr.time j)).HonestBlocks (H (tr.time j))) ellj.frame.F P := by
        rw [hFe]
        exact RunTrace.anc_upTo_of_right hrun.toLocalRun hnc hj0 hPU hFP
      have hF : ∀ B ∈ (tr.upTo (tr.time j)).HonestBlocks (H (tr.time j)),
          B.root = e.msg.head →
            Anc ((tr.upTo (tr.time j)).HonestBlocks (H (tr.time j))) ellj.frame.F B := by
        intro B hB hBr
        obtain rfl : B = W := hrj.coherent.1 hB hW (hBr.trans hWr.symm)
        exact hFPj.trans hPW
      obtain ⟨E, hE, hEr, hEs, -, -, -, hacc⟩ := AC.late_vote_accepted_of_frame_before hSj hyj
        hb'.callAt hm hlate le_rfl hdl hrs hx hv hes hF
      obtain rfl : E = W := hrj.coherent.1 (hPhij.2 hE) hW (hEr.trans hWr.symm)
      have hPt : P ∈ ellj.frame.tree :=
        AC.frame_mem_of_between sp hrj.coherent hPhij.1 hPhij.2 hE hPW hFPj
      have hheld : AC.HeldBefore R e.msg (sp.ts (s + 1 : Nat) + 2 * sp.Δ) := by
        apply AC.heldBefore_readPoint_branchU hrj.toU hyj hb' (fun h => by
          have h' := h.symm.trans hjs
          omega)
        simpa only [hes] using AC.honest_vote_early_pool_before hSj hyj hb'.callAt hgu hlate
          le_rfl hdl hrs hx hv hes (j + 1) (Or.inr rfl)
      have hval := (AC.castAt_specU hrj.toU hx (AC.upTo_castAt.mpr ⟨hqj, hcast⟩)).1
      have hs' := AC.carried_supporter_branchU hSj.run.toU hyj hb' (s := s + 1)
        (by change sp.slot (tr.time j) = _; omega) hPt hes
        ⟨hheld.1, lt_trans hheld.2
          (WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by linarith)))⟩
        ⟨E, hPhij.2 hE, hEr, hEs, hPW, by
          rcases hacc with hg | ⟨q', hq', hqt'⟩
          · exact Or.inl hg
          · exact Or.inr ⟨q', hq', by linarith⟩⟩
        (AC.honest_not_equivocator_branchU hSj.run.toU hyj hb' (hval ▸ hx))
      rw [hval] at hs'
      exact ⟨hs', hPt⟩
    have hcsj := hK.cs2 (s + 1) hgu (by linarith) (tr.time j) hj0 hjb
    have hhalf : sp.committeeSize ≤ 2 * (K.committee (s + 1) ∩ H (tr.time j)).ncard := by
      have hsplit : (K.committee (s + 1) ∩ H (tr.time j)).ncard +
          (K.committee (s + 1) ∩ (H (tr.time j))ᶜ).ncard = sp.committeeSize := by
        rw [← hK.facts.hsize (s + 1), Set.inter_comm (K.committee (s + 1)) (H (tr.time j))ᶜ,
          ← Set.sdiff_eq_compl_inter]
        exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ (Set.toFinite _)
      omega
    obtain ⟨x₀, hx₀⟩ : (K.committee (s + 1) ∩ H (tr.time j)).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by omega)
    exact older_locks_compatible_after_unlock_at hrun hnc hy hb
      (show sp.slot (tr.time j) = (s + 1) + 1 by omega) hjk
      (hsupp x₀ hx₀).2 (fun x hx => Or.inr (hsupp x hx).1.2) hhalf l hl hlt L hL hLr
  have hle : l.slot ≤ s + 2 := by
    obtain ⟨r, hrk, B, horig, _⟩ := AC.lock_provenanceU (hr := hr.toU) hrun.vstart hy k l hl'
    have hm := AC.slot_mono sp (hr.time_nonneg r) (hr.time_mono hrk.le)
    change sp.slot (tr.time r) ≤ sp.slot (tr.time k) at hm
    rw [hslot] at hm
    rcases horig with ⟨CV, ellr, A, _, hsl, _⟩ | ⟨ellr, _, _, hrt, _⟩
    · change sp.slot (tr.time r) = l.slot at hsl
      omega
    · have hls := (AC.ts_le_iff_le_slot sp (hr.time_nonneg r) (l.slot : Int)).1
        (show sp.ts l.slot ≤ (tr.projAC.upTo (tr.time k)).time r by rw [hrt]; linarith)
      change (l.slot : Int) ≤ sp.slot (tr.time r) at hls
      omega
  cases hfast : l.fast
  · obtain ⟨r, hrk, B, ⟨ellr, C, hup, hC, hB⟩, L₁, hL₁, hL₁r, hLB⟩ :=
      AC.slow_lock_provenance hr hrun.vstart hy k l hl' hfast
    have hmr := hrun.time_mono hrk.le
    have hrt : tr.time r = sp.ts l.slot + 6 * sp.Δ := hup.2.2.1
    have hls : l.slot = s + 1 := by
      have := (AC.ts_le_iff sp).1 (show sp.ts l.slot ≤ sp.ts (s + 1 : Nat) by linarith)
      omega
    rw [hls] at hup hC hrt
    have hup' := (AC.upTo_updateAt hrun.time_mono).mp hup |>.2
    obtain ⟨C', hconf, hPC', -⟩ := update_result_extends_of_finalized_at hrun hnc hsvc hawake hf
      hcatch hnr hm hjoin hfin hPg hext (hrun.antitone hmr hy) hup' (by linarith)
      (hmr.trans hkhi) (hmr.trans hkb) hK
    have hsr := Trace.upTo_state tr.projAC y (d := tr.time k) (i := r)
      (fun q hq => (hrun.time_mono hq.le).trans hmr)
    rw [hsr] at hC
    obtain rfl : C = C' := Option.some.inj (hC.symm.trans hconf)
    have hBC := (AC.deepest_mem hB).1.1.2.2
    have hLL₁ : L = L₁ := hU.1 hL (hsub hL₁) (hLr.trans hL₁r.symm)
    rw [← hLL₁] at hLB
    exact down ((hLB.mono hsub).trans
      (hBC.mono (fun Q hQ => hsub ((AC.frameIn_of_callAt hr hy hup.1).2 hQ)))) (Or.inr hPC')
  · obtain ⟨r, hrk, B, CV, hfl, L₁, hL₁, hL₁r, hLB⟩ :=
      AC.fast_lock_provenance hr hrun.vstart hy k l hl' hfast
    have hLL₁ : L = L₁ := hU.1 hL (hsub hL₁) (hLr.trans hL₁r.symm)
    rw [← hLL₁] at hLB
    have hgl : gbar g ≤ sp.ts l.slot := hgu.trans ((AC.ts_le_iff sp).2 (by omega))
    have hlk : sp.ts l.slot ≤ tr.time k := by
      have := (AC.ts_le_iff sp).2 (show (l.slot : Int) ≤ (s + 2 : Nat) by omega)
      linarith
    obtain ⟨x, hx, q, e, hv, hes, D, hD, hDr, hBD⟩ :=
      AC.fastLock_honest_vote hS.run K hS.hP hy hfl (hS.cs2 l.slot hgl hlk)
    obtain ⟨hqt, hv⟩ := AC.upTo_voteAt.mp hv
    apply down (hLB.mono hsub)
    have hPv : AC.VoteExtends (tr.HonestBlocksAt H) e.msg P := by
      rcases (show l.slot = s + 1 ∨ l.slot = s + 2 by omega) with hls | hls
      · exact hext x q e (hrun.antitone hqt hx) hv (hes.trans hls)
      · exact hext₁ x q e (hrun.antitone hqt hx) hv (hes.trans hls)
    obtain ⟨D', hD', hD'r, hPD⟩ := hPv
    have hDD' : D = D' := hU.1 (hsub hD) hD' (hDr.trans hD'r.symm)
    rw [← hDD'] at hPD
    exact AC.anc_total hU (hBD.mono hsub) hPD

private theorem anc_of_isDeepest {FGP : Type} {Φ : AC.Frm sp.n FGP} (hΦ : FrameOK Φ)
    {S : Set (AC.Blk sp.n FGP)} {D X : AC.Blk sp.n FGP} (hD : AC.IsDeepest Φ S D) (hX : X ∈ S)
    (hXt : X ∈ Φ.tree) (h : Compatible Φ.tree X D) : Φ.Anc X D := by
  refine h.elim id fun hDX => ?_
  by_cases hne : D = X
  · exact hne ▸ Relation.ReflTransGen.refl
  · have := AC.depth_lt_of_anc hΦ hDX hne hXt
    rcases hD.2 X hX (Ne.symm hne) with h | h <;> omega

/-- The deepest unvetoed fast block extends every compatible unvetoed fast ancestor. -/
theorem fast_update_of_unvetoed_at
    {y : Fin sp.n} {k s : Nat} {ell : ACLabel (goldilocksNode sp)}
    (hy : y ∈ H (tr.time k))
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr) (hu : AC.UpdateAt tr.projAC y k s ell)
    {C P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hconf : AC.getConfirmation sp (tr.projAC.state y k) ell.frame s = some C)
    (hPt : P ∈ ell.frame.tree) (hPg : P.root ≠ sp.genesisRoot) (hPC : ell.frame.Anc P C)
    (hnv : ¬ AC.conflictsWithLock sp (tr.projAC.state y k).locks ell.frame (tr.time k) P)
    (hfast : AC.FastTest sp (tr.projAC.state y k) ell.frame s P) :
    ∃ D CV, AC.FastUpdateAt tr.projAC y k s D CV ∧ Anc (tr.HonestBlocksAt H) P D := by
  have hPhi := Compose.Growing.frameIn_at hrun hnc hy hu.1
  set S := {X | X ∈ AC.confirmationPath sp ell.frame C ∧
    ¬ AC.conflictsWithLock sp (tr.projAC.state y k).locks ell.frame (tr.time k) X ∧
    AC.FastTest sp (tr.projAC.state y k) ell.frame s X}
  have hPS : P ∈ S := ⟨⟨hPt, hPg, hPC⟩, hnv, hfast⟩
  obtain ⟨D, hD⟩ := AC.exists_deepest hPhi.1 (fun X hX => hX.1.1) ⟨P, hPS⟩
  have hDd := AC.deepest_mem hD
  have hPD : ell.frame.Anc P D := anc_of_isDeepest hPhi.1 hDd hPS hPt
    (AC.anc_total hPhi.1.coherent hPC hDd.1.1.2.2)
  exact ⟨D, _, ⟨ell, C, hu, hconf, hD, rfl⟩, hPD.mono hPhi.2⟩

/-- The raw fast selection writes a live fast lock through the second following slot. -/
theorem fastLock_mem_updateConfirmation_of_select {FGP : Type} {A : AC.ACState sp.n}
    {Φ : AC.Frm sp.n FGP} {t : Time} {s : Nat} {C D : AC.Blk sp.n FGP}
    (hconf : AC.getConfirmation sp A Φ s = some C)
    (hD : AC.deepest Φ {X | X ∈ AC.confirmationPath sp Φ C ∧
      ¬ AC.conflictsWithLock sp A.locks Φ t X ∧ AC.FastTest sp A Φ s X} = some D)
    (hDt : D ∈ Φ.tree) (hlive : sp.slot t ≤ s + 2)
    (hcap : ∀ l ∈ A.locks, l.expiry ≤ l.slot + sp.k) (hs : s ≤ sp.slot t) :
    ∃ e, s + 2 ≤ e ∧ (⟨(Φ.viableAncestor D).root, s, true, e⟩ : AC.Lock) ∈
      (AC.updateConfirmation sp A Φ t s).locks := by
  classical
  have hD' : AC.deepest Φ {B | B ∈ {B | B ∈ AC.confirmationPath sp Φ C ∧
      ¬ AC.conflictsWithLock sp A.locks Φ t B} ∧ AC.FastTest sp A Φ s B} = some D := by
    rw [← hD]
    congr 1
    ext X
    simp only [Set.mem_ofPred_eq, and_assoc]
  unfold AC.updateConfirmation
  simp only [hconf]
  have hlocks : (if AC.conflictsWithLock sp A.locks Φ t C then
      { A with saved := Function.update A.saved (s : Int) (some C.root) }
      else AC.updateLatestConfirmed sp
        { A with saved := Function.update A.saved (s : Int) (some C.root) } Φ C).locks =
      A.locks := by
    split_ifs <;> simp only [AC.updateLatestConfirmed_keeps_locks]
  simp only [Option.map_some] at *
  rw [hlocks]
  exact ⟨_, AC.le_fastExpiry sp _ Φ t s hcap hs, ⟨D.root, s, true, _⟩,
    Or.inr ⟨_, Or.inl ⟨D, hD', rfl⟩, rfl⟩, D, hDt, rfl,
    hlive.trans (AC.le_fastExpiry sp _ Φ t s hcap hs), rfl⟩

/-- The AC post-state of an honest update is the update-confirmation result. -/
private theorem post_of_updateAt
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {y : Fin sp.n} {k s : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp)} (hu : AC.UpdateAt tr.projAC y k s ell) :
    tr.projAC.post k =
      AC.updateConfirmation sp (tr.projAC.state y k) ell.frame (tr.time k) s := by
  have hr := (Compose.Growing.acRun_upTo hrun hnc (hrun.time_nonneg k)).localRun
  have hc : (tr.projAC.upTo (tr.time k)).CallAt y k ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hu.1⟩
  have hs := Trace.upTo_state tr.projAC y (i := k)
    (fun q hq => hrun.time_mono hq.le)
  have he := hr.exec k ell hc.2 (hc.1 ▸ hy)
  rw [hc.1, hu.2.1, hs, Trace.upTo_post, Trace.upTo_time] at he
  have hkt : tr.time k = sp.ts s + 6 * sp.Δ := hu.2.2.1
  have hslot : sp.slot (tr.time k) = s + 1 := by
    rw [hkt]
    apply AC.slot_of_mem sp (s + 1)
    all_goals simp only [ACParams.ts]; push_cast; linarith [sp.toParams.hΔ]
  rw [show tr.projAC.post k =
    (AC.acOnTick sp y (tr.projAC.state y k) ell.frame (tr.time k)).1 from
      (congrArg Prod.fst he).symm]
  unfold AC.acOnTick
  dsimp only
  rw [hslot]
  have ht1 : ¬ tr.time k = sp.ts (s + 1 : Nat) + sp.Δ := by
    rw [hkt]; simp only [ACParams.ts]; push_cast; linarith [sp.toParams.hΔ]
  have ht2 : tr.time k = sp.ts (s + 1 : Nat) + 2 * sp.Δ := by
    rw [hkt]; simp only [ACParams.ts]; push_cast; ring
  have hj : AC.joined sp (tr.projAC.state y k) (tr.time k) := hu.2.2.2
  rw [ite_eq_right (not_not.mpr hj), ite_eq_right ht1,
    ite_eq_left ⟨ht2, Nat.succ_pos s⟩]
  simp only [Nat.add_sub_cancel]

/-- The fast floor survives a cut of a growing run at its supplied frame. -/
theorem fastFloor_step_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {P : AC.Blk sp.n (List (FG.Att sp.n))} {j m : Nat}
    (hfl : Compose.FastFloorAt tr y k P j m) (hk : sp.slot (tr.time k) ≤ m)
    (hP : P ∈ (tr.state y k).fg.toFrame.tree)
    (hP' : P ∈ (tr.state y (k + 1)).fg.toFrame.tree)
    (hva : (tr.state y k).fg.toFrame.viableAncestor P = P)
    (hu : (sp.slot (tr.time k) : Int) - 1 ≤ j ∨ Compose.UnlockKeeps tr y k P) :
    Compose.FastFloorAt tr y (k + 1) P j m := by
  have hd := hrun.time_nonneg k
  have hst : (tr.upTo (tr.time k)).state y k = tr.state y k :=
    RunTrace.upTo_state_of_le hrun.time_mono le_rfl
  have hst1 : (tr.upTo (tr.time k)).state y (k + 1) = tr.state y (k + 1) :=
    Trace.upTo_state tr y fun _ hk' => hrun.time_mono (Nat.lt_succ_iff.1 hk')
  have h := Compose.fastFloor_run_view (hrun.upTo hd) hy k (B₀ := P) (j := j) (m := m)
    (by simp only [Compose.FastFloorAt, hst]; exact hfl) hk (by rw [hst]; exact hP)
    (by rw [hst1]; exact hP') (by rw [hst]; exact hva) fun ell hc => by
      rw [hst]
      rcases hu with hs | hu
      · exact Or.inl hs
      · exact Or.inr (hu ell ((Trace.upTo_callAt_of_le _ le_rfl).mp hc))
  simp only [Compose.FastFloorAt, hst1] at h
  exact h

/-- A fresh fast lock remains a candidate while its two-slot lifetime lasts. -/
theorem toFG_candidate_of_viable_head_at {K : AC.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (AC.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) {g b : Time}
    (hK : CommitteeHalfUpTo tr H K g b)
    {P : AC.Blk sp.n (List (FG.Att sp.n))} {r : Nat} (hgr : gbar g ≤ sp.ts (r + 1 : Nat))
    {y : Fin sp.n} {j : Nat} {D : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (AC.Vote sp.n)}
    (hfu : AC.FastUpdateAt tr.projAC y j r D CV) (hPD : Anc (tr.HonestBlocksAt H) P D)
    {i : Nat} (hy : y ∈ H (tr.time i)) {ell : ACLabel (goldilocksNode sp)}
    (hc : tr.projAC.CallAt y i ell) (hji : j < i)
    (hext : ∀ x k e, x ∈ H (tr.time k) → AC.VoteAt tr.projAC x k e → e.msg.slot = r + 1 →
      tr.time k ≤ tr.time i → AC.VoteExtends (tr.HonestBlocksAt H) e.msg P)
    (hPk : ∀ k, j ≤ k → k ≤ i → P ∈ (Node.frame (tr.state y k)).tree ∧
      (Node.frame (tr.state y k)).Anc (Node.frame (tr.state y k)).fcRoot P ∧
      P ∈ (Node.frame (tr.state y k)).viableHeads)
    (hib : tr.time i ≤ b) (hslot : sp.slot (tr.time i) ≤ r + 2) :
    ∃ B ∈ AC.toFGCandidates sp (tr.projAC.state y i) ell.frame (tr.time i),
      Anc (tr.HonestBlocksAt H) P B := by
  have hmono := hrun.time_mono
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  obtain ⟨ellj, C, hu, hconf, hD, -⟩ := hfu
  have hji' := hmono hji.le
  have hyj : y ∈ H (tr.time j) := hrun.antitone hji' hy
  have hfrj := Compose.Growing.frame_of_projAC_at hrun hyj hu.1
  obtain ⟨hΦj, hΦjU⟩ := Compose.Growing.frameIn_at hrun hnc hyj hu.1
  have hDt := (AC.deepest_mem hD).1.1.1
  have hPj : P ∈ ellj.frame.tree := by rw [hfrj]; exact (hPk j le_rfl hji.le).1
  have hΦk (k : Nat) (hki : k ≤ i) : FrameOK (Node.frame (tr.state y k)) :=
    Compose.Growing.frameOK_at hrun (hrun.time_nonneg k) (hrun.antitone (hmono hki) hy)
      (fun q hq => hmono hq.le)
  have hvak (k : Nat) (hjk : j ≤ k) (hki : k ≤ i) :
      (Node.frame (tr.state y k)).viableAncestor P = P := by
    obtain ⟨hPt, hroot, hv⟩ := hPk k hjk hki
    exact AC.viableAncestor_self (hΦk k hki) hPt (Or.inl ⟨hPt, hroot, P, hPt, hv, .refl⟩)
  have hjslot : sp.slot (tr.time j) = r + 1 := by
    have hjt : tr.time j = sp.ts r + 6 * sp.Δ := hu.2.2.1
    rw [hjt]
    apply AC.slot_of_mem sp (r + 1)
    all_goals simp only [ACParams.ts]; push_cast; linarith [sp.toParams.hΔ]
  obtain ⟨e, he, hl⟩ := fastLock_mem_updateConfirmation_of_select (t := tr.time j) hconf hD hDt
    (by omega)
    (by
      have hr := (Compose.Growing.acRun_upTo hrun hnc (hrun.time_nonneg j)).localRun
      have hwf := AC.locksWF_state hr hrun.vstart hyj j
      have hs := Trace.upTo_state tr.projAC y (d := tr.time j) (i := j)
        (fun q hq => hmono hq.le)
      rw [hs] at hwf
      exact fun l hl => hwf.cap hl)
    (by omega)
  rw [← post_of_updateAt hrun hnc hyj hu] at hl
  have hyj1 : y ∈ H (tr.time (j + 1)) := hrun.antitone (hmono hji) hy
  have hl1 : (⟨(ellj.frame.viableAncestor D).root, r, true, e⟩ : AC.Lock) ∈
      (tr.state y (j + 1)).ac.locks := by
    rw [← Compose.Growing.projAC_state_at hrun hyj1, Trace.state_succ_of_call tr.projAC hu.1]
    exact hl
  have hPDj : ellj.frame.Anc P D := AC.anc_tree_of_anc_U hU hΦj hΦjU hPj hPD hDt
  have hvaj : ellj.frame.viableAncestor P = P := by rw [hfrj]; exact hvak j le_rfl hji.le
  have hbase : Compose.FastFloorAt tr y (j + 1) P r (r + 2) := by
    have hB := (AC.viableAncestor_anc hΦj hDt).1
    have hPB := AC.anc_viableAncestor_of_floor hΦj hPj hvaj hDt hPDj
    rw [hfrj] at hB hPB
    have hst (k : Nat) (hk : k ≤ j + 1) :
        (tr.upTo (tr.time (j + 1))).state y k = tr.state y k :=
      Trace.upTo_state tr y fun q hq => hmono (by omega)
    obtain ⟨hB', hPB'⟩ := Compose.floor_frame_transport
      (hrun.upTo (hrun.time_nonneg (j + 1))) hyj1 (Nat.le_succ j)
      (by rw [hst _ le_rfl]; exact (hPk (j + 1) (Nat.le_succ j) hji).1)
      (by rw [hst j (Nat.le_succ j)]; exact hB)
      (by rw [hst j (Nat.le_succ j)]; exact hPB)
    rw [hst _ le_rfl] at hB' hPB'
    exact ⟨_, hl1, rfl, rfl, he, _, hB', by rw [hfrj], hPB'⟩
  have hfloor : ∀ k, j + 1 ≤ k → k ≤ i →
      Compose.FastFloorAt tr y k P r (r + 2) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact fun _ => hbase
    | succ k hjk ih =>
      intro hki
      have hkt := hmono (show k ≤ i by omega)
      have hyk := hrun.antitone hkt hy
      have hk0 := hrun.time_nonneg k
      have hsk : sp.slot (tr.time k) ≤ r + 2 :=
        (AC.slot_mono sp hk0 hkt).trans hslot
      refine fastFloor_step_at hrun hyk (ih (by omega)) hsk (hPk k (by omega) (by omega)).1
        (hPk (k + 1) (by omega) hki).1 (hvak k (by omega) (by omega)) ?_
      by_cases hs : (sp.slot (tr.time k) : Int) - 1 ≤ r
      · exact Or.inl hs
      have hslk : sp.slot (tr.time k) = r + 2 := by omega
      have hkb := hkt.trans hib
      refine Or.inr (Compose.Growing.unlockKeeps_of_voteCompat_at hrun hnc hK.facts hyk
        subset_rfl ?_ (hPk k (by omega) (by omega)).1 ?_)
      · rw [hslk, show r + 2 - 1 = r + 1 by omega]
        exact hK.cs2 (r + 1) hgr (by
          have := (AC.ts_le_iff_le_slot sp hk0 ((r + 1 : Nat) : Int)).2 (by omega)
          linarith) (tr.time k) hk0 hkb
      · intro x hx k' hk' e' hv hes
        obtain ⟨hx', hv'⟩ := Compose.Growing.hVoteAt_iff.1 hv
        exact (hext x k' e' hx' hv' (by omega) (hmono (by omega))).voteCompat
  obtain ⟨l, hl, hls, hlf, hle, B, hB, hBr, hPB⟩ := hfloor i hji le_rfl
  have hfri := Compose.Growing.frame_of_projAC_at hrun hy hc
  obtain ⟨hΦi, hΦiU⟩ := Compose.Growing.frameIn_at hrun hnc hy hc
  obtain ⟨hPti, hrooti, hvi⟩ := hPk i hji.le le_rfl
  rw [← hfri] at hPti hrooti hvi
  have hB' : B ∈ ell.frame.tree := by rw [hfri]; exact hB
  have hPB' : ell.frame.Anc P B := by rw [hfri]; exact hPB
  have hPv : P ∈ ell.frame.viableTree ell.frame.tree := ⟨hPti, hrooti, P, hPti, hvi, .refl⟩
  have hvaP := AC.viableAncestor_self hΦi hPti (Or.inl hPv)
  have hPV := AC.anc_viableAncestor_of_floor hΦi hPti hvaP hB' hPB'
  have hVv : ell.frame.viableAncestor B ∈ ell.frame.viableTree ell.frame.tree := by
    rcases (AC.viableAncestor_spec hΦi hB').2.1 with hroot | hvt
    · rw [Anc.antisymm hΦi.coherent (hroot.trans hrooti) hPV]
      exact hPv
    · exact hvt
  have hl' : l ∈ (tr.projAC.state y i).locks := by
    rw [Compose.Growing.projAC_state_at hrun hy]; exact hl
  refine ⟨_, ⟨hVv, { l with block := (ell.frame.viableAncestor B).root },
    ⟨l, hl', B, hB', hBr, ?_, rfl⟩, rfl, hlf, ?_⟩, hPV.mono hΦiU⟩
  · change sp.slot (tr.time i) ≤ l.expiry
    omega
  · change sp.slot (tr.time i) ≤ l.slot + 2
    omega

end Consensus.Goldilocks.Healing.Growing

end
