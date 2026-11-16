module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowReportOrigin
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowWrite
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowRegularBoundary
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee

public section

/-! # Later proposal heads follow the actual historical report -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

/-- A report's own fast origin supplies its later-head route, including an earlier report. -/
theorem FrameWindow.toFG_later_proposal_head_at
    {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
    {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}
    {g ΔF b : Time} {s₀ u N floor : Nat} {kindJ : Prop}
    {J P R : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts N + sp.Δ) floor kindJ J)
    {K : SA.CommitteeDict sp.n}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr
      (SA.committeeStart sp.genesisRoot K))
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀) (hwarm : s₀ + 2 * sp.k ≤ u)
    (hmb : sp.ts N + sp.Δ ≤ b)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} (hto : SA.ToFGAt tr.projAC y i ell R)
    (hPs : P.slot = u) (hPR : Anc (tr.HonestBlocksAt H) P R)
    (hihi : tr.time i ≤ sp.ts N + sp.Δ)
    (ht : tr.time i ≤ sp.ts (u + 1 : Nat) + 2 * sp.Δ)
    {r : Nat} (hrlo : u + 3 ≤ r) (hrN : r ≤ N)
    {z : Fin sp.n} {c : Nat} (hz : z ∈ H (tr.time c))
    {ellp : ACLabel (goldilocksNode sp ro)} (hcp : tr.projAC.CallAt z c ellp)
    (hcall : ellp.call = .proposal) (hti : tr.time c = sp.ts r)
    {d : DutyHead sp.n (List (FG.Att sp.n)) (Payload sp.n)} {pay : Payload sp.n}
    (hd : (SA.acProposal sp (tr.projAC.state z c) ellp.frame (tr.time c)).2 =
      some (d, pay)) (hK : CommitteeHalfUpTo tr H K g b) :
    Anc (tr.HonestBlocksAt H) R d.head := by
  obtain ⟨a, hai, j, ellw, D, CV, hya, ha, hD, hfast, hRA⟩ :=
    toFG_fast_candidate_origin_at hrun hnc hy hto
  have hac := Compose.Growing.goldilocks_ac_projection_from hrun hnc
  have hr := hac.upTo (hrun.time_nonneg a)
  have ha' := (Trace.upTo_callAt tr.projAC).mpr ⟨le_rfl, ha⟩
  have hW := SA.frameIn_of_callAt hr.localRun hya ha'
  have hAD := (SA.viableAncestor_anc hW.1 hD).2.mono hW.2
  have hRD := hRA.trans hAD
  have hatime := hrun.time_mono hai.le
  have hfast' := (SA.upTo_fastLockAt (d := tr.time a) hrun.time_mono).mpr ⟨le_rfl, hfast⟩
  have hfast'' : SA.FastLockAt (tr.upTo (tr.time a)).projAC y a j D CV := by
    simpa only [RunTrace.upTo_projAC] using hfast'
  have hjtime : sp.ts j ≤ tr.time a := by
    rcases hfast with ⟨_, _, hu, _⟩ | ⟨_, _, _, hs, _⟩
    · have he : tr.time a = sp.ts j + 6 * sp.Δ := hu.2.2.1
      linarith only [he, sp.toParams.hΔ]
    · have hs' : sp.slot (tr.time a) = j := hs
      exact (SA.ts_le_iff_le_slot sp (hrun.time_nonneg a) _).2 (by rw [hs'])
  have hts {p q : Nat} (hpq : p ≤ q) : sp.ts p ≤ sp.ts q :=
    (SA.ts_le_iff sp).2 (by exact_mod_cast hpq)
  have hk := sp.two_le_k
  have hPD := (Anc.slot_le hac.localRun.coherent (hPR.trans hRD)).1
  -- the label is after the window start, so after GST (`hm`), before the count:
  -- `u ≤ D.slot ≤ slot(t_a) ≤ j + 1`
  have hs₀j : sp.ts s₀ ≤ sp.ts j := by
    have hDa := Compose.Growing.frame_slot_le_at hrun hnc hya ha D hD
    have hsa : sp.slot (tr.time a) ≤ j + 1 := by
      rcases hfast with ⟨_, _, hu, _⟩ | ⟨_, _, _, hs, _⟩
      · have he : tr.time a = sp.ts j + 6 * sp.Δ := hu.2.2.1
        by_contra hn
        have h2 := (SA.ts_le_iff_le_slot sp (hrun.time_nonneg a) ((j + 2 : Nat) : Int)).2
          (by push_cast; omega)
        have h8 : sp.ts ((j + 2 : Nat) : Int) = sp.ts j + 8 * sp.Δ := by
          simp only [SAParams.ts]; push_cast; ring
        linarith only [he, h2, h8, sp.toParams.hΔ]
      · have hs' : sp.slot (tr.time a) = j := hs
        omega
    exact hts (by omega)
  have hDj := Healing.fast_selection_slot_le (hrun.upTo (hrun.time_nonneg a)) (hnc.upTo _)
    (by
      rw [RunTrace.upTo_projAC]
      exact SA.CommitteePAt.upTo hrun.time_mono hrun.antitone hK.facts.hP _)
    hya hfast'' (hK.cs2 j (by linarith only [hm, hs₀j, sp.toParams.hΔ])
      (hjtime.trans (hatime.trans (hihi.trans hmb)))
      (tr.time a) (hrun.time_nonneg a) (hatime.trans (hihi.trans hmb)))
  have hjlo : u ≤ j := by omega
  have hjhi : j ≤ u + 1 := by
    by_contra hn
    have hlo := hts (show u + 2 ≤ j by omega)
    have hstep := SA.ts_succ (u + 1) (sp := sp)
    linarith only [hlo, hjtime, hatime, ht, hstep, sp.toParams.hΔ]
  rcases hfast with hreg | hopt
  · exact hRD.trans ((hframe.regular_later_heads_at hrun hnc hsvc hawake hf hcatch hnr
      (by omega) (by omega) (by omega) hm (by omega) hmb hya
      (Or.inl ⟨CV, hreg⟩) hK r (by omega) hrN).2 (by omega) z c ellp hz hcp hcall hti d pay
      hd)
  · have halo : sp.ts s₀ ≤ tr.time a := hs₀j.trans hjtime
    have ho := (SA.upTo_optimisticLockAt hrun.time_mono).mpr ⟨le_rfl, hopt⟩
    have hat := (SA.optimisticLockAt_spec hr hya ho (SA.CommitteeDict.full sp.n)
      (fun _ _ _ => SA.mem_full _ _)).1
    apply hframe.optimistic_write_later_proposal_head_at hrun hnc hsvc hawake hf hcatch hnr
      (by linarith only [hm, sp.toParams.hΔ]) hmb (by omega) hya ha halo hat hopt hRA hAD
      ?_ (by omega) hrN hz hcp hcall hti hd hK
    rcases (SA.viableAncestor_spec hW.1 hD).2.1 with hbelow | hAv
    · exact Or.inl hbelow
    · obtain ⟨Q, hQ, hvQ, hAQ⟩ := hAv.2.2
      have he := (hrun.cutLaw y a (.ac ellw) (Compose.projAC_callAt.mp ha) hya).1
      have hvQ' := hvQ
      rw [he] at hvQ'
      refine Or.inr ⟨Q, hQ, ?_, ?_, hAQ.mono hW.2⟩
      · rw [← hframe.floor_eq y a hya halo (hatime.trans hihi)]
        exact hvQ'.2.2.2
      · intro hkind
        have hkc := (hframe.kind_iff y a hya halo (hatime.trans hihi)).mpr hkind
        have hroot := hAv.2.1.mono hW.2
        rw [he]
        rw [he] at hroot
        change Anc _ (tr.state y a).fg.fcRoot _ at hroot
        rwa [show (tr.state y a).fg.fcRoot = (tr.state y a).fg.J from ite_eq_left hkc,
          hframe.root_eq y a hya halo (hatime.trans hihi) hkind] at hroot

end Consensus.Goldilocks.Healing.Growing

end
