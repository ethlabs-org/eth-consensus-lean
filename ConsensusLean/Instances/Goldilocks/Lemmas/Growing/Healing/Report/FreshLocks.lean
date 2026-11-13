module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FreshNext
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Compatibility of all lock labels at the warm update -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Old labels use the receiver's unlock; new fast labels use an honest vote
at the counting cut, and slow labels use the raw unanimous confirmation. -/
theorem FrameWindow.unanimous_update_no_veto_at
    {g ΔF b : Time} {u floor : Nat} {kindJ : Prop}
    {J P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts u) (sp.ts (u + 1 : Nat) + 2 * sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hmargin : gbar g + 2 * sp.Δ ≤ sp.ts u)
    (hjoin : ∀ x, x ∈ H (sp.ts u + sp.Δ) → SA.JoinedAt tr.projAC x (sp.ts u + sp.Δ))
    (hTb : sp.ts (u + 1 : Nat) + 2 * sp.Δ ≤ b)
    {z : Fin sp.n} (hz : z ∈ H (sp.ts u + sp.Δ)) (hdes : z = proposer u)
    {kP : Nat} (hP : tr.ProposesAt z kP P) (hPs : P.slot = u)
    (hun : ∀ x i e, x ∈ H (tr.time i) → SA.VoteAt tr.projAC x i e →
      e.msg.slot = u → e.msg.head = P.root)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    {ell : ACLabel (goldilocksNode sp ro)} (hu : SA.UpdateAt tr.projAC y k u ell)
    (hstock : sp.committeeSize = sp.n) :
    ¬ SA.conflictsWithLock sp (tr.projAC.state y k).locks ell.frame (tr.time k) P := by
  have hΔ := sp.toParams.hΔ
  have hkt : tr.time k = sp.ts u + 6 * sp.Δ := hu.2.2.1
  have hT : sp.ts (u + 1 : Nat) + 2 * sp.Δ = sp.ts u + 6 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hkb : tr.time k ≤ b := by rw [hkt, ← hT]; exact hTb
  have hS := healthy_base_of_service_catch_before_at hrun hnc hsvc hawake hf hcatch
    (hrun.time_nonneg k) hkb hstock
  have hr := hS.run.localRun
  have hsub := RunTrace.honestBlocks_upTo_subset (H := H) hrun.time_mono (hrun.time_nonneg k)
  have hU := Compose.Growing.honest_blocks_coherent hrun hnc
  have hslot : sp.slot (tr.time k) = u + 1 := by
    rw [hkt]
    apply SA.slot_of_mem sp (u + 1)
    all_goals simp only [SAParams.ts]; push_cast; linarith
  have hs := Trace.upTo_state tr.projAC y (i := k)
    (fun q hq => hrun.time_mono hq.le)
  have hc' : (tr.projAC.upTo (tr.time k)).CallAt y k ell :=
    (Trace.upTo_callAt _).mpr ⟨le_rfl, hu.1⟩
  have hPhi := SA.frameIn_of_callAt hr hy hc'
  obtain ⟨hvi, _, _, _⟩ := hframe.unanimous_update_selection_at hrun hnc hsvc hawake hf hcatch
    hnr hmargin hjoin hTb hz hdes hP hPs hun hy hu hstock
  have hnext := hframe.unanimous_next_votes_at hrun hnc hsvc hawake hf hcatch hnr
    hmargin hjoin hTb hz hdes hP hPs hun hstock
  have hold := hframe.older_locks_compatible_at_update_at hrun hnc hsvc hawake hf hcatch hnr
    hmargin hjoin hTb hz hdes hP hPs hun hy hu hstock
  have down : ∀ {X Y}, Anc (tr.HonestBlocksAt H) X Y →
      Compatible (tr.HonestBlocksAt H) Y P → Compatible (tr.HonestBlocksAt H) X P := by
    rintro X Y hXY (h | h)
    · exact Or.inl (hXY.trans h)
    · exact SA.anc_total hU hXY h
  apply no_veto_of_lock_roots_compatible_at hrun hnc hy hu.1 hvi.1
  intro l hl L hL hLr
  by_cases hlt : l.slot < u
  · exact hold l hl hlt L hL hLr
  have hl' : l ∈ ((tr.projAC.upTo (tr.time k)).state y k).locks := by rwa [hs]
  have hle : l.slot ≤ u + 1 := by
    obtain ⟨r, hrk, B, horig, _⟩ := SA.lock_provenance hr hy k l hl'
    have hm := SA.slot_mono sp (hr.time_nonneg r) (hr.time_mono hrk.le)
    change sp.slot (tr.time r) ≤ sp.slot (tr.time k) at hm
    rw [hslot] at hm
    rcases horig with ⟨CV, ellr, A, _, hsl, _⟩ | ⟨ellr, _, _, hrt, _⟩
    · change sp.slot (tr.time r) = l.slot at hsl
      omega
    · have hls := (SA.ts_le_iff_le_slot sp (hr.time_nonneg r) (l.slot : Int)).1
        (show sp.ts l.slot ≤ (tr.projAC.upTo (tr.time k)).time r by rw [hrt]; linarith)
      change (l.slot : Int) ≤ sp.slot (tr.time r) at hls
      omega
  cases hfast : l.fast
  · obtain ⟨r, hrk, B, ⟨ellr, C, hup, hC, hB⟩, L₁, hL₁, hL₁r, hLB⟩ :=
      SA.slow_lock_provenance hr hy k l hl' hfast
    have hm := hrun.time_mono hrk.le
    have hrt : tr.time r = sp.ts l.slot + 6 * sp.Δ := hup.2.2.1
    have hls : l.slot = u := by
      have := (SA.ts_le_iff sp).1 (show sp.ts l.slot ≤ sp.ts u by linarith)
      omega
    rw [hls] at hup hC
    have hup' := (SA.upTo_updateAt hrun.time_mono).mp hup |>.2
    have hCP : C = P := by
      have hconf := (hframe.unanimous_update_selection_at hrun hnc hsvc hawake hf hcatch hnr
        hmargin hjoin hTb hz hdes hP hPs hun (hrun.antitone hm hy) hup' hstock).2.1
      have hsr := Trace.upTo_state tr.projAC y (i := r)
        (fun q hq => (hrun.time_mono hq.le).trans hm)
      rw [hsr] at hC
      exact Option.some.inj (hC.symm.trans hconf)
    have hBP := (SA.deepest_mem hB).1.1.2.2
    rw [hCP] at hBP
    have hLL₁ : L = L₁ := hU.1 hL (hsub hL₁) (hLr.trans hL₁r.symm)
    rw [← hLL₁] at hLB
    exact Or.inl ((hLB.mono hsub).trans
      (hBP.mono (fun Q hQ => hsub ((SA.frameIn_of_callAt hr hy hup.1).2 hQ))))
  · obtain ⟨r, hrk, B, CV, hfl, L₁, hL₁, hL₁r, hLB⟩ :=
      SA.fast_lock_provenance hr hy k l hl' hfast
    have hLL₁ : L = L₁ := hU.1 hL (hsub hL₁) (hLr.trans hL₁r.symm)
    rw [← hLL₁] at hLB
    have hf2 : 2 * (H (tr.time k))ᶜ.ncard < sp.n := by
      have hb := hf (tr.time k) (hrun.time_nonneg k) hkb
      have := sp.toParams.hn
      omega
    obtain ⟨x, hx, q, e, hv, hes, D, hD, hDr, hBD⟩ :=
      SA.fastLock_honest_vote hS.run hf2 hy hfl hstock
    obtain ⟨hqt, hv⟩ := SA.upTo_voteAt.mp hv
    apply down (hLB.mono hsub)
    rcases (show l.slot = u ∨ l.slot = u + 1 by omega) with hls | hls
    · have hDP : D = P := hU.1 (hsub hD) (hsub (hPhi.2 hvi.1))
        (hDr.trans (hun x q e (hrun.antitone hqt hx) hv (hes.trans hls)))
      rw [hDP] at hBD
      exact Or.inl (hBD.mono hsub)
    · obtain ⟨D', hD', hD'r, hPD⟩ := hnext x q e (hrun.antitone hqt hx) hv
        (hqt.trans hkb) (hes.trans hls)
      have hDD' : D = D' := hU.1 (hsub hD) hD' (hDr.trans hD'r.symm)
      rw [← hDD'] at hPD
      exact SA.anc_total hU (hBD.mono hsub) hPD

end Consensus.Goldilocks.Healing.Growing

end
