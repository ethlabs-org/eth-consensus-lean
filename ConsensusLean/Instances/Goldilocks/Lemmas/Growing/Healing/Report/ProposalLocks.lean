module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.LockLocal
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowRegularBoundary
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.FollowLaterBoundary
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Lift

public section

/-! # Proposal lock cases with historical write provenance -/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload gbar)
open Compose.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- A warm live lock is below the root, followed by votes, or from a current optimistic write. -/
theorem proposal_lock_prefix_cases_at
    {g ΔF b : Time} {s₀ s floor : Nat} {kindJ : Prop}
    {J X B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hframe : FrameWindow tr H (sp.ts s₀) (sp.ts (s + 1 : Nat) + sp.Δ) floor kindJ J)
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hsvc : ResetService tr H g ΔF b)
    (hawake : ∀ y t, y ∈ H t → gbar g ≤ t → t ≤ b → tr.awake y t)
    (hf : ∀ t, 0 ≤ t → t ≤ b → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hcatch : CatchRun tr H g (2 * sp.Δ)) (hnr : NoRestartAfter tr H (gbar g))
    (hm : gbar g + 4 * sp.Δ ≤ sp.ts s₀)
    (hmb : sp.ts (s + 1 : Nat) + sp.Δ ≤ b)
    {z : Fin sp.n} {i : Nat} (hz : z ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} (hc : tr.projAC.CallAt z i ell)
    (hti : tr.time i = sp.ts (s + 1 : Nat))
    {l : SA.Lock} (hl : l ∈ SA.liveLocks sp (tr.projAC.state z i).locks ell.frame (tr.time i))
    (hwarm : s₀ + sp.k ≤ l.slot) (hpos : 0 < l.slot)
    (hpred : s₀ ≤ l.slot - 1) (hold : l.slot < s + 1)
    (hB : B ∈ ell.frame.tree) (hBr : B.root = l.block) (hXB : ell.frame.Anc X B) :
    Anc (tr.HonestBlocksAt H) X ell.frame.fcRoot ∨
      (∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → e.msg.slot = s →
        SA.VoteExtends (tr.HonestBlocksAt H) e.msg X) ∨
      ∃ a < i, ∃ D CV, z ∈ H (tr.time a) ∧ SA.OptimisticLockAt tr.projAC z a s D CV ∧
        Anc (tr.HonestBlocksAt H) X D := by
  have hPhi := frameIn_at hrun hnc hz hc
  have hΔ := sp.toParams.hΔ
  have hi : tr.time i ≤ sp.ts (s + 1 : Nat) + sp.Δ := by rw [hti]; linarith only [hΔ]
  obtain ⟨a, hai, ellw, D, hza, ha, hD, hBA, ho⟩ :=
    live_lock_selection_origin_at hrun hnc hz hc hl hB hBr
  let A := ellw.frame.viableAncestor D
  have hXA : Anc (tr.HonestBlocksAt H) X A := (Anc.mono hPhi.2 hXB).trans hBA
  have hW := frameIn_at hrun hnc hza ha
  have hAD : Anc (tr.HonestBlocksAt H) A D :=
    Anc.mono hW.2 (SA.viableAncestor_anc hW.1 hD).2
  have hregular (ho : (∃ CV, SA.FastUpdateAt tr.projAC z a l.slot D CV) ∨
      SA.SlowLockAt tr.projAC z a l.slot D) :
      ∀ y j e, y ∈ H (tr.time j) → SA.VoteAt tr.projAC y j e → e.msg.slot = s →
        SA.VoteExtends (tr.HonestBlocksAt H) e.msg X := by
    obtain ⟨ell', hu⟩ : ∃ ell', SA.UpdateAt tr.projAC z a l.slot ell' := by
      rcases ho with ⟨CV, ell', C, hu, -⟩ | ⟨ell', C, hu, -⟩ <;> exact ⟨ell', hu⟩
    have hgap : l.slot + 2 ≤ s + 1 := by
      have ht := hu.2.2.1
      change tr.time a = _ at ht
      have htime := hrun.time_mono hai.le
      rw [hti] at htime
      by_contra hn
      have he : s + 1 = l.slot + 1 := by omega
      rw [he] at htime
      simp only [SAParams.ts] at ht htime
      push_cast at htime
      linarith only [hΔ, ht, htime]
    have hall := (hframe.regular_later_heads_at hrun hnc hsvc hawake hf hcatch hnr
      hwarm hpos hpred hm hgap hmb hza ho s (by omega) (by omega)).1
    intro y j e hy hv hs
    obtain ⟨R, hR, hRr, hDR⟩ := hall y j e hy hv hs
    exact ⟨R, hR, hRr, (hXA.trans hAD).trans hDR⟩
  rcases ho with hfast | hslow | ⟨CV, hop⟩
  · exact Or.inr (Or.inl (hregular (Or.inl hfast)))
  · exact Or.inr (Or.inl (hregular (Or.inr hslow)))
  by_cases hs : l.slot = s
  · exact Or.inr (Or.inr ⟨a, hai, D, CV, hza, hs ▸ hop, hXA.trans hAD⟩)
  have hlabel : s₀ ≤ l.slot := by omega
  have hts : sp.ts s₀ ≤ sp.ts l.slot := (SA.ts_le_iff sp).2 (by exact_mod_cast hlabel)
  have halo : sp.ts s₀ ≤ tr.time a := by
    obtain ⟨_, _, _, ht, -⟩ := hop
    change sp.slot (tr.time a) = l.slot at ht
    exact hts.trans ((SA.ts_le_iff_le_slot sp (hrun.time_nonneg a) _).2 (by rw [ht]))
  rcases (SA.viableAncestor_spec hW.1 hD).2.1 with hbelow | hAv
  · exact Or.inl (unlocked_image_below_write_root_at hframe hrun hnc hz hai.le ha hc
      halo hi hXB hBA hbelow)
  obtain ⟨Q, hQ, hvQ, hAQ⟩ := hAv.2.2
  have hvQ' := hvQ
  rw [frame_of_projAC_at hrun hza ha] at hvQ'
  have hh : floor ≤ ((tr.state z a).fg.σ Q.root).h := by
    rw [← hframe.floor_eq z a hza halo ((hrun.time_mono hai.le).trans hi)]
    exact hvQ'.2.2.2
  have hJ : kindJ → Anc (tr.HonestBlocksAt H) J A := by
    intro hk
    have hkind := (hframe.kind_iff z a hza halo ((hrun.time_mono hai.le).trans hi)).mpr hk
    have hroot := Anc.mono hW.2 hAv.2.1
    change Anc (tr.HonestBlocksAt H) ellw.frame.fcRoot A at hroot
    rw [frame_of_projAC_at hrun hza ha] at hroot
    change Anc (tr.HonestBlocksAt H) (tr.state z a).fg.fcRoot A at hroot
    rwa [show (tr.state z a).fg.fcRoot = (tr.state z a).fg.J from ite_eq_left hkind,
      hframe.root_eq z a hza halo ((hrun.time_mono hai.le).trans hi) hk] at hroot
  have hsub : FrameWindow tr H (sp.ts l.slot)
      (sp.ts (s + 1 : Nat) + sp.Δ) floor kindJ J :=
    ⟨fun y j hy hlo hhi => hframe.floor_eq y j hy (hts.trans hlo) hhi,
     fun y j hy hlo hhi => hframe.kind_iff y j hy (hts.trans hlo) hhi,
     fun y j hy hlo hhi => hframe.root_eq y j hy (hts.trans hlo) hhi⟩
  have hall := (optimistic_later_heads_of_witness_at hrun hnc hsvc hawake hf hcatch hnr
    (by linarith only [hm, hts, hΔ]) hmb hsub hza hop hAD ha hQ hh hJ (Anc.mono hW.2 hAQ)
    s (by omega) (by omega)).1
  refine Or.inr (Or.inl ?_)
  intro y j e hy hv hes
  obtain ⟨R, hR, hRr, hAR⟩ := hall y j e hy hv hes
  exact ⟨R, hR, hRr, hXA.trans hAR⟩

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
