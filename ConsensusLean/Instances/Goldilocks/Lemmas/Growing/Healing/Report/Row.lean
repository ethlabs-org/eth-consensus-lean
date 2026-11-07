module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.RowClient
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Source
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ConsumeBase

public section

/-! # A report supplies a historical honest row or a higher height

This proves the frozen report-row interface without importing its placeholder. All
client execution is read through the report time, including its same-time attestation.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- An actual report either supplies a row signed while honest or is strictly higher. -/
theorem row_or_high_of_report_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {g T : Time}
    (hf : ∀ t, 0 ≤ t → t < T → 3 * (H t)ᶜ.ncard ≤ sp.n - 1)
    (hna : ∀ v k att, v ∈ H (tr.time k) → tr.SignAt v k att →
      tr.time k < T → att.h ≤ HZ tr H g)
    {y : Fin sp.n} {i : Nat} (hy : y ∈ H (tr.time i))
    {ell : ACLabel (goldilocksNode sp ro)} {R P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hR : SA.ToFGAt tr.projAC y i ell R) (hiT : tr.time i < T)
    (hPR : Anc (tr.HonestBlocksAt H) P R)
    (hkind : ((tr.state y i).fg.σ R.root).h = ((tr.state y i).fg.σ P.root).h →
      ((tr.state y i).fg.σ P.root).h = HZ tr H g ∨
      (tr.state y i).fg.hj < ((tr.state y i).fg.σ P.root).h ∨
      ((tr.state y i).fg.hj = ((tr.state y i).fg.σ P.root).h ∧
        (tr.state y i).fg.Anc (tr.state y i).fg.J R)) :
    P ∈ (tr.state y i).fg.tree ∧ R ∈ (tr.state y i).fg.tree ∧
      ((∃ k att, y ∈ H (tr.time k) ∧ tr.SignAt y k att ∧ tr.time k ≤ tr.time i ∧
        att.h = ((tr.state y i).fg.σ P.root).h ∧
        att.T = ((tr.state y i).fg.σ P.root).Th) ∨
        ((tr.state y i).fg.σ P.root).h < ((tr.state y i).fg.σ R.root).h) := by
  have ht0 := hrun.time_nonneg i
  have hle : ∀ k < i, tr.time k ≤ tr.time i := fun k hk => hrun.time_mono hk.le
  have hr := hrun.upTo ht0
  have hs := Trace.upTo_state tr y hle
  obtain ⟨hc, hto, hres⟩ := hR
  have hc' : (tr.upTo (tr.time i)).CallAt y i (.ac ell) :=
    (Trace.upTo_callAt tr).mpr ⟨le_rfl, Compose.projAC_callAt.mp hc⟩
  have hacstate : (tr.upTo (tr.time i)).projAC.state y i = tr.projAC.state y i := by
    rw [RunTrace.upTo_projAC]
    exact Trace.upTo_state tr.projAC y hle
  have hres' : (SA.acToFG sp ((tr.upTo (tr.time i)).state y i).ac ell.frame (tr.time i)).2 =
      some R := by
    rw [← Compose.projAC_state hr.toLocalRun hy i, hacstate]
    exact hres
  have hreport : SA.ToFGAt (tr.upTo (tr.time i)).projAC y i ell R :=
    ⟨Compose.projAC_callAt.mpr hc', hto, by
      rw [Compose.projAC_state hr.toLocalRun hy]
      exact hres'⟩
  have hRm : R ∈ (tr.state y i).fg.tree := by
    simpa only [hs] using Healing.toFG_mem_tree hr hy hreport
  have hPm := mem_of_honest_anc_at hrun hnc ht0 hle hy hPR hRm
  have hreach := fg_reachable_at hrun ht0 hle hy
  have hPRs := store_anc_of_honest_anc_at hrun hnc ht0 hle hy hPR hRm
  have hheight := h_le_of_store_anc hreach hPRs
  refine ⟨hPm, hRm, ?_⟩
  rcases hheight.lt_or_eq with hlt | heq
  · exact Or.inr hlt
  left
  have hf' : (H (tr.time i))ᶜ.ncard < 2 * sp.toParams.fg.q - sp.n := by
    have hbound := hf (tr.time i) ht0 hiT
    have hn := sp.toParams.hn
    change 0 < sp.n at hn
    change (H (tr.time i))ᶜ.ncard < 2 * ((2 * sp.n + 2) / 3) - sp.n
    omega
  obtain ⟨sg, hatt', ht, hfg'⟩ := Healing.toFG_attest hr.toLocalRun hy hc' hto hres'
  have hatt := ((Trace.upTo_callAt tr).mp hatt').2
  have ht' : tr.time (i + 1) = tr.time i := ht
  have hle' : ∀ k < i + 1, tr.time k ≤ tr.time i := fun k hk =>
    hrun.time_mono (Nat.lt_succ_iff.mp hk)
  have hs' := Trace.upTo_state tr y hle'
  have hfg : (tr.state y (i + 1)).fg = (tr.state y i).fg := by
    simpa only [hs, hs'] using hfg'
  obtain ⟨⟨E, hE, hEr, hER, hEh, hETh⟩, -⟩ :=
    Store.entry_state_of_source _ _ _ _ hreach R hRm
  have hEnt : EntryOf (tr.state y (i + 1)).fg R E ((tr.state y i).fg.σ P.root).h := by
    rw [hfg]
    exact ⟨⟨hE, hETh.trans hEr.symm⟩, hEh.trans heq.symm, hER⟩
  have hCh : ((tr.state y (i + 1)).fg.σ R.root).h = ((tr.state y i).fg.σ P.root).h := by
    rw [hfg]
    exact heq.symm
  have hTh : E.root = ((tr.state y i).fg.σ P.root).Th :=
    hEr.trans (Th_eq_of_anc hreach hPRs heq.symm)
  have hlock : (tr.state y (i + 1)).record.lock ((tr.state y i).fg.σ P.root).h = none ∨
      (tr.state y (i + 1)).record.lock ((tr.state y i).fg.σ P.root).h = some E.root := by
    rcases hkind heq.symm with hHZ | hk
    · rw [hHZ]
      exact Or.inl (lock_none_of_noAdvance_at hrun hna ht0 hle' hy hiT)
    · apply lock_free_or_entry_of_frame_at hrun hnc ht0 hle' hy hf' hEnt hCh
      rwa [hfg]
  have hrow := client_progress_of_lock_at hrun ht0 hle' ht'.le hy hatt hEnt hCh hlock
  rcases hrow with ⟨att, rfl, hah, haT⟩ | ⟨k, hk, att, hsign, hah, haT⟩
  · exact ⟨i + 1, att, ht'.symm ▸ hy, ⟨R, hatt⟩, ht'.le, hah, haT.trans hTh⟩
  · have hkt := hle' k hk
    exact ⟨k, att, hrun.antitone hkt hy, hsign, hkt, hah, haT.trans hTh⟩

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
