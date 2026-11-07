module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.OldSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockProvenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock

public section

/-! # Old read-point locks at honest voting cuts

The voter's local provenance is retained through its cast. Each earlier write is
therefore honest at its own cut, without any honesty premise after the cast.
-/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- Non-current live read-point locks descend from an earlier clean raw write. -/
theorem vote_old_lock_source_before_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {j u : Nat} (hy : y ∈ H (tr.time j))
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y j ell e) (hes : e.msg.slot = u)
    (hR : drainTime sp a ≤ sp.ts u)
    {l : SA.Lock} (hl : l ∈ e.readPoint.locks) (hne : l.slot ≠ u)
    (hlive : sp.slot (tr.time j) ≤ l.slot + sp.k)
    {L : SA.Blk sp.n (List (FG.Att sp.n))}
    (hL : L ∈ ell.frame.tree) (hLr : L.root = l.block) :
    ∃ r D, r < j ∧ cleanLabel sp a + sp.k + 2 ≤ l.slot ∧ l.slot < u ∧
      y ∈ H (tr.time r) ∧
      ((∃ CV, SA.FastLockAt tr.projAC y r l.slot D CV) ∨
        SA.SlowLockAt tr.projAC y r l.slot D) ∧
      Anc (tr.HonestBlocksAt H) (ell.frame.viableAncestor L) D := by
  have hm := hp.run.time_mono
  have ht := hp.run.time_nonneg j
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time j))
    (tr.upTo (tr.time j)) proposer (hp.run.upTo ht) (hp.noColl.upTo _)).localRun
  have hc' : SA.CastAt (tr.upTo (tr.time j)).projAC y j ell e := by
    rw [RunTrace.upTo_projAC]
    exact (SA.upTo_castAt).mpr ⟨le_rfl, hc⟩
  obtain ⟨hPhi, hPhiU⟩ := SA.frameIn_of_callAt hr hy hc'.1
  have hslot : sp.slot (tr.time j) = u := ((SA.castAt_spec hr hy hc').2.1).symm.trans hes
  have hclean : cleanLabel sp a + sp.k + 2 ≤ l.slot := by
    rw [Healing.drainTime_eq] at hR
    have := (SA.ts_le_iff sp).mp hR
    rw [hslot] at hlive
    rw [Healing.cleanLabel_eq]
    omega
  have hu : 0 < u := by
    rw [Healing.drainTime_eq] at hR
    have := (SA.ts_le_iff sp).mp hR
    omega
  obtain ⟨l₀, hl₀, hs, B, hB, hBr, L', hL', hL'r, hLB⟩ :=
    SA.readPoint_locks_below_stored hr hy hc'
      (by change 0 < sp.slot (tr.time j); rw [hslot]; exact hu) l hl
      (by change l.slot ≠ sp.slot (tr.time j); simpa only [hslot] using hne)
  obtain rfl : L' = L := hPhi.coherent.1 hL' hL (hL'r.trans hLr.symm)
  obtain ⟨r, hrj, D, hraw, X, hX, hXr, hXD⟩ :
      ∃ r < j, ∃ D,
        ((∃ CV, SA.FastLockAt (tr.upTo (tr.time j)).projAC y r l₀.slot D CV) ∨
          SA.SlowLockAt (tr.upTo (tr.time j)).projAC y r l₀.slot D) ∧
        ∃ X ∈ (tr.upTo (tr.time j)).HonestBlocks (H (tr.time j)),
          X.root = l₀.block ∧ Anc ((tr.upTo (tr.time j)).HonestBlocks (H (tr.time j))) X D := by
    cases hf : l₀.fast with
    | false =>
      obtain ⟨r, hrj, D, hslow, hX⟩ := SA.slow_lock_provenance hr hy j l₀ hl₀ hf
      exact ⟨r, hrj, D, Or.inr hslow, hX⟩
    | true =>
      obtain ⟨r, hrj, D, CV, hfast, hX⟩ := SA.fast_lock_provenance hr hy j l₀ hl₀ hf
      exact ⟨r, hrj, D, Or.inl ⟨CV, hfast⟩, hX⟩
  obtain rfl : X = B := hr.coherent.1 hX (hPhiU hB) (hXr.trans hBr.symm)
  have hrtime := hm hrj.le
  have hraw₀ : (∃ CV, SA.FastLockAt tr.projAC y r l₀.slot D CV) ∨
      SA.SlowLockAt tr.projAC y r l₀.slot D := by
    rw [RunTrace.upTo_projAC] at hraw
    rcases hraw with ⟨CV, hf⟩ | hs
    · exact Or.inl ⟨CV, (SA.upTo_fastLockAt hm).mp hf |>.2⟩
    · rcases hs with ⟨ell', C, hu, hC, hslow⟩
      rw [Trace.upTo_time,
        Trace.upTo_state tr.projAC y (fun _ hq => (hm hq.le).trans hrtime)] at hslow
      refine Or.inr ⟨ell', C, (SA.upTo_updateAt hm).mp hu |>.2, ?_, hslow⟩
      rwa [Trace.upTo_state tr.projAC y (fun _ hq => (hm hq.le).trans hrtime)] at hC
  have hle : l₀.slot ≤ u := by
    have hts : sp.ts l₀.slot ≤ tr.time r := by
      rcases hraw₀ with ⟨CV, hf⟩ | ⟨ell', C, hu, _⟩
      · exact ts_le_of_fastLock_at hp.run hf
      · have ht' : tr.time r = sp.ts l₀.slot + 6 * sp.Δ := hu.2.2.1
        rw [ht']
        have := sp.toParams.hΔ
        linarith
    have := (SA.ts_le_iff_le_slot sp (hp.run.time_nonneg j) l₀.slot).mp (hts.trans hrtime)
    omega
  refine ⟨r, D, hrj, hclean, by omega, hp.run.antitone hrtime hy, hs ▸ hraw₀, ?_⟩
  exact Anc.mono (RunTrace.honestBlocks_upTo_subset hm ht)
    ((Anc.mono hPhiU ((SA.anc_viableAncestor ell.frame L').trans hLB)).trans hXD)

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end
