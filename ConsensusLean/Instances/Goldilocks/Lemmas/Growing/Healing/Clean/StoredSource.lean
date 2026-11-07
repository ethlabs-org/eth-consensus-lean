module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Sources
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks

public section

/-! # A clean source compared with a protected stored lock

The lock reader is honest at an observation after all completed cuts, not necessarily at the
next event. Provenance is recovered from exactly that finite prefix.
-/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- A clean raw source compares with a protected stored lock of an honest reader. -/
theorem clean_source_stored_lock_compatible_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {r s i : Nat} {t : Time} (hx : x ∈ H (tr.time r))
    (ht : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t) (hy : y ∈ H t) (htb : t ≤ b)
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hB : SA.ResultAt tr.projAC x r s B CV ∨ SA.OptimisticLockAt tr.projAC x r s B CV)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrb : tr.time r ≤ b) {l : SA.Lock}
    (hl : l ∈ (tr.projAC.state y i).locks) (hls : cleanLabel sp a + sp.k + 2 ≤ l.slot)
    (hC : C ∈ tr.HonestBlocksAt H) (hCr : C.root = l.block) :
    Compatible (tr.HonestBlocksAt H) B C := by
  have hm := hp.run.time_mono
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hac := Compose.goldilocks_ac_projection sp ro dg (H t) (tr.upTo t) proposer
    (hp.run.upTo ht) (hp.noColl.upTo t)
  rw [RunTrace.upTo_projAC] at hac
  have sub := RunTrace.honestBlocks_upTo_subset hm (H := H) ht
  rw [← Trace.upTo_state tr.projAC y hle] at hl
  by_cases hsl : s ≤ l.slot
  · obtain ⟨L, hL, hLr, D, hLD, q, hqi, DV, hD⟩ :=
      SA.lock_below_origin hac.localRun hy i l hl
    obtain rfl : C = L := hU.1 hC (sub hL) (hCr.trans hLr.symm)
    have hD' := hD.imp (fun h => ((SA.upTo_resultAt hm).mp h).2)
      (fun h => ((SA.upTo_optimisticLockAt hm).mp h).2)
    rcases hp.clean_sources_compatible_at hc hx (hp.run.antitone (hle q hqi) hy)
        hB hD' hs (hs.trans hsl) hrb ((hle q hqi).trans htb) with h | h
    · exact SA.anc_total hU h (hLD.mono sub)
    · exact Or.inr ((hLD.mono sub).trans h)
  · have compare : ∀ {q D}, q < i →
        ((∃ DV, SA.FastLockAt tr.projAC y q l.slot D DV) ∨
          SA.SlowLockAt tr.projAC y q l.slot D) → Compatible (tr.HonestBlocksAt H) B D := by
      intro q D hqi hD
      have hts := hp.clean_window_timing_at (s := s)
        (by have := sp.two_le_k; omega) s (by have := sp.two_le_k; omega)
      have supporter : ∃ z j, z ∈ H (tr.time r) ∧ j ≤ r ∧ ∃ e,
          SA.VoteAt tr.projAC z j e ∧ e.msg.slot = s ∧
            SA.VoteExtends (tr.HonestBlocksAt H) e.msg B := by
        rcases hB with hB | hB
        · obtain ⟨z, hz, j, hjr, e, he, _, hes, hBH⟩ :=
            ProposalImpl.result_supporter_at hp hc hx hB .refl hrb hts
          exact ⟨z, j, hz, hjr.le, e, he, hes, hBH⟩
        · exact (hp.optimistic_supporter_at hx hrb hB).2
      obtain ⟨z, j, hz, hjr, e, ⟨ell, he⟩, hes, Hd, hHd, heHd, hBHd⟩ := supporter
      have hzj := hp.run.antitone (hm hjr) hz
      have hyq := hp.run.antitone (hle q hqi) hy
      have hqb := (hle q hqi).trans htb
      have hjb := (hm hjr).trans hrb
      have hv : SA.VoteExtends (tr.HonestBlocksAt H) e.msg D := by
        rcases hD with ⟨DV, hD⟩ | hD
        · exact hp.fast_source_votes_before_at hc hyq hD hls hqb j hjb z hzj ell e he
            (by omega)
        · exact hp.slow_source_votes_before_at hc hyq hD hls hqb j hjb z hzj ell e he
            (by omega)
      obtain ⟨Hd', hHd', heHd', hDHd⟩ := hv
      obtain rfl : Hd' = Hd := hU.1 hHd' hHd (heHd'.trans heHd.symm)
      exact SA.anc_total hU hBHd hDHd
    cases hf : l.fast
    · obtain ⟨q, hqi, D, hD, L, hL, hLr, hLD⟩ :=
        SA.slow_lock_provenance hac.localRun hy i l hl hf
      obtain rfl : C = L := hU.1 hC (sub hL) (hCr.trans hLr.symm)
      obtain ⟨ell, R, hu, hconf, hdeep⟩ := hD
      obtain ⟨hqt, hu⟩ := (SA.upTo_updateAt hm).mp hu
      have hstate := Trace.upTo_state tr.projAC y (d := t) (i := q)
        fun _ hk => (hm hk.le).trans hqt
      have hD' : SA.SlowLockAt tr.projAC y q l.slot D := by
        refine ⟨ell, R, hu, ?_, ?_⟩
        · rwa [hstate] at hconf
        · simpa only [hstate, Trace.upTo_time] using hdeep
      rcases compare hqi (Or.inr hD') with h | h
      · exact SA.anc_total hU h (hLD.mono sub)
      · exact Or.inr ((hLD.mono sub).trans h)
    · obtain ⟨q, hqi, D, DV, hD, L, hL, hLr, hLD⟩ :=
        SA.fast_lock_provenance hac.localRun hy i l hl hf
      obtain rfl : C = L := hU.1 hC (sub hL) (hCr.trans hLr.symm)
      rcases compare hqi (Or.inl ⟨DV, ((SA.upTo_fastLockAt hm).mp hD).2⟩) with h | h
      · exact SA.anc_total hU h (hLD.mono sub)
      · exact Or.inr ((hLD.mono sub).trans h)

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
