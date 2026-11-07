module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.SlowVotes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.FastVotes
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.FoundationSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks

public section

/-! # Older live locks compared with a clean result prefix

Lock provenance is read on the voter's own prefix. Each recovered writer is honest at its
write, and the result's supporter is transported back only to its actual voting cut.
-/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- Every older live stored lock compares with a clean raw-result prefix. -/
theorem result_prefix_stored_locks_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {r s i : Nat} (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time i))
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hres : SA.ResultAt tr.projAC x r s C CV) (hBC : Anc (tr.HonestBlocksAt H) B C)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrb : tr.time r ≤ b) (hib : tr.time i ≤ b)
    (hi : s + 1 ≤ sp.slot (tr.time i)) :
    ∀ l ∈ (tr.projAC.state y i).locks,
      sp.slot (tr.time i) ≤ l.slot + sp.k → l.slot ≤ s →
      ∀ Y ∈ tr.HonestBlocksAt H, Y.root = l.block → Compatible (tr.HonestBlocksAt H) Y B := by
  have hm := hp.run.time_mono
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hac := Compose.goldilocks_ac_projection sp ro dg (H (tr.time i))
    (tr.upTo (tr.time i)) proposer (hp.run.upTo (hp.run.time_nonneg i)) (hp.noColl.upTo _)
  rw [RunTrace.upTo_projAC] at hac
  have sub := RunTrace.honestBlocks_upTo_subset hm (H := H) (hp.run.time_nonneg i)
  have hclean : cleanLabel sp a + sp.k + 2 ≤ s := by
    have := sp.two_le_k
    omega
  have hts := hp.clean_window_timing_at hclean s (by
    have := sp.two_le_k
    omega)
  have down : ∀ {L D}, Anc (tr.HonestBlocksAt H) L D →
      Compatible (tr.HonestBlocksAt H) C D → Compatible (tr.HonestBlocksAt H) L B := by
    intro L D hLD hCD
    rcases hCD with h | h
    · exact SA.anc_total hU hLD (hBC.trans h)
    · exact SA.anc_total hU (hLD.trans h) hBC
  intro l hl hlive hle Y hY hYr
  rw [← Trace.upTo_state tr.projAC y (d := tr.time i) fun _ hq => hm hq.le] at hl
  rcases hle.lt_or_eq with hls | hls
  · have hclean : cleanLabel sp a + sp.k + 2 ≤ l.slot := by omega
    have compare : ∀ {q D}, y ∈ H (tr.time q) → tr.time q ≤ b →
        ((∃ CV, SA.FastLockAt tr.projAC y q l.slot D CV) ∨
          SA.SlowLockAt tr.projAC y q l.slot D) → Compatible (tr.HonestBlocksAt H) C D := by
      intro q D hyq hqb hsource
      obtain ⟨z, hz, j, hjr, e, ⟨ell, hcast⟩, _, hes, Hd, hHd, he, hCH⟩ :=
        ProposalImpl.result_supporter_at hp hc hx hres .refl hrb hts
      have hzj := hp.run.antitone (hm hjr.le) hz
      have hjb := (hm hjr.le).trans hrb
      have hv : SA.VoteExtends (tr.HonestBlocksAt H) e.msg D := by
        rcases hsource with ⟨CV', hfast⟩ | hslow
        · exact hp.fast_source_votes_before_at hc hyq hfast hclean hqb j hjb z hzj ell e
            hcast (by omega)
        · exact hp.slow_source_votes_before_at hc hyq hslow hclean hqb j hjb z hzj ell e
            hcast (by omega)
      obtain ⟨Hd', hHd', he', hDH⟩ := hv
      obtain rfl : Hd' = Hd := hU.1 hHd' hHd (he'.trans he.symm)
      exact SA.anc_total hU hCH hDH
    cases hf : l.fast
    · obtain ⟨q, hqi, D, hsl, L, hL, hLr, hLD⟩ :=
        SA.slow_lock_provenance hac.localRun hy i l hl hf
      obtain rfl : Y = L := hU.1 hY (sub hL) (hYr.trans hLr.symm)
      obtain ⟨ell, R, hu, hconf, hdeep⟩ := hsl
      obtain ⟨hqd, hu⟩ := (SA.upTo_updateAt hm).mp hu
      have hstate := Trace.upTo_state tr.projAC y (d := tr.time i)
        (i := q) fun _ hk => (hm hk.le).trans hqd
      have hsl' : SA.SlowLockAt tr.projAC y q l.slot D := by
        refine ⟨ell, R, hu, ?_, ?_⟩
        · rwa [hstate] at hconf
        · simpa only [hstate, Trace.upTo_time] using hdeep
      exact down (hLD.mono sub) (compare (hp.run.antitone (hm hqi.le) hy)
        ((hm hqi.le).trans hib) (Or.inr hsl'))
    · obtain ⟨q, hqi, D, CV', hfl, L, hL, hLr, hLD⟩ :=
        SA.fast_lock_provenance hac.localRun hy i l hl hf
      obtain rfl : Y = L := hU.1 hY (sub hL) (hYr.trans hLr.symm)
      exact down (hLD.mono sub) (compare (hp.run.antitone (hm hqi.le) hy)
        ((hm hqi.le).trans hib) (Or.inl ⟨CV', ((SA.upTo_fastLockAt hm).mp hfl).2⟩))
  · obtain ⟨L, hL, hLr, D, hLD, q, hqi, CV', hD⟩ :=
      SA.lock_below_origin hac.localRun hy i l hl
    obtain rfl : Y = L := hU.1 hY (sub hL) (hYr.trans hLr.symm)
    rw [hls] at hD
    have hD' := hD.imp (fun h => ((SA.upTo_resultAt hm).mp h).2)
      (fun h => ((SA.upTo_optimisticLockAt hm).mp h).2)
    exact down (hLD.mono sub) (hp.result_source_compatible_at hx
      (hp.run.antitone (hm hqi.le) hy) hres hD' hrb ((hm hqi.le).trans hib) hts)

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
