module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.StoredSource
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks

public section

/-! # Protected stored locks at an independently honest observation

Each lock's provenance is recovered on the reader's prefix through the observation. Source
votes are then compared in the historical universe, without retaining a common writer cohort.
-/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open AC (ACParams Payload Vote)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}
variable {hold : Time}

/-- Protected stored locks compare when the reader is honest after all their completed cuts. -/
theorem clean_stored_locks_compatible_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {i : Nat} {t : Time} (ht : 0 ≤ t) (hle : ∀ q < i, tr.time q ≤ t)
    (hy : y ∈ H t) (htb : t ≤ b)
    {l m : AC.Lock} (hl : l ∈ (tr.projAC.state y i).locks)
    (hm : m ∈ (tr.projAC.state y i).locks)
    (hls : cleanLabel sp a + sp.k + 2 ≤ l.slot)
    (hms : cleanLabel sp a + sp.k + 2 ≤ m.slot)
    {B C : AC.Blk sp.n (List (FG.Att sp.n))}
    (hB : B ∈ tr.HonestBlocksAt H) (hBr : B.root = l.block)
    (hC : C ∈ tr.HonestBlocksAt H) (hCr : C.root = m.block) :
    Compatible (tr.HonestBlocksAt H) B C := by
  have htmono := hp.run.time_mono
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have hac := Compose.goldilocks_ac_projection_from (hp.run.upTo ht) (hp.noColl.upTo t)
  rw [RunTrace.upTo_projAC] at hac
  have sub := RunTrace.honestBlocks_upTo_subset htmono (H := H) ht
  have state := Trace.upTo_state tr.projAC y hle
  have source : ∀ {m : AC.Lock}, m ∈ (tr.projAC.state y i).locks →
      ∃ M ∈ tr.HonestBlocksAt H, M.root = m.block ∧ ∃ E,
        Anc (tr.HonestBlocksAt H) M E ∧ ∃ r < i, ∃ CV,
          AC.ResultAt tr.projAC y r m.slot E CV ∨
            AC.OptimisticLockAt tr.projAC y r m.slot E CV := by
    intro m hm
    obtain ⟨M, hM, hMr, E, hME, r, hri, CV, hE⟩ :=
      AC.lock_below_origin hac.localRun hac.vstart hy i m (state ▸ hm)
    exact ⟨M, sub hM, hMr, E, hME.mono sub, r, hri, CV,
      hE.imp (fun h => ((AC.upTo_resultAt htmono).mp h).2)
        (fun h => ((AC.upTo_optimisticLockAt htmono).mp h).2)⟩
  have ordered : ∀ {l m : AC.Lock} {B C : AC.Blk sp.n (List (FG.Att sp.n))},
      l ∈ (tr.projAC.state y i).locks → m ∈ (tr.projAC.state y i).locks →
      cleanLabel sp a + sp.k + 2 ≤ l.slot → l.slot < m.slot →
      B ∈ tr.HonestBlocksAt H → B.root = l.block →
      C ∈ tr.HonestBlocksAt H → C.root = m.block →
      Compatible (tr.HonestBlocksAt H) B C := by
    intro l m B C hl hm hls hlm hB hBr hC hCr
    obtain ⟨q, hqi, D, hD, L, hL, hLr, hLD⟩ : ∃ q < i, ∃ D,
        ((∃ CV, AC.FastLockAt tr.projAC y q l.slot D CV) ∨
          AC.SlowLockAt tr.projAC y q l.slot D) ∧
        ∃ L ∈ tr.HonestBlocksAt H, L.root = l.block ∧ Anc (tr.HonestBlocksAt H) L D := by
      cases hf : l.fast
      · obtain ⟨q, hqi, D, ⟨ell, R, hu, hconf, hdeep⟩, L, hL, hLr, hLD⟩ :=
          AC.slow_lock_provenance hac.localRun hac.vstart hy i l (state ▸ hl) hf
        obtain ⟨hqt, hu⟩ := (AC.upTo_updateAt htmono).mp hu
        have hstate := Trace.upTo_state tr.projAC y (d := t) (i := q)
          fun _ hk => (htmono hk.le).trans hqt
        have hslow : AC.SlowLockAt tr.projAC y q l.slot D := by
          refine ⟨ell, R, hu, ?_, ?_⟩
          · rwa [hstate] at hconf
          · simpa only [hstate, Trace.upTo_time] using hdeep
        exact ⟨q, hqi, D, Or.inr hslow, L, sub hL, hLr, hLD.mono sub⟩
      · obtain ⟨q, hqi, D, CV, hD, L, hL, hLr, hLD⟩ :=
          AC.fast_lock_provenance hac.localRun hac.vstart hy i l (state ▸ hl) hf
        exact ⟨q, hqi, D, Or.inl ⟨CV, ((AC.upTo_fastLockAt htmono).mp hD).2⟩,
          L, sub hL, hLr, hLD.mono sub⟩
    obtain rfl : B = L := hU.1 hB hL (hBr.trans hLr.symm)
    obtain ⟨M, hM, hMr, E, hME, r, hri, CV, hE⟩ := source hm
    obtain rfl : C = M := hU.1 hC hM (hCr.trans hMr.symm)
    have hyr := hp.run.antitone (hle r hri) hy
    have hrb := (hle r hri).trans htb
    have hts := hp.clean_window_timing_at (hls.trans hlm.le) m.slot (by
      have := sp.two_le_k
      omega)
    have supporter : ∃ z j, z ∈ H (tr.time r) ∧ j ≤ r ∧ ∃ e,
        AC.VoteAt tr.projAC z j e ∧ e.msg.slot = m.slot ∧
          AC.VoteExtends (tr.HonestBlocksAt H) e.msg E := by
      rcases hE with hE | hE
      · obtain ⟨z, hz, j, hjr, e, he, _, hes, hEH⟩ :=
          ProposalImpl.result_supporter_at hp hyr hE .refl hrb hts
        exact ⟨z, j, hz, hjr.le, e, he, hes, hEH⟩
      · exact (hp.optimistic_supporter_at hyr hrb (Healing.gbar_le_of_cutZ_le sp hts) hE).2
    obtain ⟨z, j, hz, hjr, e, ⟨ell, he⟩, hes, Hd, hHd, heHd, hEHd⟩ := supporter
    have hzj := hp.run.antitone (htmono hjr) hz
    have hyq := hp.run.antitone (hle q hqi) hy
    have hqb := (hle q hqi).trans htb
    have hjb := (htmono hjr).trans hrb
    have hv : AC.VoteExtends (tr.HonestBlocksAt H) e.msg D := by
      rcases hD with ⟨CV, hD⟩ | hD
      · exact hp.fast_source_votes_before_at hyq hD hls hqb j hjb z hzj ell e he (by omega)
      · exact hp.slow_source_votes_before_at hyq hD hls hqb j hjb z hzj ell e he (by omega)
    obtain ⟨Hd', hHd', heHd', hDHd⟩ := hv
    obtain rfl : Hd' = Hd := hU.1 hHd' hHd (heHd'.trans heHd.symm)
    exact AC.anc_total hU (hLD.trans hDHd) (hME.trans hEHd)
  rcases lt_trichotomy l.slot m.slot with h | h | h
  · exact ordered hl hm hls h hB hBr hC hCr
  · obtain ⟨L, hL, hLr, D, hLD, q, hqi, CV, hD⟩ := source hl
    obtain ⟨M, hM, hMr, E, hME, r, hri, DV, hE⟩ := source hm
    obtain rfl : B = L := hU.1 hB hL (hBr.trans hLr.symm)
    obtain rfl : C = M := hU.1 hC hM (hCr.trans hMr.symm)
    have hcomp := hp.sources_same_label_compatible_at
      (hp.run.antitone (hle q hqi) hy) (hp.run.antitone (hle r hri) hy) hD (h ▸ hE)
      ((hle q hqi).trans htb) ((hle r hri).trans htb)
      (hp.clean_window_timing_at hls l.slot (by have := sp.two_le_k; omega))
    rcases hcomp with hDE | hED
    · exact AC.anc_total hU (hLD.trans hDE) hME
    · exact AC.anc_total hU hLD (hME.trans hED)
  · exact (ordered hm hl hms h hC hCr hB hBr).symm

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
