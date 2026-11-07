module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.ResultVotes

public section

/-! # Comparability of clean raw sources under growing faults

The later source supplies an actual vote. Both its writer and the earlier source's writer
are read at their own write; the supporter's honesty is transported back to its voting cut.
-/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- Two clean raw sources, each of a writer honest at its write, compare. -/
theorem clean_sources_compatible_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {r q s t : Nat} {C D : SA.Blk sp.n (List (FG.Att sp.n))}
    {CV DV : Set (SA.Vote sp.n)} (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time q))
    (hC : SA.ResultAt tr.projAC x r s C CV ∨ SA.OptimisticLockAt tr.projAC x r s C CV)
    (hD : SA.ResultAt tr.projAC y q t D DV ∨ SA.OptimisticLockAt tr.projAC y q t D DV)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (ht : cleanLabel sp a + 2 * sp.k + 1 ≤ t)
    (hrb : tr.time r ≤ b) (hqb : tr.time q ≤ b) :
    Compatible (tr.HonestBlocksAt H) C D := by
  have hU := Compose.Growing.honest_blocks_coherent hp.run hp.noColl
  have ordered : ∀ {x y r q s t C D CV DV}, x ∈ H (tr.time r) → y ∈ H (tr.time q) →
      (SA.ResultAt tr.projAC x r s C CV ∨ SA.OptimisticLockAt tr.projAC x r s C CV) →
      (SA.ResultAt tr.projAC y q t D DV ∨ SA.OptimisticLockAt tr.projAC y q t D DV) →
      cleanLabel sp a + 2 * sp.k + 1 ≤ s → s < t → tr.time r ≤ b → tr.time q ≤ b →
      Compatible (tr.HonestBlocksAt H) C D := by
    intro x y r q s t C D CV DV hx hy hC hD hs hst hrb hqb
    have hclean : cleanLabel sp a + sp.k + 2 ≤ s := by have := sp.two_le_k; omega
    have hts := hp.clean_window_timing_at (hclean.trans hst.le) t (by
      have := sp.two_le_k
      omega)
    have supporter : ∃ z j, z ∈ H (tr.time q) ∧ j ≤ q ∧ ∃ e,
        SA.VoteAt tr.projAC z j e ∧ e.msg.slot = t ∧
          SA.VoteExtends (tr.HonestBlocksAt H) e.msg D := by
      rcases hD with hD | hD
      · obtain ⟨z, hz, j, hjq, e, hv, _, hes, hDH⟩ :=
          ProposalImpl.result_supporter_at hp hc hy hD .refl hqb hts
        exact ⟨z, j, hz, hjq.le, e, hv, hes, hDH⟩
      · exact (hp.optimistic_supporter_at hy hqb hD).2
    obtain ⟨z, j, hz, hjq, e, ⟨ell, hcast⟩, hes, Hd, hHd, he, hDH⟩ := supporter
    have hzj := hp.run.antitone (hp.run.time_mono hjq) hz
    have hjb := (hp.run.time_mono hjq).trans hqb
    have hv : SA.VoteExtends (tr.HonestBlocksAt H) e.msg C := by
      rcases hC with hC | hC
      · exact hp.clean_result_prefix_votes_before_at hc hx hC .refl hs hrb j hjb z hzj
          ell e hcast (by omega)
      · exact hp.fast_source_votes_before_at hc hx (Or.inr hC) hclean hrb j hjb z hzj
          ell e hcast (by omega)
    obtain ⟨Hd', hHd', he', hCH⟩ := hv
    obtain rfl : Hd' = Hd := hU.1 hHd' hHd (he'.trans he.symm)
    exact SA.anc_total hU hCH hDH
  rcases lt_trichotomy s t with h | rfl | h
  · exact ordered hx hy hC hD hs h hrb hqb
  · exact hp.sources_same_label_compatible_at hx hy hC hD hrb hqb
      (hp.clean_window_timing_at (s := s) (by have := sp.two_le_k; omega) s (by
        have := sp.two_le_k
        omega))
  · exact (ordered hy hx hD hC ht h hqb hrb).symm

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
