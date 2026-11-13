module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Sources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.High
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Later

public section

/-! # A clean raw source compared with a bounded high origin -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload Vote)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- A clean raw source compares with each high origin written through the horizon. -/
theorem clean_source_compatible_high_origin_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} {r s : Nat} (hx : x ∈ H (tr.time r))
    {C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hC : SA.ResultAt tr.projAC x r s C CV ∨ SA.OptimisticLockAt tr.projAC x r s C CV)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrb : tr.time r ≤ b)
    {y : Fin sp.n} {q t : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g y q t D) (hqb : tr.time q ≤ b) :
    Compatible (tr.HonestBlocksAt H) C D := by
  have hm := hp.run.time_mono
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hU := hac.localRun.coherent
  have hclean : cleanLabel sp a + sp.k + 2 ≤ s := by have := sp.two_le_k; omega
  have hts := hp.clean_window_timing_at hclean s (by have := sp.two_le_k; omega)
  rcases lt_trichotomy t s with h | rfl | h
  · have supporter : ∃ z j, z ∈ H (tr.time r) ∧ j ≤ r ∧ ∃ e,
        SA.VoteAt tr.projAC z j e ∧ e.msg.slot = s ∧
          SA.VoteExtends (tr.HonestBlocksAt H) e.msg C := by
      rcases hC with hC | hC
      · obtain ⟨z, hz, j, hjr, e, hv, _, hes, hCH⟩ :=
          ProposalImpl.result_supporter_at hp hc hx hC .refl hrb hts
        exact ⟨z, j, hz, hjr.le, e, hv, hes, hCH⟩
      · exact (hp.optimistic_supporter_at hx hrb hC).2
    obtain ⟨z, j, hz, hjr, e, hv, hes, hCH⟩ := supporter
    exact hp.target_compatible_older_origin_at ho hqb (hp.run.antitone (hm hjr) hz)
      hv ((hm hjr).trans hrb) hes h hCH
  · obtain ⟨CV', ell, E, hcall, hfl, hD⟩ := ho.2.2.1
    obtain ⟨ell', hc', hE⟩ := Healing.fastLock_mem hfl
    obtain rfl : ell = ell' := Option.some.inj (hcall.2.symm.trans hc'.2)
    have hframe := frame_tree_subset_at hp.run hp.noColl ho.1 hcall
    have sub : ell.frame.tree ⊆ tr.HonestBlocksAt H := fun _ hB =>
      ⟨y, q, tr.time q, hp.run.time_nonneg q, fun _ hk => hm hk.le, ho.1, hframe.2 hB⟩
    have hDE : Anc (tr.HonestBlocksAt H) D E := by
      rw [hD]
      exact (SA.anc_viableAncestor ell.frame E).mono sub
    have hCE : Compatible (tr.HonestBlocksAt H) C E := by
      rcases hfl with ⟨ellX, R, hu, hR, hfast, _⟩ | hop
      · have hER := ((SA.deepest_mem hfast).1.1.2.2).mono
          ((SA.frameIn_of_callAt (hac.upTo (hp.run.time_nonneg q)).localRun ho.1
            ((Trace.upTo_callAt _).mpr ⟨le_rfl, hu.1⟩)).2)
        have hRC := hp.result_source_compatible_at ho.1 hx ⟨ellX, hu, hR, rfl⟩ hC
          hqb hrb hts
        rcases hRC with h | h
        · exact Or.inr (hER.trans h)
        · exact SA.anc_total hU h hER
      · exact hp.sources_same_label_compatible_at hx ho.1 hC (Or.inr hop) hrb hqb hts
    rcases hCE with h | h
    · exact SA.anc_total hU h hDE
    · exact Or.inr (hDE.trans h)
  · obtain ⟨CV', ell, E, hcall, hfl, hD⟩ := ho.2.2.1
    obtain ⟨ell', hc', hE⟩ := Healing.fastLock_mem hfl
    obtain rfl : ell = ell' := Option.some.inj (hcall.2.symm.trans hc'.2)
    have hframe := frame_tree_subset_at hp.run hp.noColl ho.1 hcall
    have sub : ell.frame.tree ⊆ tr.HonestBlocksAt H := fun _ hB =>
      ⟨y, q, tr.time q, hp.run.time_nonneg q, fun _ hk => hm hk.le, ho.1, hframe.2 hB⟩
    have hDE : Anc (tr.HonestBlocksAt H) D E := by
      rw [hD]
      exact (SA.anc_viableAncestor ell.frame E).mono sub
    have hf : 2 * (H (tr.time q))ᶜ.ncard < sp.n := by
      have := hp.faults _ (hp.run.time_nonneg q) hqb
      have := Fin.pos x
      omega
    have hEC := SA.fastLock_compatible_of_votes (hac.upTo (hp.run.time_nonneg q)) _
      SA.CommitteeP.full ho.1 (Nat.lt_succ_self q) ((SA.upTo_fastLockAt hm).mpr ⟨le_rfl, hfl⟩)
      (SA.cs2_full hp.stock hf) (B := C) (by
        intro z hz j hj e hv hes
        obtain ⟨hjq, hv⟩ := SA.upTo_voteAt.mp hv
        have hzj := hp.run.antitone hjq hz
        obtain ⟨ell, hcast⟩ := hv
        have hjb := hjq.trans hqb
        rcases hC with hC | hC
        · exact hp.clean_result_prefix_votes_before_at hc hx hC .refl hs hrb j hjb z hzj
            ell e hcast (by omega)
        · exact hp.fast_source_votes_before_at hc hx (Or.inr hC) hclean hrb j hjb z hzj
            ell e hcast (by omega))
    rcases hEC with h | h
    · exact Or.inr (hDE.trans h)
    · exact SA.anc_total hU h hDE

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
