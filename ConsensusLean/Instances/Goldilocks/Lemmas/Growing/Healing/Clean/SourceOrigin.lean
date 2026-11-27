module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Sources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.High
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Trees
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Node.Family
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Compatible.Later
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.HalfCommittee
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.OriginLabel
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.HighOriginSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith

public section

/-! # A clean raw source compared with a bounded high origin -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open AC (ACParams Payload Vote)

variable {sp : ACParams}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}
variable {hold : Time}

/-- A clean raw source compares with each high origin written through the horizon. -/
theorem clean_source_compatible_high_origin_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {r s : Nat} (hx : x ∈ H (tr.time r))
    {C : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hC : AC.ResultAt tr.projAC x r s C CV ∨ AC.OptimisticLockAt tr.projAC x r s C CV)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrb : tr.time r ≤ b)
    {y : Fin sp.n} {q t : Nat} {D : AC.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g y q t D) (hqb : tr.time q ≤ b) :
    Compatible (tr.HonestBlocksAt H) C D := by
  have hyo := hp.run.antitone (le_max_right _ _) ho.1
  have hm := hp.run.time_mono
  have hac := Compose.Growing.goldilocks_ac_projection_from hp.run hp.noColl
  have hU := hac.localRun.coherent
  have hclean : cleanLabel sp a + sp.k + 2 ≤ s := by have := sp.two_le_k; omega
  have hts := hp.clean_window_timing_at hclean s (by have := sp.two_le_k; omega)
  rcases lt_trichotomy t s with h | rfl | h
  · have supporter : ∃ z j, z ∈ H (tr.time r) ∧ j ≤ r ∧ ∃ e,
        AC.VoteAt tr.projAC z j e ∧ e.msg.slot = s ∧
          AC.VoteExtends (tr.HonestBlocksAt H) e.msg C := by
      rcases hC with hC | hC
      · obtain ⟨z, hz, j, hjr, e, hv, _, hes, hCH⟩ :=
          ProposalImpl.result_supporter_at hp hx hC .refl hrb hts
        exact ⟨z, j, hz, hjr.le, e, hv, hes, hCH⟩
      · exact (hp.optimistic_supporter_at hx hrb (Healing.gbar_le_of_cutZ_le sp hts) hC).2
    obtain ⟨z, j, hz, hjr, e, hv, hes, hCH⟩ := supporter
    exact hp.target_compatible_older_origin_at ho hqb (hp.run.antitone (hm hjr) hz)
      hv ((hm hjr).trans hrb) hes h hCH
  · obtain ⟨CV', ell, E, hcall, hfl, hD⟩ := ho.2.2.1
    obtain ⟨ell', hc', hE⟩ := Healing.fastLock_mem hfl
    obtain rfl : ell = ell' := Option.some.inj (hcall.2.symm.trans hc'.2)
    have hframe := frame_tree_subset_at hp.run hp.noColl hyo hcall
    have sub : ell.frame.tree ⊆ tr.HonestBlocksAt H := fun _ hB =>
      ⟨y, q, tr.time q, hp.run.time_nonneg q, fun _ hk => hm hk.le, hyo, hframe.2 hB⟩
    have hDE : Anc (tr.HonestBlocksAt H) D E := by
      rw [hD]
      exact (AC.anc_viableAncestor ell.frame E).mono sub
    have hCE : Compatible (tr.HonestBlocksAt H) C E := by
      rcases hfl with ⟨ellX, R, hu, hR, hfast, _⟩ | hop
      · have hER := ((AC.deepest_mem hfast).1.1.2.2).mono
          ((AC.frameIn_of_callAt (hac.upTo (hp.run.time_nonneg q)).localRun hyo
            ((Trace.upTo_callAt _).mpr ⟨le_rfl, hu.1⟩)).2)
        have hRC := hp.result_source_compatible_at hyo hx ⟨ellX, hu, hR, rfl⟩ hC
          hqb hrb hts
        rcases hRC with h | h
        · exact Or.inr (hER.trans h)
        · exact AC.anc_total hU h hER
      · exact hp.sources_same_label_compatible_at hx hyo hC (Or.inr hop) hrb hqb hts
    rcases hCE with h | h
    · exact AC.anc_total hU h hDE
    · exact Or.inr (hDE.trans h)
  · obtain ⟨CV', ell, E, hcall, hfl, hD⟩ := ho.2.2.1
    obtain ⟨ell', hc', hE⟩ := Healing.fastLock_mem hfl
    obtain rfl : ell = ell' := Option.some.inj (hcall.2.symm.trans hc'.2)
    have hframe := frame_tree_subset_at hp.run hp.noColl hyo hcall
    have sub : ell.frame.tree ⊆ tr.HonestBlocksAt H := fun _ hB =>
      ⟨y, q, tr.time q, hp.run.time_nonneg q, fun _ hk => hm hk.le, hyo, hframe.2 hB⟩
    have hDE : Anc (tr.HonestBlocksAt H) D E := by
      rw [hD]
      exact (AC.anc_viableAncestor ell.frame E).mono sub
    have hEC := AC.fastLock_compatible_of_votes (hac.upTo (hp.run.time_nonneg q)) _
      (AC.CommitteePAt.upTo hm hp.run.antitone hp.committeeFacts.hP _) hyo (Nat.lt_succ_self q)
      ((AC.upTo_fastLockAt hm).mpr ⟨le_rfl, hfl⟩)
      (hp.committee_cs2_at
        (Healing.gbar_le_of_cutZ_le sp (hp.cutZ_le_ts_of_highOrigin_at ho))
        ((ProposalImpl.ts_le_of_fastLock_at hp.run hfl).trans hqb) (hp.run.time_nonneg q) hqb)
      (B := C) (by
        intro z hz j hj e hv hes
        obtain ⟨hjq, hv⟩ := AC.upTo_voteAt.mp hv
        have hzj := hp.run.antitone hjq hz
        obtain ⟨ell, hcast⟩ := hv
        have hjb := hjq.trans hqb
        rcases hC with hC | hC
        · exact hp.clean_result_prefix_votes_before_at hx hC .refl hs hrb j hjb z hzj
            ell e hcast (by omega)
        · exact hp.fast_source_votes_before_at hx (Or.inr hC) hclean hrb j hjb z hzj
            ell e hcast (by omega))
    rcases hEC with h | h
    · exact Or.inr (hDE.trans h)
    · exact AC.anc_total hU h hDE

/-- **A clean raw source compares with every healed member, under the cover.** A clean source of
label at least the origin floor is itself a member of the healed family (an origin), so S1 makes it
compatible with every member written through the horizon, and a block below it is too. -/
theorem clean_source_compatible_healed_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {x : Fin sp.n} {r s : Nat} (hx : x ∈ H (tr.time r))
    {C R : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hC : AC.ResultAt tr.projAC x r s C CV ∨ AC.OptimisticLockAt tr.projAC x r s C CV)
    (hs : cleanLabel sp a + 2 * sp.k + 1 ≤ s) (hrb : tr.time r ≤ b)
    (hRC : Anc (tr.HonestBlocksAt H) R C) (hc : HighSourceCover tr H g a b)
    {D : AC.Blk sp.n (List (FG.Att sp.n))} {j : Nat}
    (hD : Compose.Growing.HealedOrigin tr H g (healedLockFloor sp a) (healedOriginFloor sp a) D j
      b) : Compatible (tr.HonestBlocksAt H) R D := by
  have hCmem : Compose.Growing.HealedOrigin tr H g (healedLockFloor sp a) (healedOriginFloor sp a)
      C s b :=
    Compose.Growing.HealedOrigin.of_origin
      (by simp only [healedOriginFloor, healedLockFloor]; omega)
      (Compose.Growing.originWithin_iff.2 ⟨x, r, CV, hx, hrb, hC⟩)
  exact Compose.Growing.compatible_of_anc_left
    (Compose.Growing.honestBlocksAt_coherent hp.run hp.noColl) hRC (hc.s1 C s D j hCmem hD)

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
