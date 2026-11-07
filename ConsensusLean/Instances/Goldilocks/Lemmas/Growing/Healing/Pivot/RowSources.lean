module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.TargetOlder
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.FoundationSources
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.Compatibility
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.FastVotes
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Compatible
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High

public section

/-! # Protected sources compared with high origins

The same-label comparison and later source votes are explicit suppliers. This keeps the
composition independent of the clean vote induction, whose result-prefix domain is supplied
by the pivot cone in turn.
-/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- The older, same-label and later cases of protected-source compatibility, without a
dependency on the source-vote induction's pending interface. -/
theorem protected_source_compatible_high_origin_of_sources_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} {r s : Nat} (hx : x ∈ H (tr.time r))
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hsource : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hrb : tr.time r ≤ b) (hts : cutZ sp.toParams g ≤ sp.ts s)
    (hsame : ∀ {y q C D CV DV}, y ∈ H (tr.time q) → tr.time q ≤ b →
      (SA.ResultAt tr.projAC x r s C CV ∨ SA.OptimisticLockAt tr.projAC x r s C CV) →
      (SA.ResultAt tr.projAC y q s D DV ∨ SA.OptimisticLockAt tr.projAC y q s D DV) →
      Compatible (tr.HonestBlocksAt H) C D)
    (hnext : ∀ i, tr.time i ≤ b → ∀ z, z ∈ H (tr.time i) → ∀ e,
      SA.VoteAt tr.projAC z i e → s < e.msg.slot →
      SA.VoteExtends (tr.HonestBlocksAt H) e.msg B)
    {y : Fin sp.n} {q t : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g y q t D) (hqb : tr.time q ≤ b) :
    Compatible (tr.HonestBlocksAt H) B D := by
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hcoh := hac.localRun.coherent
  have hframe : ∀ z k ell, z ∈ H (tr.time k) → tr.projAC.CallAt z k ell →
      ell.frame.tree ⊆ tr.HonestBlocksAt H := by
    intro z k ell hz hk
    exact (SA.frameIn_of_callAt (hac.upTo (hp.run.time_nonneg k)).localRun hz
      ((Trace.upTo_callAt _).mpr ⟨le_rfl, hk⟩)).2
  have evidence : ∃ C CV,
      (SA.ResultAt tr.projAC x r s C CV ∨ SA.OptimisticLockAt tr.projAC x r s C CV) ∧
      Anc (tr.HonestBlocksAt H) B C := by
    rcases hsource with ⟨CV, ⟨ell, C, hu, hR, hfast, _⟩ | hop⟩ | ⟨ell, C, hu, hR, hslow⟩
    · exact ⟨C, _, Or.inl ⟨ell, hu, hR, rfl⟩,
        ((SA.deepest_mem hfast).1.1.2.2).mono
          (hframe x r ell hx hu.1)⟩
    · exact ⟨B, CV, Or.inr hop, .refl⟩
    · exact ⟨C, _, Or.inl ⟨ell, hu, hR, rfl⟩,
        ((SA.deepest_mem hslow).1.1.2.2).mono
          (hframe x r ell hx hu.1)⟩
  obtain ⟨C, CV, hC, hBC⟩ := evidence
  rcases lt_trichotomy t s with h | rfl | h
  · have supporter : ∃ z j e, z ∈ H (tr.time j) ∧ j ≤ r ∧
        SA.VoteAt tr.projAC z j e ∧ e.msg.slot = s ∧
        SA.VoteExtends (tr.HonestBlocksAt H) e.msg C := by
      rcases hC with hC | hC
      · obtain ⟨z, hz, j, hj, e, hv, _, hes, hCH⟩ :=
          result_supporter_at hp hc hx hC (.refl : Anc (tr.HonestBlocksAt H) C C) hrb hts
        exact ⟨z, j, e, hp.run.antitone (hp.run.time_mono hj.le) hz, hj.le, hv, hes, hCH⟩
      · obtain ⟨_, z, j, hz, hj, e, hv, hes, hCH⟩ := hp.optimistic_supporter_at hx hrb hC
        exact ⟨z, j, e, hp.run.antitone (hp.run.time_mono hj) hz, hj, hv, hes, hCH⟩
    obtain ⟨z, j, e, hz, hj, hv, hes, W, hW, hWr, hCW⟩ := supporter
    exact target_compatible_older_origin_at hp ho hqb hz hv
      ((hp.run.time_mono hj).trans hrb) hes h ⟨W, hW, hWr, hBC.trans hCW⟩
  · obtain ⟨_, E, EV, _, hfl, hDE⟩ := highOrigin_raw_head_at hp.run hp.noColl ho
    have hcomp : Compatible (tr.HonestBlocksAt H) C E := by
      rcases hfl with ⟨ell, R, hu, hR, hfast, _⟩ | hop
      · have hER := ((SA.deepest_mem hfast).1.1.2.2).mono
          (hframe y q ell ho.1 hu.1)
        rcases hsame ho.1 hqb hC (Or.inl ⟨ell, hu, hR, rfl⟩) with h | h
        · exact SA.anc_total hcoh h hER
        · exact Or.inr (hER.trans h)
      · exact hsame ho.1 hqb hC (Or.inr hop)
    rcases hcomp with h | h
    · exact SA.anc_total hcoh (hBC.trans h) hDE
    · exact SA.anc_total hcoh hBC (hDE.trans h)
  · obtain ⟨_, E, EV, _, hfl, hDE⟩ := highOrigin_raw_head_at hp.run hp.noColl ho
    have hf : 2 * (H (tr.time q))ᶜ.ncard < sp.n := by
      have hf := hp.faults (tr.time q) (hp.run.time_nonneg q) hqb
      have hn : 0 < sp.n := sp.toParams.hn
      omega
    have hEB := SA.fastLock_compatible_of_votes (hac.upTo (hp.run.time_nonneg q)) ho.1
      (Nat.lt_succ_self q) ((SA.upTo_fastLockAt hp.run.time_mono).mpr ⟨le_rfl, hfl⟩) hf
      (by
        intro z hz j _ e hv hes
        obtain ⟨hjt, hv⟩ := SA.upTo_voteAt.mp hv
        exact hnext j (hjt.trans hqb) z (hp.run.antitone hjt hz) e hv (by omega))
    rcases hEB with h | h
    · exact Or.inr (hDE.trans h)
    · exact SA.anc_total hcoh h hDE

/-- A clean protected source compares with every bounded high origin at its own honest cut. -/
theorem protected_source_compatible_high_origin_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hc : CatchRun tr H g (2 * sp.Δ))
    {x : Fin sp.n} {r s : Nat} (hx : x ∈ H (tr.time r))
    {B : SA.Blk sp.n (List (FG.Att sp.n))}
    (hsource : (∃ CV, SA.FastLockAt tr.projAC x r s B CV) ∨ SA.SlowLockAt tr.projAC x r s B)
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) (hrb : tr.time r ≤ b)
    {y : Fin sp.n} {q t : Nat} {D : SA.Blk sp.n (List (FG.Att sp.n))}
    (ho : HighOrigin tr H g y q t D) (hqb : tr.time q ≤ b) :
    Compatible (tr.HonestBlocksAt H) B D := by
  have hts := hp.clean_window_timing_at hs s (by have := sp.two_le_k; omega)
  apply protected_source_compatible_high_origin_of_sources_at hp hc hx hsource hrb hts
    (fun hy hqb hC hD => hp.sources_same_label_compatible_at hx hy hC hD hrb hqb hts)
    ?_ ho hqb
  intro i hib z hz e ⟨ell, hcast⟩ hsi
  rcases hsource with ⟨CV, hfast⟩ | hslow
  · exact hp.fast_source_votes_before_at hc hx hfast hs hrb i hib z hz ell e hcast hsi
  · exact hp.slow_source_votes_before_at hc hx hslow hs hrb i hib z hz ell e hcast hsi

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end
