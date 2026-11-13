module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Pivot.Foundation
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Clean.RawWriterTree
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Outcome.Frames
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ProposalService
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Raw writer ancestors in a later voter's frozen tree

The source, stamping and genesis reasoning is in the generic AC supplier
(`Clean/RawWriterTree`). This module only projects the owed reset service and growing catch-up
into its per-cut inputs.
-/

namespace Consensus.Goldilocks.Healing.Growing.ProposalImpl

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- An ancestor of a raw write is available at a later honest voter's read point. -/
theorem raw_writer_voterBlockTree_before_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) (hcatch : CatchRun tr H g (2 * sp.Δ))
    {x y : Fin sp.n} {r s i : Nat} (hx : x ∈ H (tr.time r)) (hy : y ∈ H (tr.time i))
    {B C : SA.Blk sp.n (List (FG.Att sp.n))} {CV : Set (SA.Vote sp.n)}
    (hwriter : SA.ResultAt tr.projAC x r s C CV ∨ SA.FastLockAt tr.projAC x r s C CV)
    (hBC : Anc (tr.HonestBlocksAt H) B C)
    (hgs : SA.gbar g + 4 * sp.Δ ≤ sp.ts s)
    {ell : ACLabel (goldilocksNode sp ro)} {e : SA.Em sp (List (FG.Att sp.n))}
    (hc : SA.CastAt tr.projAC y i ell e) (hs : s < e.msg.slot)
    (hF : Anc (tr.HonestBlocksAt H) ell.frame.F B) :
    B ∈ SA.voterBlockTree sp e.readPoint ell.frame e.msg.slot := by
  have hm := hp.run.time_mono
  have hac := Compose.Growing.goldilocks_ac_projection sp ro dg H tr proposer hp.run hp.noColl
  have hsvc := hp.sync.ac_service_at hp.run (lo := SA.gbar g) (hi := tr.time i) (le_gbar g)
  have hΔ := sp.toParams.hΔ
  have hcatchAC : ∀ x q D, x ∈ H (tr.time q) → tr.projAC.AcceptAt x q D →
      tr.time q < SA.gbar g → ∀ y j ell, y ∈ H (tr.time j) →
      tr.projAC.CallAt y j ell → SA.gbar g + 2 * sp.Δ ≤ tr.time j → tr.time j ≤ tr.time i →
      Anc (tr.HonestBlocksAt H) ell.frame.F D →
      ∃ k ≤ j, tr.projAC.AcceptAt y k D ∧ tr.time k < SA.gbar g + 2 * sp.Δ := by
    intro x q D hxq hq hqt y j ell hyj hcall hlate _ hFD
    have hpre := hp.run.upTo (hp.run.time_nonneg q)
    have hq' : (tr.upTo (tr.time q)).projAC.AcceptAt x q D := by
      rw [RunTrace.upTo_projAC]
      exact ACTrace.upTo_acceptAt.mpr ⟨le_rfl, hq⟩
    obtain ⟨q₀, _, hacc, htime⟩ := Healing.fg_accept_before hpre.toLocalRun hxq hq'
    have hacc₀ := (RunTrace.upTo_acceptAt tr).mp hacc |>.2
    have htime₀ : tr.time q₀ = tr.time q := htime
    obtain ⟨j₀, hj₀, hj₀j⟩ := Healing.exists_firstCutFrom_le hlate
    have hrj := hp.run.upTo (hp.run.time_nonneg j)
    have hfr := Outcome.frame_of_call hp.run hyj hcall
    have hFD' : Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F D := by rwa [hfr] at hFD
    have hprev := Healing.run_F_mono hrj.toLocalRun hyj hj₀j
    rw [RunTrace.upTo_state_of_le hm (hm hj₀j), RunTrace.upTo_state_of_le hm le_rfl] at hprev
    have hsub := RunTrace.honestBlocks_upTo_subset hm (H := H) (hp.run.time_nonneg j)
    obtain ⟨k, hkj₀, hak⟩ := hcatch x q₀ D (htime₀ ▸ hxq) hacc₀ (htime₀ ▸ hqt) y j₀
      (hp.run.antitone hlate hyj) hj₀ ((hprev.mono hsub).trans hFD')
    have hkj : k < j := lt_of_lt_of_le hkj₀ hj₀j
    have hak' := (RunTrace.upTo_acceptAt tr).mpr ⟨hm hkj.le, hak⟩
    obtain ⟨hAC, hACt, _⟩ := Healing.ac_block_after hrj.toLocalRun hyj hak'
    rw [RunTrace.upTo_projAC] at hAC
    refine ⟨k + 1, by omega, ACTrace.upTo_acceptAt.mp hAC |>.2, ?_⟩
    change tr.time (k + 1) = tr.time k at hACt
    rw [hACt]
    exact hj₀.2 k hkj₀
  apply SA.Growing.raw_writer_voterBlockTree_window_before_at
    (by rw [hac.stock]; exact sp.toParams.hn) hac.localRun hsvc hcatchAC
    hx hy hwriter hBC hc (by omega) le_rfl ?_ hF
  have hsm : sp.ts s ≤ sp.ts ((e.msg.slot : Int) - 1) := (SA.ts_le_iff sp).mpr (by omega)
  linarith

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end
