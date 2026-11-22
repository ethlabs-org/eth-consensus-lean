module
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Compose.Relay
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
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK)
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
  have hac := Compose.Growing.goldilocks_ac_projection_from hp.run hp.noColl
  have hsvc := hp.sync.ac_service_at hp.run (lo := SA.gbar g) (hi := tr.time i) (le_gbar g)
  have hΔ := sp.toParams.hΔ
  have hcatchAC : ∀ x q D, x ∈ H (tr.time q) → tr.projAC.AcceptAt x q D →
      tr.time q < SA.gbar g → ∀ y j ell, y ∈ H (tr.time j) →
      tr.projAC.CallAt y j ell → SA.gbar g + 2 * sp.Δ ≤ tr.time j → tr.time j ≤ tr.time i →
      Anc (tr.HonestBlocksAt H) ell.frame.F D →
      ∃ k ≤ j, tr.projAC.AcceptAt y k D ∧ tr.time k < SA.gbar g + 2 * sp.Δ := by
    intro x q D hxq hq hqt y j ell hyj hcall hlate _ hFD
    exact hp.run.toLocalRun.acCatchAt hp.catchUp hxq hq hqt hyj hcall hlate hFD
  apply SA.Growing.raw_writer_voterBlockTree_window_before_at
    hp.committee_pos hac.localRun hac.vstart hsvc hcatchAC
    hx hy hwriter hBC hc (by omega) le_rfl ?_ hF
  have hsm : sp.ts s ≤ sp.ts ((e.msg.slot : Int) - 1) := (SA.ts_le_iff sp).mpr (by omega)
  linarith

end Consensus.Goldilocks.Healing.Growing.ProposalImpl

end
