module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FrameSourceGeometry

public section

/-! # Goldilocks under `Sleepy`: honest sources of a crossing and of the justification

The actual-store geometry is generic in the AC (`Compose/Run/FrameSourceGeometry`). These
facades supply the FG projection of the Goldilocks run and retain the established vocabulary.
The frame geometry imports this module privately. -/

namespace Consensus.Goldilocks.Compose

open SA (SAParams ReplayOrder Vote Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

section Geometry

variable (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n)
  {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {G : SA.Blk sp.n (List (FG.Att sp.n)) → Prop}

include hrun hnc hf hy in
/-- A crossing quorum has an honest attestation, whose source satisfies `G`. -/
theorem frame_crossing_source_of {h₀ : Nat} (hsrc : RowsAbove tr H G y i h₀)
    {W : SA.Blk sp.n (List (FG.Att sp.n))}
    (hW : W ∈ (tr.state y i).fg.tree) {j : Nat} (hj0 : h₀ ≤ j) (hj1 : 1 ≤ j)
    (hj2 : j < ((tr.state y i).fg.σ W.root).h) :
    ∃ E ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc E W ∧
      ((tr.state y i).fg.σ E.root).h = j ∧ ((tr.state y i).fg.σ E.root).Th = E.root ∧
      ∃ D, G D ∧ IsHonestSource tr H D E.root := by
  have hs : FrameGeometry.RowsAbove tr H G y i h₀ := FrameGeometry.rowsAbove_iff.2
    fun X hX a ha hav hE hh => by
      obtain ⟨D, hD, hDs⟩ := rowsAbove_iff.1 hsrc X hX a ha hav hE hh
      exact ⟨D, hD, FrameGeometry.isHonestSource_iff.2 (isHonestSource_iff.1 hDs)⟩
  obtain ⟨E, hE, hEW, hEh, hET, D, hD, hDs⟩ :=
    FrameGeometry.frame_crossing_source_of hrun.toLocalRun (projFG_localRun hrun hnc)
      hf hy hs hW hj0 hj1 hj2
  exact ⟨E, hE, hEW, hEh, hET, D, hD, isHonestSource_iff.2 (FrameGeometry.isHonestSource_iff.1 hDs)⟩

include hrun hnc hf hy in
/-- **The justification has an honest source**: at `h_j ≥ 1`, `Σ.J` is an entry block of height
`h_j`, and an honest attestation of its target quorum has a source satisfying `G`. -/
theorem justified_honest_source_of (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hj : 1 ≤ (tr.state y i).fg.hj) :
    ((tr.state y i).fg.σ (tr.state y i).fg.J.root).h = (tr.state y i).fg.hj ∧
      ((tr.state y i).fg.σ (tr.state y i).fg.J.root).Th = (tr.state y i).fg.J.root ∧
      ∃ D, G D ∧ IsHonestSource tr H D (tr.state y i).fg.J.root := by
  have hs : FrameGeometry.RowsAbove tr H G y i (tr.state y i).fg.hj := FrameGeometry.rowsAbove_iff.2
    fun X hX a ha hav hE hh => by
      obtain ⟨D, hD, hDs⟩ := rowsAbove_iff.1 hsrc X hX a ha hav hE hh
      exact ⟨D, hD, FrameGeometry.isHonestSource_iff.2 (isHonestSource_iff.1 hDs)⟩
  obtain ⟨hh, hT, D, hD, hDs⟩ := FrameGeometry.justified_honest_source_of
    hrun.toLocalRun (projFG_localRun hrun hnc) hf hy hs hj
  exact ⟨hh, hT, D, hD, isHonestSource_iff.2 (FrameGeometry.isHonestSource_iff.1 hDs)⟩

end Geometry

end Consensus.Goldilocks.Compose

end
