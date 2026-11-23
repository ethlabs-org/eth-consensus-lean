module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameBase
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FrameGeometry
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameSources
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FrameViability

public section

/-! # Goldilocks under `Sleepy`: honest-store frame geometry

S3 of the Sleepy invariant. With the source origins relevant at a cut compatible with an origin `C`
and with each other, every target or progress quorum has an honest attestation (`q > f`), whose
named entry is on the origin chain; comparable sources of one height name one entry, so there is no
contest from genesis, the floor is `max(1, h_max − 1)`, and `fc_root` (`Σ.J` or `Σ.F`) is compatible
with `C`.

Both are stated for a block `B` with the hypotheses the argument uses, not only for origins, so
that the proposal-adoption bootstrap (S3P) applies them to the protected
proposal.

The store vocabulary (heights and entries along a held chain, the FG projection, the honest sources
`IsHonestSource`, `HonestRowsSourced`, `RowsAbove`) is in `FrameBase`, imported publicly; the
honest source of a crossing quorum and of `Σ.J` under `RowsAbove` (`frame_crossing_source_of`,
`justified_honest_source_of`) is in `FrameSources`, imported privately.

`FrameFrozen` proves the frozen witness and `FrameLabels` assembles the following consequences:

* **Full reads** (`held_origin_viable_before`): a held block compatible with every origin, above
  `fc_root`, is in the full viable tree: it is viable itself, or a maximal-height carrier extends
  the named entry of an honest crossing source above it.
* **Votes** (`vote_frame`): at an honest slot-`(s+1)` vote, a block compatible with the origins of
  labels `≤ s` and extended by an honest slot-`s` vote is in the viable tree of the voter block
  tree, or at or below `fc_root` (inside the honest blocks). The
  sources the voter's FG has seen have labels at most `s` (a label-`(s+1)` source is reported at
  the earliest in the tick at `t_{s+1} + Δ`, after the votes there), so `P_{s+1}` compares them;
  the frozen witness is an honest head (of a crossing source when the floor is above `B`, the
  honest slot-`s` head extending `B` otherwise), accepted before the freeze. -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams ReplayOrder Vote Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-! ### The store of an honest node whose honest attestations have compatible sources -/

section Geometry

variable {ini} (hrun : GoldilocksRun proposer dg H tr ini)
  (hnc : NoCollRun dg tr)
  (hf : 2 * Hᶜ.ncard < sp.n)
  {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {G : AC.Blk sp.n (List (FG.Att sp.n)) → Prop}

include hrun in
/-- With `h_j = 0`, `Σ.J` is genesis. -/
theorem justified_genesis (h0 : (tr.state y i).fg.hj = 0) (hy : y ∈ H) :
    (tr.state y i).fg.J = sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload :=
  FrameGeometry.justified_genesis hrun.toLocalRun h0 hy

include hrun hnc hf hy in
/-- **The floor, or a crossing source above the block**: with no contest the floor is
`h_max − 1`; when it is above a held block `B`, a carrier of height `h_max` crossed it with an
honest source `D`, whose entry `E` of height `h_max − 1` extends `B`. -/
theorem floor_or_crossing_of (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D')
    {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B) (hB : B ∈ (tr.state y i).fg.tree) :
    (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ B.root).h ∨
      ∃ D E X, G D ∧ IsHonestSource tr H D E.root ∧ E ∈ (tr.state y i).fg.tree ∧
        (tr.state y i).fg.Anc B E ∧
        ((tr.state y i).fg.σ E.root).h = (tr.state y i).fg.headHeightFloor ∧
        X ∈ (tr.state y i).fg.tree ∧ (tr.state y i).fg.Anc E X ∧ (tr.state y i).fg.IsViable X := by
  obtain h | ⟨D, E, X, hD, hDs, hrest⟩ :=
    FrameGeometry.floor_or_crossing_of hrun.toLocalRun (projFG_localRun hrun hnc)
      hf hy hsrc.toFrameGeometry hGG hGB hB
  · exact Or.inl h
  · exact Or.inr ⟨D, E, X, hD,
      isHonestSource_iff.mpr (FrameGeometry.isHonestSource_iff.mp hDs), hrest⟩

end Geometry

/-- The scoped floor argument needs a fault bound, not the Sleepy regime. Only honest attestations
whose entry height is at least the reader's `h_j` need source witnesses. -/
theorem floor_or_crossing_scoped {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr)
    (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {G : AC.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hsrc : ∀ X ∈ (tr.state y i).fg.tree, ∀ a ∈ X.fgPayload, a.val ∈ H →
      (tr.state y i).fg.hj ≤ ((tr.state y i).fg.σ a.T).h →
      ∃ D, G D ∧ IsHonestSource tr H D a.T)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D')
    {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hB : B ∈ (tr.state y i).fg.tree) :
    (tr.state y i).fg.headHeightFloor ≤ ((tr.state y i).fg.σ B.root).h ∨
      ∃ D E X, G D ∧ IsHonestSource tr H D E.root ∧ E ∈ (tr.state y i).fg.tree ∧
        (tr.state y i).fg.Anc B E ∧
        ((tr.state y i).fg.σ E.root).h = (tr.state y i).fg.headHeightFloor ∧
        X ∈ (tr.state y i).fg.tree ∧ (tr.state y i).fg.Anc E X ∧
        (tr.state y i).fg.IsViable X :=
  floor_or_crossing_of hrun hnc hf hy
    (rowsAbove_iff.2 fun X hX a ha hav _ h => hsrc X hX a ha hav h) hGG hGB hB

section Wrappers

variable (hrun : GoldilocksRun proposer dg H tr) (hnc : NoCollRun dg tr) (hsl : tr.SleepyRun H ΔF)
  {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {G : AC.Blk sp.n (List (FG.Att sp.n)) → Prop}

/-- Justification provenance uses only the numerical fault bound and the supplied attestation
sources. -/
theorem justified_honest_source_before {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {G : AC.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hsrc : HonestRowsSourced tr H G y i)
    (hj : 1 ≤ (tr.state y i).fg.hj) :
    ((tr.state y i).fg.σ (tr.state y i).fg.J.root).h = (tr.state y i).fg.hj ∧
      ((tr.state y i).fg.σ (tr.state y i).fg.J.root).Th = (tr.state y i).fg.J.root ∧
      ∃ D, G D ∧ IsHonestSource tr H D (tr.state y i).fg.J.root :=
  justified_honest_source_of hrun hnc hf hy (hsrc.above _) hj

/-- `frame_crossing_source` with the numerical fault bound in place of `Sleepy`. -/
theorem frame_crossing_source_before {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {G : AC.Blk sp.n (List (FG.Att sp.n)) → Prop} (hsrc : HonestRowsSourced tr H G y i)
    {W : AC.Blk sp.n (List (FG.Att sp.n))} (hW : W ∈ (tr.state y i).fg.tree) {j : Nat}
    (hj1 : 1 ≤ j) (hj2 : j < ((tr.state y i).fg.σ W.root).h) :
    ∃ E ∈ (tr.state y i).fg.tree, (tr.state y i).fg.Anc E W ∧
      ((tr.state y i).fg.σ E.root).h = j ∧ ((tr.state y i).fg.σ E.root).Th = E.root ∧
      ∃ D, G D ∧ IsHonestSource tr H D E.root :=
  frame_crossing_source_of hrun hnc hf hy (hsrc.above 0) hW (Nat.zero_le j) hj1 hj2

end Wrappers

end Consensus.Goldilocks.Compose

end
