module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameFrozen
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.SourceLabels
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameWitness
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FrameViability
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks under `Sleepy`: source labels and frame viability

The source labels at a vote (`SourceLabels`) bound the origins used by the frame argument.
`Frame` supplies the honest-store geometry and `FrameFrozen` supplies the frozen witness; together
they establish full-read and vote-frame viability (S3 of `SleepyInvariantUpTo`). -/

namespace Consensus.Goldilocks.Compose

open AC (ACParams ReplayOrder Vote Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {ΔF : Time} {proposer : Nat → Fin sp.n}

/-- **S3 at full reads, over sources `G`**: with `f < n/2`, the honest attestations at heights
`≥ h_j` sourced by `G`, the sources pairwise compatible and compatible with `B`, a held block `B` is
at or below `fc_root` or in the full viable tree. -/
private theorem held_viable_of {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) (i : Nat)
    {G : AC.Blk sp.n (List (FG.Att sp.n)) → Prop}
    (hsrc : RowsAbove tr H G y i (tr.state y i).fg.hj)
    (hGG : ∀ D D', G D → G D' → Compatible (tr.HonestBlocks H) D D')
    {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  exact FrameGeometry.held_viable_of hrun.toLocalRun (projFG_localRun hrun hnc)
    hf hy hsrc.toFrameGeometry hGG hGB hBt

/-- Full-read viability of a held origin, with `f < n/2` and the origins whose event precedes the
cut pairwise compatible. -/
private theorem held_origin_viable_of {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n) {y : Fin sp.n} (hy : y ∈ H) (i : Nat)
    (hP : ∀ C s C' s', OriginBefore tr H C s i → OriginBefore tr H C' s' i →
      Compatible (tr.HonestBlocks H) C C')
    {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C s, OriginBefore tr H C s i → Compatible (tr.HonestBlocks H) B C)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree := by
  have hU := (projFG_localRun hrun hnc).coherent
  have hsrc : HonestRowsSourced tr H (fun D => ∃ C, (∃ l, OriginBefore tr H C l i) ∧
      Anc (tr.HonestBlocks H) D C) y i := by
    rw [honestRowsSourced_iff]
    intro X hX a ha hav
    obtain ⟨m, hm, -, k, hk, hsg⟩ := honest_row_signed_before hrun hnc hy hX ha hav
    obtain ⟨D, -, hDs, C, l, hC, hDC⟩ := attestation_source hrun hnc hav hsg
    obtain ⟨z, hz, k', hk', CV, h⟩ := originBefore_iff.1 hC
    exact ⟨D, ⟨C, ⟨l, originBefore_iff.2 ⟨z, hz, k', by omega, CV, h⟩⟩, hDC⟩, hDs⟩
  obtain ⟨hGG, hGB⟩ := below_tips_compatible hU (Q := fun C => ∃ l, OriginBefore tr H C l i)
    (fun C C' ⟨l, hC⟩ ⟨l', hC'⟩ => hP C l C' l' hC hC') (fun C ⟨l, hC⟩ => hBc C l hC)
  exact held_viable_of hrun hnc hf hy i (hsrc.above _) hGG hGB hBt

/-- Full-read viability uses the finite frontier and fault bound, with no service premise. -/
theorem held_origin_viable_before {b : Time} {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : NoCollRun dg tr) (hf : 2 * Hᶜ.ncard < sp.n)
    (hP : ∀ s, OriginsBelowUpTo tr H s b) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) (hi : ∀ k < i, tr.time k ≤ b) {B : AC.Blk sp.n (List (FG.Att sp.n))}
    (hBc : ∀ C s, OriginBefore tr H C s i → Compatible (tr.HonestBlocks H) B C)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree :=
  held_origin_viable_of hrun hnc hf hy i
    (fun C l C' l' hC hC' => originsBelowUpTo_iff.1 (hP (l + l' + 1)) C l C' l' (by omega)
      (by omega) (hC.within hi) (hC'.within hi)) hBc hBt

end Consensus.Goldilocks.Compose

end
