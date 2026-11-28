module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FrameViability

public section

/-! # Viable-ancestor candidacy from honest FG rows

A held block compatible with the sources remains a candidate even when the sources are
not pairwise compatible (`held_viable_of_rows`, Compose/Run/FrameViability). This is geometry of
the actual FG stores over any AC. -/

namespace Consensus.Goldilocks.Compose.FrameGeometry

variable {P : Params} {A : NodeAC P} {tr : RunTrace A}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {proposer : Nat → Fin P.n}

/-- A held block compatible with every source stays a viable-ancestor candidate. -/
theorem held_candidate_of_rows {ini} (hr : Node.LocalRun proposer dg H sg tr ini)
    (hfg : FGLocalRun A.genesisPayload H (tr.HonestBlocks H) tr.projFG)
    (hf : 2 * Hᶜ.ncard < P.n) {y : Fin P.n} (hy : y ∈ H) (i : Nat)
    {G : A.Blk → Prop} (hsrc : HonestRowsSourced tr H G y i) {B : A.Blk}
    (hGB : ∀ D, G D → Compatible (tr.HonestBlocks H) D B)
    (hBt : B ∈ (Node.frame (tr.state y i)).tree) :
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).F ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree :=
  held_viable_of_rows hr hfg hf hy (hsrc.above _) hGB hBt

end Consensus.Goldilocks.Compose.FrameGeometry

end
