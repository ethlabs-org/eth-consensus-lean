module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Quorum
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Invariants

public section

/-! # Goldilocks FG: accountable safety, chain level (G1.3)

The quorum witnesses of a chain (G0.2 (f), (g), not transcribed in `M₁`): every height
`1 ≤ j < h` that the chain left has a quorum of attestations on the chain whose height pair
is `(j, E)` for a root `E` of the chain, and a finalized `h_F ≥ 1` has a quorum of
attestations on the chain whose finality pair is `(h_F, F)`. They follow from the bits
of the chain state (each progress bit and each finality bit of a pending pair has its
attestation on the chain) by induction over the chain.

Then G1.2 and G1.3: take the chain with the lower finalized height `j ≥ 1` (neither
finalized block is genesis, which is on both chains); the other chain left height `j`, with
a root that is not the finalized block; quorum intersection gives `2q − n` validators with a
finality pair `(j, F)` and a height pair `(j, E)`, `E ≠ F`: E1. -/

namespace Consensus.Goldilocks.FG

namespace FGParams

variable (gp : FGParams)

/-- The quorum witnesses of a chain: each height left has a quorum of height pairs on a root
of the chain, and a finalized height `h_F ≥ 1` a quorum of finality pairs `(h_F, F)`. -/
private def Witnessed (c : List (FGBlock gp.n)) (σ : ChainState gp.n) : Prop :=
  (∀ j, 1 ≤ j → j < σ.h → ∃ E ∈ gp.roots c, ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧
    ∀ v ∈ Q, ∃ a ∈ gp.chainAtts c, a.val = v ∧ a.h = j ∧ a.T = E) ∧
  (1 ≤ σ.hF → ∃ Q : Finset (Fin gp.n), gp.q ≤ Q.card ∧
    ∀ v ∈ Q, ∃ a ∈ gp.chainAtts c, a.val = v ∧ a.fin = some (σ.hF, σ.F))

private theorem witnessed {c : List (FGBlock gp.n)} {σ : ChainState gp.n}
    (h : gp.chainState c = some σ) : gp.Witnessed c σ := by
  sorry

end FGParams

/-- **G1.3** (with G1.2 as its core). -/
theorem accountable_safety (gp : FGParams) : AccountableSafety gp := by
  sorry

end Consensus.Goldilocks.FG

end
