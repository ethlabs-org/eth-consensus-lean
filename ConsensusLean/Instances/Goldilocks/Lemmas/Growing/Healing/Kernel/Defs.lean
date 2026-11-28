module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PreAdvance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.CallLag
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameLag
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Rise

public section

/-! # Per-cut interfaces of the growing drain kernel

These interfaces keep the snapshot frontier fixed and read honesty separately at every cut.
They do not reconstruct the reset for a terminal honest cohort.
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {tr : GoldilocksTrace sp} {H : Time → Set (Fin sp.n)}

/-- The bounded-gap proposal evidence includes honesty through the slot's vote deadline. -/
def ProposalGap (tr : GoldilocksTrace sp) (H : Time → Set (Fin sp.n))
    (proposer : Nat → Fin sp.n) (G s₀ N : Nat) : Prop :=
  ∀ a, s₀ ≤ a → a + G ≤ N + 1 → ∃ x, a ≤ x ∧ x < a + G ∧
    proposer x ∈ H (sp.ts x + sp.Δ) ∧
      ∃ k Q, tr.ProposesAt (proposer x) k Q ∧ Q.slot = x

/-- Characterization for consumers without exporting the proposal-gap definition body. -/
theorem proposalGap_iff {proposer : Nat → Fin sp.n} {G s₀ N : Nat} :
    ProposalGap tr H proposer G s₀ N ↔
      ∀ a, s₀ ≤ a → a + G ≤ N + 1 → ∃ x, a ≤ x ∧ x < a + G ∧
        proposer x ∈ H (sp.ts x + sp.Δ) ∧
          ∃ k Q, tr.ProposesAt (proposer x) k Q ∧ Q.slot = x := Iff.rfl

end Consensus.Goldilocks.Healing.Growing

end
