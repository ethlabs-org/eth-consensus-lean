module
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace AvailableChain.Gen.Pure

/-- DC: DecoupledConsensusProofs/Protocol/ForkChoice/Views/WeakConfirmationSupport.lean:114;
INTENTIONAL: Extract the finite-set count core and use the exact honest-over-faulty bound;
record blueprint/02-clean.md:67. -/
def HonestOriginOfCountStatement : Prop :=
  ∀ {Seat : Type} [DecidableEq Seat] (H F P D : Finset Seat),
    H ⊆ D → P ⊆ D → Disjoint H F → F.card < H.card →
    D.card < 2 * P.card → ∃ k ∈ P, k ∉ F

/-- DC: DecoupledConsensusProofs/Protocol/ForkChoice/Views/WeakConfirmationSupport.lean:114;
INTENTIONAL: Give the defining equation of the finite-set count contract;
record blueprint/02-clean.md:67. -/
theorem HonestOriginOfCountStatement_def : HonestOriginOfCountStatement =
    (∀ {Seat : Type} [DecidableEq Seat] (H F P D : Finset Seat),
      H ⊆ D → P ⊆ D → Disjoint H F → F.card < H.card →
      D.card < 2 * P.card → ∃ k ∈ P, k ∉ F) := by rfl

end AvailableChain.Gen.Pure
