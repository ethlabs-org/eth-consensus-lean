module
public import AvailableChainGeneric.Statements.Pure.HonestCount

public section

namespace AvailableChain.Gen.Pure

/-- DC: DecoupledConsensusProofs/Protocol/ForkChoice/Views/WeakConfirmationSupport.lean:114;
INTENTIONAL: Extract the finite-set count core and use the exact honest-over-faulty bound;
record blueprint/02-clean.md:67. -/
theorem honest_origin_of_count_statement : HonestOriginOfCountStatement := by
  rw [HonestOriginOfCountStatement_def]
  intro Seat _ H F P D hHD hPD hHF hFH hmajority
  classical
  by_contra hnone
  have hPF : P ⊆ F := by
    intro k hk
    by_contra hnot
    exact hnone ⟨k, hk, hnot⟩
  have hdis : Disjoint H P := by
    apply Finset.disjoint_left.mpr
    intro k hkH hkP
    exact Finset.disjoint_left.mp hHF hkH (hPF hkP)
  have hsum : H.card + P.card ≤ D.card := by
    rw [← Finset.card_union_of_disjoint hdis]
    exact Finset.card_le_card (Finset.union_subset hHD hPD)
  have hcount := Finset.card_le_card hPF
  omega

-- Keep the DecidableEq binder in the exact requested public contract.
set_option linter.unusedDecidableInType false in
/-- DC: DecoupledConsensusProofs/Protocol/ForkChoice/Views/WeakConfirmationSupport.lean:114;
INTENTIONAL: Expose the protocol-free honest-origin count with no global-size premise;
record blueprint/02-clean.md:67. -/
theorem honest_origin_of_count {Seat : Type} [DecidableEq Seat] (H F P D : Finset Seat)
    (hHD : H ⊆ D) (hPD : P ⊆ D) (hHF : Disjoint H F) (hFH : F.card < H.card)
    (hmajority : D.card < 2 * P.card) : ∃ k ∈ P, k ∉ F :=
  honest_origin_of_count_statement H F P D hHD hPD hHF hFH hmajority

end AvailableChain.Gen.Pure
