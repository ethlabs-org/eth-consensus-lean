module
public import AvailableChainGeneric.Statements.V2.Duty.LinkedHolders

public section

open AvailableChain AvailableChain.V2 AvailableChain.V2.D AvailableChain.V2.D.Engine

namespace AvailableChain.Gen.V2.Duty

-- Source: AvailableChainGeneric/Proofs/V2/Linked.lean:11.
theorem linked_holder_eq_statement : LinkedHolderEqStatement := by
  rw [LinkedHolderEqStatement_def]
  intro V In P F rho hL ℓ ℓ' hℓ hℓ' i j h
  obtain ⟨N, e, hF⟩ := hL
  obtain ⟨hi, hsi⟩ := hF ℓ hℓ
  obtain ⟨hj, hsj⟩ := hF ℓ' hℓ'
  rw [hsi i, hsj j]
  exact congrArg e (Fin.ext h)

variable {V In : Type} {P : ProtocolSpecD In}

set_option linter.unusedVariables false in
-- Source: AvailableChainGeneric/Proofs/V2/Linked.lean:24.
theorem linked_holder_eq {F : P.Label → Prop} {rho : D.Run V P} (hL : D.Linked F rho)
    {ℓ ℓ' : P.Label} (hℓ : F ℓ) (hℓ' : F ℓ')
    (i : Fin (P.seats ℓ)) (j : Fin (P.seats ℓ')) (h : i.val = j.val) :
    rho.seatOf ℓ i = rho.seatOf ℓ' j :=
  @linked_holder_eq_statement V In P F rho hL ℓ ℓ' hℓ hℓ' i j h

-- Source: AvailableChainGeneric/Proofs/V2/Linked.lean:31.
theorem linked_card_le_of_holders_statement : LinkedCardLeOfHoldersStatement := by
  rw [LinkedCardLeOfHoldersStatement_def]
  intro V In P F rho hL I X hI
  obtain ⟨N, e, hF⟩ := hL
  have hsub : I ⊆ X.image (fun x => (e.symm x).val) := by
    intro k hk
    obtain ⟨ℓ, hℓ, i, hik, hiX⟩ := hI k hk
    obtain ⟨hN, hs⟩ := hF ℓ hℓ
    refine Finset.mem_image.mpr ⟨rho.seatOf ℓ i, hiX, ?_⟩
    rw [hs i, e.symm_apply_apply]
    exact hik
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

set_option linter.unusedVariables false in
-- Source: AvailableChainGeneric/Proofs/V2/Linked.lean:46.
theorem linked_card_le_of_holders {F : P.Label → Prop} {rho : D.Run V P}
    (hL : D.Linked F rho) (I : Finset Nat) (X : Finset V)
    (hI : ∀ k ∈ I, ∃ ℓ, F ℓ ∧ ∃ i : Fin (P.seats ℓ),
      i.val = k ∧ rho.seatOf ℓ i ∈ X) : I.card ≤ X.card :=
  @linked_card_le_of_holders_statement V In P F rho hL I X hI

end AvailableChain.Gen.V2.Duty
