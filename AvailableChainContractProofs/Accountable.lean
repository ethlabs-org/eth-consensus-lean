module
public import AvailableChainContract.Claims

@[expose] public section

/-! # Finalized agreement from accountability

`finalizedSafe_of_claims`: in a valid run with fewer than a third faulty, the
honest finalized reads agree. It follows from `finalizedAccountable` and
`honestNeverSlashed`: the slashed validators are never honest, so they are at
most the faulty ones. -/

namespace AvailableChain.Contract

open AvailableChain.Generic

variable {V : Type} [Fintype V] [DecidableEq V] {F : Family} {E : Env V}

namespace Run

variable (rho : Run F E)

theorem ViewIdx_mono {v : V} {i j : Nat} (h : i ≤ j) : rho.ViewIdx v i ⊆ rho.ViewIdx v j := by
  rintro o ⟨k, o₀, hk, hr, hc⟩
  exact ⟨k, o₀, lt_of_lt_of_le hk h, hr, hc⟩

omit [DecidableEq V] in
theorem Slashable_mono {A B : Set (protoOf F E).Object} (h : A ⊆ B) {x : V}
    (hx : rho.Slashable A x) : rho.Slashable B x := by
  obtain ⟨o, ho, o', ho', h1, h2, h3⟩ := hx
  exact ⟨o, h ho, o', h ho', h1, h2, h3⟩

theorem ViewIdx_subset_Observed {v : V} (hv : v ∈ rho.honest) {i : Nat}
    (hi : i ≤ rho.events.length) : rho.ViewIdx v i ⊆ rho.Observed :=
  fun _ ho => ⟨v, hv, rho.ViewIdx_mono hi ho⟩

/-- Under `HonestNeverSlashed`, everything slashed on what honest nodes saw is
faulty. -/
theorem slashedBy_subset_faulty (hns : rho.HonestNeverSlashed)
    {A : Set (protoOf F E).Object} (hA : A ⊆ rho.Observed) :
    rho.slashedBy A ⊆ rho.faulty := by
  classical
  intro x hx
  have hs : rho.Slashable A x := by
    unfold slashedBy at hx
    simpa using hx
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, fun hh => ?_⟩
  exact hns x hh (rho.Slashable_mono hA hs)

end Run

/-- Finalized agreement under a third faulty, from the claims. -/
theorem finalizedSafe_of_claims {F : Family} {C : Constants} (hC : Claims F C)
    (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (E : Env V) (rho : Run F E)
    (hv : rho.ExecutionValid) (hb : rho.BelowOneThird) :
    rho.AgreeFrom (protoOf F E).finalized 0 := by
  intro u hu v hv' i j hi hj
  rcases hC.finalizedAccountable V E rho hv u hu v hv' i j hi hj with hcomp | hcard
  · exact hcomp
  · exfalso
    have hsub : rho.ViewIdx u i ∪ rho.ViewIdx v j ⊆ rho.Observed :=
      Set.union_subset (rho.ViewIdx_subset_Observed hu hi.2) (rho.ViewIdx_subset_Observed hv' hj.2)
    have hle := Finset.card_le_card
      (rho.slashedBy_subset_faulty (hC.honestNeverSlashed V E rho hv) hsub)
    unfold Run.BelowOneThird at hb
    omega

end AvailableChain.Contract

end
