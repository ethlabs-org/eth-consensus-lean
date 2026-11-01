module
public import AvailableChainKitFG.CausalCap -- shake: keep (examples)

@[expose] public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.KitFG.Tests

open AvailableChain.SimplexFG

/-! G17 tests use the E4/cfg1 examples from SimplexFG/ChainState.
All finite checks use kernel reduction. -/

/-- Genesis meets the height-zero finality premise but has no rows.
Thus neither finality row conclusion can hold without `0 < y`. -/
theorem finality_zero_counterexample :
    E4.weightOf (∅ : Finset (Fin 4)) < E4.q ∧
    (derive E4 cfg1 (.genesis : FGBlock (Fin 4))).h_F = 0 ∧
    chainRows (.genesis : FGBlock (Fin 4)) = ∅ ∧
    ¬ (∃ a ∈ chainRows (.genesis : FGBlock (Fin 4)), a.signer ∉ (∅ : Finset (Fin 4))) := by
  decide +kernel

/-- Height `y = 0` is valid for the causal cap: B1 crosses height one. -/
theorem causal_zero_witness :
    0 + 2 ≤ (derive E4 cfg1 B1).h ∧
    rowT 1 ∈ chainRows B1 ∧ (rowT 1).signer ∉ ({0, 2} : Finset (Fin 4)) ∧
    (rowT 1).height_pair = .vote (0 + 1) genesisRoot false := by
  decide +kernel

/-- A quorum can be entirely faulty when the strict FaultQ bound is absent. -/
theorem faultQ_counterexample :
    E4.weightOf ({0, 1, 2} : Finset (Fin 4)) = E4.q ∧
    2 ≤ (derive E4 cfg1 B1).h ∧
    (∀ a ∈ chainRows B1, a.signer ∈ ({0, 1, 2} : Finset (Fin 4))) := by
  decide +kernel

/-- The finality rows have empty height pairs; B1 supplies the height rows. -/
def BFinal : FGBlock (Fin 4) :=
  .node B1 2 ⟨100⟩ 0
    [⟨0, .empty, some ⟨1, genesisRoot⟩⟩,
     ⟨1, .empty, some ⟨1, genesisRoot⟩⟩,
     ⟨2, .empty, some ⟨1, genesisRoot⟩⟩]

/-- The positive boundary `y = 1` has both row witnesses. -/
theorem finality_positive_witness :
    E4.weightOf ({0, 2} : Finset (Fin 4)) < E4.q ∧
    (derive E4 cfg1 BFinal).h_F = 1 ∧
    (⟨1, .empty, some ⟨1, genesisRoot⟩⟩ : Row (Fin 4)) ∈ chainRows BFinal ∧
    rowT 1 ∈ chainRows BFinal := by
  decide +kernel

-- The row predicate is retained by both forms at the smallest causal height.
example : ∃ a ∈ chainRows B1, a.signer ∉ ({0, 2} : Finset (Fin 4)) ∧
    a.height_pair = .vote 1 genesisRoot false ∧
    ∃ T t, a.height_pair = .vote (0 + 1) T t := by
  exact causalCap_row E4 cfg1 {0, 2} (by decide +kernel) 0 B1
    (fun a => a.height_pair = .vote 1 genesisRoot false)
    (by decide +kernel) (by decide +kernel)

example : ∃ a ∈ chainRows B1, a.signer ∉ ({0, 2} : Finset (Fin 4)) ∧
    a.height_pair = .vote 1 genesisRoot false ∧
    ∃ T t, a.height_pair = .vote (0 + 1) T t := by
  exact causalCap_justified_row E4 cfg1 {0, 2} (by decide +kernel) 0 B1
    (fun a => a.height_pair = .vote 1 genesisRoot false)
    (by decide +kernel) (by decide +kernel)

example : ∃ a ∈ chainRows BFinal, a.signer ∉ ({0, 2} : Finset (Fin 4)) ∧
    a.signer = 1 ∧
    a.finality_pair = some ⟨(derive E4 cfg1 BFinal).h_F, (derive E4 cfg1 BFinal).F.root⟩ := by
  exact finalityCap_row E4 cfg1 {0, 2} (by decide +kernel) 1 BFinal
    (fun a => a.signer = 1) (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : ∃ a ∈ chainRows BFinal, a.signer ∉ ({0, 2} : Finset (Fin 4)) ∧
    a.signer = 1 ∧ ∃ T t, a.height_pair = .vote 1 T t := by
  exact finalityCap_height_row E4 cfg1 {0, 2} (by decide +kernel) 1 BFinal
    (fun a => a.signer = 1) (by decide +kernel) (by decide +kernel) (by decide +kernel)

-- The old cap is the contrapositive special case of the new row statement.
example {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
    (E : Electorate V) (cfg : FGConfig) (faulty : Finset V)
    (hcap : E.weightOf faulty < E.q) (M : Height) (B : FGBlock V)
    (hrows : ∀ a ∈ chainRows B, a.signer ∉ faulty →
      ∀ h T t, a.height_pair = .vote h T t → h ≤ M) :
    (derive E cfg B).h ≤ M + 1 ∧ (derive E cfg B).h_j ≤ M := by
  unfold Height at *
  have hh : (derive E cfg B).h ≤ M + 1 := by
    by_contra hh
    obtain ⟨a, -, -, hr, T, t, hp⟩ := causalCap_row E cfg faulty hcap M B
      (fun a => ∀ h T t, a.height_pair = .vote h T t → h ≤ M) hrows (by unfold Height at *; omega)
    have := hr (M + 1) T t hp
    unfold Height at *
    omega
  have := justified_below_height E cfg B
  exact ⟨hh, by unfold Height at *; omega⟩

-- The unchanged API still applies directly.
example : (derive E4 cfg1 B1).h ≤ 1 + 1 ∧ (derive E4 cfg1 B1).h_j ≤ 1 :=
  causalCap E4 cfg1 {0, 2} (by decide +kernel) 1 B1 (by
    have hrows : ∀ a ∈ chainRows B1, a.height_pair = .vote 1 genesisRoot false := by
      decide +kernel
    intro a ha _ h T t hp
    have := (hrows a ha).symm.trans hp
    cases this
    exact Nat.le_refl 1)

end AvailableChain.KitFG.Tests
end
