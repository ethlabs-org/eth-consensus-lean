module
public import AvailableChainKitFG.FinalityConsume -- shake: keep (axioms)

set_option linter.privateModule false

namespace AvailableChain.KitFG.Tests.FinalityConsume

open AvailableChain.SimplexFG

#print axioms transition_finality_of_cover
#print axioms derive_finality_of_cover

-- Stored bits suffice when the transition has no rows.
example {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
    (E : Electorate V) (cfg : FGConfig) (σ : ChainState V) (B : FGBlock V)
    (hlt : σ.h_F < σ.h_j) (hq : E.IsQuorum σ.finalize) :
    (transition E cfg σ B []).F = σ.J ∧
      (transition E cfg σ B []).h_F = σ.h_j := by
  exact transition_finality_of_cover E cfg σ B [] σ.finalize hlt hq
    (fun _ hi => Or.inl hi)

def fcFinalRow (i : Fin 4) : Row (Fin 4) :=
  ⟨i, .empty, some ⟨1, genesisRoot⟩⟩

def fcStoredState : ChainState (Fin 4) :=
  { derive E4 cfg1 B1 with finalize := {0, 1} }

-- One row completes the quorum; the other two bits are already stored.
example : (transition E4 cfg1 fcStoredState B1 [fcFinalRow 2]).F = .genesis ∧
    (transition E4 cfg1 fcStoredState B1 [fcFinalRow 2]).h_F = 1 := by
  exact transition_finality_of_cover E4 cfg1 fcStoredState B1 [fcFinalRow 2]
    {0, 1, 2} (by decide +kernel) (by unfold Electorate.IsQuorum; decide +kernel)
    (by decide +kernel)

def fcFinalChild : FGBlock (Fin 4) :=
  .node B1 2 ⟨100⟩ 0 [fcFinalRow 0, fcFinalRow 1, fcFinalRow 2]

-- A child consumes coverage supplied entirely by its own rows.
example : (derive E4 cfg1 fcFinalChild).F = .genesis ∧
    (derive E4 cfg1 fcFinalChild).h_F = 1 := by
  exact derive_finality_of_cover E4 cfg1 fcFinalChild (by decide +kernel)
    {0, 1, 2} (by decide +kernel) (by unfold Electorate.IsQuorum; decide +kernel)
    (by decide +kernel)

def fcBothRow (i : Fin 4) : Row (Fin 4) :=
  ⟨i, .vote 2 B1.root false, some ⟨1, genesisRoot⟩⟩

def fcBothChild : FGBlock (Fin 4) :=
  .node B1 2 ⟨101⟩ 0 [fcBothRow 0, fcBothRow 1, fcBothRow 2]

-- Finality keeps the old pending pair when the same transition justifies B1.
example : (derive E4 cfg1 fcBothChild).F = .genesis ∧
    (derive E4 cfg1 fcBothChild).h_F = 1 ∧
    (derive E4 cfg1 fcBothChild).J = B1 ∧
    (derive E4 cfg1 fcBothChild).h_j = 2 ∧
    (derive E4 cfg1 fcBothChild).finalize = ∅ := by
  have hf := derive_finality_of_cover E4 cfg1 fcBothChild (by decide +kernel)
    {0, 1, 2} (by decide +kernel) (by unfold Electorate.IsQuorum; decide +kernel)
    (by decide +kernel)
  exact ⟨hf.1, hf.2, by decide +kernel⟩

-- Duplicate rows and unrelated rows do not remove coverage.
example : (transition E4 cfg1 fcStoredState B1
      [rowT 3, fcFinalRow 2, fcFinalRow 2, rowT 0]).F = .genesis ∧
    (transition E4 cfg1 fcStoredState B1
      [rowT 3, fcFinalRow 2, fcFinalRow 2, rowT 0]).h_F = 1 := by
  exact transition_finality_of_cover E4 cfg1 fcStoredState B1
    [rowT 3, fcFinalRow 2, fcFinalRow 2, rowT 0] {0, 1, 2}
    (by decide +kernel) (by unfold Electorate.IsQuorum; decide +kernel)
    (by decide +kernel)

def fcEmptyElectorate : Electorate (Fin 0) := ⟨fun _ => 1, fun _ => Nat.one_pos⟩

def fcEmptyState : ChainState (Fin 0) :=
  { ChainState.initial with h := 2, h_j := 1 }

-- An empty electorate has an empty quorum. No row or nonempty-set premise is needed.
example : fcEmptyElectorate.IsQuorum ∅ ∧
    (transition fcEmptyElectorate cfg0 fcEmptyState .genesis []).F = .genesis ∧
    (transition fcEmptyElectorate cfg0 fcEmptyState .genesis []).h_F = 1 := by
  refine ⟨by unfold Electorate.IsQuorum; decide +kernel, ?_⟩
  exact transition_finality_of_cover fcEmptyElectorate cfg0 fcEmptyState .genesis []
    ∅ (by decide +kernel) (by unfold Electorate.IsQuorum; decide +kernel) (by simp)

-- The strict pending-height premise excludes the genesis state.
example : ¬ (derive E4 cfg1 (.genesis : FGBlock (Fin 4))).h_F <
    (derive E4 cfg1 (.genesis : FGBlock (Fin 4))).h_j := by
  decide +kernel

-- A row for another finality height cannot complete the missing bit.
example : (transition E4 cfg1 fcStoredState B1
    [⟨2, .empty, some ⟨2, genesisRoot⟩⟩]).h_F = 0 := by
  decide +kernel

end AvailableChain.KitFG.Tests.FinalityConsume
