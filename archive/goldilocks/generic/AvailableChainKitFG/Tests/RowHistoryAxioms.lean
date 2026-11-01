module
public import AvailableChainKitFG.Correspondence
public import AvailableChainKitFG.RowHistory -- shake: keep (axioms)

public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.KitFG.Tests.RowHistory

open AvailableChain.SimplexFG

/-- ROOT-DIGEST W3: use a closed finite table for both ancestor chains. -/
theorem finite_chain_roots {V : Type} [DecidableEq V] [RowCodec V]
    (T : Finset (FGBlock V)) (hcl : ∀ B ∈ T, B.parent ∈ T)
    (hinj : ∀ X ∈ T, ∀ Y ∈ T, X.root = Y.root → X = Y)
    (A B : FGBlock V) (hA : A ∈ T) (hB : B ∈ T) : RootInjectiveOn A B := by
  intro X Y hX hY hr
  have mem : ∀ Z, (FGBlock.Preceq Z A ∨ FGBlock.Preceq Z B) → Z ∈ T := by
    intro Z hZ
    rcases hZ with hZ | hZ
    · exact ancestor_closed_of_parent_closed T hcl A hA Z hZ
    · exact ancestor_closed_of_parent_closed T hcl B hB Z hZ
  exact hinj X (mem X hX) Y (mem Y hY) hr

#print axioms height_occurrence_keys
#print axioms finality_occurrence_history

def heightCarrier : FGBlock (Fin 4) := .node .genesis 1 ⟨100⟩ 0 [rowT 0]
def heightTail : FGBlock (Fin 4) := .node heightCarrier 2 ⟨101⟩ 0 []

-- The occurrence can be at the endpoint: W = P.
example : FGBlock.Preceq .genesis heightCarrier.parent ∧
    (derive E4 cfg1 heightCarrier.parent).h = (derive E4 cfg1 heightCarrier).h ∧
    (derive E4 cfg1 heightCarrier.parent).T_h.root =
      (derive E4 cfg1 heightCarrier).T_h.root := by
  exact height_occurrence_keys E4 cfg1 (u := rowT 0) (y := 1)
    (finite_chain_roots {.genesis, heightCarrier, heightTail} (by decide +kernel) (by
        decide +kernel)
      _ _ (by decide +kernel) (by decide +kernel))
    (List.mem_singleton_self _) (preceq_refl _) rfl rfl ⟨rfl, rfl⟩
    (by decide +kernel)

-- The endpoint is one block after the occurrence.
example : FGBlock.Preceq .genesis heightCarrier.parent ∧
    (derive E4 cfg1 heightCarrier.parent).h = (derive E4 cfg1 heightTail).h ∧
    (derive E4 cfg1 heightCarrier.parent).T_h.root =
      (derive E4 cfg1 heightTail).T_h.root := by
  exact height_occurrence_keys E4 cfg1 (u := rowT 0) (y := 1)
    (finite_chain_roots {.genesis, heightCarrier, heightTail} (by decide +kernel) (by
        decide +kernel)
      _ _ (by decide +kernel) (by decide +kernel))
    (List.mem_singleton_self _) (preceq_parent_node heightCarrier 2 ⟨101⟩ 0 [])
    rfl rfl ⟨rfl, rfl⟩ (by decide +kernel)

-- The history keys supply the existing target bit conversion directly.
example : 0 ∈ (derive E4 cfg1 heightTail).target_participation := by
  have hk := (height_occurrence_keys E4 cfg1 (u := rowT 0) (y := 1)
    (W := heightCarrier) (P := heightTail) (U := .genesis)
    (finite_chain_roots {.genesis, heightCarrier, heightTail} (by decide +kernel) (by
        decide +kernel)
      _ _ (by decide +kernel) (by decide +kernel))
    (List.mem_singleton_self _) (preceq_parent_node heightCarrier 2 ⟨101⟩ 0 [])
    rfl rfl ⟨rfl, rfl⟩ (by decide +kernel)).2
  exact bit_first_inclusion_persist E4 cfg1 .target .genesis heightTail 1 ⟨100⟩ 0
    [rowT 0] (rowT 0) (List.mem_singleton_self _)
    (preceq_parent_node heightCarrier 2 ⟨101⟩ 0 []) rfl hk

-- Timeout rows supply progress at the first fold, but do not supply a target.
example : (rowX 0).signer ∈ chainBits .progress
    ([rowX 0].foldl process_row (derive E4 cfg1 .genesis)) := by
  exact bit_first_inclusion .progress _ _ _ (List.mem_singleton_self _)
    (by unfold rowMatchesBit; decide +kernel)

example : (rowX 0).signer ∉ chainBits .target
    ([rowX 0].foldl process_row (derive E4 cfg1 .genesis)) := by
  rw [bit_fold_iff]
  simp [chainBits, derive, ChainState.initial, rowMatchesBit, rowX, FGBlock.root]

def finalityRow : Row (Fin 4) :=
  ⟨0, .vote 2 B1.root true, some ⟨1, genesisRoot⟩⟩
def finalityCarrier : FGBlock (Fin 4) := .node B1 2 ⟨102⟩ 0 [finalityRow]
def finalityTail : FGBlock (Fin 4) := .node finalityCarrier 3 ⟨103⟩ 0 []

-- The finality pair is at the strict boundary z = h - 1, with W = P.
example : ∀ Z, FGBlock.Preceq finalityCarrier.parent Z →
    FGBlock.Preceq Z finalityCarrier →
    (derive E4 cfg1 Z).J = .genesis ∧ (derive E4 cfg1 Z).h_j = 2 - 1 ∧
      (derive E4 cfg1 Z).h_F < 2 - 1 := by
  exact finality_occurrence_history E4 cfg1 (u := finalityRow) (h := 2)
    (finite_chain_roots {.genesis, B1, finalityCarrier, finalityTail} (by decide +kernel) (by
        decide +kernel)
      _ _ (by decide +kernel) (by decide +kernel))
    (List.mem_singleton_self _) (preceq_refl _) rfl rfl
    ⟨rfl, by decide +kernel⟩ (by decide +kernel)

-- Every point on the one-block extension still has the pending pair.
set_option maxHeartbeats 800000 in
-- Kernel reduction evaluates the content roots through three blocks.
example : ∀ Z, FGBlock.Preceq finalityCarrier.parent Z →
    FGBlock.Preceq Z finalityTail →
    (derive E4 cfg1 Z).J = .genesis ∧ (derive E4 cfg1 Z).h_j = 1 ∧
      (derive E4 cfg1 Z).h_F < 1 := by
  exact finality_occurrence_history E4 cfg1 (u := finalityRow) (h := 2)
    (finite_chain_roots {.genesis, B1, finalityCarrier, finalityTail} (by decide +kernel) (by
        decide +kernel)
      _ _ (by decide +kernel) (by decide +kernel))
    (List.mem_singleton_self _) (preceq_parent_node finalityCarrier 3 ⟨103⟩ 0 []) rfl rfl
    ⟨rfl, by decide +kernel⟩ (by decide +kernel)

-- The same carried pair supplies the existing finality bit conversion.
example : finalityRow.signer ∈ (derive E4 cfg1 finalityCarrier).finalize := by
  exact finality_first_inclusion_persist E4 cfg1 B1 finalityCarrier 2 ⟨102⟩ 0 [finalityRow]
    finalityRow (List.mem_singleton_self _) (preceq_refl _)
    ⟨1, genesisRoot⟩ rfl (by decide +kernel)
    (by unfold rowMatchesBit; decide +kernel)

end AvailableChain.KitFG.Tests.RowHistory
end

-- ROOT-DIGEST: public fixture dependency audit.
#print axioms AvailableChain.KitFG.Tests.RowHistory.finite_chain_roots
