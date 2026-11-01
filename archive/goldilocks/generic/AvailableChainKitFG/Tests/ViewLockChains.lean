module
public import AvailableChainKitFG.ViewLockChains -- shake: keep (axioms)
public import AvailableChainKitFG.Correspondence

public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

set_option maxRecDepth 4096

namespace AvailableChain.KitFG.Tests.ViewLockChains

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

def carrier : FGBlock (Fin 4) :=
  .node childA 3 ⟨100⟩ 0
    [⟨0, .empty, some ⟨2, B1a.root⟩⟩,
     ⟨1, .empty, some ⟨2, B1a.root⟩⟩,
     ⟨2, .empty, some ⟨2, B1a.root⟩⟩]

def vw : View (Fin 4) := {B1b, childA}

private theorem no_slash :
    ∀ W ∈ vw, ∀ a ∈ chainRows carrier, ∀ b ∈ chainRows W, ¬ Slashable a b := by
  decide +kernel

-- A real finalization supplies the chain form; the carrier need not be in the view.
example : ViewLock E4 cfg1 2 B1a vw := by
  apply viewLock_of_chains E4 cfg1 carrier B1a vw 2
    (by
      intro W hW
      exact finite_chain_roots {.genesis, B1a, B1b, childA, carrier} (by decide +kernel) (by
          decide +kernel)
        carrier W (by decide +kernel) (by
          rcases Finset.mem_insert.mp hW with rfl | hW
          · decide +kernel
          · rw [Finset.mem_singleton.mp hW]; decide +kernel))
    (by decide +kernel) (by decide +kernel)
  rintro W hW ⟨S, hS, hev⟩
  by_cases hempty : S = ∅
  · subst S
    change 2 * E4.q ≤ E4.totalWeight + E4.weightOf ∅ at hS
    exact (by decide +kernel : ¬ (2 * E4.q ≤ E4.totalWeight + E4.weightOf ∅)) hS
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨a, ha, b, hb, _, _, hab⟩ := hev i hi
    exact no_slash W hW a ha b hb hab

-- One faulty seat still satisfies the strict weight bound: 1 + 4 < 2 * 3.
example : ViewLock E4 cfg1 2 B1a vw := by
  apply viewLock_of_honest_chains E4 cfg1 carrier B1a vw 2 {3}
    (by
      intro W hW
      exact finite_chain_roots {.genesis, B1a, B1b, childA, carrier} (by decide +kernel) (by
          decide +kernel)
        carrier W (by decide +kernel) (by
          rcases Finset.mem_insert.mp hW with rfl | hW
          · decide +kernel
          · rw [Finset.mem_singleton.mp hW]; decide +kernel))
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro W hW a ha b hb _
  exact no_slash W hW a ha b hb

-- The sibling is at the threshold and does not extend the checkpoint.
example :
    carrier ∉ vw ∧ B1b ∈ vw ∧ hOf E4 cfg1 B1b = 2 ∧ ¬ FGBlock.Preceq B1a B1b ∧
    (derive E4 cfg1 carrier).h_F = 2 ∧
    2 < hOf E4 cfg1 childA := by
  decide +kernel

-- The carrier certificate height need not be the checkpoint state height.
example :
    (derive E4 cfg1 (.genesis : FGBlock (Fin 4))).h_F = 0 ∧
    hOf E4 cfg1 (.genesis : FGBlock (Fin 4)) = 1 := by
  decide +kernel

end AvailableChain.KitFG.Tests.ViewLockChains
end

-- ROOT-DIGEST: public fixture dependency audit.
#print axioms AvailableChain.KitFG.Tests.ViewLockChains.finite_chain_roots
