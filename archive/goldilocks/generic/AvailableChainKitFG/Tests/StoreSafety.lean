module
public import AvailableChainKitFG.Correspondence
public import AvailableChainKitFG.StoreSafetySimplex

public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.KitFG.Tests.StoreSafety

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

/-- ROOT-DIGEST W3: close the finite table before checking distinct roots. -/
private theorem finite_view_roots {V : Type} [DecidableEq V] [RowCodec V]
    (T : Finset (FGBlock V)) (hcl : ∀ B ∈ T, B.parent ∈ T)
    (hinj : ∀ X ∈ T, ∀ Y ∈ T, X.root = Y.root → X = Y) : ViewRootInj T := by
  rintro X Y ⟨W, hW, hX⟩ ⟨U, hU, hY⟩ hr
  exact hinj X (ancestor_closed_of_parent_closed T hcl W hW X hX)
    Y (ancestor_closed_of_parent_closed T hcl U hU Y hY) hr

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

-- The concrete store supplies the shared structural invariant at initialization.
theorem store_safety_initial_test (E : Electorate V) (cfg : FGConfig) :
    FGStoreInvariant (simplexHeightView E cfg) (simplexFinalityView E cfg) Store.init :=
  (simplexStoreSafety E cfg).invariant Store.init (simplexStoreSafety E cfg).initial_good

-- The store adapter keeps tree inclusion and accepted ancestry through a step.
theorem store_safety_step_test (E : Electorate V) (cfg : FGConfig)
    (st : Store V) (B : FGBlock V) (hi : StoreInv E cfg st)
    (hinj : ViewRootInj st.TF) (hstep : StoreStepRoots st B) :
    StoreInv E cfg (on_block E cfg st B) ∧
      st.TF ⊆ (on_block E cfg st B).TF ∧ FGBlock.Preceq st.F (on_block E cfg st B).F :=
  ⟨((simplexStoreSafety E cfg).step_good st B ⟨hi, hinj⟩ hstep).1,
    (simplexStoreSafety E cfg).tree_mono st B ⟨hi, hinj⟩,
    (simplexStoreSafety E cfg).accepted_F_mono st B ⟨hi, hinj⟩⟩

private def ssFinalGenesis : FGBlock (Fin 4) :=
  .node B1 2 ⟨100⟩ 0 [⟨0, .empty, some ⟨1, genesisRoot⟩⟩,
    ⟨1, .empty, some ⟨1, genesisRoot⟩⟩, ⟨2, .empty, some ⟨1, genesisRoot⟩⟩]

-- Certificate height 1 remains 1. Only the accepted genesis threshold is zero.
private theorem store_accepted_genesis_threshold_test :
    (simplexFinalityView E4 cfg1 ssFinalGenesis).h_F = 1 ∧
      acceptedThreshold (simplexFinalityView E4 cfg1 ssFinalGenesis).F
        (simplexFinalityView E4 cfg1 ssFinalGenesis).h_F = 0 ∧
      ¬ (simplexFinalityView E4 cfg1 ssFinalGenesis).h_F <
        (simplexHeightView E4 cfg1 .genesis).h := by decide

-- The accepted wrapper applies when the historical strict-height test fails.
private theorem store_accepted_genesis_lock_test :
    FGBlock.Preceq (simplexFinalityView E4 cfg1 ssFinalGenesis).F .genesis := by
  apply accepted_lock_of_fault_bound E4 _ _ (simplexCertificateLaws E4 cfg1)
    ssFinalGenesis _ .genesis
    (finite_chain_roots {.genesis, B1, ssFinalGenesis} (by decide +kernel) (by decide +kernel)
      _ _ (by decide +kernel) (by decide +kernel)) ∅ rfl (by decide) (by decide)
  intro a ha b hb _
  exact (Finset.notMem_empty b hb).elim

-- Away from genesis, the accepted wrapper keeps the carrier's scalar threshold.
example (F : FGBlock V) (j : Height) (hF : F ≠ .genesis) :
    acceptedThreshold F j = j := by
  rw [acceptedThreshold_def, ite_eq_right hF]

/-- [ROOT-DIGEST W3; DC RootInjectiveOnAncestors] One finite positive insertion. -/
theorem first_step_roots : StoreStepRoots (Store.init : Store (Fin 4)) B1 := by
  intro A B hA hB hr
  simp only [Store.init, Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp,
    exists_eq_left, FGBlock.Preceq, FGBlock.preceq, B1, Bool.or_eq_true,
    decide_eq_true_eq, or_assoc] at hA hB
  rcases hA with (rfl | rfl | rfl) <;> rcases hB with (rfl | rfl | rfl) <;>
    first | rfl | simp [FGBlock.root, genesisRoot] at hr

/-- [ROOT-DIGEST W3; DC RootInjectiveOnAncestors] Good includes old-tree root uniqueness. -/
theorem first_step_good :
    StoreInv E4 cfg1 (on_block E4 cfg1 Store.init B1) ∧
      ViewRootInj (on_block E4 cfg1 Store.init B1).TF :=
  (simplexStoreSafety E4 cfg1).step_good Store.init B1
    (simplexStoreSafety E4 cfg1).initial_good first_step_roots

def collision : FGBlock (Fin 4) := .node .genesis 2 B1.root 0 [rowT 0, rowT 1, rowT 2]
def collisionChild : FGBlock (Fin 4) := .node collision 3 ⟨22⟩ 0
  [rowAt 2 collision.root false 0, rowAt 2 collision.root false 1,
    rowAt 2 collision.root false 2]
def beforeCollision : Store (Fin 4) :=
  on_block E4 cfg1 (on_block E4 cfg1 (on_block E4 cfg1 Store.init B1) collision) childA

/-- [ROOT-DIGEST W3; DC RootInjectiveOnAncestors] Equal maximal keys cause fallback. -/
theorem same_key_fallback :
    lexMax E4 cfg1 .genesis {.genesis, B1, collision, childA, collisionChild} =
      (0, .genesis) := by decide +kernel

/-- [ROOT-DIGEST W3; DC RootInjectiveOnAncestors] The old invariant holds before the bad step. -/
theorem same_key_before_inv : StoreInv E4 cfg1 beforeCollision := by
  constructor <;> decide +kernel

/-- [ROOT-DIGEST W3; DC RootInjectiveOnAncestors] The old arbitrary-step claim is false. -/
theorem same_key_breaks_pair : ¬ StoreInv E4 cfg1
    (on_block E4 cfg1 beforeCollision collisionChild) := by
  intro h
  have hne :
      ((on_block E4 cfg1 beforeCollision collisionChild).h_j,
        (on_block E4 cfg1 beforeCollision collisionChild).J) ≠
      lexMax E4 cfg1 (on_block E4 cfg1 beforeCollision collisionChild).F
        (on_block E4 cfg1 beforeCollision collisionChild).TF := by decide +kernel
  exact hne h.pair

/-- [ROOT-DIGEST W3; DC RootInjectiveOnAncestors] Arbitrary StoreInv preservation is false. -/
theorem no_unscoped_step :
    ¬ (∀ (st : Store (Fin 4)) (B : FGBlock (Fin 4)),
      StoreInv E4 cfg1 st → StoreInv E4 cfg1 (on_block E4 cfg1 st B)) := by
  intro h
  exact same_key_breaks_pair (h beforeCollision collisionChild same_key_before_inv)

/-- [ROOT-DIGEST W3; DC RootInjectiveOnAncestors] The scoped API refuses this premise. -/
theorem same_key_no_step_roots : ¬ StoreStepRoots beforeCollision collisionChild := by
  intro h
  have heq := h B1 collision
    ⟨B1, by decide +kernel, preceq_refl B1⟩
    ⟨collision, by decide +kernel, preceq_refl collision⟩ rfl
  exact (by decide : B1 ≠ collision) heq


#print axioms first_step_roots
#print axioms first_step_good
#print axioms same_key_fallback
#print axioms same_key_before_inv
#print axioms same_key_breaks_pair
#print axioms no_unscoped_step
#print axioms same_key_no_step_roots

#print axioms store_safety_initial_test
#print axioms store_safety_step_test
#print axioms store_accepted_genesis_threshold_test
#print axioms store_accepted_genesis_lock_test
#print axioms no_slashableWeight_of_fault_bound
#print axioms finalized_preceq_of_no_evidence
#print axioms finalized_preceq_of_fault_bound
#print axioms finalized_compatible_of_fault_bound
#print axioms viewLock_of_certificate
#print axioms viewLock_of_fault_certificate
#print axioms accepted_lock_of_no_evidence
#print axioms accepted_lock_of_fault_bound
#print axioms FGStoreSafety.of_certificate
#print axioms FGStoreSafety.accepted_lock_no_evidence
#print axioms FGStoreSafety.accepted_lock_fault
#print axioms simplexStoreInvariant
#print axioms simplexStoreSafety

end AvailableChain.KitFG.Tests.StoreSafety
end

-- ROOT-DIGEST: public fixture dependency audit.
#print axioms AvailableChain.KitFG.Tests.StoreSafety.beforeCollision
#print axioms AvailableChain.KitFG.Tests.StoreSafety.collision
#print axioms AvailableChain.KitFG.Tests.StoreSafety.collisionChild
#print axioms AvailableChain.KitFG.Tests.StoreSafety.finite_chain_roots
