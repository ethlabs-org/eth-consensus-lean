module
public import AvailableChainKitFG.WindowStore
public import AvailableChainKitFG.WindowReaders -- shake: keep (axioms)
public import AvailableChainKitFG.WindowProvenance -- shake: keep (axioms)

set_option linter.privateModule false

namespace AvailableChain.KitFG.Tests.P0b2C

open AvailableChain.SimplexFG hiding derive process_row on_block
open AvailableChain.SimplexFG.Window

private def E : Electorate (Fin 2) :=
  ⟨fun i => if i = 0 then 3 else 1, fun i => by split <;> decide⟩
private def cfg : FGConfig := ⟨0⟩
private def B1 : FGBlock (Fin 2) :=
  .node .genesis 1 ⟨10⟩ 0 [⟨0, .vote 1 genesisRoot false, none⟩]
private def B2 : FGBlock (Fin 2) :=
  .node B1 2 ⟨11⟩ 0 [⟨0, .vote 2 B1.root false, none⟩]
private def B3 : FGBlock (Fin 2) :=
  .node B2 3 ⟨12⟩ 0 [⟨0, .vote 3 B2.root false, some ⟨2, B1.root⟩⟩]

private theorem p0b2c_quorum_nonempty : ¬ E.IsQuorum ∅ := by
  unfold Electorate.IsQuorum
  decide +kernel

private theorem p0b2c_generic_FGCertificateLaws :
    FGCertificateLaws E (Window.certificateHeight E cfg 2) (Window.certificateFinality E cfg 2) :=
      by
  let laws := Window.windowCertificateLaws E cfg 2 p0b2c_quorum_nonempty (by decide)
  exact {
    height := laws.height
    initial := laws.initial
    justified_zero := laws.justified_zero
    finalized_zero := laws.finalized_zero
    finalized_preceq_justified := laws.finalized_preceq_justified
    heights_ordered := laws.heights_ordered
    finalized_mono := laws.finalized_mono
    finality_origin := laws.finality_origin }

private theorem p0b2c_generic_FGSelectionLaws :
    FGSelectionLaws E (Window.certificateHeight E cfg 2) (Window.certificateFinality E cfg 2)
      (Window.certificateSelection E cfg 2) := by
  let laws := Window.windowSelectionLaws E cfg 2 p0b2c_quorum_nonempty (by decide)
  exact {
    initial := laws.initial
    ordered := laws.ordered
    bounds := laws.bounds
    entry_origin := laws.entry_origin
    none_iff := laws.none_iff
    greatest := laws.greatest
    write := laws.write
    prune := laws.prune
    pruned_covered := laws.pruned_covered }

private theorem p0b2c_generic_FGStoreSafety :
    FGStoreSafety E (Window.certificateHeight E cfg 2) (Window.certificateFinality E cfg 2)
      (id : Store (Fin 2) → Store (Fin 2))
      (fun _ B => (Window.certificateHeight E cfg 2 B, Window.certificateFinality E cfg 2 B))
      Store.init (on_block E cfg 2)
      (FGStoreInvariant (Window.certificateHeight E cfg 2) (Window.certificateFinality E cfg 2))
      StoreStepRoots := by
  let laws := Window.windowStoreSafety E cfg 2 p0b2c_quorum_nonempty (by decide)
  exact {
    initial_good := laws.initial_good
    invariant := laws.invariant
    step_good := laws.step_good
    tree_mono := laws.tree_mono
    accepted_F_mono := laws.accepted_F_mono
    cache_eq := laws.cache_eq
    F_lock_no_evidence := laws.F_lock_no_evidence
    F_lock_fault := laws.F_lock_fault }

/-- Selection observes the folded entries before pruning and target append. -/
private theorem p0b2c_selection_phases :
    (Window.certificateSelection E cfg 2).before B3 =
      [⟨1, .genesis, ∅⟩, ⟨2, B1, {0}⟩] ∧
    (Window.certificateSelection E cfg 2).chosen B3 = some ⟨2, B1, {0}⟩ ∧
    (Window.certificateSelection E cfg 2).afterPrune B3 = [] ∧
    (derive E cfg 2 B3).W = [⟨3, B2, ∅⟩] := by
  exact ⟨rfl, rfl, rfl, by decide +kernel⟩

/-- A real finalization supplies an earlier birth and exact later row carriers. -/
private theorem p0b2c_finality_origin :
    ∃ C D, StrictPrefix C D ∧ FGBlock.Preceq D B3 ∧
      JustificationBirth E (Window.certificateHeight E cfg 2) C 2 B1 ∧
      FinalityQCAfter E C D 2 B1 := by
  obtain ⟨C, D, hCD, hDB, hb, _, _, hqc⟩ :=
    p0b2c_generic_FGCertificateLaws.finality_origin B3 (by decide +kernel)
  exact ⟨C, D, hCD, hDB, hb, hqc⟩

/-- Dropping the selected ready entry fails the complete selection law. -/
private theorem p0b2c_dropped_choice_rejected :
    ¬ FGSelectionLaws E (Window.certificateHeight E cfg 2)
      (Window.certificateFinality E cfg 2)
      { Window.certificateSelection E cfg 2 with chosen := fun _ => none } := by
  intro bad
  have h := (bad.none_iff B3).mp rfl ⟨2, B1, {0}⟩ (by
    change _ ∈ (Window.certificateSelection E cfg 2).before B3
    rw [p0b2c_selection_phases.1]
    exact List.mem_cons_of_mem _ (List.mem_singleton_self _))
  exact h (by unfold Electorate.IsQuorum; decide +kernel)

/-- A bit from the birth block cannot certify its newly appended entry. -/
private theorem p0b2c_birth_row_ignored :
    let own : FGBlock (Fin 2) :=
      .node B1 2 ⟨11⟩ 0 [⟨0, .vote 2 B1.root false, some ⟨2, B1.root⟩⟩]
    (Window.certificateSelection E cfg 2).chosen own = none ∧
    (derive E cfg 2 own).W = [⟨1, .genesis, ∅⟩, ⟨2, B1, ∅⟩] := by
  decide +kernel

/-- Admission of an actual child retains its tree and updates the height cache. -/
private theorem p0b2c_store_child :
    (on_block E cfg 2 Store.init B1).TF = {B1, .genesis} ∧
    (on_block E cfg 2 Store.init B1).h_max = 2 := by
  decide +kernel

/-- Store safety preserves the invariant for a concrete admitted child. -/
private theorem p0b2c_store_invariant_child :
    FGStoreInvariant (Window.certificateHeight E cfg 2) (Window.certificateFinality E cfg 2)
      (on_block E cfg 2 Store.init B1) := by
  apply p0b2c_generic_FGStoreSafety.step_good _ _
    p0b2c_generic_FGStoreSafety.initial_good
  intro A B hA hB hr
  simp only [Store.init, Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp,
    exists_eq_left, FGBlock.Preceq, FGBlock.preceq, B1, Bool.or_eq_true,
    decide_eq_true_eq, or_assoc] at hA hB
  rcases hA with (rfl | rfl | rfl) <;> rcases hB with (rfl | rfl | rfl) <;>
    first | rfl | simp [FGBlock.root, genesisRoot] at hr

/-- A colliding child fails the exact root premise used by the store proof. -/
private theorem p0b2c_root_collision_rejected :
    let bad : FGBlock (Fin 2) := .node .genesis 1 genesisRoot 0 []
    ¬ StoreStepRoots Store.init bad := by
  intro bad h
  have he := h bad .genesis
    ⟨bad, Finset.mem_insert_self _ _, preceq_refl _⟩
    ⟨.genesis, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), preceq_refl _⟩ rfl
  change FGBlock.node .genesis 1 genesisRoot 0 ([] : List (Row (Fin 2))) = .genesis at he
  cases he

#print axioms p0b2c_store_invariant_child
#print axioms p0b2c_root_collision_rejected
#print axioms p0b2c_quorum_nonempty
#print axioms p0b2c_generic_FGCertificateLaws
#print axioms p0b2c_generic_FGSelectionLaws
#print axioms p0b2c_generic_FGStoreSafety
#print axioms p0b2c_selection_phases
#print axioms p0b2c_finality_origin
#print axioms p0b2c_dropped_choice_rejected
#print axioms p0b2c_birth_row_ignored
#print axioms p0b2c_store_child

end AvailableChain.KitFG.Tests.P0b2C
