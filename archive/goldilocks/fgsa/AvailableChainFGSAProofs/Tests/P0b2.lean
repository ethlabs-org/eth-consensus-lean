module
public import AvailableChainFGSA.Proofs.WindowStore

set_option linter.privateModule false

namespace AvailableChain.FGSA.Tests.P0b2

open AvailableChain.SimplexFG
open AvailableChain.KitFG

private abbrev p : Params :=
  { Δ := 1, n := 1, k := 2, η := 11, deltaPos := by decide, nPos := by decide,
    kLarge := by decide, etaNonneg := by decide,
    R := 2, δt := 0, RLarge := by decide, digest := fun d => ⟨d.slot + 1⟩ }

private def B1 : FGBlock (Fin p.n) :=
  .node .genesis 1 ⟨10⟩ 0 [⟨0, .vote 1 genesisRoot false, none⟩]
private def B2 : FGBlock (Fin p.n) :=
  .node B1 2 ⟨11⟩ 0 [⟨0, .vote 2 B1.root false, none⟩]
private def B3 : FGBlock (Fin p.n) :=
  .node B2 3 ⟨12⟩ 0 [⟨0, .vote 3 B2.root false, some ⟨2, B1.root⟩⟩]

/-- The unchanged FG-SA premises supply the full refinement record. -/
private theorem p0b2h_fgsa_complete_refinement (p : Params) (K : Nat) (hK : 2 ≤ K) :
    HeightFoldRefinement p.E p.cfg FGSA.Window.projectHeight FGSA.Window.initial
      (FGSA.Window.transition p K) (FGSA.Window.derive p K) where
  initial_height := (FGSA.Window.heightRefinement p K hK).initial_height
  derive_genesis := (FGSA.Window.heightRefinement p K hK).derive_genesis
  derive_node := (FGSA.Window.heightRefinement p K hK).derive_node
  step_height := (FGSA.Window.heightRefinement p K hK).step_height

private theorem height_projection (p : Params) (K : Nat) (hK : 2 ≤ K)
    (B : FGBlock (Fin p.n)) :
    FGSA.Window.projectHeight (FGSA.Window.derive p K B) =
      KitFG.Window.projectHeight (SimplexFG.Window.derive p.E p.cfg K B) :=
  (FGSA.Window.windowHeightBridge p K hK B).trans
    (KitFG.Window.windowHeightBridge p.E p.cfg K hK B).symm

/-- The same non-genesis finalization occurs in both folds, with the same retained entry. -/
private theorem inhabited_adapter :
    (FGSA.Window.derive p 2 B3).F = B1 ∧
    (SimplexFG.Window.derive p.E p.cfg 2 B3).F = B1 ∧
    (FGSA.Window.derive p 2 B3).W = [⟨3, B2, ∅⟩] ∧
    (SimplexFG.Window.derive p.E p.cfg 2 B3).W = [⟨3, B2, ∅⟩] := by
  decide +kernel

private theorem closed_cover :
    FGBlock.Preceq B1 (FGSA.Window.derive p 2 B3).F ∧
      2 ≤ (FGSA.Window.derive p 2 B3).h_F := by
  exact FGSA.Window.window_finality_of_cover p 2 (by decide)
    B2 3 ⟨12⟩ 0 [⟨0, .vote 3 B2.root false, some ⟨2, B1.root⟩⟩]
    ⟨2, B1, ∅⟩ (by decide +kernel) {0} (by unfold Electorate.IsQuorum; decide +kernel) (by
      intro i hi
      have hi' : i = 0 := Finset.mem_singleton.mp hi
      subst i
      exact Or.inr ⟨_, List.mem_singleton_self _, rfl, rfl⟩)

/-- Every field of the existing height law record remains available. -/
private theorem p0b2h_fgsa_complete_height (p : Params) (K : Nat) (hK : 2 ≤ K) :
    FGHeightLaws p.E (fun B => FGSA.Window.projectHeight (FGSA.Window.derive p K B)) where
  one_le_h := (FGSA.Window.windowHeightLaws p K hK).one_le_h
  h_mono := (FGSA.Window.windowHeightLaws p K hK).h_mono
  node_cases := (FGSA.Window.windowHeightLaws p K hK).node_cases
  entry_preceq := (FGSA.Window.windowHeightLaws p K hK).entry_preceq
  entry_same_height := (FGSA.Window.windowHeightLaws p K hK).entry_same_height
  entry_idem := (FGSA.Window.windowHeightLaws p K hK).entry_idem
  entry_plateau := (FGSA.Window.windowHeightLaws p K hK).entry_plateau
  justified_preceq_entry := (FGSA.Window.windowHeightLaws p K hK).justified_preceq_entry
  justified_below_height := (FGSA.Window.windowHeightLaws p K hK).justified_below_height
  target_sub_progress := (FGSA.Window.windowHeightLaws p K hK).target_sub_progress
  target_origin := (FGSA.Window.windowHeightLaws p K hK).target_origin
  progress_origin := (FGSA.Window.windowHeightLaws p K hK).progress_origin
  height_crossing := (FGSA.Window.windowHeightLaws p K hK).height_crossing
  justification_certificate := (FGSA.Window.windowHeightLaws p K hK).justification_certificate

#print axioms p0b2h_fgsa_complete_refinement
#print axioms height_projection
#print axioms inhabited_adapter
#print axioms closed_cover
#print axioms p0b2h_fgsa_complete_height

private theorem p0b2c_fgsa_FGCertificateLaws (p : Params) (K : Nat) (hK : 2 ≤ K) :
    FGCertificateLaws p.E (FGSA.Window.certificateHeight p K) (FGSA.Window.certificateFinality p
      K) := by
  let laws := FGSA.Window.windowCertificateLaws p K hK
  exact {
    height := laws.height
    initial := laws.initial
    justified_zero := laws.justified_zero
    finalized_zero := laws.finalized_zero
    finalized_preceq_justified := laws.finalized_preceq_justified
    heights_ordered := laws.heights_ordered
    finalized_mono := laws.finalized_mono
    finality_origin := laws.finality_origin }

private theorem p0b2c_fgsa_FGSelectionLaws (p : Params) (K : Nat) (hK : 2 ≤ K) :
    FGSelectionLaws p.E (FGSA.Window.certificateHeight p K) (FGSA.Window.certificateFinality p K)
      (FGSA.Window.certificateSelection p K) := by
  let laws := FGSA.Window.windowSelectionLaws p K hK
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

private theorem p0b2c_fgsa_FGStoreSafety (p : Params) (K : Nat) (hK : 2 ≤ K) :
    FGStoreSafety p.E (FGSA.Window.certificateHeight p K) (FGSA.Window.certificateFinality p K)
      (id : Store (Fin p.n) → Store (Fin p.n))
      (fun _ B => (FGSA.Window.certificateHeight p K B, FGSA.Window.certificateFinality p K B))
      Store.init (FGSA.Window.on_block p K)
      (FGStoreInvariant (FGSA.Window.certificateHeight p K) (FGSA.Window.certificateFinality p K))
      StoreStepRoots := by
  let laws := FGSA.Window.windowStoreSafety p K hK
  exact {
    initial_good := laws.initial_good
    invariant := laws.invariant
    step_good := laws.step_good
    tree_mono := laws.tree_mono
    accepted_F_mono := laws.accepted_F_mono
    cache_eq := laws.cache_eq
    F_lock_no_evidence := laws.F_lock_no_evidence
    F_lock_fault := laws.F_lock_fault }

private theorem p0b2c_fgsa_selection_phases :
    (FGSA.Window.certificateSelection p 2).before B3 =
      [⟨1, .genesis, ∅⟩, ⟨2, B1, {0}⟩] ∧
    (FGSA.Window.certificateSelection p 2).chosen B3 = some ⟨2, B1, {0}⟩ ∧
    (FGSA.Window.certificateSelection p 2).afterPrune B3 = [] := by
  exact ⟨rfl, rfl, rfl⟩

#print axioms p0b2c_fgsa_FGCertificateLaws
#print axioms p0b2c_fgsa_FGSelectionLaws
#print axioms p0b2c_fgsa_FGStoreSafety
#print axioms p0b2c_fgsa_selection_phases

end AvailableChain.FGSA.Tests.P0b2
