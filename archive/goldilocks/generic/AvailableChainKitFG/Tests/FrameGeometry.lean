module
public import AvailableChainKitFG.FrameGeometry -- shake: keep (axioms)
public import AvailableChainKitFG.CausalCapCore -- shake: keep (axioms)
public import AvailableChainKitFG.StoreSafetySimplex
public import AvailableChainKitFG.FrameChannels -- shake: keep (axioms)
public import AvailableChainKitFG.CausalCap -- shake: keep (axioms)

public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.KitFG.Tests.FrameGeometry

open AvailableChain.SimplexFG

/-- ROOT-DIGEST W3: close the finite table before checking distinct roots. -/
private theorem finite_view_roots {V : Type} [DecidableEq V] [RowCodec V]
    (T : Finset (FGBlock V)) (hcl : ∀ B ∈ T, B.parent ∈ T)
    (hinj : ∀ X ∈ T, ∀ Y ∈ T, X.root = Y.root → X = Y) : ViewRootInj T := by
  rintro X Y ⟨W, hW, hX⟩ ⟨U, hU, hY⟩ hr
  exact hinj X (ancestor_closed_of_parent_closed T hcl W hW X hX)
    Y (ancestor_closed_of_parent_closed T hcl U hU Y hY) hr

-- The generic forms recover the old statements at the SimplexFG views.
variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

example (E : Electorate V) (cfg : FGConfig) (st : Store V) (hi : StoreInv E cfg st) (hinj :
    ViewRootInj st.TF) :
    storeControls E cfg st = fjControls E cfg st.F st.TF :=
  storeControlsView_eq_fjControlsView_of_inv _ _ st (simplexStoreInvariant E cfg st hi hinj)
    (candidateJ_rootInj_of_viewRootInj E _ (simplexHeightLaws E cfg) st.TF hinj)

example (E : Electorate V) (cfg : FGConfig) (st : Store V) (hi : StoreInv E cfg st) (hinj :
    ViewRootInj st.TF) :
    storeFrame E cfg st st.TF = (fjFrame E cfg st.F st.TF).D := by
  rw [storeFrame_of_bridge E cfg (simplexHeightView E cfg) (fun _ => rfl),
    fjFrame_of_bridge E cfg (simplexHeightView E cfg) (fun _ => rfl)]
  exact storeFrameView_full_of_inv _ _ st (simplexStoreInvariant E cfg st hi hinj)
    (candidateJ_rootInj_of_viewRootInj E _ (simplexHeightLaws E cfg) st.TF hinj)

example (E : Electorate V) (cfg : FGConfig) (st : Store V) (hi : StoreInv E cfg st) (hinj :
    ViewRootInj st.TF)
    (B : FGBlock V) (hn : (storeControls E cfg st).contest = false)
    (hc : ∀ W ∈ st.TF, ∀ U, FGBlock.Preceq U W → hOf E cfg U < hOf E cfg W →
      FGBlock.Preceq (derive E cfg U).T_h B) :
    (storeControls E cfg st).lo ≤ hOf E cfg B :=
  storeFrameView_height_of_crossed_prefix_of_inv E _ (simplexHeightLaws E cfg) _ st
    (simplexStoreInvariant E cfg st hi hinj) B hn hc

example (E : Electorate V) (cfg : FGConfig) (c : Controls V)
    (blocks : Finset (FGBlock V)) (B : FGBlock V) :
    B ∈ filteredFrom E cfg c blocks ↔ B ∈ blocks ∧ FGBlock.Preceq c.F B ∧
      FGBlock.Preceq c.Z B ∧ ∃ W ∈ blocks, FGBlock.Preceq B W ∧ c.lo ≤ hOf E cfg W :=
  mem_filteredFrom_of_bridge E cfg (simplexHeightView E cfg) (fun _ => rfl) c blocks B

example (E : Electorate V) (cfg : FGConfig) (faulty : Finset V)
    (hcap : E.weightOf faulty < E.q) (y : Height) (B : FGBlock V) (R : Row V → Prop)
    (hrows : ∀ a ∈ chainRows B, a.signer ∉ faulty → R a)
    (hy : 0 < y) (hF : y ≤ (derive E cfg B).h_F) :
    ∃ a ∈ chainRows B, a.signer ∉ faulty ∧ R a ∧
      a.finality_pair = some ⟨(derive E cfg B).h_F, (derive E cfg B).F.root⟩ :=
  finalityCap_row_of_certificate E _ _ (simplexCertificateLaws E cfg)
    faulty hcap y B R hrows hy hF

private def frameGeometryStore : Store (Fin 4) := on_block E4 cfg1 Store.init B1

private theorem frameGeometry_store_inv :
    FGStoreInvariant (simplexHeightView E4 cfg1) (simplexFinalityView E4 cfg1)
      frameGeometryStore :=
  simplexStoreInvariant E4 cfg1 _
    (storeInv_on_block E4 cfg1 _ B1 (storeInv_init E4 cfg1) (fun _ => finite_view_roots _ (by
        decide +kernel) (by decide +kernel)))
    (finite_view_roots _ (by decide +kernel) (by decide +kernel))

example : storeControlsView (simplexHeightView E4 cfg1) frameGeometryStore =
    fjControlsView (simplexHeightView E4 cfg1) frameGeometryStore.F frameGeometryStore.TF :=
  storeControlsView_eq_fjControlsView_of_inv _ _ _ frameGeometry_store_inv (by decide +kernel)

example : storeFrameView (simplexHeightView E4 cfg1) frameGeometryStore frameGeometryStore.TF =
    (fjFrameView (simplexHeightView E4 cfg1) frameGeometryStore.F frameGeometryStore.TF).D :=
  storeFrameView_full_of_inv _ _ _ frameGeometry_store_inv (by decide +kernel)

example : B1 ∈ filteredFromView (simplexHeightView E4 cfg1)
    (storeControlsView (simplexHeightView E4 cfg1) frameGeometryStore) frameGeometryStore.TF := by
  apply (mem_filteredFromView _ _ _ B1).2
  refine ⟨by decide, by decide, by decide, B1, by decide, preceq_refl B1, by decide⟩

example : (storeControlsView (simplexHeightView E4 cfg1)
    (Store.init : Store (Fin 4))).lo ≤ (simplexHeightView E4 cfg1 .genesis).h := by
  apply storeFrameView_height_of_crossed_prefix_of_inv E4 _ (simplexHeightLaws E4 cfg1)
    _ _ (simplexStoreInvariant E4 cfg1 _ (storeInv_init E4 cfg1)
      (finite_view_roots _ (by decide +kernel) (by decide +kernel))) .genesis (by decide)
  intro W hW U hU hlt
  have hW' : W = .genesis := Finset.mem_singleton.mp hW
  subst W
  have hU' := preceq_genesis.mp hU
  subst U
  exact (Nat.lt_irrefl _ hlt).elim

private def frameGeometryFinalBlock : FGBlock (Fin 4) :=
  .node B1 2 ⟨100⟩ 0 [⟨0, .empty, some ⟨1, genesisRoot⟩⟩,
    ⟨1, .empty, some ⟨1, genesisRoot⟩⟩, ⟨2, .empty, some ⟨1, genesisRoot⟩⟩]

example : ∃ a ∈ chainRows frameGeometryFinalBlock,
    a.signer ∉ ({0, 2} : Finset (Fin 4)) ∧ True ∧
      a.finality_pair = some ⟨1, genesisRoot⟩ :=
  finalityCap_row_of_certificate E4 _ _ (simplexCertificateLaws E4 cfg1)
    {0, 2} (by decide) 1 frameGeometryFinalBlock (fun _ => True)
    (fun _ _ _ => True.intro) (by decide) (by decide)

-- The height record does not fix the height of J. No nonempty electorate
-- premise occurs in that record or in the requested frame statements.
private def frameGeometryEmptyElectorate : Electorate (Fin 0) :=
  ⟨fun _ => 1, fun _ => Nat.one_pos⟩

private def frameGeometryBadHeight (B : FGBlock (Fin 0)) : FGHeight (Fin 0) :=
  { simplexHeightView frameGeometryEmptyElectorate cfg1 B with
    J := (simplexHeightView frameGeometryEmptyElectorate cfg1 B).T_h }

private theorem frameGeometry_bad_height_laws :
    FGHeightLaws frameGeometryEmptyElectorate frameGeometryBadHeight := by
  refine { simplexHeightLaws frameGeometryEmptyElectorate cfg1 with
    justified_preceq_entry := fun B => preceq_refl _
    justification_certificate := ?_ }
  intro D _
  refine ⟨∅, ?_, ?_⟩
  · change frameGeometryEmptyElectorate.q ≤ frameGeometryEmptyElectorate.weightOf ∅
    decide
  intro i hi
  exact (Finset.notMem_empty i hi).elim

theorem frameGeometry_missing_J_height :
    ∃ (E : Electorate (Fin 0)) (H : FGHeightView (Fin 0)),
      FGHeightLaws E H ∧ ∃ C, (H C).h_j ≠ 0 ∧ (H (H C).J).h ≠ (H C).h_j := by
  refine ⟨frameGeometryEmptyElectorate, frameGeometryBadHeight,
    frameGeometry_bad_height_laws, .node .genesis 1 ⟨101⟩ 0 [], ?_⟩
  decide +kernel

-- The bridge supplies the new record without a certificate-law premise.
example (E : Electorate V) (cfg : FGConfig) :
    FGJustificationLaws (simplexHeightView E cfg) :=
  FGJustificationLaws.of_bridge (fun _ => rfl)

example (E : Electorate V) (cfg : FGConfig) (st : Store V) (hi : StoreInv E cfg st) (hinj :
    ViewRootInj st.TF)
    (hc : ∀ W ∈ st.TF, ∀ U, FGBlock.Preceq U W → hOf E cfg U < hOf E cfg W →
      FGBlock.Preceq st.J (derive E cfg U).T_h ∨
        FGBlock.Preceq (derive E cfg U).T_h st.J) :
    (storeControls E cfg st).contest = false :=
  storeFrameView_noContest_of_crossed_of_inv E _ (simplexHeightLaws E cfg) _ st
    (simplexStoreInvariant E cfg st hi hinj) (FGJustificationLaws.of_bridge (fun _ => rfl)) hc

example (E : Electorate V) (cfg : FGConfig) (st : Store V) (hi : StoreInv E cfg st) (hinj :
    ViewRootInj st.TF)
    (B : FGBlock V) (hJB : FGBlock.Preceq st.J B ∨ FGBlock.Preceq B st.J)
    (hc : ∀ W ∈ st.TF, ∀ U, FGBlock.Preceq U W → hOf E cfg U < hOf E cfg W →
      FGBlock.Preceq (derive E cfg U).T_h B ∨ FGBlock.Preceq B (derive E cfg U).T_h)
    (ht : (storeControls E cfg st).contest = true) :
    FGBlock.Preceq B st.J ∧ ∀ W ∈ st.TF, hOf E cfg W = st.h_max →
      ¬ FGBlock.Preceq st.J W → FGBlock.Preceq B W :=
  storeFrameView_contest_of_compatible_of_inv E _ (simplexHeightLaws E cfg) _ st
    (simplexStoreInvariant E cfg st hi hinj) (FGJustificationLaws.of_bridge (fun _ => rfl))
    B hJB hc ht

example (E : Electorate V) (cfg : FGConfig) (st : Store V) (hi : StoreInv E cfg st) (hinj :
    ViewRootInj st.TF)
    (B : FGBlock V) (hB : B ∈ st.TF) (hFB : FGBlock.Preceq st.F B)
    (hJB : FGBlock.Preceq st.J B ∨ FGBlock.Preceq B st.J)
    (hc : ∀ W ∈ st.TF, ∀ U, FGBlock.Preceq U W → hOf E cfg U < hOf E cfg W →
      FGBlock.Preceq (derive E cfg U).T_h B ∨ FGBlock.Preceq B (derive E cfg U).T_h) :
    FGBlock.Preceq B (storeControls E cfg st).Z ∨
      B ∈ filteredFrom E cfg (storeControls E cfg st) st.TF := by
  rw [storeControls_of_bridge E cfg (simplexHeightView E cfg) (fun _ => rfl),
    filteredFrom_of_bridge E cfg (simplexHeightView E cfg) (fun _ => rfl)]
  exact storeFrameView_retention_of_compatible_of_inv E _ (simplexHeightLaws E cfg) _ st
    (simplexStoreInvariant E cfg st hi hinj) (FGJustificationLaws.of_bridge (fun _ => rfl))
    B hB hFB hJB hc

example : (storeControlsView (simplexHeightView E4 cfg1) frameGeometryStore).contest = false := by
  apply storeFrameView_noContest_of_crossed_of_inv E4 _ (simplexHeightLaws E4 cfg1) _ _
    frameGeometry_store_inv (FGJustificationLaws.of_bridge (fun _ => rfl))
  intro W _ U _ _
  have hJ : frameGeometryStore.J = .genesis := by decide
  exact Or.inl (hJ ▸ genesis_preceq _)

private theorem frameGeometry_contested_store_inv :
    FGStoreInvariant (simplexHeightView E4 cfg1) (simplexFinalityView E4 cfg1) stC := by
  have hi : StoreInv E4 cfg1 stC := by
    constructor <;> decide +kernel
  exact simplexStoreInvariant E4 cfg1 stC hi
    (finite_view_roots _ (by decide +kernel) (by decide +kernel))

example : (storeControlsView (simplexHeightView E4 cfg1) stC).contest = true ∧
    FGBlock.Preceq (.genesis : FGBlock (Fin 4)) stC.J ∧
      ∀ W ∈ stC.TF, (simplexHeightView E4 cfg1 W).h = stC.h_max →
        ¬ FGBlock.Preceq stC.J W → FGBlock.Preceq .genesis W := by
  refine ⟨by decide +kernel, ?_⟩
  apply storeFrameView_contest_of_compatible_of_inv E4 (simplexHeightView E4 cfg1)
    (simplexHeightLaws E4 cfg1) (simplexFinalityView E4 cfg1) stC
    frameGeometry_contested_store_inv (FGJustificationLaws.of_bridge (fun _ => rfl)) .genesis
    (Or.inr (genesis_preceq _)) _ (by decide +kernel)
  intro W _ U _ _
  exact Or.inr (genesis_preceq _)

example : B1 ∈ filteredFromView (simplexHeightView E4 cfg1)
    (storeControlsView (simplexHeightView E4 cfg1) frameGeometryStore) frameGeometryStore.TF := by
  have hret := storeFrameView_retention_of_compatible_of_inv E4 _ (simplexHeightLaws E4 cfg1)
    _ _ frameGeometry_store_inv (FGJustificationLaws.of_bridge (fun _ => rfl)) B1
    (by decide) (by decide) (by decide) (by
      intro W hWmem U hU _
      have htree : frameGeometryStore.TF = {.genesis, B1} := by decide
      have hW : W = .genesis ∨ W = B1 := by
        simpa only [htree, Finset.mem_insert, Finset.mem_singleton] using hWmem
      rcases hW with rfl | rfl
      · have he := preceq_genesis.mp hU
        subst U
        exact Or.inl (genesis_preceq _)
      · exact Or.inl (preceq_trans ((simplexHeightLaws E4 cfg1).entry_preceq U) hU))
  exact hret.resolve_left (by decide)

#print axioms FGJustificationLaws.of_bridge
#print axioms storeFrameView_noContest_of_crossed_of_inv
#print axioms storeFrameView_contest_of_compatible_of_inv
#print axioms storeFrameView_retention_of_compatible_of_inv
#print axioms frameGeometry_contested_store_inv

#print axioms mem_filteredFromView
#print axioms mem_filteredFrom_of_bridge
#print axioms storeControlsView_eq_fjControlsView_of_inv
#print axioms storeFrameView_full_of_inv
#print axioms storeFrameView_height_of_crossed_prefix_of_inv
#print axioms finalityCap_row_of_certificate
#print axioms frameGeometry_store_inv
#print axioms frameGeometry_missing_J_height

end AvailableChain.KitFG.Tests.FrameGeometry
end
