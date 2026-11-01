module
public import AvailableChainKitFG.HeightLaws -- shake: keep (axioms)

public section

/-! ROOT-DIGEST W3: explicit roots for finite test fixtures. -/

namespace AvailableChain.KitFG.Tests.HeightBridge

open AvailableChain.SimplexFG

set_option maxRecDepth 4096

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- First instantiate the bridge with the SimplexFG evaluator. -/
theorem heightBridge_simplex_instance (E : Electorate V) (cfg : FGConfig) :
    HeightBridge E cfg (simplexHeightView E cfg) :=
  heightBridge_of_refinement E cfg heightOf .initial (transition E cfg) (derive E cfg)
    (simplexHeightRefinement E cfg)

-- The bridge also accepts a different state type with an ignored field.
example (E : Electorate V) (cfg : FGConfig) :
    HeightFoldRefinement E cfg (fun w : ChainState V × Unit => heightOf w.1)
      (.initial, ())
      (fun w B rs => (transition E cfg w.1 B rs, ()))
      (fun B => (derive E cfg B, ())) := by
  refine ⟨rfl, rfl, fun _ _ _ _ _ => rfl, ?_⟩
  intro w σ B rs heq
  exact transition_height_eq_of_rowsEq E cfg heq B rs rs (heightSelector_id _ _)

-- Transfer the complete record to the selected evaluator.
example (E : Electorate V) (cfg : FGConfig) :
    FGHeightLaws E (fun B => heightOf (deriveWithSelector E cfg selectHeightRows B)) :=
  heightLaws_of_bridge E cfg _
    (deriveWithSelector_height E cfg selectHeightRows heightSelector_selectHeightRows)

-- A selector can read an omitted finality field.
def finalitySelector (σ : ChainState V) (rs : List (Row V)) : List (Row V) :=
  if σ.h_F = 0 then selectHeightRows σ rs else rs

omit [DecidableEq V] [Fintype V] in
/-- Reading h_F does not add a selector-congruence premise. -/
theorem heightBridge_finality_selector : HeightSelector (finalitySelector (V := V)) := by
  intro σ rs
  unfold finalitySelector
  split_ifs
  · exact heightSelector_selectHeightRows σ rs
  · exact heightSelector_id σ rs

example (E : Electorate V) (cfg : FGConfig) (B : FGBlock V) :
    simplexHeightView E cfg B = heightOf (deriveWithSelector E cfg finalitySelector B) :=
  heightBridge_selector E cfg _ (heightBridge_simplex_instance E cfg)
    finalitySelector heightBridge_finality_selector B

example (E : Electorate V) (cfg : FGConfig) (σ : ChainState V)
    (B : FGBlock V) (rs : List (Row V)) :
    heightOf (transition E cfg σ B rs) =
      heightOf (transition E cfg σ B (selectHeightRows σ rs)) :=
  heightStepBridge_selector E cfg heightOf (transition E cfg)
    (simplexHeightRefinement E cfg).step_height selectHeightRows
    heightSelector_selectHeightRows σ σ rfl B rs

example (E : Electorate V) (cfg : FGConfig) (B : FGBlock V) :
    (simplexHeightView E cfg B).h = (derive E cfg B).h ∧
    (simplexHeightView E cfg B).T_h = (derive E cfg B).T_h ∧
    (simplexHeightView E cfg B).target_participation = (derive E cfg B).target_participation ∧
    (simplexHeightView E cfg B).progress = (derive E cfg B).progress :=
  heightBridge_fields E cfg _ (heightBridge_simplex_instance E cfg) B

example (E : Electorate V) (cfg : FGConfig) (B : FGBlock V) :
    (simplexHeightView E cfg B).h = (deriveWithSelector E cfg selectHeightRows B).h ∧
    (simplexHeightView E cfg B).T_h = (deriveWithSelector E cfg selectHeightRows B).T_h ∧
    (simplexHeightView E cfg B).target_participation =
      (deriveWithSelector E cfg selectHeightRows B).target_participation ∧
    (simplexHeightView E cfg B).progress =
      (deriveWithSelector E cfg selectHeightRows B).progress :=
  heightBridge_selector_fields E cfg _ (heightBridge_simplex_instance E cfg)
    selectHeightRows heightSelector_selectHeightRows B

-- A parent target bit combines with two later rows before timeout maturity.
def targetParent : FGBlock (Fin 4) := .node .genesis 0 ⟨100⟩ 0 [rowT 0]
def targetChild : FGBlock (Fin 4) := .node targetParent 1 ⟨101⟩ 0 [rowT 1, rowT 2]

example : (deriveWithSelector E4 ⟨5⟩ selectHeightRows targetChild).h = 2 ∧
    (deriveWithSelector E4 ⟨5⟩ selectHeightRows targetChild).h_j = 1 := by decide +kernel

-- Mixed coverage includes an old target bit and two timeout rows.
def mixedEarly : FGBlock (Fin 4) := .node targetParent 1 ⟨102⟩ 0 [rowX 1, rowX 2]
def mixedBoundary : FGBlock (Fin 4) := .node targetParent 2 ⟨103⟩ 0 [rowX 1, rowX 2]

example : (deriveWithSelector E4 ⟨2⟩ selectHeightRows mixedEarly).h = 1 ∧
    (deriveWithSelector E4 ⟨2⟩ selectHeightRows mixedEarly).progress = {0, 1, 2} ∧
    (deriveWithSelector E4 ⟨2⟩ selectHeightRows mixedBoundary).h = 2 ∧
    (deriveWithSelector E4 ⟨2⟩ selectHeightRows mixedBoundary).h_j = 0 := by decide +kernel

-- Delay zero permits progress at the entry slot itself.
def zeroBoundary : FGBlock (Fin 4) := .node .genesis 0 ⟨104⟩ 0 [rowX 0, rowX 1, rowX 2]

example : (deriveWithSelector E4 cfg0 selectHeightRows zeroBoundary).h = 2 ∧
    (deriveWithSelector E4 cfg0 selectHeightRows zeroBoundary).h_j = 0 := by decide +kernel

-- Target quorum has priority when target and mature progress are both ready.
example : (deriveWithSelector E4 cfg0 selectHeightRows B1).h = 2 ∧
    (deriveWithSelector E4 cfg0 selectHeightRows B1).h_j = 1 ∧
    (deriveWithSelector E4 cfg0 selectHeightRows B1).J = .genesis := by decide +kernel

#print axioms heightOf_def
#print axioms simplexHeightView_def
#print axioms HeightBridge_def
#print axioms HeightRowsEq_def
#print axioms HeightSelector_def
#print axioms selectHeightRows_def
#print axioms HeightStepBridge_def
#print axioms deriveWithSelector_def
#print axioms simplexHeightRefinement
#print axioms heightBridge_of_refinement
#print axioms heightStepBridge_selector
#print axioms heightBridge_selector
#print axioms heightBridge_fields
#print axioms heightBridge_selector_fields
#print axioms simplexHeightLaws
#print axioms heightLaws_of_bridge
#print axioms heightBridge_simplex_instance
#print axioms heightBridge_finality_selector

end AvailableChain.KitFG.Tests.HeightBridge
end
