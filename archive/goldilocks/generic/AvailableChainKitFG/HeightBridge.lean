module
public import AvailableChainKitFG.HeightFold

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- SimplexFG satisfies the initial, recursive, and one-step obligations. -/
theorem simplexHeightRefinement
    (E : Electorate V) (cfg : FGConfig) :
    HeightFoldRefinement E cfg heightOf
      (ChainState.initial : ChainState V)
      (transition E cfg) (derive E cfg) := by
  refine ⟨rfl, rfl, fun _ _ _ _ _ => rfl, ?_⟩
  intro w σ B rs heq
  exact transition_height_eq_of_rowsEq E cfg heq B rs rs (heightSelector_id _ _)

/-- A one-step projection bridge lifts through the original block tree. -/
theorem heightBridge_of_refinement
    (E : Electorate V) (cfg : FGConfig)
    {Ω : Type} (π : Ω → FGHeight V)
    (initial : Ω)
    (step : Ω → FGBlock V → List (Row V) → Ω)
    (d : FGBlock V → Ω)
    (href : HeightFoldRefinement E cfg π initial step d) :
    HeightBridge E cfg (fun B => π (d B)) := by
  intro B
  change π (d B) = heightOf (derive E cfg B)
  induction B with
  | genesis =>
      rw [href.derive_genesis]
      exact href.initial_height
  | node p s r_s x rs ih =>
      rw [href.derive_node]
      exact href.step_height (d p) (derive E cfg p) (.node p s r_s x rs) rs ih

/-- A bridge step also equals a height-preserving selected row step. -/
theorem heightStepBridge_selector
    (E : Electorate V) (cfg : FGConfig)
    {Ω : Type} (π : Ω → FGHeight V)
    (step : Ω → FGBlock V → List (Row V) → Ω)
    (hstep : HeightStepBridge E cfg π step)
    (sel : ChainState V → List (Row V) → List (Row V))
    (hsel : HeightSelector sel)
    (w : Ω) (σ : ChainState V)
    (hσ : π w = heightOf σ)
    (B : FGBlock V) (rs : List (Row V)) :
    π (step w B rs) =
      heightOf (transition E cfg σ B (sel σ rs)) :=
  (hstep w σ B rs hσ).trans
    (transition_height_eq_of_rowsEq E cfg rfl B (sel σ rs) rs (hsel σ rs)).symm

/-- A derive bridge is unchanged by any selector that preserves coverage. -/
theorem heightBridge_selector
    (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v)
    (sel : ChainState V → List (Row V) → List (Row V))
    (hsel : HeightSelector sel) (B : FGBlock V) :
    v B = heightOf (deriveWithSelector E cfg sel B) :=
  (hb B).trans (deriveWithSelector_height E cfg sel hsel B).symm

/-- The bridge supplies the four height and coverage field equalities. -/
theorem heightBridge_fields
    (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v)
    (B : FGBlock V) :
    (v B).h = (derive E cfg B).h ∧
    (v B).T_h = (derive E cfg B).T_h ∧
    (v B).target_participation =
      (derive E cfg B).target_participation ∧
    (v B).progress = (derive E cfg B).progress :=
  ⟨congrArg FGHeight.h (hb B), congrArg FGHeight.T_h (hb B),
    congrArg FGHeight.target_participation (hb B), congrArg FGHeight.progress (hb B)⟩

/-- The selected derive has the same four fields as the bridged view. -/
theorem heightBridge_selector_fields
    (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v)
    (sel : ChainState V → List (Row V) → List (Row V))
    (hsel : HeightSelector sel) (B : FGBlock V) :
    (v B).h = (deriveWithSelector E cfg sel B).h ∧
    (v B).T_h = (deriveWithSelector E cfg sel B).T_h ∧
    (v B).target_participation =
      (deriveWithSelector E cfg sel B).target_participation ∧
    (v B).progress = (deriveWithSelector E cfg sel B).progress := by
  have heq := heightBridge_selector E cfg v hb sel hsel B
  exact ⟨congrArg FGHeight.h heq, congrArg FGHeight.T_h heq,
    congrArg FGHeight.target_participation heq, congrArg FGHeight.progress heq⟩

end AvailableChain.KitFG
end
