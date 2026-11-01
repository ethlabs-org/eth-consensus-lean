module
public import AvailableChainKitFG.HeightLawsDef
public import AvailableChainKitFG.HeightBridge -- shake: keep (re-export)

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- The existing raw-block certificates supply every height law. -/
theorem simplexHeightLaws
    (E : Electorate V) (cfg : FGConfig) :
    FGHeightLaws E (simplexHeightView E cfg) := by
  refine {
    one_le_h := one_le_h E cfg
    h_mono := h_mono E cfg
    node_cases := derive_node_height_entry_cases E cfg
    entry_preceq := entry_preceq E cfg
    entry_same_height := entry_same_height E cfg
    entry_idem := entry_idem E cfg
    entry_plateau := entry_eq_on_plateau E cfg
    justified_preceq_entry := fun B => (chainOrder_derive E cfg B).justified_preceq_target
    justified_below_height := justified_below_height E cfg
    target_sub_progress := fun B => (derive_witnesses E cfg B).target_sub
    target_origin := ?_
    progress_origin := ?_
    height_crossing := height_crossing E cfg
    justification_certificate := justification_certificate E cfg }
  · intro B i hi
    obtain ⟨a, ⟨W, hW, ha⟩, hs, hm⟩ := (derive_witnesses E cfg B).target i hi
    exact ⟨W, a, hW, ha, hs, hm⟩
  · intro B i hi
    obtain ⟨a, ⟨W, hW, ha⟩, hs, hm⟩ := (derive_witnesses E cfg B).progress i hi
    exact ⟨W, a, hW, ha, hs, hm⟩

/-- Equality of height views transfers the complete height-law record. -/
theorem heightLaws_of_bridge
    (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v) :
    FGHeightLaws E v := by
  have heq : v = simplexHeightView E cfg := funext hb
  rw [heq]
  exact simplexHeightLaws E cfg

end AvailableChain.KitFG
end
