module
public import AvailableChainKitFG.HeightCoreDef -- shake: keep (re-export)
public import AvailableChainKitFG.HeightLawsDef
public import AvailableChainKitFG.JustificationLawsDef
public import AvailableChainKitFG.NoEarlyMixed
public import AvailableChainKitFG.RowHistory

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- A crossing before maturity justifies the entry through the bridge. -/
theorem no_mixed_cross_before_maturity_of_bridge
    (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v)
    {U X : FGBlock V} (y : Height)
    (hX : X ≠ .genesis)
    (hUX : FGBlock.Preceq U X.parent)
    (hU : (v U).h = y)
    (hentry : (v U).T_h = U)
    (hparent : (v X.parent).h = y)
    (hearly : X.slot < U.slot + cfg.timeoutDelay)
    (hcross : (v X).h = y + 1) :
    (v X).J = U ∧ (v X).h_j = y := by
  have heq : ∀ B, v B = heightOf (derive E cfg B) := hb
  simp only [heq, heightOf_def] at hU hentry hparent hcross ⊢
  exact no_mixed_cross_before_maturity E cfg y hX hUX hU hentry hparent hearly hcross

/-- The bridge preserves the first height crossing edge. -/
theorem first_height_crossing_edge_of_bridge
    (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v)
    {D P : FGBlock V} (y : Height)
    (hDP : FGBlock.Preceq D P)
    (hD : (v D).h = y)
    (hP : y < (v P).h) :
    ∃ C : FGBlock V,
      C ≠ .genesis ∧
      FGBlock.Preceq D C.parent ∧
      FGBlock.Preceq C P ∧
      (v C.parent).h = y ∧
      (v C).h = y + 1 := by
  have heq : ∀ B, v B = heightOf (derive E cfg B) := hb
  simp only [heq, heightOf_def] at hD hP ⊢
  exact first_height_crossing_edge E cfg y hDP hD hP

/-- A crossing retains an honest matching row under the faulty-weight bound. -/
theorem crossing_honest_matching_row_of_bridge
    (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v)
    (faulty : Finset V) {C : FGBlock V} (y : Height)
    (hC : C ≠ .genesis)
    (hparent : (v C.parent).h = y)
    (hcross : (v C).h = y + 1)
    (hcap : E.weightOf faulty < E.q) :
    ∃ (W : FGBlock V) (a : Row V),
      FGBlock.Preceq W C ∧ a ∈ W.rows ∧
      a.signer ∉ faulty ∧
      a.height_pair.matchesEntry y (v C.parent).T_h.root = true := by
  have heq : ∀ B, v B = heightOf (derive E cfg B) := hb
  simp only [heq, heightOf_def] at hparent hcross ⊢
  exact crossing_honest_matching_row E cfg faulty y hC hparent hcross hcap

/-- Equal endpoint heights retain justification through the bridge. -/
theorem justification_eq_on_plateau_of_bridge
    (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v)
    {D P : FGBlock V}
    (hDP : FGBlock.Preceq D P)
    (hh : (v D).h = (v P).h) :
    (v P).J = (v D).J ∧ (v P).h_j = (v D).h_j := by
  have heq : ∀ B, v B = heightOf (derive E cfg B) := hb
  simp only [heq, heightOf_def] at hh ⊢
  exact justification_eq_on_plateau E cfg hDP hh

/-- A matching height occurrence retains its ancestry and height keys. -/
theorem height_occurrence_keys_of_bridge
    (E : Electorate V) (cfg : FGConfig)
    (v : FGHeightView V) (hb : HeightBridge E cfg v)
    {u : Row V} {W P U : FGBlock V}
    {y : Height} {χ : Bool}
    (hroot : RootInjectiveOn P U) (occ : u ∈ W.rows)
    (path : FGBlock.Preceq W P)
    (heightMatch :
      u.height_pair =
        .vote (v W.parent).h (v W.parent).T_h.root χ)
    (name : u.height_pair = .vote y U.root χ)
    (entry : (v U).h = y ∧ (v U).T_h = U)
    (endpoint : (v P).h = y) :
    FGBlock.Preceq U W.parent ∧
    (v W.parent).h = (v P).h ∧
    (v W.parent).T_h.root = (v P).T_h.root := by
  have heq : ∀ B, v B = heightOf (derive E cfg B) := hb
  simp only [heq, heightOf_def] at heightMatch entry endpoint ⊢
  exact height_occurrence_keys E cfg hroot occ path heightMatch name entry endpoint

/-- A one-step crossing from an entry at height y writes this entry or keeps a lower
justification. -/
theorem cross_cases_of_laws
    {E : Electorate V} {v : FGHeightView V}
    (laws : FGHeightLaws E v) (jlaws : FGJustificationLaws v)
    {U W : FGBlock V} {y : Height}
    (hU : (v U).h = y ∧ (v U).T_h = U)
    (hUW : FGBlock.Preceq U W.parent)
    (hP : (v W.parent).h = y) (hW : (v W).h = y + 1) :
    ((v W.parent).h = y ∧ (v W).h = y + 1 ∧ (v W).J = U ∧ (v W).h_j = y) ∨
    ((v W.parent).h = y ∧ (v W).h = y + 1 ∧ (v W).h_j < y) := by
  have hj := laws.justified_below_height W
  rw [hW] at hj
  by_cases heq : (v W).h_j = y
  · left
    have hy : y ≠ 0 := by
      have := laws.one_le_h U
      rw [hU.1] at this
      simp only [Height] at *
      omega
    have hJh := jlaws.J_height W (heq ▸ hy)
    rw [heq] at hJh
    have hJW := preceq_trans (laws.justified_preceq_entry W) (laws.entry_preceq W)
    have hPW : FGBlock.Preceq W.parent W := by
      cases W with
      | genesis => exact preceq_refl _
      | node P s r_s x rs => exact preceq_parent_node P s r_s x rs
    have hUW' := preceq_trans hUW hPW
    have hJ : (v W).J = U := by
      rcases preceq_total_of_common hJW hUW' with hJU | hUJ
      · have ht := laws.entry_plateau hJU (hJh.trans hU.1.symm)
        rw [jlaws.J_entry W, hU.2] at ht
        exact ht
      · have ht := laws.entry_plateau hUJ (hU.1.trans hJh.symm)
        rw [hU.2, jlaws.J_entry W] at ht
        exact ht.symm
    exact ⟨hP, hW, hJ, heq⟩
  · right
    exact ⟨hP, hW, by simp only [Height] at *; omega⟩

end AvailableChain.KitFG
end
