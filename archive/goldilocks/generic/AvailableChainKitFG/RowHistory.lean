module
public import AvailableChainKitFG.Certificates
public import AvailableChainKitFG.RowBits
public import AvailableChainKitFG.RootScopeDef

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- [R6] A height occurrence names an entry on the carrier parent's chain.
Equal endpoint heights preserve both height keys. -/
theorem height_occurrence_keys (E : Electorate V) (cfg : FGConfig)
    {u : Row V} {W P U : FGBlock V} {y : Height} {χ : Bool}
    (hroot : RootInjectiveOn P U) (occ : u ∈ W.rows) (path : FGBlock.Preceq W P)
    (r6 : u.height_pair =
      .vote (derive E cfg W.parent).h (derive E cfg W.parent).T_h.root χ)
    (name : u.height_pair = .vote y U.root χ)
    (entry : (derive E cfg U).h = y ∧ (derive E cfg U).T_h = U)
    (endpoint : (derive E cfg P).h = y) :
    FGBlock.Preceq U W.parent ∧
      (derive E cfg W.parent).h = (derive E cfg P).h ∧
      (derive E cfg W.parent).T_h.root = (derive E cfg P).T_h.root := by
  have hparent : FGBlock.Preceq W.parent P := by
    cases W with
    | genesis => simp [FGBlock.rows] at occ
    | node p s r_s x rows => exact preceq_trans (preceq_parent_node p s r_s x rows) path
  obtain ⟨hh, ht, _⟩ := NamedHeightPair.vote.inj (r6.symm.trans name)
  have hT : (derive E cfg W.parent).T_h = U := hroot _ _ (Or.inl (preceq_trans (entry_preceq E cfg
    W.parent) hparent))
    (Or.inr (preceq_refl U)) ht
  have hU : FGBlock.Preceq U W.parent := by
    rw [← entry.2, ← hT, entry_idem]
    exact entry_preceq E cfg W.parent
  have hk := hh.trans endpoint.symm
  exact ⟨hU, hk, congrArg FGBlock.root (entry_eq_on_plateau E cfg hparent hk)⟩

/-- [R3/R6] A pending finality pair below the carried height has the same
justification and positive debt at every state from the carrier parent.
`carried` names the height in the row; `r6` binds it to the parent height. -/
theorem finality_occurrence_history (E : Electorate V) (cfg : FGConfig)
    {u : Row V} {W P K : FGBlock V} {h z : Height} {t : BlockId} {χ : Bool}
    (hroot : RootInjectiveOn P P) (_occ : u ∈ W.rows) (_path : FGBlock.Preceq W P)
    (r6 : u.height_pair = .vote (derive E cfg W.parent).h t χ)
    (carried : u.height_pair = .vote h t χ)
    (form : u.finality_pair = some ⟨z, K.root⟩ ∧ z < h)
    (pending : (derive E cfg P).J = K ∧ (derive E cfg P).h_j = z ∧
      (derive E cfg P).h_F < z) :
    ∀ Z, FGBlock.Preceq W.parent Z → FGBlock.Preceq Z P →
      (derive E cfg Z).J = K ∧ (derive E cfg Z).h_j = z ∧
        (derive E cfg Z).h_F < z := by
  have hh := (NamedHeightPair.vote.inj (r6.symm.trans carried)).1
  have hbelow : z < (derive E cfg W.parent).h := hh ▸ form.2
  have hm : rowMatchesBit .finality (derive E cfg P) u := by
    exact ⟨pending.2.2.trans_eq pending.2.1.symm,
      by simpa only [pending.1, pending.2.1] using form.1⟩
  intro Z hWZ hZP
  obtain ⟨hkZ, hmZ⟩ := finality_match_before E cfg hZP u ⟨z, K.root⟩ form.1
    (hbelow.trans_le (h_mono E cfg hWZ)) hm
  have hj : (derive E cfg Z).h_j = z := hkZ.1.trans pending.2.1
  exact ⟨(hroot _ _
    (Or.inl (preceq_trans (derive_anchors_preceq E cfg Z).2 hZP))
    (Or.inl (derive_anchors_preceq E cfg P).2) hkZ.2).trans pending.1, hj, hmZ.1.trans_eq hj⟩

end AvailableChain.KitFG
end
