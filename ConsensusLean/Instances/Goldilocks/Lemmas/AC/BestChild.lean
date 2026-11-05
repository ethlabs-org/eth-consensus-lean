module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain

public section

/-! # Goldilocks SA: the best child carries over to another view

For two frames `Φp`, `Φy` with views `Vp`, `Vy` at times `tp`, `ty`, the best eligible child `C`
of a block `X` in a walked tree `Tp` of `Φp` is also the best eligible child of `X` in a walked
tree `Ty` of `Φy`, when `X` is a viable head of `Φp` (so a child of `X` is eligible there only by
its slot or by a strict majority), `C` is not of `Φp`'s current slot (so it is eligible by its
majority), the two views have the same voters and the same scores on the blocks of both trees,
`C ∈ Ty`, and every child of `X` in `Ty` is in `Tp` (`isBest_transfer`). Only the winner is
compared: a competitor eligible in `Φy` but not in `Φp` has no majority, so its score is below
`C`'s. When `X` is a viable head of neither frame, every child of `X` is eligible in both, and
the same holds with the same scores (`isBest_transfer_low`). Used by the Sleepy suffix
(`Compose/Service/Suffix`) and HS.3 (`Healing/AgreeSuffix`). The anchor of a
well-formed frame extends `fc_root` (`fcRoot_anc_getAnchor`), and a nonempty set of tree blocks
has a best block (`exists_isBest`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

/-- **The best child carries over** (see the module docstring). -/
theorem isBest_transfer {Φp Φy : Frm sp.n FGP} {Tp Ty : Set (Blk sp.n FGP)} {Vp Vy : View sp.n}
    {σ : Int} {tp ty : Time} {X C : Blk sp.n FGP} (hXv : X ∈ Φp.viableHeads)
    (hCs : C.slot ≠ sp.slot tp) (hvot : voters Vp.votes = voters Vy.votes)
    (hsc : ∀ B ∈ Φp.tree, B ∈ Φy.tree →
      goldfishScore sp Φy Vy σ B = goldfishScore sp Φp Vp σ B)
    (hTp : Tp ⊆ Φp.tree) (hTy : Ty ⊆ Φy.tree) (hCy : C ∈ Ty)
    (hrefl : ∀ B ∈ Ty, B.parent = some X.root → B ∈ Tp)
    (hC : IsBest sp (goldfishScore sp Φp Vp σ)
      {B | B ∈ Tp ∧ B.parent = some X.root ∧ goldfishEligible sp Φp tp Vp σ B} C) :
    IsBest sp (goldfishScore sp Φy Vy σ)
      {B | B ∈ Ty ∧ B.parent = some X.root ∧ goldfishEligible sp Φy ty Vy σ B} C := by
  obtain ⟨⟨hCp, hCX, hCel⟩, hbest⟩ := hC
  have hmaj : (voters Vp.votes).ncard < 2 * goldfishScore sp Φp Vp σ C := by
    rcases hCel with h | h | h
    · exact absurd ⟨X, hXv, hCX⟩ h
    · exact absurd h hCs
    · exact h
  refine ⟨⟨hCy, hCX, Or.inr (Or.inr ?_)⟩, fun B hB hBC => ?_⟩
  · rw [← hvot, hsc C (hTp hCp) (hTy hCy)]; exact hmaj
  have hBp := hrefl B hB.1 hB.2.1
  rw [hsc B (hTp hBp) (hTy hB.1), hsc C (hTp hCp) (hTy hCy)]
  by_cases hel : goldfishEligible sp Φp tp Vp σ B
  · exact hbest B ⟨hBp, hB.2.1, hel⟩ hBC
  · left
    have : ¬ (voters Vp.votes).ncard < 2 * goldfishScore sp Φp Vp σ B :=
      fun h => hel (Or.inr (Or.inr h))
    omega

/-- **The best child carries over below low parents**: when `X` is a viable head of neither
frame (by root), every child of `X` is eligible in both, so with the same scores, `C ∈ Ty` and
every child of `X` in `Ty` in `Tp`, the best child carries over. -/
theorem isBest_transfer_low {Φp Φy : Frm sp.n FGP} {Tp Ty : Set (Blk sp.n FGP)}
    {Vp Vy : View sp.n} {σ : Int} {tp ty : Time} {X C : Blk sp.n FGP}
    (hXp : ∀ W ∈ Φp.viableHeads, W.root ≠ X.root) (hXy : ∀ W ∈ Φy.viableHeads, W.root ≠ X.root)
    (hsc : ∀ B ∈ Φp.tree, B ∈ Φy.tree →
      goldfishScore sp Φy Vy σ B = goldfishScore sp Φp Vp σ B)
    (hTp : Tp ⊆ Φp.tree) (hTy : Ty ⊆ Φy.tree) (hCy : C ∈ Ty)
    (hrefl : ∀ B ∈ Ty, B.parent = some X.root → B ∈ Tp)
    (hC : IsBest sp (goldfishScore sp Φp Vp σ)
      {B | B ∈ Tp ∧ B.parent = some X.root ∧ goldfishEligible sp Φp tp Vp σ B} C) :
    IsBest sp (goldfishScore sp Φy Vy σ)
      {B | B ∈ Ty ∧ B.parent = some X.root ∧ goldfishEligible sp Φy ty Vy σ B} C := by
  have low : ∀ {Φ : Frm sp.n FGP} {t V B}, (∀ W ∈ Φ.viableHeads, W.root ≠ X.root) →
      B.parent = some X.root → goldfishEligible sp Φ t V σ B := fun hX hB =>
    Or.inl fun ⟨W, hW, hBW⟩ => hX W hW (Option.some_injective _ (hBW.symm.trans hB))
  obtain ⟨⟨hCp, hCX, -⟩, hbest⟩ := hC
  refine ⟨⟨hCy, hCX, low hXy hCX⟩, fun B hB hBC => ?_⟩
  have hBp := hrefl B hB.1 hB.2.1
  rw [hsc B (hTp hBp) (hTy hB.1), hsc C (hTp hCp) (hTy hCy)]
  exact hbest B ⟨hBp, hB.2.1, low hXp hB.2.1⟩ hBC

/-- The anchor of a well-formed frame extends `fc_root`: it is `fc_root` or the deepest of a set
holding `fc_root`, and a live lock block is viable (so above `fc_root`) or at or below it. -/
theorem fcRoot_anc_getAnchor {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (A : SAState sp.n) (t : Time) :
    Φ.Anc Φ.fcRoot (getAnchor sp A Φ t) := by
  have hS : liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot} ⊆ Φ.tree := by
    rintro X (hX | hX)
    · exact hX.1
    · exact (Set.mem_singleton_iff.1 hX) ▸ hΦ.fcRoot_mem
  obtain ⟨D, hD⟩ := exists_deepest hΦ hS ⟨Φ.fcRoot, Or.inr rfl⟩
  have hA : getAnchor sp A Φ t = D := by unfold getAnchor; rw [hD, Option.getD_some]
  rw [hA]
  have hD' := deepest_mem hD
  have hcomp : Compatible Φ.tree Φ.fcRoot D := by
    rcases hD'.1 with hL | hf
    · rcases liveLockBlock_candidate hΦ hL with h | h
      · exact Or.inl h.2.1
      · exact Or.inr h
    · rw [Set.mem_singleton_iff.1 hf]
      exact Or.inl .refl
  refine hcomp.elim id fun hDf => ?_
  by_cases hne : D = Φ.fcRoot
  · exact hne ▸ .refl
  · rcases hD'.2 _ (Or.inr rfl) (Ne.symm hne) with h | ⟨h, -⟩ <;>
      have := depth_lt_of_anc hΦ hDf hne hΦ.fcRoot_mem <;> omega

/-- A nonempty set of blocks of a well-formed frame's tree has a best block for any score. -/
theorem exists_isBest {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {S : Set (Blk sp.n FGP)}
    (hS : S ⊆ Φ.tree) (hne : S.Nonempty) (score : Blk sp.n FGP → Nat) :
    ∃ C, IsBest sp score S C := by
  have hfin : S.Finite := hΦ.finite.subset hS
  obtain ⟨D, hD, hmax⟩ := hfin.exists_maximalFor score S hne
  obtain ⟨D', ⟨hD'S, hD'd⟩, hmin⟩ :=
    (hfin.subset (Set.sep_subset S fun C => score C = score D)).exists_minimalFor
      Block.root _ ⟨D, hD, rfl⟩
  refine ⟨D', hD'S, fun C hC hne => ?_⟩
  rcases lt_or_ge (score C) (score D') with h | h
  · exact Or.inl h
  have hCd : score C = score D' := le_antisymm (hD'd ▸ hmax hC (hD'd ▸ h)) h
  refine Or.inr ⟨hCd, lt_of_le_of_ne ?_ fun hr => hne (hΦ.coherent.1 (hS hC) (hS hD'S) hr.symm)⟩
  exact le_of_not_gt fun hlt => (hmin ⟨hC, hCd.trans hD'd⟩ hlt.le).not_gt hlt

end Consensus.Goldilocks.SA

end
