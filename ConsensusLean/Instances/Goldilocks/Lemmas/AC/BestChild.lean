module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic

public section

/-! # Goldilocks SA: the best child carries over to another view

For two frames `Φp`, `Φy` with views `Vp`, `Vy` at times `tp`, `ty`, the best eligible child `C`
of a block `X` in a walked tree `Tp` of `Φp` is also the best eligible child of `X` in a walked
tree `Ty` of `Φy`, when `X` is a viable head of `Φp` (so a child of `X` is eligible there only by
its slot or by a strict majority), `C` is not of `Φp`'s current slot (so it is eligible by its
majority), the two views have the same voters and the same scores on the blocks of both trees,
`C ∈ Ty`, and every child of `X` in `Ty` is in `Tp`. Only the winner is compared: a competitor
eligible in `Φy` but not in `Φp` has no majority, so its score is below `C`'s. Used by the
Sleepy suffix (`Compose/Service/Suffix`, workbench#12 §3). -/

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

end Consensus.Goldilocks.SA

end
