module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic

public section

/-! # Goldilocks SA: the best child from a transferred majority

The counting step of the vote transfer (Goldfish's argument, claims A1.8): if a set `SX` of
validators are supporters of `C` in a view whose support is among its votes, and the view's
voters are among `VX` with `|VX| < 2|SX|`, then every child `Cx ⪯ C` of a block `X` is
eligible (its score is a strict majority of the voters) and the best eligible child of `X`
(any other child's supporters are disjoint from `Cx`'s, so its score is strictly smaller). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

/-- **The best child.** -/
theorem isBest_of_majority {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {V : View sp.n}
    (hsupp : V.support ⊆ V.votes) {σ : Int} {t : Time} {T : Set (Blk sp.n FGP)}
    (hT : T ⊆ Φ.tree) {C : Blk sp.n FGP} (hC : C ∈ Φ.tree) {SX VX : Set (Fin sp.n)}
    (h1 : SX ⊆ supporters Φ V σ C) (h2 : voters V.votes ⊆ VX) (h3 : VX.ncard < 2 * SX.ncard)
    {X Cx : Blk sp.n FGP} (hCx : Cx ∈ T) (hp : Cx.parent = some X.root) (hCxC : Φ.Anc Cx C) :
    IsBest sp (goldfishScore sp Φ V σ)
      {B | B ∈ T ∧ B.parent = some X.root ∧ goldfishEligible sp Φ t V σ B} Cx := by
  sorry

end Consensus.Goldilocks.SA

end
