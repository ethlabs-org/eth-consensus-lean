module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order

public section

/-! # Goldilocks SA: the best child from a transferred majority

The counting step of the vote transfer (Goldfish's argument, claims A1.8): if a set `SX` of
validators are supporters of `C` in a view whose support is among its votes, and the view's
voters are among `VX` with `|VX| < 2|SX|`, then every child `Cx ⪯ C` of a block `X` is
eligible (its score is a strict majority of the voters) and the best eligible child of `X`
(any other child's supporters are disjoint from `Cx`'s, so its score is strictly smaller). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

/-- Two children of one block in a coherent tree that are compatible are equal. -/
private theorem eq_of_compatible_siblings {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    {X D Cx : Blk sp.n FGP} (hD : D ∈ Φ.tree) (hCx : Cx ∈ Φ.tree)
    (hpD : D.parent = some X.root) (hpC : Cx.parent = some X.root)
    (h : Compatible Φ.tree D Cx) : D = Cx := by
  have key : ∀ {B B' : Blk sp.n FGP}, B ∈ Φ.tree → B.parent = some X.root →
      B'.parent = some X.root → Φ.Anc B B' → B = B' := by
    intro B B' hB hpB hpB' hBB'
    by_contra hne
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hBB' with rfl | ⟨Y, hBY, e⟩
    · exact hne rfl
    · -- `Y` is the tree parent of `B'`, which has the root of `B`'s parent
      have hY : Y.root = X.root := Option.some.inj (e.2.2.symm.trans hpB')
      have hYB : Y.slot < B.slot := hΦ.coherent.2 Y e.1 B hB (hpB.trans (congrArg some hY.symm))
      have := (Anc.slot_le hΦ.coherent hBY).1
      omega
  rcases h with h | h
  · exact key hD hpD hpC h
  · exact (key hCx hpC hpD h).symm

/-- **The best child.** -/
theorem isBest_of_majority {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {V : View sp.n}
    (hsupp : V.support ⊆ V.votes) {σ : Int} {t : Time} {T : Set (Blk sp.n FGP)}
    (hT : T ⊆ Φ.tree) {C : Blk sp.n FGP} {SX VX : Set (Fin sp.n)}
    (h1 : SX ⊆ supporters Φ V σ C) (h2 : voters V.votes ⊆ VX) (h3 : VX.ncard < 2 * SX.ncard)
    {X Cx : Blk sp.n FGP} (hCx : Cx ∈ T) (hp : Cx.parent = some X.root) (hCxC : Φ.Anc Cx C) :
    IsBest sp (goldfishScore sp Φ V σ)
      {B | B ∈ T ∧ B.parent = some X.root ∧ goldfishEligible sp Φ t V σ B} Cx := by
  have hsC : SX ⊆ supporters Φ V σ Cx :=
    h1.trans ((supporters_antitone sp) FGP Φ V σ Cx C hCxC)
  have hSX : SX.ncard ≤ (supporters Φ V σ Cx).ncard := Set.ncard_le_ncard hsC
  have hVX : (voters V.votes).ncard ≤ VX.ncard := Set.ncard_le_ncard h2
  have hsupv : ∀ B, supporters Φ V σ B ⊆ voters V.votes := by
    rintro B i ⟨-, x, hx, hval, -⟩
    exact ⟨x, hsupp hx, hval⟩
  have heqv : equivocators V.votes ⊆ voters V.votes := by
    rintro i ⟨x, hx, -, -, -, hval, -⟩
    exact ⟨x, hx, hval⟩
  refine ⟨⟨hCx, hp, Or.inr (Or.inr ?_)⟩, fun D hD hne => Or.inl ?_⟩
  · simp only [goldfishScore]
    omega
  -- `D`'s and `Cx`'s supporters and the equivocators are disjoint sets of voters
  have hdisj : Disjoint (supporters Φ V σ D) (supporters Φ V σ Cx) := by
    rw [Set.disjoint_left]
    rintro i ⟨hi, x, hx, hval, -, hxD⟩ ⟨-, x', hx', hval', -, hxC⟩
    have hxx : x = x' := by
      by_contra hxx
      exact hi ⟨x, hsupp hx, x', hsupp hx', hxx, hval, hval'⟩
    subst hxx
    exact hne (eq_of_compatible_siblings hΦ (hT hD.1) (hT hCx) hD.2.1 hp
      (compatible_of_ancR hΦ hxD hxC))
  have hdisjE : ∀ B, Disjoint (equivocators V.votes) (supporters Φ V σ B) := fun B =>
    Set.disjoint_left.2 fun i hi hs => hs.1 hi
  have hsum := Set.ncard_le_ncard (Set.union_subset (Set.union_subset heqv (hsupv D)) (hsupv Cx))
  rw [Set.ncard_union_eq (Set.disjoint_union_left.2 ⟨(hdisjE Cx), hdisj⟩),
    Set.ncard_union_eq (hdisjE D)] at hsum
  simp only [goldfishScore]
  omega

end Consensus.Goldilocks.SA

end
