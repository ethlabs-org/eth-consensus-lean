module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic

public section

/-! # Goldilocks SA: views and counting (A0.2's support clause, A0.3's view facts)

Facts about vote views that hold in any well-formed frame, with no reachability: support heads
are in the tree, supporters shrink and opponents grow along ancestry, and majorities lie on one
chain. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- A support vote of a vote view is resolved before the cutoff, so its head is in the tree. -/
theorem voteView_support_inTree {n : Nat} {FGP : Type} {A : SAState n} {Φ : Frm n FGP} {σ : Int}
    {cutoff : ETime} {x : Vote n} (hx : x ∈ (voteView A Φ σ cutoff).support) : InTree Φ x.head := by
  simp only [voteView, voteViewList, View.ofLists, Set.mem_ofPred_eq, List.mem_filter,
    decide_eq_true_eq] at hx
  exact inTree_of_resolutionTime_ne_top (ne_top_of_lt hx.2)

/-- In a well-formed frame, the opponents of `Φ.F` in any view are its equivocators. -/
theorem opponents_F {FGP : Type} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (V : View sp.n) (s : Int) :
    opponents sp Φ V s Φ.F = equivocators V.votes := by
  ext i
  simp only [opponents, Set.mem_union, Set.mem_ofPred_eq, or_iff_left_iff_imp]
  rintro ⟨x, -, -, -, H, hH, -, hc⟩
  exact absurd (compatible_F hΦ hH) hc

/-- **A0.2, support heads and the opponents of `Φ.F`.** -/
theorem support_in_tree : SupportInTree sp := by
  intro FGP A Φ hΦ
  refine ⟨fun σ cutoff s' => ⟨fun x hx => voteView_support_inTree hx, opponents_F sp hΦ _ _⟩,
    fun s s' => ⟨fun x hx => ?_, opponents_F sp hΦ _ _⟩⟩
  rcases hx with hx | ⟨B, -, -, -, -, H, hH, hr, -⟩
  · exact voteView_support_inTree hx
  · exact ⟨H, hH, hr⟩

/-- **A0.3, supporters.** -/
theorem supporters_antitone : SupportersAntitone sp := by
  intro FGP Φ V s B C hBC i ⟨hne, x, hx, hval, hslot, R, hR, hroot, hCR⟩
  exact ⟨hne, x, hx, hval, hslot, R, hR, hroot, Relation.ReflTransGen.trans hBC hCR⟩

/-- In a coherent tree, the descendant of a block that conflicts with `H` conflicts with `H`. -/
theorem not_compatible_of_anc {n : Nat} {FGP : Type} {S : Set (Blk n FGP)} (hS : Coherent S)
    {H B C : Blk n FGP} (hBC : Anc S B C) (hHB : ¬ Compatible S H B) : ¬ Compatible S H C := by
  rintro (hHC | hCH)
  · exact hHB (anc_total hS hHC hBC)
  · exact hHB (Or.inr (hBC.trans hCH))

/-- **A0.3, opponents.** -/
theorem opponents_monotone : OpponentsMonotone sp := by
  intro FGP Φ V s B C hΦ hBC i hi
  rcases hi with hi | ⟨x, hx, hv, hs, H, hH, hr, hc⟩
  · exact Or.inl hi
  · exact Or.inr ⟨x, hx, hv, hs, H, hH, hr, not_compatible_of_anc hΦ.coherent hBC hc⟩

/-- Two blocks extended by heads with one root (in a coherent tree) are compatible. -/
theorem compatible_of_ancR {n : Nat} {FGP : Type} {Φ : Frm n FGP} (hΦ : FrameOK Φ) {r : Nat}
    {B C : Blk n FGP} (hB : AncR Φ B r) (hC : AncR Φ C r) : Compatible Φ.tree B C := by
  obtain ⟨R, hR, hRr, hBR⟩ := hB
  obtain ⟨R', hR', hR'r, hCR'⟩ := hC
  have : R = R' := hΦ.coherent.1 hR hR' (hRr.trans hR'r.symm)
  subst this
  exact anc_total hΦ.coherent hBR hCR'

/-- Two sets of validators whose sizes add up to more than a bound `m ≥ |S ∪ T|` meet. -/
theorem inter_nonempty_of_ncard {n : Nat} {S T : Set (Fin n)} {m : Nat}
    (hm : (S ∪ T).ncard ≤ m) (h : m < S.ncard + T.ncard) : (S ∩ T).Nonempty := by
  have := Set.ncard_union_add_ncard_inter S T (Set.toFinite _) (Set.toFinite _)
  exact Set.nonempty_of_ncard_ne_zero (by omega)

/-- **A0.3, majority blocks.** -/
theorem majority_chain : MajorityChain sp := by
  intro FGP Φ V s B C hΦ hsub hB hC hsB hsC
  have hvot : ∀ D, supporters Φ V s D ⊆ voters V.votes := by
    rintro D i ⟨-, x, hx, hv, -⟩
    exact ⟨x, hsub hx, hv⟩
  have hu : (supporters Φ V s B ∪ supporters Φ V s C).ncard ≤ (voters V.votes).ncard :=
    Set.ncard_le_ncard (Set.union_subset (hvot B) (hvot C)) (Set.toFinite _)
  obtain ⟨i, ⟨hne, x, hx, hxv, -, hxB⟩, ⟨-, y, hy, hyv, -, hyC⟩⟩ :=
    inter_nonempty_of_ncard hu (by omega)
  have hxy : x = y := by
    by_contra hxy
    exact hne ⟨x, hsub hx, y, hsub hy, hxy, hxv, hyv⟩
  subst hxy
  exact compatible_of_ancR hΦ hxB hyC

/-- **A0.3, optimistic blocks.** -/
theorem optimistic_chain : OptimisticChain sp := by
  intro FGP A Φ s B C hΦ he hB hC hvB hvC
  set vB := optimisticVoters sp A Φ s B
  set vC := optimisticVoters sp A Φ s C
  set E := equivocators {x | x ∈ A.pool s}
  have hu : (vB ∪ vC).ncard ≤ sp.n := by
    have := Set.ncard_le_ncard (Set.subset_univ (vB ∪ vC)) (Set.toFinite _)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have hi := Set.ncard_union_add_ncard_inter vB vC (Set.toFinite _) (Set.toFinite _)
  have hnot : ¬ (vB ∩ vC ⊆ E) := by
    intro hsub
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  obtain ⟨i, ⟨⟨x, hx, hxv, hxB⟩, ⟨y, hy, hyv, hyC⟩⟩, hiE⟩ := Set.not_subset.mp hnot
  have hxy : x = y := by
    by_contra hxy
    exact hiE ⟨x, hx, y, hy, hxy, hxv, hyv⟩
  subst hxy
  exact compatible_of_ancR hΦ hxB hyC

end Consensus.Goldilocks.SA

end
