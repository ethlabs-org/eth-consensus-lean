module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.SupportCounting
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic

public section

/-! # The same-row selector (proofs)

Paper `e439ef2`, §10. Two counted supports of strict majorities over one denominator `D`
intersect (`inter_nonempty_of_majority`); the intersecting identity's head extends both blocks,
so in a coherent `U` they are comparable. For an eligible `R` and the selected `C`, comparability
in `U` is not enough: when `C ⪯ R` in `U`, the frame's own ancestry gives `C ⪯ R` in the tree
(`frameAnc_of_anc_U`: the tree path from `Φ.F` up to `R`, which eligibility supplies, is the
unique parent path in `U`, and `C`, at or above `Φ.F`, lies on it), the tree depth is then strictly
larger at `R` unless `C = R` (`depth_lt_of_frameAnc`: the ancestors of `R` in the tree are a
finite chain), and the deepest selection excludes a strictly deeper eligible `R`. -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type}

/-- The rfl link: `confirmationScore` counts `scoreSupporters`. -/
theorem confirmationScore_eq_ncard (A : SAState sp.n) (Φ : Frm sp.n FGP) (j : Nat)
    (B : Blk sp.n FGP) : confirmationScore sp A Φ j B = (scoreSupporters A Φ j B).ncard := rfl

/-- Two subsets of `D`, each a strict majority of `D`, intersect. -/
theorem inter_nonempty_of_majority {D S S' : Set (Fin sp.n)} (hS : S ⊆ D) (hS' : S' ⊆ D)
    (h : D.ncard < 2 * S.ncard) (h' : D.ncard < 2 * S'.ncard) : (S ∩ S').Nonempty := by
  by_contra hne
  have hdis : Disjoint S S' :=
    Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hne)
  have hu := Set.ncard_union_eq hdis (Set.toFinite S) (Set.toFinite S')
  have hle := Set.ncard_le_ncard (Set.union_subset hS hS') (Set.toFinite D)
  omega

/-- The selected result of row `j` is in the tree, at or above `Φ.F`, a strict majority of the
row's voters, and the deepest such block. -/
private theorem selected_spec {A : SAState sp.n} {Φ : Frm sp.n FGP} {j : Nat} {C : Blk sp.n FGP}
    (h : getConfirmation sp A Φ j = some C) :
    IsDeepest Φ {B | B ∈ Φ.tree ∧ Φ.Anc Φ.F B ∧
      (voters {v | v ∈ A.pool j}).ncard < 2 * confirmationScore sp A Φ j B} C :=
  deepest_mem h

/-- Under the selector hypotheses, two blocks with strict-majority scores are comparable in `U`. -/
private theorem comparable_of_majority {U : Set (Blk sp.n FGP)} {D : Set (Fin sp.n)}
    {head : Fin sp.n → Blk sp.n FGP} {A A' : SAState sp.n} {Φ Φ' : Frm sp.n FGP} {j : Nat}
    {B B' : Blk sp.n FGP} (hU : Coherent U) (hH : SelectorHyp U D head A Φ j)
    (hH' : SelectorHyp U D head A' Φ' j) (hB : D.ncard < 2 * confirmationScore sp A Φ j B)
    (hB' : D.ncard < 2 * confirmationScore sp A' Φ' j B') : Anc U B B' ∨ Anc U B' B := by
  have hs := hH.supporters_sub B
  have hs' := hH'.supporters_sub B'
  obtain ⟨x, hx, hx'⟩ := inter_nonempty_of_majority (fun y hy => (hs hy).1)
    (fun y hy => (hs' hy).1) hB hB'
  exact anc_total hU (hs hx).2.2 (hs' hx').2.2

theorem selected_results_comparable : SelectedResultsComparable := by
  intro sp FGP U D head A A' Φ Φ' j C C' hU hH hH' hC hC'
  have h1 := (selected_spec hC).1.2.2
  have h2 := (selected_spec hC').1.2.2
  rw [hH.denominator] at h1
  rw [hH'.denominator] at h2
  exact comparable_of_majority hU hH hH' h1 h2

/-- A block of a coherent `U` at or above `Φ.F` (in the tree) that is an ancestor in `U` of a
block `R` of the tree at or above `Φ.F` is an ancestor of `R` in the tree: the tree path from
`Φ.F` to `R` is the unique parent path in `U`. -/
private theorem frameAnc_of_anc_U {U : Set (Blk sp.n FGP)} (hU : Coherent U) {Φ : Frm sp.n FGP}
    (hΦU : Φ.tree ⊆ U) {C R : Blk sp.n FGP} (hFC : Φ.Anc Φ.F C) (hFR : Φ.Anc Φ.F R)
    (hCR : Anc U C R) : Φ.Anc C R := by
  have hFCU : Anc U Φ.F C := hFC.mono hΦU
  induction hFR with
  | refl =>
    obtain rfl := Anc.antisymm hU hCR hFCU
    exact Relation.ReflTransGen.refl
  | @tail Z Z' hFZ e ih =>
    obtain rfl | ⟨P, hCP, eP⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hCR
    · exact Relation.ReflTransGen.refl
    · have hPZ : P = Z := hU.1 eP.1 (hΦU e.1)
        (Option.some_injective _ (eP.2.2.symm.trans e.2.2))
      subst hPZ
      exact (ih hCP).tail e

/-- The ancestors of a block in a coherent tree are finite (a chain, one per slot below it). -/
private theorem ancestors_finite {Φ : Frm sp.n FGP} (hΦ : Coherent Φ.tree) (R : Blk sp.n FGP) :
    {A | Φ.Anc A R}.Finite := by
  refine Set.Finite.of_finite_image (f := fun A : Blk sp.n FGP => A.slot)
    ((Set.finite_Iic R.slot).subset ?_) ?_
  · rintro _ ⟨A, hA, rfl⟩
    exact (hA.slot_le hΦ).1
  · intro A hA A' hA' hs
    rcases anc_total hΦ hA hA' with h | h
    · by_contra hne; have := (h.slot_le hΦ).2 hne; simp at hs; omega
    · by_contra hne; have := (h.slot_le hΦ).2 (Ne.symm hne); simp at hs; omega

/-- In a coherent tree, depth strictly increases along strict ancestry. -/
private theorem depth_lt_of_frameAnc {Φ : Frm sp.n FGP} (hΦ : Coherent Φ.tree)
    {C R : Blk sp.n FGP} (h : Φ.Anc C R) (hne : C ≠ R) : depth Φ C < depth Φ R :=
  Set.ncard_lt_ncard ⟨fun _ hX => hX.trans h, fun hsub => hne
    (Anc.antisymm hΦ h (hsub (Relation.ReflTransGen.refl : Φ.Anc R R)))⟩ (ancestors_finite hΦ R)

theorem eligible_below_selected : EligibleBelowSelected := by
  intro sp FGP U D head A Φ j R C hU hH hR hFR hRmaj hC
  have hsp := selected_spec hC
  have hCmaj := hsp.1.2.2
  rw [hH.denominator] at hCmaj
  rcases comparable_of_majority hU hH hH hRmaj hCmaj with h | h
  · exact h
  · by_cases hRC : R = C
    · exact hRC ▸ Relation.ReflTransGen.refl
    · have hΦ : Coherent Φ.tree := hU.mono hH.tree_sub
      have hloc := frameAnc_of_anc_U hU hH.tree_sub hsp.1.2.1 hFR h
      have hlt := depth_lt_of_frameAnc hΦ hloc (Ne.symm hRC)
      have hRin : R ∈ {B | B ∈ Φ.tree ∧ Φ.Anc Φ.F B ∧
          (voters {v | v ∈ A.pool j}).ncard < 2 * confirmationScore sp A Φ j B} :=
        ⟨hR, hFR, by rw [hH.denominator]; exact hRmaj⟩
      rcases hsp.2 R hRin hRC with h' | ⟨h', -⟩ <;> omega

end Consensus.Goldilocks.SA

end
