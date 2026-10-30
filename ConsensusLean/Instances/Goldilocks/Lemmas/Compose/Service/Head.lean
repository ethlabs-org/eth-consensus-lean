module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views

public section

/-! # Goldilocks SA: the head reaches the record, and the confirmed tip is the record

The fork-choice half of A1.6, at one AC state and a well-formed frame. `ac_head` walks the viable
tree from the anchor (the deepest of the live lock blocks and `fc_root`) with the latest view. It
ends at a descendant of a block `R` of the tree when the anchor is compatible with `R` and either
`R` is at or below the anchor, or `R` is in the viable tree and a strict majority of the latest
view's voters support it (`anc_acHead`): on the path from the anchor to `R`, the child towards `R`
extends `fc_root` (the anchor is at least as deep as `fc_root`), is eligible by majority, and is
the best child, since a validator that supports a sibling cannot support it (the view's support is
among its votes, and a non-equivocator has one vote). When the head extends the record's block,
`ac_confirmed` is that block (`acConfirmed_eq`); when the tree holds no block named by the record,
it is `Φ.F` (`acConfirmed_eq_F`). -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type}

/-- Two distinct children of one block of a coherent set conflict. -/
private theorem not_anc_sibling {S : Set (Blk sp.n FGP)} (hS : Coherent S) {X D Y : Blk sp.n FGP}
    (hX : X ∈ S) (hDS : D ∈ S) (hD : D.parent = some X.root) (hY : Y.parent = some X.root)
    (hne : D ≠ Y) : ¬ Anc S D Y := by
  intro h
  obtain rfl | ⟨Z, hDZ, hZY⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 h
  · exact hne rfl
  obtain rfl : Z = X := hS.1 hZY.1 hX (Option.some.inj (hZY.2.2.symm.trans hY))
  have h₁ := (Anc.slot_le hS hDZ).1
  have h₂ := hS.2 Z hX D hDS hD
  omega

/-- The support of the latest view is among its votes. -/
private theorem latestView_support {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time} {v : Vote sp.n}
    (hv : v ∈ (latestView sp A Φ t).1.support) : v ∈ (latestView sp A Φ t).1.votes := by
  simp only [latestView, voteView, voteViewList, View.ofLists, Set.mem_ofPred_eq,
    List.mem_filter] at hv ⊢
  exact hv.1

/-- The supporters in the latest view are among its voters. -/
private theorem supporters_subset_voters {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    (B : Blk sp.n FGP) :
    supporters Φ (latestView sp A Φ t).1 (latestView sp A Φ t).2 B ⊆
      voters (latestView sp A Φ t).1.votes := by
  rintro i ⟨-, x, hx, hxi, -⟩
  exact ⟨x, latestView_support hx, hxi⟩

/-- In the latest view, no validator supports two conflicting blocks. -/
private theorem supporters_disjoint {A : SAState sp.n} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    {t : Time} {D Y : Blk sp.n FGP} (hc : ¬ Compatible Φ.tree D Y) :
    Disjoint (supporters Φ (latestView sp A Φ t).1 (latestView sp A Φ t).2 D)
      (supporters Φ (latestView sp A Φ t).1 (latestView sp A Φ t).2 Y) := by
  rw [Set.disjoint_left]
  rintro i ⟨hne, x, hx, hxi, -, hD⟩ ⟨-, x', hx', hx'i, -, hY⟩
  obtain rfl : x = x' := by
    by_contra h
    exact hne ⟨x, latestView_support hx, x', latestView_support hx', h, hxi, hx'i⟩
  exact hc (compatible_of_ancR hΦ hD hY)

/-- **The head reaches `R`.** At a well-formed frame, `ac_head(𝒜, Φ, t)` extends `R ∈ Φ.tree`
when the anchor is compatible with `R`, and `R` is at or below the anchor, or `R` is in the
viable tree and a strict majority of the latest view's voters support it. -/
theorem anc_acHead {A : SAState sp.n} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time}
    {R : Blk sp.n FGP} (hR : R ∈ Φ.tree) (hcomp : Compatible Φ.tree (getAnchor sp A Φ t) R)
    (hsup : Φ.Anc R (getAnchor sp A Φ t) ∨ (R ∈ Φ.viableTree Φ.tree ∧
      (voters (latestView sp A Φ t).1.votes).ncard <
        2 * (supporters Φ (latestView sp A Φ t).1 (latestView sp A Φ t).2 R).ncard)) :
    Φ.Anc R (acHead sp A Φ t) := by
  set V := (latestView sp A Φ t).1
  set s := (latestView sp A Φ t).2
  set a := getAnchor sp A Φ t
  have hvt : Φ.viableTree Φ.tree ⊆ Φ.tree := fun X hX => hX.1
  have hS : liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot} ⊆ Φ.tree := by
    rintro X (hX | hX)
    · exact hX.1
    · exact (Set.mem_singleton_iff.1 hX) ▸ hΦ.fcRoot_mem
  obtain ⟨D, hD⟩ := exists_deepest hΦ hS ⟨Φ.fcRoot, Or.inr rfl⟩
  have ha : a = D := by simp only [a, getAnchor, hD, Option.getD_some]
  have hdeep := deepest_mem hD
  rw [← ha] at hdeep
  have haT : a ∈ Φ.tree := hS hdeep.1
  change Φ.Anc R (ghost sp (Φ.viableTree Φ.tree) (goldfishScore sp Φ V s)
    (goldfishEligible sp Φ t V s) Φ.tree.ncard a)
  rcases hsup with hRa | ⟨hRv, hmaj⟩
  · exact hRa.trans (anc_ghost hvt _ haT)
  rcases hcomp with haR | hRa
  swap
  · exact hRa.trans (anc_ghost hvt _ haT)
  refine anc_ghost_of_best hΦ.coherent hvt (hΦ.finite.subset hvt) hR _ haR
    (Set.ncard_le_ncard (fun X hX => hX.1.1) hΦ.finite) fun X haX hXR hne => ?_
  obtain rfl | ⟨Y, hXY, hYR⟩ := Relation.ReflTransGen.cases_head_iff.1 hXR
  · exact absurd rfl hne
  -- `Y`, the child of `X` towards `R`, extends `fc_root`
  have hfY : Φ.Anc Φ.fcRoot Y := by
    rcases anc_total hΦ.coherent hRv.2.1 hYR with h | h
    · exact h
    by_cases hY : Y = Φ.fcRoot
    · exact hY ▸ Relation.ReflTransGen.refl
    by_cases haf : a = Φ.fcRoot
    · exact haf ▸ haX.tail hXY
    have hlt := depth_lt_of_anc hΦ ((haX.tail hXY).trans h) haf hΦ.fcRoot_mem
    rcases hdeep.2 Φ.fcRoot (Or.inr rfl) (Ne.symm haf) with h' | ⟨h', -⟩ <;> omega
  obtain ⟨W, hW, hWv, hRW⟩ := hRv.2.2
  have hYv : Y ∈ Φ.viableTree Φ.tree := ⟨hXY.2.1, hfY, W, hW, hWv, hYR.trans hRW⟩
  have hsub : (supporters Φ V s R).ncard ≤ (supporters Φ V s Y).ncard :=
    Set.ncard_le_ncard (supporters_antitone sp FGP Φ V s Y R hYR) (Set.toFinite _)
  refine ⟨Y, ⟨⟨hYv, hXY.2.2, Or.inr (Or.inr ?_)⟩, fun D' hD' hne' => Or.inl ?_⟩, hYR⟩
  · simp only [goldfishScore]
    omega
  -- a sibling `D'` of `Y` has fewer supporters
  have hc : ¬ Compatible Φ.tree D' Y := by
    rintro (h | h)
    · exact not_anc_sibling hΦ.coherent hXY.1 hD'.1.1 hD'.2.1 hXY.2.2 hne' h
    · exact not_anc_sibling hΦ.coherent hXY.1 hXY.2.1 hXY.2.2 hD'.2.1 (Ne.symm hne') h
  have hu : (supporters Φ V s D' ∪ supporters Φ V s Y).ncard =
      (supporters Φ V s D').ncard + (supporters Φ V s Y).ncard :=
    Set.ncard_union_eq (supporters_disjoint (A := A) (t := t) hΦ hc) (Set.toFinite _)
      (Set.toFinite _)
  have hle : (supporters Φ V s D' ∪ supporters Φ V s Y).ncard ≤ (voters V.votes).ncard :=
    Set.ncard_le_ncard (Set.union_subset (supporters_subset_voters (A := A) (t := t) D')
      (supporters_subset_voters (A := A) (t := t) Y)) (Set.toFinite _)
  simp only [goldfishScore]
  omega

/-- **The confirmed tip is the record** when the head extends the block `R` of the tree named by
`latest_confirmed`. -/
theorem acConfirmed_eq {A : SAState sp.n} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time}
    {R : Blk sp.n FGP} (hR : R ∈ Φ.tree) (hr : R.root = A.latestConfirmed)
    (hH : Φ.Anc R (acHead sp A Φ t)) : acConfirmed sp A Φ t = R := by
  have hin : InTree Φ A.latestConfirmed := ⟨R, hR, hr⟩
  have hl : lookup Φ A.latestConfirmed = some R := by
    unfold lookup
    rw [dite_eq_left_of_eq_true (eq_true hin)]
    obtain ⟨h₁, h₂⟩ := hin.choose_spec
    rw [hΦ.coherent.1 h₁ hR (h₂.trans hr.symm)]
  set S := {X | X ∈ Φ.tree ∧ Φ.Anc X R ∧ Φ.Anc X (acHead sp A Φ t)}
  have hS : S ⊆ Φ.tree := fun X hX => hX.1
  obtain ⟨D, hD⟩ := exists_deepest hΦ hS ⟨R, hR, Relation.ReflTransGen.refl, hH⟩
  have hch : ∀ B ∈ S, ∀ C ∈ S, Compatible Φ.tree B C := fun B hB C hC =>
    anc_total hΦ.coherent hB.2.1 hC.2.1
  have hRD := anc_deepest hΦ hS hch hD R ⟨hR, Relation.ReflTransGen.refl, hH⟩
  have hDR := (deepest_mem hD).1.2.1
  change (deepest Φ {X | X ∈ Φ.tree ∧ Φ.Anc X ((lookup Φ A.latestConfirmed).getD Φ.F) ∧
    Φ.Anc X (acHead sp A Φ t)}).getD Φ.F = R
  rw [hl, Option.getD_some]
  change (deepest Φ S).getD Φ.F = R
  rw [hD, Option.getD_some]
  exact Anc.antisymm hΦ.coherent hDR hRD

/-- At a well-formed frame, the head is in the tree. -/
private theorem acHead_mem {A : SAState sp.n} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (t : Time) :
    acHead sp A Φ t ∈ Φ.tree := by
  have hS : liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot} ⊆ Φ.tree := by
    rintro X (hX | hX)
    · exact hX.1
    · exact (Set.mem_singleton_iff.1 hX) ▸ hΦ.fcRoot_mem
  obtain ⟨D, hD⟩ := exists_deepest hΦ hS ⟨Φ.fcRoot, Or.inr rfl⟩
  have haT : getAnchor sp A Φ t ∈ Φ.tree := by
    simp only [getAnchor, hD, Option.getD_some]
    exact hS (deepest_mem hD).1
  have h := anc_ghost (fun X (hX : X ∈ Φ.viableTree Φ.tree) => hX.1)
    (score := goldfishScore sp Φ (latestView sp A Φ t).1 (latestView sp A Φ t).2)
    (eligible := goldfishEligible sp Φ t (latestView sp A Φ t).1 (latestView sp A Φ t).2)
    Φ.tree.ncard haT
  by_cases he : getAnchor sp A Φ t = acHead sp A Φ t
  · exact he ▸ haT
  · exact (Anc.mem h he).2

/-- **The confirmed tip falls back to `Φ.F`** when the tree holds no block named by
`latest_confirmed`. -/
theorem acConfirmed_eq_F {A : SAState sp.n} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time}
    (hr : ¬ InTree Φ A.latestConfirmed) : acConfirmed sp A Φ t = Φ.F := by
  have hl : lookup Φ A.latestConfirmed = none := by
    unfold lookup
    exact dite_eq_right hr
  set S := {X | X ∈ Φ.tree ∧ Φ.Anc X Φ.F ∧ Φ.Anc X (acHead sp A Φ t)}
  have hS : S ⊆ Φ.tree := fun X hX => hX.1
  obtain ⟨D, hD⟩ := exists_deepest hΦ hS
    ⟨Φ.F, hΦ.rooted.1, Relation.ReflTransGen.refl, hΦ.rooted.2 _ (acHead_mem hΦ t)⟩
  have hDS := (deepest_mem hD).1
  change (deepest Φ {X | X ∈ Φ.tree ∧ Φ.Anc X ((lookup Φ A.latestConfirmed).getD Φ.F) ∧
    Φ.Anc X (acHead sp A Φ t)}).getD Φ.F = Φ.F
  rw [hl, Option.getD_none]
  change (deepest Φ S).getD Φ.F = Φ.F
  rw [hD, Option.getD_some]
  exact Anc.antisymm hΦ.coherent hDS.2.1 (hΦ.rooted.2 _ hDS.1)

end Consensus.Goldilocks.SA

end
