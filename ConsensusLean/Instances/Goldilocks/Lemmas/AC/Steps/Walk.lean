module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order

public section

/-! # Goldilocks SA: the head walk

Facts about `ghost`, the walk behind every head: it only descends (each step goes to a child in
the walked tree), and it passes a block `C` when, at every block between its start and `C`, the
child towards `C` is the best eligible child; the walk then ends at a descendant of `C`, given
enough steps (one per slot between the start and `C`, since slots increase along parent edges
in a coherent set). The vote-transfer lemmas (A1.2–A1.4, A1.8) supply the best-child condition
from their counting arguments. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

/-- The best of a set by score (ties by root) is unique. -/
theorem IsBest.unique {score : Blk sp.n FGP → Nat} {S : Set (Blk sp.n FGP)} {C D : Blk sp.n FGP}
    (hC : IsBest sp score S C) (hD : IsBest sp score S D) : C = D := by
  by_contra hne
  rcases hC.2 D hD.1 (Ne.symm hne) with h | ⟨h, h'⟩ <;>
    rcases hD.2 C hC.1 hne with h₂ | ⟨h₂, h₂'⟩ <;> omega

/-- The walk only descends: it ends at a descendant (inside `S ⊇ tree`) of its start. -/
theorem anc_ghost {S tree : Set (Blk sp.n FGP)} (hT : tree ⊆ S) {score : Blk sp.n FGP → Nat}
    {eligible : Blk sp.n FGP → Prop} (fuel : Nat) {a : Blk sp.n FGP} (ha : a ∈ S) :
    Anc S a (ghost sp tree score eligible fuel a) := by
  induction fuel generalizing a with
  | zero => exact Relation.ReflTransGen.refl
  | succ f ih =>
    rw [ghost]
    split
    · rename_i h
      have hc := h.choose_spec.1
      exact Relation.ReflTransGen.head ⟨ha, hT hc.1, hc.2.1⟩ (ih (hT hc.1))
    · exact Relation.ReflTransGen.refl

/-- **The walk passes `C`.** In a coherent `S ⊇ tree` with `tree` finite, a walk from `a ⪯ C`
with at least as many steps as there are blocks of `tree` strictly above `a` and at or below
`C`, at each block `X` with `a ⪯ X ≺ C` of which the best eligible child of the walked tree is
an ancestor of `C`, ends at a descendant of `C`. -/
theorem anc_ghost_of_best {S tree : Set (Blk sp.n FGP)} (hS : Coherent S) (hT : tree ⊆ S)
    (hfin : tree.Finite) {score : Blk sp.n FGP → Nat} {eligible : Blk sp.n FGP → Prop}
    {C : Blk sp.n FGP} (hC : C ∈ S) (fuel : Nat) {a : Blk sp.n FGP} (haC : Anc S a C)
    (hfuel : {X | X ∈ tree ∧ Anc S a X ∧ Anc S X C ∧ X ≠ a}.ncard ≤ fuel)
    (hbest : ∀ X, Anc S a X → Anc S X C → X ≠ C → ∃ Cx,
      IsBest sp score {B | B ∈ tree ∧ B.parent = some X.root ∧ eligible B} Cx ∧ Anc S Cx C) :
    Anc S C (ghost sp tree score eligible fuel a) := by
  induction fuel generalizing a with
  | zero =>
    by_cases he : a = C
    · subst he; exact Relation.ReflTransGen.refl
    · exfalso
      obtain ⟨Cx, hbx, hxC⟩ := hbest a Relation.ReflTransGen.refl haC he
      have ha : a ∈ S := (Anc.mem haC he).1
      have hslot : a.slot < Cx.slot := hS.2 a ha Cx (hT hbx.1.1) hbx.1.2.1
      have hmem : Cx ∈ {X | X ∈ tree ∧ Anc S a X ∧ Anc S X C ∧ X ≠ a} :=
        ⟨hbx.1.1, Relation.ReflTransGen.single ⟨ha, hT hbx.1.1, hbx.1.2.1⟩, hxC,
          fun h => by rw [h] at hslot; omega⟩
      have := Set.ncard_pos (hfin.subset fun X hX => hX.1) |>.2 ⟨Cx, hmem⟩
      omega
  | succ f ih =>
    by_cases he : a = C
    · subst he
      exact anc_ghost hT (f + 1) hC
    obtain ⟨Cx, hbx, hxC⟩ := hbest a Relation.ReflTransGen.refl haC he
    have ha : a ∈ S := (Anc.mem haC he).1
    rw [ghost]
    rw [dite_eq_left_of_eq_true (eq_true ⟨Cx, hbx⟩)]
    have hch : (⟨Cx, hbx⟩ : ∃ C, IsBest sp score
        {B | B ∈ tree ∧ B.parent = some a.root ∧ eligible B} C).choose = Cx :=
      IsBest.unique (Exists.choose_spec _) hbx
    rw [hch]
    have hslot : a.slot < Cx.slot := hS.2 a ha Cx (hT hbx.1.1) hbx.1.2.1
    have hax : Anc S a Cx := Relation.ReflTransGen.single ⟨ha, hT hbx.1.1, hbx.1.2.1⟩
    refine ih hxC ?_ fun X haX hXC hne => hbest X (hax.trans haX) hXC hne
    -- one block fewer: `Cx` itself
    have hsub : {X | X ∈ tree ∧ Anc S Cx X ∧ Anc S X C ∧ X ≠ Cx} ⊆
        {X | X ∈ tree ∧ Anc S a X ∧ Anc S X C ∧ X ≠ a} \ {Cx} := by
      rintro X ⟨hX, hCxX, hXC, hne⟩
      refine ⟨⟨hX, hax.trans hCxX, hXC, fun h => ?_⟩, hne⟩
      subst h
      have := (Anc.slot_le hS hCxX).1
      omega
    have hmem : Cx ∈ {X | X ∈ tree ∧ Anc S a X ∧ Anc S X C ∧ X ≠ a} :=
      ⟨hbx.1.1, hax, hxC, fun h => by rw [h] at hslot; omega⟩
    have hfin' : {X | X ∈ tree ∧ Anc S a X ∧ Anc S X C ∧ X ≠ a}.Finite :=
      hfin.subset fun X hX => hX.1
    have := Set.ncard_le_ncard hsub (hfin'.sdiff)
    rw [Set.ncard_sdiff (Set.singleton_subset_iff.2 hmem), Set.ncard_singleton] at this
    omega

/-- **Two walks agree** when, at every block the first walk visits before its last step, the two
trees give the same eligible children and the two scores agree on them. -/
theorem ghost_congr {T₁ T₂ : Set (Blk sp.n FGP)} {sc₁ sc₂ : Blk sp.n FGP → Nat}
    {el₁ el₂ : Blk sp.n FGP → Prop} (f : Nat) (a : Blk sp.n FGP)
    (hstep : ∀ k < f,
      {B | B ∈ T₁ ∧ B.parent = some (ghost sp T₁ sc₁ el₁ k a).root ∧ el₁ B} =
        {B | B ∈ T₂ ∧ B.parent = some (ghost sp T₁ sc₁ el₁ k a).root ∧ el₂ B} ∧
      ∀ B ∈ {B | B ∈ T₁ ∧ B.parent = some (ghost sp T₁ sc₁ el₁ k a).root ∧ el₁ B},
        sc₁ B = sc₂ B) :
    ghost sp T₁ sc₁ el₁ f a = ghost sp T₂ sc₂ el₂ f a := by
  induction f generalizing a with
  | zero => rfl
  | succ f ih =>
    obtain ⟨hS, hsc⟩ := hstep 0 (Nat.succ_pos f)
    simp only [ghost] at hS hsc
    have hbest : ∀ C, IsBest sp sc₁ {B | B ∈ T₁ ∧ B.parent = some a.root ∧ el₁ B} C ↔
        IsBest sp sc₂ {B | B ∈ T₂ ∧ B.parent = some a.root ∧ el₂ B} C := by
      intro C
      rw [← hS]
      constructor
      · rintro ⟨hC, h⟩
        refine ⟨hC, fun D hD hne => ?_⟩
        rw [← hsc D hD, ← hsc C hC]
        exact h D hD hne
      · rintro ⟨hC, h⟩
        refine ⟨hC, fun D hD hne => ?_⟩
        rw [hsc D hD, hsc C hC]
        exact h D hD hne
    rw [ghost, ghost]
    by_cases h₁ : ∃ C, IsBest sp sc₁ {B | B ∈ T₁ ∧ B.parent = some a.root ∧ el₁ B} C
    · have h₂ : ∃ C, IsBest sp sc₂ {B | B ∈ T₂ ∧ B.parent = some a.root ∧ el₂ B} C :=
        let ⟨C, hC⟩ := h₁; ⟨C, (hbest C).1 hC⟩
      simp only [h₁, h₂, ↓reduceDIte]
      have he : h₁.choose = h₂.choose :=
        IsBest.unique ((hbest _).1 h₁.choose_spec) h₂.choose_spec
      rw [← he]
      refine ih _ fun k hk => ?_
      have := hstep (k + 1) (by omega)
      simp only [ghost, h₁, ↓reduceDIte] at this
      exact this
    · have h₂ : ¬ ∃ C, IsBest sp sc₂ {B | B ∈ T₂ ∧ B.parent = some a.root ∧ el₂ B} C :=
        fun ⟨C, hC⟩ => h₁ ⟨C, (hbest C).2 hC⟩
      simp only [h₁, h₂, ↓reduceDIte]

/-- **A stopped walk stays**: once the walk has no best child, more fuel does not move it. -/
theorem ghost_fuel_stable {T : Set (Blk sp.n FGP)} {sc : Blk sp.n FGP → Nat}
    {el : Blk sp.n FGP → Prop} {f f' : Nat} (hf : f ≤ f') {a : Blk sp.n FGP}
    (h : ¬ ∃ C, IsBest sp sc {B | B ∈ T ∧ B.parent = some (ghost sp T sc el f a).root ∧ el B} C) :
    ghost sp T sc el f' a = ghost sp T sc el f a := by
  induction f generalizing a f' with
  | zero =>
    cases f' with
    | zero => rfl
    | succ f' => simp only [ghost] at h ⊢; simp only [h, ↓reduceDIte]
  | succ f ih =>
    obtain ⟨f', rfl⟩ : ∃ g, f' = g + 1 := ⟨f' - 1, by omega⟩
    rw [ghost, ghost]
    split
    · rename_i hb
      simp only [ghost, hb, ↓reduceDIte] at h
      exact ih (by omega) h
    · rfl

end Consensus.Goldilocks.SA

end
