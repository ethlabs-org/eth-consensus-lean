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

end Consensus.Goldilocks.SA

end
