module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk

public section

/-! # Goldilocks SA: where a walk stops

`WalkEnd T sc el a E`: the walk of `T` (scores `sc`, eligibility `el`) from `a` stops at `E`,
some number of steps in, with no best eligible child at `E`. The end of a walk does not
depend on the fuel once it stops (`WalkEnd.unique`); a walk that passes `X` ends where the walk
from `X` ends (`WalkEnd.of_anc`); a walk with at least one step per block of `T` above its start
stops (`walkEnd_ghost`); and two walks whose eligible children and scores agree at every block
other than the first walk's end end together (`WalkEnd.congr`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

/-- The eligible children of `X` in `T`. -/
abbrev eligibleChildren (T : Set (Blk sp.n FGP)) (el : Blk sp.n FGP → Prop) (X : Blk sp.n FGP) :
    Set (Blk sp.n FGP) :=
  {B | B ∈ T ∧ B.parent = some X.root ∧ el B}

/-- The walk of `T` from `a` stops at `E`. -/
def WalkEnd (T : Set (Blk sp.n FGP)) (sc : Blk sp.n FGP → Nat) (el : Blk sp.n FGP → Prop)
    (a E : Blk sp.n FGP) : Prop :=
  ∃ f, ghost sp T sc el f a = E ∧ ¬ ∃ C, IsBest sp sc (eligibleChildren T el E) C

variable {T T₂ S : Set (Blk sp.n FGP)} {sc sc₂ : Blk sp.n FGP → Nat}
  {el el₂ : Blk sp.n FGP → Prop} {a E X : Blk sp.n FGP}

private theorem ghost_succ_eq_of_best {f : Nat} {C : Blk sp.n FGP}
    (hC : IsBest sp sc (eligibleChildren T el a) C) :
    ghost sp T sc el (f + 1) a = ghost sp T sc el f C := by
  rw [ghost, dite_eq_left_of_eq_true (eq_true ⟨C, hC⟩)]
  have hch : (⟨C, hC⟩ : ∃ C, IsBest sp sc (eligibleChildren T el a) C).choose = C :=
    IsBest.unique (Exists.choose_spec _) hC
  rw [hch]

theorem walkEnd_iff : WalkEnd (sp := sp) T sc el a E ↔
    ∃ f, ghost sp T sc el f a = E ∧ ¬ ∃ C, IsBest sp sc (eligibleChildren T el E) C := Iff.rfl

/-- A stopped walk ends at its start. -/
theorem walkEnd_self (h : ¬ ∃ C, IsBest sp sc (eligibleChildren T el a) C) :
    WalkEnd (sp := sp) T sc el a a :=
  ⟨0, rfl, h⟩

/-- One step: the walk from `a` ends where the walk from its best eligible child ends. -/
theorem WalkEnd.step {C : Blk sp.n FGP} (hC : IsBest sp sc (eligibleChildren T el a) C)
    (h : WalkEnd (sp := sp) T sc el C E) : WalkEnd (sp := sp) T sc el a E := by
  obtain ⟨f, hf, hs⟩ := h
  exact ⟨f + 1, (ghost_succ_eq_of_best hC).trans hf, hs⟩

/-- The step back: a walk from `a` that ends elsewhere goes through the best child of `a`. -/
theorem WalkEnd.of_step (h : WalkEnd (sp := sp) T sc el a E) (hne : a ≠ E) :
    ∃ C, IsBest sp sc (eligibleChildren T el a) C ∧ WalkEnd (sp := sp) T sc el C E := by
  obtain ⟨f, hf, hs⟩ := h
  cases f with
  | zero => exact absurd hf hne
  | succ f =>
    rw [ghost] at hf
    split at hf
    · rename_i hb
      exact ⟨_, hb.choose_spec, f, hf, hs⟩
    · exact absurd hf hne

/-- The end of a walk is unique. -/
theorem WalkEnd.unique {E' : Blk sp.n FGP} (h : WalkEnd (sp := sp) T sc el a E)
    (h' : WalkEnd (sp := sp) T sc el a E') : E = E' := by
  obtain ⟨f, rfl, hs⟩ := h
  obtain ⟨f', rfl, hs'⟩ := h'
  rcases le_total f f' with hle | hle
  · exact (ghost_fuel_stable hle hs).symm
  · exact ghost_fuel_stable hle hs'

/-- The end of a walk extends its start. -/
theorem WalkEnd.anc (hT : T ⊆ S) (ha : a ∈ S) (h : WalkEnd (sp := sp) T sc el a E) :
    Anc S a E := by
  obtain ⟨f, rfl, -⟩ := h
  exact anc_ghost hT f ha

/-- **A walk passes the blocks between its start and its end**: from such a block the walk ends
at the same block. -/
theorem WalkEnd.of_anc (hS : Coherent S) (hT : T ⊆ S) (ha : a ∈ S)
    (h : WalkEnd (sp := sp) T sc el a E) (haX : Anc S a X) (hXE : Anc S X E) :
    WalkEnd (sp := sp) T sc el X E := by
  obtain ⟨f, hf, hs⟩ := h
  induction f generalizing a with
  | zero =>
    obtain rfl : a = E := hf
    obtain rfl := Anc.antisymm hS haX hXE
    exact ⟨0, rfl, hs⟩
  | succ f ih =>
    by_cases hX : a = X
    · exact hX ▸ ⟨f + 1, hf, hs⟩
    rw [ghost] at hf
    split at hf
    · rename_i hb
      set C := hb.choose
      have hC := hb.choose_spec
      have hCS : C ∈ S := hT hC.1.1
      refine ih hCS ?_ hf
      -- `C` is a child of `a` below `E`, and `a ≺ X ⪯ E`: so `C ⪯ X`
      have hCE : Anc S C E := hf ▸ anc_ghost hT f hCS
      rcases anc_total hS hCE hXE with h | h
      · exact h
      · by_cases hXC : X = C
        · exact hXC ▸ Relation.ReflTransGen.refl
        obtain ⟨Y, hXY, hYC⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 h |>.resolve_left
          fun e => hXC e.symm
        obtain rfl : Y = a := hS.1 hYC.1 ha (Option.some.inj (hYC.2.2.symm.trans hC.1.2.1))
        exact absurd (Anc.antisymm hS haX hXY) hX
    · rename_i hb
      subst hf
      exact absurd (Anc.antisymm hS haX hXE) hX

/-- **Enough fuel stops the walk**: with at least one step per block of `T` above its start, the
walk stops. -/
theorem walkEnd_ghost (hS : Coherent S) (hT : T ⊆ S) (hfin : T.Finite) (f : Nat) (ha : a ∈ S)
    (hfuel : {Y | Y ∈ T ∧ Anc S a Y ∧ Y ≠ a}.ncard ≤ f) :
    WalkEnd (sp := sp) T sc el a (ghost sp T sc el f a) := by
  induction f generalizing a with
  | zero =>
    refine ⟨0, rfl, fun ⟨C, hC⟩ => ?_⟩
    have hCa : C ∈ {Y | Y ∈ T ∧ Anc S a Y ∧ Y ≠ a} := by
      refine ⟨hC.1.1, Relation.ReflTransGen.single ⟨ha, hT hC.1.1, hC.1.2.1⟩, fun h => ?_⟩
      have := hS.2 a ha C (hT hC.1.1) hC.1.2.1
      rw [h] at this; omega
    have := Set.ncard_pos (hfin.subset fun Y hY => hY.1) |>.2 ⟨C, hCa⟩
    omega
  | succ f ih =>
    by_cases hb : ∃ C, IsBest sp sc (eligibleChildren T el a) C
    · obtain ⟨C, hC⟩ := hb
      have hCS : C ∈ S := hT hC.1.1
      have hslot := hS.2 a ha C hCS hC.1.2.1
      have hac : Anc S a C := Relation.ReflTransGen.single ⟨ha, hCS, hC.1.2.1⟩
      have hmem : C ∈ {Y | Y ∈ T ∧ Anc S a Y ∧ Y ≠ a} :=
        ⟨hC.1.1, hac, fun h => by rw [h] at hslot; omega⟩
      have hsub : {Y | Y ∈ T ∧ Anc S C Y ∧ Y ≠ C} ⊆
          {Y | Y ∈ T ∧ Anc S a Y ∧ Y ≠ a} \ {C} := by
        rintro Y ⟨hY, hCY, hne⟩
        refine ⟨⟨hY, hac.trans hCY, fun h => ?_⟩, hne⟩
        subst h
        have := (Anc.slot_le hS hCY).1
        omega
      have hfin' : {Y | Y ∈ T ∧ Anc S a Y ∧ Y ≠ a}.Finite := hfin.subset fun Y hY => hY.1
      have hle := Set.ncard_le_ncard hsub hfin'.sdiff
      rw [Set.ncard_sdiff (Set.singleton_subset_iff.2 hmem), Set.ncard_singleton] at hle
      rw [ghost_succ_eq_of_best hC]
      exact (ih hCS (by omega)).step hC
    · have hg : ghost sp T sc el (f + 1) a = a := by simp only [ghost, hb, ↓reduceDIte]
      rw [hg]
      exact walkEnd_self hb

/-- **Two walks that agree away from the first walk's end**: if at every block other than `E`
(by root) the eligible children and their scores agree, the walk of the second tree from `a`
ends where its walk from `E` ends. -/
theorem WalkEnd.congr {E' : Blk sp.n FGP} (hS : Coherent S) (hT : T ⊆ S) (ha : a ∈ S)
    (hE : E ∈ S)
    (hag : ∀ X, X.root ≠ E.root → eligibleChildren T el X = eligibleChildren T₂ el₂ X ∧
      ∀ B ∈ eligibleChildren T el X, sc B = sc₂ B)
    (h : WalkEnd (sp := sp) T sc el a E) (h₂ : WalkEnd (sp := sp) T₂ sc₂ el₂ E E') :
    WalkEnd (sp := sp) T₂ sc₂ el₂ a E' := by
  obtain ⟨f, hf, hs⟩ := h
  induction f generalizing a with
  | zero =>
    obtain rfl : a = E := hf
    exact h₂
  | succ f ih =>
    by_cases hr : a.root = E.root
    · obtain rfl : a = E := hS.1 ha hE hr
      exact h₂
    rw [ghost] at hf
    split at hf
    · rename_i hb
      have hC := hb.choose_spec
      obtain ⟨heq, hsc⟩ := hag a hr
      have hC₂ : IsBest sp sc₂ (eligibleChildren T₂ el₂ a) hb.choose := by
        rw [← heq]
        refine ⟨hC.1, fun D hD hne => ?_⟩
        rw [← hsc D hD, ← hsc _ hC.1]
        exact hC.2 D hD hne
      exact (ih (hT hC.1.1) hf).step hC₂
    · subst hf
      exact absurd rfl hr

end Consensus.Goldilocks.SA

end
