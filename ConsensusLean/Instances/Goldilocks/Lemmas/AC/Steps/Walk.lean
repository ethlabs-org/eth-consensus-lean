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

/-- **Walks compose**: `k + m` steps from `a` are `m` steps from where `k` steps from `a` end. -/
theorem ghost_add {T : Set (Blk sp.n FGP)} {sc : Blk sp.n FGP → Nat} {el : Blk sp.n FGP → Prop}
    (k m : Nat) (a : Blk sp.n FGP) :
    ghost sp T sc el (k + m) a = ghost sp T sc el m (ghost sp T sc el k a) := by
  classical
  induction k generalizing a with
  | zero => simp [ghost]
  | succ k ih =>
    rw [show k + 1 + m = (k + m) + 1 by omega, ghost, ghost]
    split
    · exact ih _
    · rename_i h
      cases m with
      | zero => rfl
      | succ m => rw [ghost, dite_eq_right_iff.2 fun h' => absurd h' h]

/-- **The voter's walk follows the proposer's to `P`.** Two walks from `D`: the first ends at `Q`
and stops there; at every block it visits before `Q`, the second walk's eligible children are
eligible for the first with equal scores (competitors reflect), and the first walk's best child is
eligible for the second (the winner persists); at `Q` the second walk's only eligible child is `P`,
where it stops. Then the second walk ends at `P` (with one more step). -/
theorem ghost_follow {T₁ T₂ : Set (Blk sp.n FGP)} {sc₁ sc₂ : Blk sp.n FGP → Nat}
    {el₁ el₂ : Blk sp.n FGP → Prop} {Q P : Blk sp.n FGP} (f : Nat) (D : Blk sp.n FGP)
    (h₁ : ghost sp T₁ sc₁ el₁ f D = Q)
    (hstop : ¬ ∃ C, IsBest sp sc₁ {B | B ∈ T₁ ∧ B.parent = some Q.root ∧ el₁ B} C)
    (hstep : ∀ k < f, ghost sp T₁ sc₁ el₁ k D ≠ Q →
      (∀ B ∈ {B | B ∈ T₂ ∧ B.parent = some (ghost sp T₁ sc₁ el₁ k D).root ∧ el₂ B},
        B ∈ {B | B ∈ T₁ ∧ B.parent = some (ghost sp T₁ sc₁ el₁ k D).root ∧ el₁ B} ∧
          sc₂ B = sc₁ B) ∧
      ∀ C, IsBest sp sc₁ {B | B ∈ T₁ ∧ B.parent = some (ghost sp T₁ sc₁ el₁ k D).root ∧ el₁ B} C →
        C ∈ {B | B ∈ T₂ ∧ B.parent = some (ghost sp T₁ sc₁ el₁ k D).root ∧ el₂ B})
    (hQ : P ∈ {B | B ∈ T₂ ∧ B.parent = some Q.root ∧ el₂ B} ∧
      ∀ B ∈ {B | B ∈ T₂ ∧ B.parent = some Q.root ∧ el₂ B}, B = P)
    (hP : ¬ ∃ C, IsBest sp sc₂ {B | B ∈ T₂ ∧ B.parent = some P.root ∧ el₂ B} C) :
    ghost sp T₂ sc₂ el₂ (f + 1) D = P := by
  classical
  induction f generalizing D with
  | zero =>
    simp only [ghost] at h₁
    subst h₁
    have hb : IsBest sp sc₂ {B | B ∈ T₂ ∧ B.parent = some D.root ∧ el₂ B} P :=
      ⟨hQ.1, fun B hB hne => absurd (hQ.2 B hB) hne⟩
    rw [ghost, dite_eq_left_of_eq_true (eq_true ⟨P, hb⟩),
      IsBest.unique (Exists.choose_spec ⟨P, hb⟩) hb]
    rfl
  | succ f ih =>
    by_cases hDQ : D = Q
    · subst hDQ
      have hb : IsBest sp sc₂ {B | B ∈ T₂ ∧ B.parent = some D.root ∧ el₂ B} P :=
        ⟨hQ.1, fun B hB hne => absurd (hQ.2 B hB) hne⟩
      rw [ghost, dite_eq_left_of_eq_true (eq_true ⟨P, hb⟩),
        IsBest.unique (Exists.choose_spec ⟨P, hb⟩) hb]
      exact ghost_fuel_stable (f := 0) (Nat.zero_le _) (by simpa [ghost] using hP)
    · -- walk 1 moves from `D` to its best child `C`
      have hmove : ∃ C, IsBest sp sc₁ {B | B ∈ T₁ ∧ B.parent = some D.root ∧ el₁ B} C := by
        by_contra h
        rw [ghost, dite_eq_right_iff.2 fun h' => absurd h' h] at h₁
        exact hDQ h₁
      obtain ⟨C, hC⟩ := hmove
      have h1C : ghost sp T₁ sc₁ el₁ (f + 1) D = ghost sp T₁ sc₁ el₁ f C := by
        rw [ghost, dite_eq_left_of_eq_true (eq_true ⟨C, hC⟩),
          IsBest.unique (Exists.choose_spec ⟨C, hC⟩) hC]
      obtain ⟨hrefl, hpers⟩ := hstep 0 (Nat.succ_pos f) (by simpa [ghost] using hDQ)
      simp only [ghost] at hrefl hpers
      have hC₂ : IsBest sp sc₂ {B | B ∈ T₂ ∧ B.parent = some D.root ∧ el₂ B} C := by
        refine ⟨hpers C hC, fun B hB hne => ?_⟩
        obtain ⟨hB₁, hBs⟩ := hrefl B hB
        rw [hBs, (hrefl C (hpers C hC)).2]
        exact hC.2 B hB₁ hne
      rw [ghost, dite_eq_left_of_eq_true (eq_true ⟨C, hC₂⟩),
        IsBest.unique (Exists.choose_spec ⟨C, hC₂⟩) hC₂]
      refine ih C (h1C ▸ h₁) fun k hk hne => ?_
      have := hstep (k + 1) (by omega)
      rw [show k + 1 = 1 + k by omega, ghost_add, ghost, dite_eq_left_of_eq_true (eq_true ⟨C, hC⟩),
        IsBest.unique (Exists.choose_spec ⟨C, hC⟩) hC] at this
      simp only [ghost] at this
      exact this hne




/-- One step of a walk that has a best child. -/
theorem ghost_succ_of_best {T : Set (Blk sp.n FGP)} {sc : Blk sp.n FGP → Nat}
    {el : Blk sp.n FGP → Prop} (m : Nat) (a : Blk sp.n FGP) {C : Blk sp.n FGP}
    (hC : IsBest sp sc {B | B ∈ T ∧ B.parent = some (ghost sp T sc el m a).root ∧ el B} C) :
    ghost sp T sc el (m + 1) a = C := by
  rw [ghost_add m 1, ghost, dite_eq_left_of_eq_true (eq_true ⟨C, hC⟩)]
  exact IsBest.unique (Exists.choose_spec _) hC

/-- **A walk with at least as many steps as its tree has blocks has stopped**: its end has no best
child (each step goes to a child of a larger slot in the tree). -/
theorem ghost_stopped {S T : Set (Blk sp.n FGP)} (hS : Coherent S) (hT : T ⊆ S) (hfin : T.Finite)
    {sc : Blk sp.n FGP → Nat} {el : Blk sp.n FGP → Prop} {f : Nat} (hf : T.ncard ≤ f)
    (a : Blk sp.n FGP) :
    ¬ ∃ C, IsBest sp sc {B | B ∈ T ∧ B.parent = some (ghost sp T sc el f a).root ∧ el B} C := by
  rintro ⟨C, hC⟩
  -- every earlier position had a best child too (a stopped walk stays stopped)
  have hall : ∀ m ≤ f, ∃ Cm, IsBest sp sc
      {B | B ∈ T ∧ B.parent = some (ghost sp T sc el m a).root ∧ el B} Cm := by
    intro m hm
    by_contra h
    have := ghost_fuel_stable (T := T) (sc := sc) (el := el) hm (a := a) h
    exact h (this ▸ ⟨C, hC⟩)
  -- the positions `1, …, f + 1` are blocks of `T` with strictly increasing slots
  set g : Nat → Blk sp.n FGP := fun m => ghost sp T sc el (m + 1) a
  have hgT : ∀ m ≤ f, g m ∈ T := by
    intro m hm
    obtain ⟨Cm, hCm⟩ := hall m hm
    simp only [g]
    rw [ghost_succ_of_best m a hCm]
    exact hCm.1.1
  have hgs : ∀ m < f, (g m).slot < (g (m + 1)).slot := by
    intro m hm
    obtain ⟨Cm, hCm⟩ := hall (m + 1) hm
    have h1 : g (m + 1) = Cm := ghost_succ_of_best (m + 1) a hCm
    rw [h1]
    exact hS.2 _ (hT (hgT m hm.le)) _ (hT hCm.1.1) hCm.1.2.1
  have hmono : StrictMonoOn (fun m => (g m).slot) {m | m ≤ f} := by
    intro m hm m' hm' hlt
    induction m', hlt using Nat.le_induction with
    | base => exact hgs m (by simp only [Set.mem_ofPred_eq] at hm'; omega)
    | succ m' hle ih =>
      simp only [Set.mem_ofPred_eq] at hm hm'
      exact (ih (by simp only [Set.mem_ofPred_eq]; omega)).trans (hgs m' (by omega))
  have hinj : Set.InjOn g {m | m ≤ f} := fun m hm m' hm' h => by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := hmono hm hm' hlt; simp only [h] at this; omega
    · have := hmono hm' hm hlt; simp only [h] at this; omega
  have hsub : g '' {m | m ≤ f} ⊆ T := by rintro _ ⟨m, hm, rfl⟩; exact hgT m hm
  have hcard := Set.ncard_le_ncard hsub hfin
  rw [hinj.ncard_image] at hcard
  have : ({m | m ≤ f} : Set Nat).ncard = f + 1 := by
    rw [show ({m | m ≤ f} : Set Nat) = ↑(Finset.range (f + 1)) by ext; simp]
    rw [Set.ncard_coe_finset, Finset.card_range]
  omega




/-- **A walk visits every block between its start and its end** (in a coherent `S ⊇ tree`). -/
theorem ghost_visits {S tree : Set (Blk sp.n FGP)} (hS : Coherent S) (hT : tree ⊆ S)
    {sc : Blk sp.n FGP → Nat} {el : Blk sp.n FGP → Prop} (f : Nat) {a X : Blk sp.n FGP}
    (haX : Anc S a X) (hX : Anc S X (ghost sp tree sc el f a)) :
    ∃ k ≤ f, ghost sp tree sc el k a = X := by
  induction f generalizing a with
  | zero => exact ⟨0, le_rfl, by simp only [ghost] at hX ⊢; exact Anc.antisymm hS haX hX⟩
  | succ f ih =>
    by_cases hXa : X = a
    · exact ⟨0, Nat.zero_le _, hXa.symm⟩
    have ha : a ∈ S := (Anc.mem haX (Ne.symm hXa)).1
    rw [ghost] at hX
    split at hX
    · rename_i hb
      set C := hb.choose
      have hC := hb.choose_spec
      have hCS : C ∈ S := hT hC.1.1
      have hCX : Anc S C X := by
        rcases Anc.total hS hX (anc_ghost hT f hCS) with h | h
        · obtain rfl | ⟨Z, hXZ, hZC⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 h
          · exact Relation.ReflTransGen.refl
          · obtain rfl : Z = a := hS.1 hZC.1 ha (Option.some.inj (hZC.2.2.symm.trans hC.1.2.1))
            exact absurd (Anc.antisymm hS haX hXZ) (Ne.symm hXa)
        · exact h
      obtain ⟨k, hk, hg⟩ := ih hCX hX
      refine ⟨k + 1, by omega, ?_⟩
      rw [ghost, dite_eq_left_of_eq_true (eq_true hb)]
      exact hg
    · exact absurd (Anc.antisymm hS haX hX) (Ne.symm hXa)

end Consensus.Goldilocks.SA

end
