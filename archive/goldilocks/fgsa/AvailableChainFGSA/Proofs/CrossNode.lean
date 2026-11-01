module
public import AvailableChainFGSA.Proofs.Metadata
public import AvailableChainFGSA.Proofs.NamedStore

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-! ROOT-DIGEST W1; DC NamedRootCollisionFree. The cross-store carrier uses
scoped root equality for content agreement. Erasure is structurally injective. -/

/-- [ROOT-DIGEST-2 W1; DC NamedRootCollisionFree] Full agreement is symmetric. -/
theorem contentAgree_symm {n : Nat} {st st' : State n} (hc : ContentAgree st st') :
    ContentAgree st' st := by
  intro s N ho s' N' ho' hr
  have he := (hc s' N' ho' s N ho hr.symm).1
  subst N'
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- [ROOT-DIGEST-2 W1; DC NamedStore.bodies] Local agreement needs no run premise. -/
theorem contentAgree_self (p : Params) (st : State p.n) (h : CStoreInv p st)
    (m : MetaInv p st) : ContentAgree st st := by
  intro s N ho s' N' ho' hr
  have he := namedBodies_root_injective p st h m
    ((mem_namedBodies st N).mpr (Or.inr ⟨s, ho⟩))
    ((mem_namedBodies st N').mpr (Or.inr ⟨s', ho'⟩)) hr
  subst N'
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- [ROOT-DIGEST-2 W1; DC NamedRootCollisionFree; S2] Named cross-store identity
supplies full content agreement. Stored named bodies are covered by the run premise. -/
theorem contentAgree (p : Params) {st st' : State p.n}
    (_m : MetaInv p st) (_m' : MetaInv p st')
    (hroot : ∀ X ∈ st.namedBodies, ∀ Y ∈ st'.namedBodies, X.root = Y.root → X = Y) :
    ContentAgree st st' := by
  intro s N ho s' N' ho' hr
  have he := hroot N ((mem_namedBodies st N).mpr (Or.inr ⟨s, ho⟩))
    N' ((mem_namedBodies st' N').mpr (Or.inr ⟨s', ho'⟩)) hr
  subst N'
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
[helper] The erased ancestor of a stored FG block has a stored FG ancestor,
with the same erasure. -/
theorem eraseFG_ancestor_preceq {n : Nat} {T : Finset (FGBlock (Fin n))}
    (hcl : ∀ B ∈ T, B.parent ∈ T) {B : FGBlock (Fin n)} (hB : B ∈ T) {c : Block}
    (hc : Block.Preceq c (eraseFG B)) : ∃ C ∈ T, eraseFG C = c ∧ FGBlock.Preceq C B := by
  induction B with
  | genesis =>
      simp only [eraseFG, Block.Preceq, Block.preceq, decide_eq_true_eq] at hc
      exact ⟨.genesis, hB, hc.symm, KitFG.preceq_refl _⟩
  | node P s r_s r rows ih =>
      simp only [eraseFG, Block.Preceq, Block.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hc
      rcases hc with hc | hc
      · exact ⟨.node P s r_s r rows, hB, hc.symm, KitFG.preceq_refl _⟩
      · obtain ⟨C, hC, hCe, hCP⟩ := ih (hcl _ hB) hc
        exact ⟨C, hC, hCe, KitFG.preceq_node_of_preceq s r_s r rows hCP⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
[ROOT-DIGEST W2; bp.carrier.v1; K5 cross-node] Cross-store
reconstruction: stored FG blocks at two stores with the same erasure are equal. -/
theorem stored_fg_eq_of_erase_eq (p : Params) (st st' : State p.n)
    (_h : CStoreInv p st) (_h' : CStoreInv p st') (_m : MetaInv p st) (_m' : MetaInv p st')
    {X Y : FGBlock (Fin p.n)} (_hX : X ∈ st.fg.TF) (_hY : Y ∈ st'.fg.TF)
    (he : eraseFG X = eraseFG Y) : X = Y :=
  eraseFG_injective he

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Compatibility wrapper for `stored_fg_eq_of_erase_eq`.
Delete after F2 (GLY E-13). -/
theorem fg_eq_of_eraseFG_eq_across (p : Params) (st st' : State p.n)
    (h : CStoreInv p st) (h' : CStoreInv p st') (m : MetaInv p st) (m' : MetaInv p st')
    (hc : ContentAgree st st') {X Y : FGBlock (Fin p.n)} (hX : X ∈ st.fg.TF) (hY : Y ∈ st'.fg.TF)
    (he : eraseFG X = eraseFG Y) : X = Y :=
  stored_fg_eq_of_erase_eq p st st' h h' m m' hX hY he

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
[helper] Stored FG blocks at two stores with equal roots are equal. -/
theorem fg_eq_of_root_eq_across (p : Params) (st st' : State p.n)
    (h : CStoreInv p st) (h' : CStoreInv p st') (m : MetaInv p st) (m' : MetaInv p st')
    (hc : ContentAgree st st') {X Y : FGBlock (Fin p.n)} (hX : X ∈ st.fg.TF) (hY : Y ∈ st'.fg.TF)
    (hr : X.root = Y.root) : X = Y := by
  by_cases hXg : X = .genesis
  · subst hXg
    exact (h'.rootInj _ h'.fg.gen _ hY hr).symm ▸ rfl
  by_cases hYg : Y = .genesis
  · subst hYg
    exact h.rootInj _ hX _ h.fg.gen hr
  obtain ⟨s, N, ho, he, -⟩ := stored_wire_of_block p st h m hX hXg
  obtain ⟨s', N', ho', he', -⟩ := stored_wire_of_block p st' h' m' hY hYg
  have hpay := hc s N ho s' N' ho' (by
    rw [← named_erase_root, ← named_erase_root, he, he', eraseFG_root, eraseFG_root, hr])
  exact eraseFG_injective (he.symm.trans (hpay.2.1.trans he'))

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
[bp bp.carrier.v1; K5 cross-node] Erasure preserves and reflects ancestry
across two stores. -/
theorem stored_fg_preceq_iff_erase (p : Params) (st st' : State p.n)
    (h : CStoreInv p st) (h' : CStoreInv p st') (m : MetaInv p st) (m' : MetaInv p st')
    {X Y : FGBlock (Fin p.n)} (hX : X ∈ st.fg.TF) (hY : Y ∈ st'.fg.TF) :
    FGBlock.Preceq X Y ↔ Block.Preceq (eraseFG X) (eraseFG Y) := by
  refine ⟨eraseFG_preceq, fun hp => ?_⟩
  obtain ⟨C, hC, hCe, hCY⟩ := eraseFG_ancestor_preceq h'.fg.closed hY hp
  rw [stored_fg_eq_of_erase_eq p st st' h h' m m' hX hC hCe.symm]
  exact hCY

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Compatibility wrapper for `stored_fg_preceq_iff_erase`.
Delete after F2 (GLY E-13). -/
theorem preceq_iff_across (p : Params) (st st' : State p.n)
    (h : CStoreInv p st) (h' : CStoreInv p st') (m : MetaInv p st) (m' : MetaInv p st')
    (hc : ContentAgree st st') {X Y : FGBlock (Fin p.n)} (hX : X ∈ st.fg.TF) (hY : Y ∈ st'.fg.TF) :
    FGBlock.Preceq X Y ↔ Block.Preceq (eraseFG X) (eraseFG Y) :=
  stored_fg_preceq_iff_erase p st st' h h' m m' hX hY

theorem stored_fg_compatible_eq_erase (p : Params) (st st' : State p.n)
    (h : CStoreInv p st) (h' : CStoreInv p st') (m : MetaInv p st) (m' : MetaInv p st')
    {X Y : FGBlock (Fin p.n)} (hX : X ∈ st.fg.TF) (hY : Y ∈ st'.fg.TF) :
    FGBlock.compatible X Y = Block.compatible (eraseFG X) (eraseFG Y) := by
  have h1 := stored_fg_preceq_iff_erase p st st' h h' m m' hX hY
  have h2 := stored_fg_preceq_iff_erase p st' st h' h m' m hY hX
  unfold FGBlock.Preceq at h1 h2
  unfold Block.Preceq at h1 h2
  unfold FGBlock.compatible Block.compatible
  rw [Bool.eq_iff_iff.2 h1, Bool.eq_iff_iff.2 h2]

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Compatibility wrapper for `stored_fg_compatible_eq_erase`.
Delete after F2 (GLY E-13). -/
theorem compatible_iff_across (p : Params) (st st' : State p.n)
    (h : CStoreInv p st) (h' : CStoreInv p st') (m : MetaInv p st) (m' : MetaInv p st')
    (hc : ContentAgree st st') {X Y : FGBlock (Fin p.n)} (hX : X ∈ st.fg.TF) (hY : Y ∈ st'.fg.TF) :
    FGBlock.compatible X Y = Block.compatible (eraseFG X) (eraseFG Y) :=
  stored_fg_compatible_eq_erase p st st' h h' m m' hX hY

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
[bp bp.carrier.v1; K5 cross-node; r188 N4] The `KitFG.accountable` premise
for two chains at two stores (bp01 §2.2 step 6). -/
theorem stored_fg_roots_injective (p : Params) (st st' : State p.n)
    (h : CStoreInv p st) (h' : CStoreInv p st') (m : MetaInv p st) (m' : MetaInv p st') (hc :
      ContentAgree st st')
    {B₁ B₂ : FGBlock (Fin p.n)} (h₁ : B₁ ∈ st.fg.TF)
    (h₂ : B₂ ∈ st'.fg.TF) : KitFG.RootInjectiveOn B₁ B₂ := by
  have mem := KitFG.ancestor_closed_of_parent_closed _ h.fg.closed B₁ h₁
  have mem' := KitFG.ancestor_closed_of_parent_closed _ h'.fg.closed B₂ h₂
  intro X Y hX hY hr
  rcases hX with hX | hX <;> rcases hY with hY | hY
  · exact h.rootInj _ (mem _ hX) _ (mem _ hY) hr
  · exact fg_eq_of_root_eq_across p st st' h h' m m' hc (mem _ hX) (mem' _ hY) hr
  · exact (fg_eq_of_root_eq_across p st st' h h' m m' hc (mem _ hY) (mem' _ hX) hr.symm).symm
  · exact h'.rootInj _ (mem' _ hX) _ (mem' _ hY) hr

set_option linter.unusedVariables false in
/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Compatibility wrapper for `stored_fg_roots_injective`.
Delete after F2 (GLY E-13). -/
theorem rootInjectiveOn_across (p : Params) (st st' : State p.n)
    (h : CStoreInv p st) (h' : CStoreInv p st') (m : MetaInv p st) (m' : MetaInv p st')
    (hc : ContentAgree st st') {B₁ B₂ : FGBlock (Fin p.n)} (h₁ : B₁ ∈ st.fg.TF)
    (h₂ : B₂ ∈ st'.fg.TF) : KitFG.RootInjectiveOn B₁ B₂ :=
  stored_fg_roots_injective p st st' h h' m m' hc h₁ h₂

end AvailableChain.FGSA
end
