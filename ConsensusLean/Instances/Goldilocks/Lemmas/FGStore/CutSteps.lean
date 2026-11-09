module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.CutBase

public section

/-! # Goldilocks FG store: the steps of G1.10 at the scope of C1.1

The store-local facts behind `cut_scope` (`FGStore/Cut`), shared with its growing-fault sibling
(`Growing/Compose/Cut`): one block of the state transition (`step_fields`), an accepted block's
moves of `Σ.F` and `Σ.J` (`onBlock_FJ`), the tree, `Σ.F` and heights of an honest node along its
cuts (`tree_mono`, `accept_mem`, `F_mono`, `h_mono`), the entries of a chain (`J_entry`,
`entry_between`), and (a), (b) at an accepted block given the core at the excluded entries
(`scope_block_of`). -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type}

/-- One accepted block keeps the height and the entry, or enters the next height by itself; it
keeps the justification, or justifies the parent's entry at the parent's height. -/
theorem step_fields {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n}
    {B : FG.FGBlock gp.n} (h : gp.stateTransition σ B = some σ') :
    ((σ'.h = σ.h ∧ σ'.Th = σ.Th) ∨ (σ'.h = σ.h + 1 ∧ σ'.Th = B.root)) ∧
      ((σ'.J = σ.J ∧ σ'.hj = σ.hj) ∨ (σ'.J = σ.Th ∧ σ'.hj = σ.h)) := by
  obtain ⟨-, rfl⟩ := gp.stateTransition_eq_some.1 h
  obtain ⟨f, p, t, he⟩ := FG.ChainState.foldl_processAtt_eq { σ with s := B.slot } B.atts
  rw [he]
  dsimp only
  obtain ⟨F, hF, σ₁, rfl, -, hcase⟩ := gp.heightEvents_cases
    { σ with s := B.slot, L := B.root, fin := f, prog := p, target := t }
  rcases hcase with ⟨-, he'⟩ | ⟨-, -, he'⟩ | ⟨-, -, he'⟩ <;> rw [he']
  · exact ⟨Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩
  · exact ⟨Or.inr ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩

/-- A block below one that is compatible with `B` is compatible with `B`. -/
theorem compatible_of_anc {n : Nat} {FGP ACP : Type} {S : Set (Block n FGP ACP)}
    (hS : Coherent S) {A B C : Block n FGP ACP} (hAC : Goldilocks.Anc S A C)
    (hC : Compatible S C B) : Compatible S A B := by
  rcases hC with hCB | hBC
  · exact Or.inl (hAC.trans hCB)
  · exact Anc.total hS hAC hBC

/-- An accepted block keeps `Σ.J` or moves it to the block of its state's justification; it
keeps `Σ.F` or moves it below the new `Σ.J`. -/
theorem onBlock_FJ {st st' : Store P ACP} {X : NodeBlock P ACP}
    (h : st.onBlock X = some st') :
    (st'.J = st.J ∨ st'.blocks (st'.σ X.root).J = some st'.J) ∧
      (st'.F = st.F ∨ st'.Anc st'.F st'.J) := by
  obtain ⟨pr, σ', -, -, -, -, -, rfl⟩ := onBlock_eq_some h
  set st₁ : Store P ACP :=
    { st with blocks := Function.update st.blocks X.root (some X),
              σ := Function.update st.σ X.root σ' }
  obtain ⟨atts, he⟩ := addAtts_eq (updateFinality st₁ σ') X.fgPayload
  obtain ⟨hb, hσ, -, -, hJ, hF⟩ := updateFinality_spec st₁ σ'
  have ht : ({ updateFinality st₁ σ' with atts := atts } : Store P ACP).tree = st₁.tree := by
    simp only [tree, hb]
  have h₁ : st₁.σ X.root = σ' := Function.update_self ..
  rw [he, Store.Anc, ht]
  simp only [hb, hσ, h₁]
  exact ⟨hJ.imp (·.1) (·.1), hF.imp id (·.2.2.2)⟩

section Run

variable {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}

/-! ## The tree of an honest node -/

/-- The tree of an honest node only grows. -/
theorem tree_mono (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H)
    {k m : Nat} (hkm : k ≤ m) : (tr.store y k).tree ⊆ (tr.store y m).tree :=
  fun Z (hZ : (tr.store y k).blocks Z.root = some Z) => (held_mono hr hy hkm hZ).1

/-- An accepted block is in the tree after its cut. -/
theorem accept_mem (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H)
    {i : Nat} {X : NodeBlock P ACP} (hX : tr.AcceptAt y i X) :
    X ∈ (tr.store y (i + 1)).tree := by
  obtain ⟨-, -, -, -, -, -, hb, -⟩ := onBlock_fields (accept_onBlock hr hy hX)
  change (tr.store y (i + 1)).blocks X.root = some X
  rw [hb, Function.update_self]

/-- The finalized tip of an honest node moves only to descendants. -/
theorem F_mono (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {k m : Nat}
    (hkm : k ≤ m) : (tr.store y m).Anc (tr.store y k).F (tr.store y m).F := by
  induction m, hkm using Nat.le_induction with
  | base => exact .refl
  | succ m _ ih =>
    rcases store_step hr hy m with he | ⟨X, -, hX⟩ | ⟨a, -, he⟩
    · rw [he]
      exact ih
    · exact (ih.mono (tree_mono hr hy m.le_succ)).trans
        ((finalized_monotone P ACP acp₀ _ (store_reachable hr hy m)).1 X _ hX)
    · obtain ⟨atts, he'⟩ := (tr.store y m).onAttestation_eq a
      rw [he, he']
      exact ih

/-- Along ancestry the height does not decrease. -/
theorem h_mono (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {A W : NodeBlock P ACP} (h : (tr.store y i).Anc A W) :
    ((tr.store y i).σ A.root).h ≤ ((tr.store y i).σ W.root).h := by
  induction h with
  | refl => exact le_rfl
  | tail _ hYW ih =>
    rcases (step_fields (step_σ hr hy hYW.2.1 hYW.2.2)).1 with ⟨hh, -⟩ | ⟨hh, -⟩ <;> omega

/-- The justification of a held block's state names a held ancestor: genesis, or the entry of
the justified height. -/
theorem J_entry (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {W : NodeBlock P ACP} (hW : W ∈ (tr.store y i).tree) :
    ∃ E ∈ (tr.store y i).tree, E.root = ((tr.store y i).σ W.root).J ∧
      (tr.store y i).Anc E W ∧ (E = P.genesisBlock acp₀ ∨
        (((tr.store y i).σ E.root).h = ((tr.store y i).σ W.root).hj ∧
          ((tr.store y i).σ E.root).Th = E.root)) := by
  have hreach := store_reachable hr hy i
  have hg := (accepted_tree P ACP acp₀ _ hreach).2.2.1
  have hA := (accepted_tree P ACP acp₀ _ hreach).2.2.2 W hW
  clear hW
  induction hA with
  | refl =>
    rw [show (P.genesisBlock acp₀).root = P.genesisRoot from rfl, σ_genesis hr hy]
    exact ⟨_, hg, rfl, .refl, Or.inl rfl⟩
  | tail _ hYW ih =>
    rcases (step_fields (step_σ hr hy hYW.2.1 hYW.2.2)).2 with ⟨hJ, hj⟩ | ⟨hJ, hj⟩
    · obtain ⟨E, hE, h1, hEY, h2⟩ := ih
      refine ⟨E, hE, h1.trans hJ.symm, hEY.tail hYW, ?_⟩
      rw [hj]
      exact h2
    · obtain ⟨E, hE, h1, hEY, h2, h3⟩ := (entry_state_of_source P ACP acp₀ _ hreach _ hYW.1).1
      exact ⟨E, hE, h1.trans hJ.symm, hEY.tail hYW, Or.inr ⟨h2.trans hj.symm, h3.trans h1.symm⟩⟩

/-- Every height between those of `A` and `X ⪰ A` is entered strictly above `A`, at or
below `X`. -/
theorem entry_between (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H)
    {i : Nat} {A X : NodeBlock P ACP} (hAX : (tr.store y i).Anc A X) {k : Nat}
    (h1 : ((tr.store y i).σ A.root).h < k) (h2 : k ≤ ((tr.store y i).σ X.root).h) :
    ∃ W, (tr.store y i).Anc A W ∧ A ≠ W ∧ (tr.store y i).Anc W X ∧
      ((tr.store y i).σ W.root).h = k ∧ ((tr.store y i).σ W.root).Th = W.root := by
  induction hAX with
  | refl => omega
  | @tail Y X hAY hYX ih =>
    rcases (step_fields (step_σ hr hy hYX.2.1 hYX.2.2)).1 with ⟨hh, -⟩ | ⟨hh, hTh⟩
    · obtain ⟨W, h3, h4, h5, h6⟩ := ih (by omega)
      exact ⟨W, h3, h4, h5.tail hYX, h6⟩
    · by_cases hle : k ≤ ((tr.store y i).σ Y.root).h
      · obtain ⟨W, h3, h4, h5, h6⟩ := ih hle
        exact ⟨W, h3, h4, h5.tail hYX, h6⟩
      · have := h_mono hr hy hAY
        refine ⟨X, hAY.tail hYX, fun he => ?_, .refl, by omega, hTh⟩
        subst he
        omega

/-! ## The scope of C1.1 -/

/-- **(a) and (b) at a block accepted from the first cut at `Ts` on**, given the core at the
excluded entries (`quorum_free_entries`, or a growing-fault form of it): an entry that conflicts
with `B` on the accepted block's chain strictly extends `y`'s `Σ.F` at `Ts`, so it is excluded,
and the core keeps it unjustified there. -/
theorem scope_block_of (hr : FGLocalRun acp₀ H U tr) {B : NodeBlock P ACP}
    {Ts : Time} {y : Fin P.n} (hy : y ∈ H) {j₀ : Nat} (hj₀ : Ts ≤ tr.time j₀)
    (hmin : ∀ k < j₀, tr.time k < Ts) (hK : Compatible U (tr.store y j₀).F B) {i : Nat}
    {X : NodeBlock P ACP} (hji : j₀ ≤ i) (hX : tr.AcceptAt y i X)
    (core : ∀ E ∈ Store.excludedEntries H U tr Ts B, ∀ h,
      ∀ A ∈ (tr.store y (i + 1)).tree, (tr.store y (i + 1)).Anc A X →
      ((tr.store y (i + 1)).σ A.root).h = h → ((tr.store y (i + 1)).σ A.root).Th = E.root →
      ((tr.store y (i + 1)).σ X.root).h = h ∧ ((tr.store y (i + 1)).σ X.root).Th = E.root ∧
        ((tr.store y (i + 1)).σ X.root).prog.card < P.fg.q) :
    (∀ A' ∈ (tr.store y (i + 1)).tree, (tr.store y (i + 1)).Anc A' X → ∀ Jb,
      (tr.store y (i + 1)).blocks ((tr.store y (i + 1)).σ A'.root).J = some Jb →
        Compatible U Jb B) ∧
    (¬ Compatible U X B → ∀ Pc, Goldilocks.Anc U Pc X → Goldilocks.Anc U Pc B →
      (∀ Q, Goldilocks.Anc U Q X → Goldilocks.Anc U Q B → Goldilocks.Anc U Q Pc) →
      ((tr.store y (i + 1)).σ X.root).h ≤ ((tr.store y (i + 1)).σ Pc.root).h + 1) := by
  have hsub := hr.tree_subset y hy (i + 1)
  have hcoh : Coherent (tr.store y (i + 1)).tree := hr.coherent.mono hsub
  have excluded {E} (hEX : (tr.store y (i + 1)).Anc E X) (hc : ¬ Compatible U E B) :
      E ∈ Store.excludedEntries H U tr Ts B ∧
      (tr.store y (i + 1)).Anc (tr.store y j₀).F E ∧ E ≠ (tr.store y j₀).F := by
    have hacc := accept_onBlock hr hy hX
    obtain ⟨-, -, -, -, -, hFX, -, -⟩ := onBlock_eq_some hacc
    rw [← (tree_grows P ACP acp₀ _ (store_reachable hr hy i)).1 X _ hacc] at hFX
    have hF₀X : (tr.store y (i + 1)).Anc (tr.store y j₀).F X :=
      ((F_mono hr hy hji).mono (tree_mono hr hy i.le_succ)).trans hFX
    have hne : E ≠ (tr.store y j₀).F := fun he => hc (he ▸ hK)
    rcases Anc.total hcoh hF₀X hEX with h | h
    · exact ⟨Store.mem_excludedEntries.mpr ⟨hc, y, hy, j₀, hj₀, hmin, h.mono hsub, hne⟩, h, hne⟩
    · exact absurd (compatible_of_anc hr.coherent (h.mono hsub) hK) hc
  refine ⟨fun A' hA' hA'X Jb hJb => ?_, fun hXB Pc hPX hPB hdeep => ?_⟩
  · by_contra hc
    obtain ⟨E, hE, hEr, hEA', hcase⟩ := J_entry hr hy hA'
    have hJE : Jb = E := by
      rw [← hEr] at hJb
      exact Option.some.inj (hJb.symm.trans hE)
    rw [hJE] at hc
    obtain ⟨hex, hF₀E, hne⟩ := excluded (hEA'.trans hA'X) hc
    rcases hcase with rfl | ⟨hh, hTh⟩
    · have hF₀ : (tr.store y j₀).F ∈ (tr.store y (i + 1)).tree := tree_mono hr hy (by omega)
        (cache_invariants P ACP acp₀ _ (store_reachable hr hy j₀)).1
      exact hne (Anc.antisymm hcoh hF₀E
        ((accepted_tree P ACP acp₀ _ (store_reachable hr hy (i + 1))).2.2.2 _ hF₀)).symm
    · have := (core E hex _ E hE (hEA'.trans hA'X) hh hTh).1
      have := h_mono hr hy hA'X
      have := (one_le_h hr hy hA').2
      omega
  · have hPXs := anc_of_U hr hy hPX (accept_mem hr hy hX)
    by_contra hlt
    obtain ⟨W, hPW, hne, hWX, hWh, hWTh⟩ := entry_between hr hy hPXs
      (k := ((tr.store y (i + 1)).σ Pc.root).h + 1) (by omega) (by omega)
    have hc : ¬ Compatible U W B := by
      rintro (hWB | hBW)
      · exact hne (Anc.antisymm hr.coherent (hPW.mono hsub) (hdeep W (hWX.mono hsub) hWB))
      · exact hXB (Or.inr (hBW.trans (hWX.mono hsub)))
    have := (core W (excluded hWX hc).1 _ W (Anc.mem hPW hne).2 hWX hWh hWTh).1
    omega

end Run

end Consensus.Goldilocks.Store

end
