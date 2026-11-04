module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Order
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Entries

public section

/-! # Goldilocks FG store: G1.10 at the scope of C1.1

The excluded entries of C1.1's scope are the blocks that conflict with `B` and strictly extend
the `Σ.F` of some honest node at `Ts` (`excludedEntries`). Under (K0) (at `Ts` the `Σ.F` and
`Σ.J` of every honest node are compatible with `B`), every entry that conflicts with `B` on the
chain of a block that an honest `y` accepts from `Ts` on strictly extends `y`'s `Σ.F` at `Ts`,
so it is excluded, and the core (`quorum_free_entries`) keeps it unjustified there: (a) no
justification on such a chain conflicts with `B`; (b) a block that conflicts with `B` is at most
one height above its deepest common ancestor with `B`; (c) `y`'s `Σ.F` and `Σ.J`, which move
only when a block is accepted (to its justification and below), stay compatible with `B`
(`cut_scope`; claims G1.10, "The scope of C1.1"). -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type}

/-- The excluded entries of C1.1's scope: conflicting with `B`, strictly above an honest `Σ.F`
at `Ts` (the state before the first cut of the run at a time `≥ Ts`). -/
def excludedEntries (H : Set (Fin P.n)) (U : Set (NodeBlock P ACP)) (tr : FGTrace P ACP)
    (Ts : Time) (B : NodeBlock P ACP) : Set (NodeBlock P ACP) :=
  {E | ¬ Compatible U E B ∧ ∃ z ∈ H, ∃ j, Ts ≤ tr.time j ∧ (∀ k < j, tr.time k < Ts) ∧
    Goldilocks.Anc U (tr.store z j).F E ∧ E ≠ (tr.store z j).F}

/-- Membership in `excludedEntries`. -/
theorem mem_excludedEntries {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)} {tr : FGTrace P ACP}
    {Ts : Time} {B E : NodeBlock P ACP} : E ∈ excludedEntries H U tr Ts B ↔
      ¬ Compatible U E B ∧ ∃ z ∈ H, ∃ j, Ts ≤ tr.time j ∧ (∀ k < j, tr.time k < Ts) ∧
        Goldilocks.Anc U (tr.store z j).F E ∧ E ≠ (tr.store z j).F := Iff.rfl

/-! ## One block of the state transition -/

/-- One accepted block keeps the height and the entry, or enters the next height by itself; it
keeps the justification, or justifies the parent's entry at the parent's height. -/
private theorem step_fields {gp : FG.FGParams} {σ σ' : FG.ChainState gp.n}
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
private theorem compatible_of_anc {n : Nat} {FGP ACP : Type} {S : Set (Block n FGP ACP)}
    (hS : Coherent S) {A B C : Block n FGP ACP} (hAC : Goldilocks.Anc S A C)
    (hC : Compatible S C B) : Compatible S A B := by
  rcases hC with hCB | hBC
  · exact Or.inl (hAC.trans hCB)
  · exact Anc.total hS hAC hBC

/-- An accepted block keeps `Σ.J` or moves it to the block of its state's justification; it
keeps `Σ.F` or moves it below the new `Σ.J`. -/
private theorem onBlock_FJ {st st' : Store P ACP} {X : NodeBlock P ACP}
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
private theorem tree_mono (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H)
    {k m : Nat} (hkm : k ≤ m) : (tr.store y k).tree ⊆ (tr.store y m).tree :=
  fun Z (hZ : (tr.store y k).blocks Z.root = some Z) => (held_mono hr hy hkm hZ).1

/-- An accepted block is in the tree after its cut. -/
private theorem accept_mem (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H)
    {i : Nat} {X : NodeBlock P ACP} (hX : tr.AcceptAt y i X) :
    X ∈ (tr.store y (i + 1)).tree := by
  obtain ⟨-, -, -, -, -, -, hb, -⟩ := onBlock_fields (accept_onBlock hr hy hX)
  change (tr.store y (i + 1)).blocks X.root = some X
  rw [hb, Function.update_self]

/-- The finalized tip of an honest node moves only to descendants. -/
private theorem F_mono (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {k m : Nat}
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

/-- The state of a held block has height at least `1`, above its justification. -/
theorem one_le_h (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {B : NodeBlock P ACP} (hB : B ∈ (tr.store y i).tree) :
    1 ≤ ((tr.store y i).σ B.root).h ∧
      ((tr.store y i).σ B.root).hj < ((tr.store y i).σ B.root).h := by
  obtain ⟨c, -, -, -, hc⟩ := chain_state_of_chain P ACP acp₀ _ (store_reachable hr hy i) B hB
  obtain ⟨h1, -, h2, -⟩ := FG.chain_invariants P.fg _ _ hc
  exact ⟨h1, h2⟩

/-- A held block that names a parent has its parent held. -/
theorem parent_held (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {B : NodeBlock P ACP} (hB : B ∈ (tr.store y i).tree) {r : Nat} (hp : B.parent = some r) :
    ∃ Y, ParentIn (tr.store y i).tree Y B := by
  rcases ((accepted_tree P ACP acp₀ _ (store_reachable hr hy i)).2.2.2 B hB).cases_tail with
    rfl | ⟨Y, -, hY⟩
  · exact absurd hp (by simp [Params.genesisBlock])
  · exact ⟨Y, hY⟩

/-- `U`-ancestry below a held block is ancestry in the tree. -/
theorem anc_of_U (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {A C : NodeBlock P ACP} (h : Goldilocks.Anc U A C) (hC : C ∈ (tr.store y i).tree) :
    (tr.store y i).Anc A C := by
  induction h with
  | refl => exact .refl
  | tail _ hYC ih =>
    obtain ⟨Z, hZ⟩ := parent_held hr hy hC hYC.2.2
    obtain rfl : Z = _ := hr.coherent.1 (hr.tree_subset y hy i hZ.1) hYC.1
      (Option.some.inj (hZ.2.2.symm.trans hYC.2.2))
    exact (ih hZ.1).tail hZ

/-- Along ancestry the height does not decrease. -/
private theorem h_mono (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {A W : NodeBlock P ACP} (h : (tr.store y i).Anc A W) :
    ((tr.store y i).σ A.root).h ≤ ((tr.store y i).σ W.root).h := by
  induction h with
  | refl => exact le_rfl
  | tail _ hYW ih =>
    rcases (step_fields (step_σ hr hy hYW.2.1 hYW.2.2)).1 with ⟨hh, -⟩ | ⟨hh, -⟩ <;> omega

/-- The justification of a held block's state names a held ancestor: genesis, or the entry of
the justified height. -/
private theorem J_entry (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H) {i : Nat}
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
private theorem entry_between (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H)
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

/-- An entry that conflicts with `B` on the chain of a block accepted from the first cut at
`Ts` on strictly extends `y`'s `Σ.F` there, so it is excluded. -/
private theorem excluded_of_accept (hr : FGLocalRun acp₀ H U tr) {y : Fin P.n} (hy : y ∈ H)
    {B : NodeBlock P ACP} {Ts : Time} {j₀ : Nat} (hj₀ : Ts ≤ tr.time j₀)
    (hmin : ∀ k < j₀, tr.time k < Ts) (hK : Compatible U (tr.store y j₀).F B) {i : Nat}
    (hji : j₀ ≤ i) {X : NodeBlock P ACP} (hX : tr.AcceptAt y i X) {E : NodeBlock P ACP}
    (hEX : (tr.store y (i + 1)).Anc E X) (hc : ¬ Compatible U E B) :
    E ∈ excludedEntries H U tr Ts B ∧ (tr.store y (i + 1)).Anc (tr.store y j₀).F E ∧
      E ≠ (tr.store y j₀).F := by
  have hsub := hr.tree_subset y hy (i + 1)
  have hcoh : Coherent (tr.store y (i + 1)).tree := hr.coherent.mono hsub
  have hacc := accept_onBlock hr hy hX
  obtain ⟨-, -, -, -, -, hFX, -, -⟩ := onBlock_eq_some hacc
  rw [← (tree_grows P ACP acp₀ _ (store_reachable hr hy i)).1 X _ hacc] at hFX
  have hF₀X : (tr.store y (i + 1)).Anc (tr.store y j₀).F X :=
    ((F_mono hr hy hji).mono (tree_mono hr hy i.le_succ)).trans hFX
  have hne : E ≠ (tr.store y j₀).F := fun he => hc (he ▸ hK)
  rcases Anc.total hcoh hF₀X hEX with h | h
  · exact ⟨⟨hc, y, hy, j₀, hj₀, hmin, h.mono hsub, hne⟩, h, hne⟩
  · exact absurd (compatible_of_anc hr.coherent (h.mono hsub) hK) hc

/-- (a) and (b) at a block accepted from the first cut at `Ts` on, in the scope of the core. -/
private theorem scope_block (hr : FGLocalRun acp₀ H U tr) {B : NodeBlock P ACP}
    {Ts T₀ T : Time} (hT₀ : P.IsPublic T₀) (hT : P.IsPublic T)
    (hK1 : ∀ E ∈ excludedEntries H U tr Ts B, (namers P ACP H tr T₀ E).ncard < P.fg.q)
    (hrows : ∀ v ∈ H, ∀ j a, tr.SignAt v j a → T₀ < tr.time j → tr.time j ≤ T →
      ∀ E ∈ excludedEntries H U tr Ts B, a.T ≠ E.root)
    {y : Fin P.n} (hy : y ∈ H) {j₀ : Nat} (hj₀ : Ts ≤ tr.time j₀)
    (hmin : ∀ k < j₀, tr.time k < Ts) (hK : Compatible U (tr.store y j₀).F B) {i : Nat}
    {X : NodeBlock P ACP} (hji : j₀ ≤ i) (hX : tr.AcceptAt y i X)
    (htime : tr.time i < T + P.Δ ∨
      (tr.time i = T + P.Δ ∧ X.proposer = y ∧ P.slotTime X.slot = T + P.Δ)) :
    (∀ A' ∈ (tr.store y (i + 1)).tree, (tr.store y (i + 1)).Anc A' X → ∀ Jb,
      (tr.store y (i + 1)).blocks ((tr.store y (i + 1)).σ A'.root).J = some Jb →
        Compatible U Jb B) ∧
    (¬ Compatible U X B → ∀ Pc, Goldilocks.Anc U Pc X → Goldilocks.Anc U Pc B →
      (∀ Q, Goldilocks.Anc U Q X → Goldilocks.Anc U Q B → Goldilocks.Anc U Q Pc) →
      ((tr.store y (i + 1)).σ X.root).h ≤ ((tr.store y (i + 1)).σ Pc.root).h + 1) := by
  have core := quorum_free_entries P ACP acp₀ H U tr (excludedEntries H U tr Ts B) T₀ T y hr
    hT₀ hT hy hK1 hrows i X hX htime
  have hsub := hr.tree_subset y hy (i + 1)
  have hcoh : Coherent (tr.store y (i + 1)).tree := hr.coherent.mono hsub
  refine ⟨fun A' hA' hA'X Jb hJb => ?_, fun hXB Pc hPX hPB hdeep => ?_⟩
  · by_contra hc
    obtain ⟨E, hE, hEr, hEA', hcase⟩ := J_entry hr hy hA'
    have hJE : Jb = E := by
      rw [← hEr] at hJb
      exact Option.some.inj (hJb.symm.trans hE)
    rw [hJE] at hc
    obtain ⟨hex, hF₀E, hne⟩ := excluded_of_accept hr hy hj₀ hmin hK hji hX (hEA'.trans hA'X) hc
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
    have := (core W (excluded_of_accept hr hy hj₀ hmin hK hji hX hWX hc).1 _ W
      (Anc.mem hPW hne).2 hWX hWh hWTh).1
    omega

end Run

/-- **G1.10 at the scope of C1.1.** (a), (b) at every block that the honest `y` accepts in
`[Ts, T + Δ)`, or its own proposal at `T + Δ`; (c) `y`'s `Σ.F` and `Σ.J` after every cut in
`[Ts, T + Δ]` up to which `y` accepted only such blocks. -/
theorem cut_scope {acp₀ : ACP} {H : Set (Fin P.n)} {U : Set (NodeBlock P ACP)}
    {tr : FGTrace P ACP} (hr : FGLocalRun acp₀ H U tr) {B : NodeBlock P ACP} {Ts T₀ T : Time}
    (hT₀ : P.IsPublic T₀) (hT : P.IsPublic T)
    (hK0 : ∀ z ∈ H, ∀ j, Ts ≤ tr.time j → (∀ k < j, tr.time k < Ts) →
      Compatible U (tr.store z j).F B ∧ Compatible U (tr.store z j).J B)
    (hK1 : ∀ E ∈ excludedEntries H U tr Ts B, (namers P ACP H tr T₀ E).ncard < P.fg.q)
    (hrows : ∀ v ∈ H, ∀ j a, tr.SignAt v j a → T₀ < tr.time j → tr.time j ≤ T →
      ∀ E ∈ excludedEntries H U tr Ts B, a.T ≠ E.root)
    {y : Fin P.n} (hy : y ∈ H) :
    (∀ i X, tr.AcceptAt y i X → Ts ≤ tr.time i →
      (tr.time i < T + P.Δ ∨ (tr.time i = T + P.Δ ∧ X.proposer = y ∧ P.slotTime X.slot = T + P.Δ)) →
      let S := tr.store y (i + 1)
      (∀ A' ∈ S.tree, S.Anc A' X → ∀ Jb, S.blocks (S.σ A'.root).J = some Jb → Compatible U Jb B) ∧
      (¬ Compatible U X B → ∀ Pc, Goldilocks.Anc U Pc X → Goldilocks.Anc U Pc B →
        (∀ Q, Goldilocks.Anc U Q X → Goldilocks.Anc U Q B → Goldilocks.Anc U Q Pc) →
        (S.σ X.root).h ≤ (S.σ Pc.root).h + 1)) ∧
    (∀ i, Ts ≤ tr.time i → tr.time i ≤ T + P.Δ →
      (∀ j ≤ i, ∀ X, tr.AcceptAt y j X → Ts ≤ tr.time j → tr.time j < T + P.Δ ∨
        (tr.time j = T + P.Δ ∧ X.proposer = y ∧ P.slotTime X.slot = T + P.Δ)) →
      Compatible U (tr.store y (i + 1)).F B ∧ Compatible U (tr.store y (i + 1)).J B) := by
  classical
  have first : ∀ i, Ts ≤ tr.time i →
      ∃ j₀ ≤ i, Ts ≤ tr.time j₀ ∧ ∀ k < j₀, tr.time k < Ts := fun i hi =>
    have hex : ∃ k, Ts ≤ tr.time k := ⟨i, hi⟩
    ⟨Nat.find hex, Nat.find_min' hex hi, Nat.find_spec hex,
      fun k hk => not_le.1 (Nat.find_min hex hk)⟩
  refine ⟨fun i X hX hTi htime => ?_, fun i hTi _ hsc => ?_⟩
  · obtain ⟨j₀, hji, hj₀, hmin⟩ := first i hTi
    exact scope_block hr hT₀ hT hK1 hrows hy hj₀ hmin (hK0 y hy j₀ hj₀ hmin).1 hji hX htime
  obtain ⟨j₀, hji, hj₀, hmin⟩ := first i hTi
  suffices h : ∀ m, j₀ ≤ m → m ≤ i + 1 →
      Compatible U (tr.store y m).F B ∧ Compatible U (tr.store y m).J B from
    h (i + 1) (by omega) le_rfl
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact fun _ => hK0 y hy j₀ hj₀ hmin
  | succ m hjm ih =>
    intro hmi
    have ih := ih (by omega)
    rcases store_step hr hy m with he | ⟨X, hX, hXo⟩ | ⟨a, -, he⟩
    · rw [he]
      exact ih
    · obtain ⟨hJ, hF⟩ := onBlock_FJ hXo
      have hTm : Ts ≤ tr.time m := hj₀.trans (hr.time_mono hjm)
      have hJc : Compatible U (tr.store y (m + 1)).J B := by
        rcases hJ with hJ | hJ
        · rw [hJ]
          exact ih.2
        · exact (scope_block hr hT₀ hT hK1 hrows hy hj₀ hmin (hK0 y hy j₀ hj₀ hmin).1 hjm hX
            (hsc m (by omega) X hX hTm)).1 X (accept_mem hr hy hX) .refl _ hJ
      refine ⟨?_, hJc⟩
      rcases hF with hF | hF
      · rw [hF]
        exact ih.1
      · exact compatible_of_anc hr.coherent (hF.mono (hr.tree_subset y hy _)) hJc
    · obtain ⟨atts, he'⟩ := (tr.store y m).onAttestation_eq a
      rw [he, he']
      exact ih

end Consensus.Goldilocks.Store

end
