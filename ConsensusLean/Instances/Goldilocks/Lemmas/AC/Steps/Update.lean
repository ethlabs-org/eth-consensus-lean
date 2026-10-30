module
public import ConsensusLean.Instances.Goldilocks.Statements.AC.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views

public section

/-! # Goldilocks SA: the update after an optimistic confirmation (A1.4 (b))

If every honest slot-`(s+1)` vote extends `B`, an honest node `z` at its update of slot `s + 1`
that holds the votes of at least `n/2` honest voters, all resolved before `t_{s+1} + 2Δ`, counts
each of them for every block of its tree at or above `B` (or at or above `Φ.F`, when `B` is
below it): their heads are in `z`'s tree and extend `B`. With `f < n/2`, those blocks beat the
participation bound `voters < 2 · score` and pass the fast test, so the result, the deepest such
block (the candidates lie on one chain), extends `B`, and so does the fast test's block on its
path. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

/-- A nonempty set of blocks of a well-formed frame's tree has a deepest block. -/
private theorem exists_deepest_eq {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {S : Set (Blk sp.n FGP)}
    (hS : S ⊆ Φ.tree) (hne : S.Nonempty) : ∃ D, deepest Φ S = some D := by
  have hfin : S.Finite := hΦ.finite.subset hS
  obtain ⟨D, hD, hmax⟩ := hfin.exists_maximalFor (depth Φ) S hne
  obtain ⟨D', ⟨hD'S, hD'd⟩, hmin⟩ :=
    (hfin.subset (Set.sep_subset S fun C => depth Φ C = depth Φ D)).exists_minimalFor
      Block.root _ ⟨D, hD, rfl⟩
  have h : ∃ D, IsDeepest Φ S D := by
    refine ⟨D', hD'S, fun C hC hne => ?_⟩
    rcases lt_or_ge (depth Φ C) (depth Φ D') with h | h
    · exact Or.inl h
    have hCd : depth Φ C = depth Φ D' := le_antisymm (hD'd ▸ hmax hC (hD'd ▸ h)) h
    refine Or.inr ⟨hCd, lt_of_le_of_ne ?_ fun hr => hne (hΦ.coherent.1 (hS hC) (hS hD'S) hr.symm)⟩
    exact le_of_not_gt fun hlt => (hmin ⟨hC, hCd.trans hD'd⟩ hlt.le).not_gt hlt
  unfold deepest
  split_ifs
  exact ⟨_, rfl⟩

/-- A block of `S` compatible with the deepest block of `S` (in a well-formed frame) is at or
below it. -/
private theorem anc_of_isDeepest {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {S : Set (Blk sp.n FGP)}
    {D X : Blk sp.n FGP} (hD : IsDeepest Φ S D) (hX : X ∈ S) (hXt : X ∈ Φ.tree)
    (h : Compatible Φ.tree X D) : Φ.Anc X D := by
  refine h.elim id fun hDX => ?_
  by_cases hne : D = X
  · exact hne ▸ Relation.ReflTransGen.refl
  · have := depth_lt_of_anc hΦ hDX hne hXt
    rcases hD.2 X hX (Ne.symm hne) with h | h <;> omega

/-- Inside a coherent `U ⊇ Φ.tree` of a well-formed frame, a block between `Φ.F` and a block of
the tree is in the tree. -/
private theorem mem_tree_of_between {U : Set (Blk sp.n FGP)} (hU : Coherent U)
    {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {B C : Blk sp.n FGP}
    (hFB : Anc U Φ.F B) (h : Anc U B C) : C ∈ Φ.tree → B ∈ Φ.tree := by
  induction h with
  | refl => exact id
  | @tail c d hBc e ih =>
    intro hd
    by_cases hdF : d = Φ.F
    · subst hdF
      exact (Anc.antisymm hU hFB (hBc.tail e)) ▸ hΦ.rooted.1
    obtain rfl | ⟨p, -, hp⟩ :=
      (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (hΦ.rooted.2 d hd)
    · exact absurd rfl hdF
    have hpc : p = c := hU.1 (hΦU hp.1) e.1 (Option.some_injective _ (hp.2.2.symm.trans e.2.2))
    exact ih (hpc ▸ hp.1)

/-- An honest node's calls run inside a `U` that holds genesis (the root of its initial
frame). -/
private theorem genesis_mem_U {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) :
    ∃ G ∈ U, G.root = sp.genesisRoot ∧ G.parent = none := by
  induction i using Nat.strong_induction_on generalizing ℓ with
  | _ i ih =>
    rcases hr.frameLaw y hy i ℓ hc with
      ⟨-, Φ₀, ⟨htree, hroot, -, hpar, -⟩, ⟨-, hΦ₀U⟩, -⟩ | ⟨j, ℓ', hj, hc', -, -⟩
    · exact ⟨Φ₀.F, hΦ₀U (htree ▸ Set.mem_singleton _), hroot, hpar⟩
    · exact ih j hj hc'

variable (sp)

/-- **A1.4 (b).** -/
theorem optimistic_next_update : OptimisticNextUpdate sp := by
  intro FGP ro H U tr hrun s x z i₀ k B CV ℓ _ _ hf _ hext hz hup hh hres
  have hr := hrun.localRun
  have hU := hr.coherent
  obtain ⟨hc, -, -, -⟩ := hup
  obtain ⟨hΦ, hΦU⟩ : FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
    rcases hr.frameLaw z hz k ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1
  set A := tr.state z k
  set Φ := ℓ.frame
  set Hv := {v | v ∈ H ∧ ∃ x' ∈ A.pool (s + 1), x'.val = v}
  have hps := state_pool_slot sp hr hz k (s + 1)
  -- an honest vote of the pool: no second vote, resolved early, its head extends `B`
  have key : ∀ v ∈ A.pool (s + 1), v.val ∈ H →
      v.val ∉ equivocators {x | x ∈ A.pool (s + 1)} ∧
      resolutionTime A Φ v < ETime.of (sp.ts (s + 1 : Nat) + 2 * sp.Δ) ∧
      ∃ Hd ∈ Φ.tree, Hd.root = v.head ∧ Anc U B Hd := by
    intro v hv hvH
    refine ⟨?_, hres v hv hvH, ?_⟩
    · rintro ⟨x₁, hx₁, x₂, hx₂, hne, h₁, h₂⟩
      obtain ⟨j₁, -, e₁, hv₁, rfl⟩ := hrun.honest.pool_vote z hz k _ x₁ hx₁ (h₁ ▸ hvH)
      obtain ⟨j₂, -, e₂, hv₂, rfl⟩ := hrun.honest.pool_vote z hz k _ x₂ hx₂ (h₂ ▸ hvH)
      rw [h₁] at hv₁
      rw [h₂] at hv₂
      exact hne (congrArg Emission.msg (one_vote_per_slot sp _ _ _ _ _ hr _ hvH _ _ _ _ hv₁ hv₂
        ((hps _ hx₁).trans (hps _ hx₂).symm)).2)
    · obtain ⟨j, -, e, hve, rfl⟩ := hrun.honest.pool_vote z hz k _ v hv hvH
      obtain ⟨Hd, hHdU, hHdr, hBHd⟩ := hext _ hvH j e hve (hps _ hv)
      obtain ⟨Hd', hHd', hr'⟩ := inTree_of_resolutionTime_ne_top (ne_top_of_lt (hres _ hv hvH))
      exact ⟨Hd', hHd', hr', hU.1 (hΦU hHd') hHdU (hr'.trans hHdr.symm) ▸ hBHd⟩
  -- an honest vote of the pool exists
  obtain ⟨_, hvH, v₀, hv₀, rfl⟩ : Hv.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨-, -, Hd₀, hHd₀, -, hBHd₀⟩ := key v₀ hv₀ hvH
  -- `B*`: `B` if it is in the tree, else `Φ.F`
  obtain ⟨Bs, hBsΦ, hFBs, hBBs, hBsv, hgen⟩ : ∃ Bs ∈ Φ.tree, Φ.Anc Φ.F Bs ∧ Anc U B Bs ∧
      (∀ Hd ∈ Φ.tree, Anc U B Hd → Φ.Anc Bs Hd) ∧
      (B.root ≠ sp.genesisRoot → Bs.root ≠ sp.genesisRoot) := by
    by_cases hB : B ∈ Φ.tree
    · exact ⟨B, hB, hΦ.rooted.2 B hB, Relation.ReflTransGen.refl,
        fun Hd hHd h => anc_tree_of_anc_U hU hΦ hΦU hB h hHd, id⟩
    have hBF : Anc U B Φ.F := (anc_total hU hBHd₀ ((hΦ.rooted.2 Hd₀ hHd₀).mono hΦU)).resolve_right
      fun h => hB (mem_tree_of_between hU hΦ hΦU h hBHd₀ hHd₀)
    refine ⟨Φ.F, hΦ.rooted.1, Relation.ReflTransGen.refl, hBF,
      fun Hd hHd _ => hΦ.rooted.2 Hd hHd, fun _ hg => ?_⟩
    obtain ⟨G, hGU, hGr, hGp⟩ := genesis_mem_U hr hz hc
    have hFG := hU.1 (hΦU hΦ.rooted.1) hGU (hg.trans hGr.symm)
    obtain h | ⟨c, -, hcF⟩ := (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hBF
    · exact hB (h ▸ hΦ.rooted.1)
    · rw [hFG] at hcF
      simp [hcF.2.2] at hGp
  -- every honest voter of the pool supports `B*`
  have hscore : Hv.ncard ≤ confirmationScore sp A Φ (s + 1) Bs := by
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro _ ⟨hwH, v, hv, rfl⟩
    obtain ⟨hne, hres', Hd, hHd, hHdr, hBHd⟩ := key v hv hwH
    exact ⟨hne, v, ⟨hv, hres'⟩, rfl, by rw [hps v hv], Hd, hHd, hHdr, hBsv Hd hHd hBHd⟩
  have hvot : (voters {v | v ∈ A.pool (s + 1)}).ncard ≤ Hv.ncard + Hᶜ.ncard := by
    refine (Set.ncard_le_ncard (t := Hv ∪ Hᶜ) ?_ (Set.toFinite _)).trans
      (Set.ncard_union_le _ _)
    rintro i ⟨v, hv, rfl⟩
    by_cases hi : v.val ∈ H
    · exact Or.inl ⟨hi, v, hv, rfl⟩
    · exact Or.inr hi
  have hBsS : Bs ∈ {C | C ∈ Φ.tree ∧ Φ.Anc Φ.F C ∧
      (voters {v | v ∈ A.pool (s + 1)}).ncard < 2 * confirmationScore sp A Φ (s + 1) C} :=
    ⟨hBsΦ, hFBs, by omega⟩
  obtain ⟨C, hC⟩ := exists_deepest_eq hΦ (fun _ h => h.1) ⟨Bs, hBsS⟩
  have hCd := deepest_mem hC
  have hBsC : Φ.Anc Bs C := anc_of_isDeepest hΦ hCd hBsS hBsΦ
    (majority_chain sp _ Φ ⟨{v | v ∈ A.pool (s + 1)}, {v | v ∈ A.pool (s + 1) ∧
      resolutionTime A Φ v < ETime.of (sp.ts (s + 1 : Nat) + 2 * sp.Δ)}⟩ _ Bs C hΦ
      (fun _ h => h.1) hBsΦ hCd.1.1 hBsS.2.2 hCd.1.2.2)
  refine ⟨C, hC, hBBs.trans (hBsC.mono hΦU), fun hg => ?_⟩
  have hBsP : Bs ∈ {X | X ∈ confirmationPath sp Φ C ∧ FastTest sp A Φ (s + 1) X} :=
    ⟨⟨hBsΦ, hgen hg, hBsC⟩, by unfold FastTest; omega⟩
  obtain ⟨D, hD⟩ := exists_deepest_eq hΦ (fun _ h => h.1.1) ⟨Bs, hBsP⟩
  have hDd := deepest_mem hD
  exact ⟨D, hD, hBBs.trans ((anc_of_isDeepest hΦ hDd hBsP hBsΦ
    (anc_total hΦ.coherent hBsC hDd.1.1.2.2)).mono hΦU)⟩

end Consensus.Goldilocks.SA

end
