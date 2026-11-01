module
public import AvailableChainSimplexFG
public import AvailableChainKitFG.Accountable
public import AvailableChainKitFG.StoreInvDef
public import AvailableChainKitFG.FrameSelection

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V] (E : Electorate V)
  (cfg : FGConfig)

/-! ## Collision freedom and the selector -/

omit [Fintype V] in
/-- [helper] Collision freedom passes to a subset. -/
theorem viewRootInj_mono {Vw Vw' : View V} (hinj : ViewRootInj Vw') (h : Vw ⊆ Vw') :
    ViewRootInj Vw := fun X Y ⟨W, hW, hXW⟩ ⟨W', hW', hYW'⟩ hr =>
  hinj X Y ⟨W, h hW, hXW⟩ ⟨W', h hW', hYW'⟩ hr

-- port: DC/DecoupledConsensusProofs/Protocol/ForkChoice/Goldfish/Walk.lean:66-75
omit [Fintype V] in
/-- [helper] `pickPair` returns `none` on an empty set. -/
theorem pickPair_empty {α : Type} [DecidableEq α] (p : α → Bool) :
    pickPair (∅ : Finset α) p = none := by
  unfold pickPair
  rw [dite_eq_right]
  rintro ⟨x, ⟨hx, -⟩, -⟩
  exact Finset.notMem_empty x hx

/-- [helper] Under collision freedom, two blocks of a view whose pairs have one
lex key carry one pair. -/
theorem pair_eq_of_lexKey_eq {Vw : View V} (hinj : ViewRootInj Vw) {W W' : FGBlock V}
    (hW : W ∈ Vw) (hW' : W' ∈ Vw)
    (hk : lexKey ((derive E cfg W).h_j, (derive E cfg W).J) =
      lexKey ((derive E cfg W').h_j, (derive E cfg W').J)) :
    ((derive E cfg W).h_j, (derive E cfg W).J) =
      ((derive E cfg W').h_j, (derive E cfg W').J) := by
  have hk' := toLex.injective hk
  simp only [Prod.mk.injEq] at hk'
  obtain ⟨h1, h2⟩ := hk'
  have hJ : (derive E cfg W).J = (derive E cfg W').J :=
    hinj _ _ ⟨W, hW, (derive_anchors_preceq E cfg W).2⟩
      ⟨W', hW', (derive_anchors_preceq E cfg W').2⟩ (BlockId.ext h2)
  rw [h1, hJ]

/-- [helper] If a block K of the view carries a pair with `F ⪯ J` whose key is at
least the key of every such pair, then `lexMax` selects K's pair. -/
theorem lexMax_eq_of_greatest (F : FGBlock V) (Vw : View V) (hinj : ViewRootInj Vw)
    (K : FGBlock V) (hK : K ∈ Vw) (hFK : FGBlock.Preceq F (derive E cfg K).J)
    (hmax : ∀ W ∈ Vw, FGBlock.Preceq F (derive E cfg W).J →
      lexKey ((derive E cfg W).h_j, (derive E cfg W).J) ≤
        lexKey ((derive E cfg K).h_j, (derive E cfg K).J)) :
    lexMax E cfg F Vw = ((derive E cfg K).h_j, (derive E cfg K).J) := by
  unfold lexMax
  dsimp only
  have hmem : ∀ q, q ∈ (Vw.filter (fun W => FGBlock.preceq F (derive E cfg W).J)).image
      (fun W => ((derive E cfg W).h_j, (derive E cfg W).J)) ↔
      ∃ W ∈ Vw, FGBlock.Preceq F (derive E cfg W).J ∧
        ((derive E cfg W).h_j, (derive E cfg W).J) = q := by
    intro q
    simp only [Finset.mem_image, Finset.mem_filter, FGBlock.Preceq, and_assoc]
  have hp : ((derive E cfg K).h_j, (derive E cfg K).J) ∈
      (Vw.filter (fun W => FGBlock.preceq F (derive E cfg W).J)).image
        (fun W => ((derive E cfg W).h_j, (derive E cfg W).J)) :=
    (hmem _).2 ⟨K, hK, hFK, rfl⟩
  have hsup : ((Vw.filter (fun W => FGBlock.preceq F (derive E cfg W).J)).image
      (fun W => ((derive E cfg W).h_j, (derive E cfg W).J))).sup lexKey =
      lexKey ((derive E cfg K).h_j, (derive E cfg K).J) := by
    apply le_antisymm
    · apply Finset.sup_le
      intro q hq
      obtain ⟨W, hW, hFW, rfl⟩ := (hmem q).1 hq
      exact hmax W hW hFW
    · exact Finset.le_sup hp
  rw [hsup, pickPair_eq_of_unique _ _ _ hp (by simp)]
  · rfl
  · intro q hq hk
    obtain ⟨W, hW, -, rfl⟩ := (hmem q).1 hq
    exact pair_eq_of_lexKey_eq E cfg hinj hW hK (by simpa using hk)

/-- [helper] With a block whose pair has `F ⪯ J`, and under collision freedom,
`lexMax` selects the pair of some block with `F ⪯ J` and the greatest key. -/
theorem lexMax_spec (F : FGBlock V) (Vw : View V) (hinj : ViewRootInj Vw)
    (hne : ∃ K ∈ Vw, FGBlock.Preceq F (derive E cfg K).J) :
    ∃ K ∈ Vw, FGBlock.Preceq F (derive E cfg K).J ∧
      lexMax E cfg F Vw = ((derive E cfg K).h_j, (derive E cfg K).J) ∧
      ∀ W ∈ Vw, FGBlock.Preceq F (derive E cfg W).J →
        lexKey ((derive E cfg W).h_j, (derive E cfg W).J) ≤
          lexKey ((derive E cfg K).h_j, (derive E cfg K).J) := by
  have hS : (Vw.filter (fun W => FGBlock.Preceq F (derive E cfg W).J)).Nonempty := by
    obtain ⟨K, hK, hFK⟩ := hne
    exact ⟨K, Finset.mem_filter.2 ⟨hK, hFK⟩⟩
  obtain ⟨K, hKS, hKmax⟩ := Finset.exists_max_image _
    (fun W => lexKey ((derive E cfg W).h_j, (derive E cfg W).J)) hS
  rw [Finset.mem_filter] at hKS
  have hmax : ∀ W ∈ Vw, FGBlock.Preceq F (derive E cfg W).J →
      lexKey ((derive E cfg W).h_j, (derive E cfg W).J) ≤
        lexKey ((derive E cfg K).h_j, (derive E cfg K).J) :=
    fun W hW hFW => hKmax W (Finset.mem_filter.2 ⟨hW, hFW⟩)
  exact ⟨K, hKS.1, hKS.2, lexMax_eq_of_greatest E cfg F Vw hinj K hKS.1 hKS.2 hmax, hmax⟩

/-- [helper] With no block whose pair has `F ⪯ J`, `lexMax` falls back to
`(0, genesis)`. -/
theorem lexMax_of_none (F : FGBlock V) (Vw : View V)
    (hno : ∀ W ∈ Vw, ¬ FGBlock.Preceq F (derive E cfg W).J) :
    lexMax E cfg F Vw = (0, .genesis) := by
  unfold lexMax
  dsimp only
  have hempty : (Vw.filter (fun W => FGBlock.preceq F (derive E cfg W).J)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    exact hno
  rw [hempty, Finset.image_empty, pickPair_empty]
  rfl

omit [DecidableEq V] [Fintype V] in
/-- [helper] The fallback key `(0, genesisRoot)` is the least key. -/
theorem lexKey_fallback_le (p : Height × FGBlock V) :
    lexKey ((0, .genesis) : Height × FGBlock V) ≤ lexKey p := by
  have h0 : lexKey ((0, .genesis) : Height × FGBlock V) = ⊥ := rfl
  rw [h0]
  exact bot_le

/-- [helper] Inserting a block B: the pair of B enters exactly when its J extends
F and its key is greater (the J step of `update_finality`). -/
theorem lexMax_insert (F : FGBlock V) (Vw : View V) (B : FGBlock V)
    (hinj : ViewRootInj (insert B Vw))
    (hne : ∃ K ∈ Vw, FGBlock.Preceq F (derive E cfg K).J) :
    lexMax E cfg F (insert B Vw) =
      if FGBlock.Preceq F (derive E cfg B).J ∧
          lexKey (lexMax E cfg F Vw) < lexKey ((derive E cfg B).h_j, (derive E cfg B).J)
        then ((derive E cfg B).h_j, (derive E cfg B).J) else lexMax E cfg F Vw := by
  obtain ⟨K, hK, hFK, hlex, hmax⟩ :=
    lexMax_spec E cfg F Vw (viewRootInj_mono hinj (Finset.subset_insert B Vw)) hne
  split_ifs with hc
  · apply lexMax_eq_of_greatest E cfg F _ hinj B (Finset.mem_insert_self B Vw) hc.1
    intro W hW hFW
    rcases Finset.mem_insert.1 hW with rfl | hW
    · exact le_refl _
    · rw [hlex] at hc
      exact le_of_lt (lt_of_le_of_lt (hmax W hW hFW) hc.2)
  · rw [hlex]
    apply lexMax_eq_of_greatest E cfg F _ hinj K (Finset.mem_insert_of_mem hK) hFK
    intro W hW hFW
    rcases Finset.mem_insert.1 hW with rfl | hW
    · rw [hlex] at hc
      exact not_lt.1 (fun hlt => hc ⟨hFW, hlt⟩)
    · exact hmax W hW hFW

/-- [helper] An F advance from F to `F'` with `F ⪯ F' ⪯ J` keeps the selected
pair: every pair with `F' ⪯ J'` also has `F ⪯ J'`. -/
theorem lexMax_of_advance (F F' : FGBlock V) (Vw : View V) (hinj : ViewRootInj Vw)
    (hne : ∃ K ∈ Vw, FGBlock.Preceq F (derive E cfg K).J)
    (hFF' : FGBlock.Preceq F F') (hF'J : FGBlock.Preceq F' (lexMax E cfg F Vw).2) :
    lexMax E cfg F' Vw = lexMax E cfg F Vw := by
  obtain ⟨K, hK, -, hlex, hmax⟩ := lexMax_spec E cfg F Vw hinj hne
  rw [hlex] at hF'J ⊢
  exact lexMax_eq_of_greatest E cfg F' Vw hinj K hK hF'J
    (fun W hW hFW => hmax W hW (preceq_trans hFF' hFW))

/-! ## The frontier -/

/-- [helper] A nonempty block set holds a block at the frontier height. -/
theorem exists_frontier (Vw : View V) (hne : Vw.Nonempty) :
    ∃ W ∈ Vw, hOf E cfg W = frontier E cfg Vw := by
  obtain ⟨W, hW, hsup⟩ := Finset.exists_mem_eq_sup Vw hne (hOf E cfg)
  refine ⟨W, hW, ?_⟩
  have h1 := one_le_h E cfg W
  unfold SimplexFG.frontier hOf at *
  rw [hsup]
  simp only [Height] at *
  omega

/-- [helper] Every block of the set is at or below the frontier. -/
theorem le_frontier {Vw : View V} {W : FGBlock V} (hW : W ∈ Vw) :
    hOf E cfg W ≤ frontier E cfg Vw :=
  le_trans (Finset.le_sup (f := hOf E cfg) hW) le_sup_left

/-- [helper] The frontier of a set with one more block. -/
theorem frontier_insert (Vw : View V) (B : FGBlock V) :
    frontier E cfg (insert B Vw) = max (frontier E cfg Vw) (hOf E cfg B) := by
  unfold SimplexFG.frontier
  rw [Finset.sup_insert]
  simp only [Height] at *
  omega

/-- [helper] The frontier grows with the block set. -/
theorem frontier_mono {Vw Vw' : View V} (h : Vw ⊆ Vw') :
    frontier E cfg Vw ≤ frontier E cfg Vw' := by
  unfold SimplexFG.frontier
  exact sup_le_sup_right (Finset.sup_mono h) 1

/-- [helper] The lex pair grows with the block set, when roots are
collision-free on the larger set. -/
theorem lexMax_mono (F : FGBlock V) {Vw Vw' : View V} (h : Vw ⊆ Vw')
    (hinj : ViewRootInj Vw') :
    lexKey (lexMax E cfg F Vw) ≤ lexKey (lexMax E cfg F Vw') := by
  by_cases hne : ∃ K ∈ Vw, FGBlock.Preceq F (derive E cfg K).J
  · obtain ⟨K, hK, hFK, hlex, -⟩ := lexMax_spec E cfg F Vw (viewRootInj_mono hinj h) hne
    obtain ⟨_, _, -, hlex', hmax'⟩ := lexMax_spec E cfg F Vw' hinj ⟨K, h hK, hFK⟩
    rw [hlex, hlex']
    exact hmax' K (h hK) hFK
  · push Not at hne
    rw [lexMax_of_none E cfg F Vw hne]
    exact lexKey_fallback_le _

/-! ## The state height -/

/-- [helper] The two forms of the state height in the pinned statements:
`hOf E cfg W` (the frame files) and `(derive E cfg W).h` (the certificate
files). Use it to compose lemmas across the two forms. -/
@[simp] theorem hOf_eq (W : FGBlock V) : hOf E cfg W = (derive E cfg W).h := rfl

/-! ## `update_finality` -/

/-- [pin fj.frame.v4] (Trees: cumulative) `update_finality` writes only the live caches;
it does not change the tree (alfs4 lines 847–860). -/
theorem update_finality_TF (st : Store V) (B : FGBlock V) :
    (update_finality E cfg st B).TF = st.TF := by
  unfold update_finality
  dsimp only
  split_ifs <;> rfl

/-- [helper] `update_finality` sets `h_max := max h_max h(B)` (alfs4 line 849). -/
theorem update_finality_h_max (st : Store V) (B : FGBlock V) :
    (update_finality E cfg st B).h_max = max st.h_max (hOf E cfg B) := by
  unfold update_finality
  dsimp only
  split_ifs <;> rfl

/-- [helper] The J step of `update_finality` (alfs4 lines 850–854). The F step
does not write the pair. -/
theorem update_finality_pair (st : Store V) (B : FGBlock V) :
    ((update_finality E cfg st B).h_j, (update_finality E cfg st B).J) =
      if FGBlock.Preceq st.F (derive E cfg B).J ∧
          lexKey (st.h_j, st.J) < lexKey ((derive E cfg B).h_j, (derive E cfg B).J)
        then ((derive E cfg B).h_j, (derive E cfg B).J) else (st.h_j, st.J) := by
  unfold update_finality
  dsimp only
  by_cases hc : FGBlock.Preceq st.F (derive E cfg B).J ∧
      lexKey (st.h_j, st.J) < lexKey ((derive E cfg B).h_j, (derive E cfg B).J)
  · have hb : (FGBlock.preceq st.F (derive E cfg B).J && decide (lexKey (st.h_j, st.J) <
        lexKey ((derive E cfg B).h_j, (derive E cfg B).J))) = true := by
      simpa [FGBlock.Preceq] using hc
    rw [ite_eq_left hc, ite_eq_left hb]
    split_ifs <;> rfl
  · have hb : ¬ (FGBlock.preceq st.F (derive E cfg B).J && decide (lexKey (st.h_j, st.J) <
        lexKey ((derive E cfg B).h_j, (derive E cfg B).J))) = true := by
      simpa [FGBlock.Preceq] using hc
    rw [ite_eq_right hc, ite_eq_right hb]
    split_ifs <;> rfl

/-- [helper] The F step of `update_finality` (alfs4 lines 855–858): F does not
change, or it moves to `σ.F` with `F ⪯ σ.F`, `σ.F ∈ TF` and `σ.F ⪯ J` for the
new J. -/
theorem update_finality_F_cases (st : Store V) (B : FGBlock V) :
    (update_finality E cfg st B).F = st.F ∨
      (FGBlock.Preceq st.F (derive E cfg B).F ∧ (derive E cfg B).F ∈ st.TF ∧
        FGBlock.Preceq (derive E cfg B).F (update_finality E cfg st B).J ∧
        (update_finality E cfg st B).F = (derive E cfg B).F) := by
  unfold update_finality
  dsimp only
  split_ifs with h1 h2 h2
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    obtain ⟨⟨⟨hF, -⟩, hJ⟩, hV⟩ := h2
    exact Or.inr ⟨hF, (Finset.mem_filter.1 hV).1, hJ, rfl⟩
  · exact Or.inl rfl
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    obtain ⟨⟨⟨hF, -⟩, hJ⟩, hV⟩ := h2
    exact Or.inr ⟨hF, (Finset.mem_filter.1 hV).1, hJ, rfl⟩
  · exact Or.inl rfl

/-- [pin fg.accountable.v1] (local F never retreats) F only moves to a
descendant. -/
theorem update_finality_F_mono (st : Store V) (B : FGBlock V) :
    FGBlock.Preceq st.F (update_finality E cfg st B).F := by
  rcases update_finality_F_cases E cfg st B with h | ⟨hF, -, -, h⟩
  · rw [h]
    exact preceq_refl _
  · rw [h]
    exact hF

/-! ## The store invariant -/

omit [Fintype V] [RowCodec V] in
/-- [helper] A parent-closed block set is ancestor-closed. -/
theorem ancestor_closed_of_parent_closed (T : Finset (FGBlock V))
    (hcl : ∀ B ∈ T, B.parent ∈ T) : ∀ B ∈ T, ∀ A, FGBlock.Preceq A B → A ∈ T := by
  intro B hB A hAB
  induction B with
  | genesis =>
      rw [preceq_genesis] at hAB
      subst hAB
      exact hB
  | node p s r_s r rs ih =>
      simp only [FGBlock.Preceq, FGBlock.preceq, Bool.or_eq_true, decide_eq_true_eq] at hAB
      rcases hAB with rfl | hAp
      · exact hB
      · exact ih (hcl _ hB) hAp

/-- [pin fj.frame.v4] (Trees: parent-closed; initialization, alfs4 lines 474–482)
The initial store, the genesis tree, satisfies the invariant. -/
theorem storeInv_init : StoreInv E cfg (Store.init (V := V)) := by
  have hinj : ViewRootInj ({.genesis} : View V) := by
    rintro X Y ⟨W, hW, hXW⟩ ⟨W', hW', hYW'⟩ -
    rw [Finset.mem_singleton] at hW hW'
    subst hW hW'
    rw [preceq_genesis] at hXW hYW'
    rw [hXW, hYW']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro B hB
    simp only [Store.init, Finset.mem_singleton] at hB ⊢
    rw [hB]
    rfl
  · exact Finset.mem_singleton_self _
  · exact Finset.mem_singleton_self _
  · change 1 = SimplexFG.frontier E cfg {.genesis}
    simp [SimplexFG.frontier, hOf, derive, ChainState.initial]
  · change ((0 : Height), FGBlock.genesis) = lexMax E cfg .genesis {.genesis}
    rw [lexMax_eq_of_greatest E cfg .genesis {.genesis} hinj .genesis
      (Finset.mem_singleton_self _) (preceq_refl _)]
    · rfl
    · rintro W hW -
      rw [Finset.mem_singleton] at hW
      rw [hW]
  · exact preceq_refl _
  · exact ⟨.genesis, Finset.mem_singleton_self _, rfl⟩

/-- [helper] The accepted branch of `on_block`: B enters the tree, then
`update_finality` runs. The invariant needs only the parent check and
collision freedom on the new tree. -/
theorem storeInv_accept (st : Store V) (B : FGBlock V) (h : StoreInv E cfg st)
    (hpar : B.parent ∈ st.TF) (hinj : ViewRootInj (insert B st.TF)) :
    StoreInv E cfg (update_finality E cfg { st with TF := insert B st.TF } B) := by
  have hTF := update_finality_TF E cfg { st with TF := insert B st.TF } B
  have hsub : st.TF ⊆ insert B st.TF := Finset.subset_insert B st.TF
  obtain ⟨K, hK, hKF⟩ := h.Fcar
  have hne : ∃ K ∈ st.TF, FGBlock.Preceq st.F (derive E cfg K).J :=
    ⟨K, hK, hKF ▸ derive_F_preceq_J E cfg K⟩
  -- The pair after the J step, over the new tree, for the old F.
  have hpairJ : ((update_finality E cfg { st with TF := insert B st.TF } B).h_j,
      (update_finality E cfg { st with TF := insert B st.TF } B).J) =
      lexMax E cfg st.F (insert B st.TF) := by
    rw [update_finality_pair, lexMax_insert E cfg st.F st.TF B hinj hne, ← h.pair]
  -- The J after the J step extends the old F.
  have hFJ : FGBlock.Preceq st.F (update_finality E cfg { st with TF := insert B st.TF } B).J := by
    have hp := update_finality_pair E cfg { st with TF := insert B st.TF } B
    dsimp only at hp
    split_ifs at hp with hc
    · rw [(Prod.mk.inj hp).2]
      exact hc.1
    · rw [(Prod.mk.inj hp).2]
      exact h.FJ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hTF]
    intro C hC
    rcases Finset.mem_insert.1 hC with rfl | hC
    · exact hsub hpar
    · exact hsub (h.closed C hC)
  · rw [hTF]
    exact hsub h.gen
  · rw [hTF]
    rcases update_finality_F_cases E cfg { st with TF := insert B st.TF } B with
      hF | ⟨-, hmem, -, hF⟩
    · rw [hF]
      exact hsub h.Fmem
    · rw [hF]
      exact hmem
  · rw [hTF, update_finality_h_max, frontier_insert, ← h.hmax]
  · rw [hTF]
    rcases update_finality_F_cases E cfg { st with TF := insert B st.TF } B with
      hF | ⟨hadv, -, hJ, hF⟩
    · rw [hF]
      exact hpairJ
    · rw [hF, hpairJ]
      refine (lexMax_of_advance E cfg st.F _ _ hinj ⟨K, hsub hK, ?_⟩ hadv ?_).symm
      · exact hKF ▸ derive_F_preceq_J E cfg K
      · rw [← hpairJ]
        exact hJ
  · rcases update_finality_F_cases E cfg { st with TF := insert B st.TF } B with
      hF | ⟨-, -, hJ, hF⟩
    · rw [hF]
      exact hFJ
    · rw [hF]
      exact hJ
  · rw [hTF]
    rcases update_finality_F_cases E cfg { st with TF := insert B st.TF } B with
      hF | ⟨-, -, -, hF⟩
    · rw [hF]
      exact ⟨K, hsub hK, hKF⟩
    · rw [hF]
      exact ⟨B, Finset.mem_insert_self B st.TF, rfl⟩

/-- [helper] The refused branch of `on_block` (alfs4 lines 794–801): the store
does not change. -/
theorem on_block_of_refused (st : Store V) (B : FGBlock V)
    (hc : B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot) :
    on_block E cfg st B = st := by
  unfold on_block
  rw [ite_eq_left hc]

/-- [helper] The accepted branch of `on_block` (alfs4 lines 806–812): B enters
the tree, then `update_finality` runs. -/
theorem on_block_of_accepted (st : Store V) (B : FGBlock V)
    (hc : ¬ (B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot)) :
    on_block E cfg st B = update_finality E cfg { st with TF := insert B st.TF } B := by
  unfold on_block
  rw [ite_eq_right hc]

/-- [pin fg.accountable.v1] (local F never retreats, on_block step) `on_block`
moves F only to a descendant: a refused block changes nothing, and an accepted
block runs `update_finality` on the store with B inserted, whose F is the old F. -/
theorem on_block_F_mono (st : Store V) (B : FGBlock V) :
    FGBlock.Preceq st.F (on_block E cfg st B).F := by
  by_cases hc : B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot
  · rw [on_block_of_refused E cfg st B hc]
    exact preceq_refl _
  · rw [on_block_of_accepted E cfg st B hc]
    exact update_finality_F_mono E cfg { st with TF := insert B st.TF } B

/-- [pin fj.frame.v4] (update_finality and on_block, with `ViewRootInj`)
`on_block` keeps the invariant. A refused block changes nothing. Roots must be
collision-free on the new tree only when B is accepted (`F ⪯ B`). -/
theorem storeInv_on_block (st : Store V) (B : FGBlock V) (h : StoreInv E cfg st)
    (hinj : FGBlock.Preceq st.F B → ViewRootInj (insert B st.TF)) :
    StoreInv E cfg (on_block E cfg st B) := by
  by_cases hc : B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot
  · rw [on_block_of_refused E cfg st B hc]
    exact h
  · rw [on_block_of_accepted E cfg st B hc]
    simp only [not_or, not_not, Bool.not_eq_false] at hc
    obtain ⟨-, hpar, hFB, -⟩ := hc
    exact storeInv_accept E cfg st B h hpar (hinj hFB)

/-- [pin fj.frame.v4] (Trees: cumulative; alfs4 lines 352–356) `on_block` never removes a
block from the tree. -/
theorem on_block_TF_subset (st : Store V) (B : FGBlock V) :
    st.TF ⊆ (on_block E cfg st B).TF := by
  by_cases hc : B ∈ st.TF ∨ B.parent ∉ st.TF ∨ FGBlock.preceq st.F B = false ∨
      B.slot ≤ B.parent.slot
  · rw [on_block_of_refused E cfg st B hc]
  · rw [on_block_of_accepted E cfg st B hc, update_finality_TF]
    exact Finset.subset_insert B st.TF

omit [Fintype V] [RowCodec V] in
/-- [pin fj.frame.v4] (Trees: act(Σ) is a view; AP interface) The active view is a
subset of the tree. -/
theorem activeView_subset (st : Store V) : activeView st ⊆ st.TF := by
  exact Finset.filter_subset _ _

/-! ## The controls and the filtered tree -/

/-- [pin fj.frame.v1] (the lo table; fjControls of any block set) `lo = H`
exactly in a contest, and `lo = H − 1` otherwise. -/
theorem fjFrame_lo (F : FGBlock V) (Vw : View V) :
    (fjControls E cfg F Vw).lo =
      if (fjControls E cfg F Vw).contest then (fjControls E cfg F Vw).H
      else (fjControls E cfg F Vw).H - 1 := by
  rfl

/-- [pin fj.frame.v1] The special case: the `fjFrame` domain is the filtered tree of the
same set under its own controls. -/
theorem fjFrame_D (F : FGBlock V) (Vw : View V) :
    (fjFrame E cfg F Vw).D = filteredFrom E cfg (fjControls E cfg F Vw) Vw := by
  rfl

/-- [pin fj.frame.v4] CENTRAL: the ALFS
controls (DC's live caches, contest over TF) are the FJ_FRAME controls of the
full admitted tree. -/
theorem storeControls_eq_fjControls (st : Store V) (h : StoreInv E cfg st) :
    storeControls E cfg st = fjControls E cfg st.F st.TF := by
  unfold storeControls fjControls
  dsimp only
  rw [← h.hmax, ← h.pair]

/-- [pin fj.frame.v4] (get_filtered_block_tree) On the full tree, the ALFS
filtered tree is the `fjFrame` domain. -/
theorem storeFrame_full (st : Store V) (h : StoreInv E cfg st) :
    storeFrame E cfg st st.TF = (fjFrame E cfg st.F st.TF).D := by
  unfold storeFrame
  rw [storeControls_eq_fjControls E cfg st h, fjFrame_D]

/-- [pin fj.frame.v4] (viability; any controls,
any block set) The filtered tree holds exactly the blocks of the set at or
above Z and F that have a witness in the set at height ≥ lo. -/
theorem mem_filteredFrom (c : Controls V) (blocks : Finset (FGBlock V)) (B : FGBlock V) :
    B ∈ filteredFrom E cfg c blocks ↔ B ∈ blocks ∧ FGBlock.Preceq c.F B ∧
      FGBlock.Preceq c.Z B ∧ ∃ W ∈ blocks, FGBlock.Preceq B W ∧ c.lo ≤ hOf E cfg W := by
  simp only [filteredFrom, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
  simp only [FGBlock.Preceq, and_assoc]

/-- [helper] In the uncontested phase of `fjControls`, every block of the set at
the frontier height extends J. -/
theorem fjControls_J_preceq_of_rootIsJ (F : FGBlock V) (Vw : View V)
    (hr : (fjControls E cfg F Vw).rootIsJ = true) (W : FGBlock V) (hW : W ∈ Vw)
    (hH : hOf E cfg W = (fjControls E cfg F Vw).H) :
    FGBlock.Preceq (fjControls E cfg F Vw).J W := by
  unfold Controls.rootIsJ fjControls at hr
  unfold fjControls at hH ⊢
  dsimp only at hr hH ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at hr
  obtain ⟨hHj, hc⟩ := hr
  rcases hc with hc | hc
  · exact absurd hHj hc
  · by_contra hn
    exact hc ⟨W, hW, hH, hn⟩

/-- [pin fj.frameFeasible.v1] (1) (any controls, any block set) A nonempty
filtered tree holds a block of state height ≥ lo. -/
theorem filteredFrom_reachesLo (c : Controls V) (blocks : Finset (FGBlock V))
    (hne : (filteredFrom E cfg c blocks).Nonempty) :
    ∃ W ∈ filteredFrom E cfg c blocks, c.lo ≤ hOf E cfg W := by
  obtain ⟨B, hB⟩ := hne
  obtain ⟨-, hF, hZ, W, hW, hBW, hlo⟩ := (mem_filteredFrom E cfg c blocks B).1 hB
  exact ⟨W, (mem_filteredFrom E cfg c blocks W).2
    ⟨hW, preceq_trans hF hBW, preceq_trans hZ hBW, W, hW, preceq_refl W, hlo⟩, hlo⟩

/-- [helper] (weak geometry form of part (3); any controls, any ancestor-closed
block set; Astra K02) If the filtered tree is not empty and `F ⪯ Z`, then Z is
in it. This plan reads it as the FG input of `ap.headReachesLo.v5` clause 3 on
the frozen voter tree. That link is the plan's own reading; the registry has no
such discharge. -/
theorem filteredFrom_Z_mem (c : Controls V) (blocks : Finset (FGBlock V))
    (hclosed : ∀ B ∈ blocks, ∀ A, FGBlock.Preceq A B → A ∈ blocks)
    (hFZ : FGBlock.Preceq c.F c.Z) (hne : (filteredFrom E cfg c blocks).Nonempty) :
    c.Z ∈ filteredFrom E cfg c blocks := by
  obtain ⟨B, hB⟩ := hne
  obtain ⟨-, -, hZ, W, hW, hBW, hlo⟩ := (mem_filteredFrom E cfg c blocks B).1 hB
  have hZW := preceq_trans hZ hBW
  exact (mem_filteredFrom E cfg c blocks c.Z).2
    ⟨hclosed W hW c.Z hZW, hFZ, preceq_refl _, W, hW, hZW, hlo⟩

/-- [pin fj.frameFeasible.v1] (4) (any controls, any ancestor-closed block set)
A block of the filtered tree below lo has a child in the filtered tree toward
its witness (r148 line 229, "Below lo every viable node has a viable child"). -/
theorem filteredFrom_viable_child (c : Controls V) (blocks : Finset (FGBlock V))
    (hclosed : ∀ B ∈ blocks, ∀ A, FGBlock.Preceq A B → A ∈ blocks)
    (B : FGBlock V) (hB : B ∈ filteredFrom E cfg c blocks) (hlow : hOf E cfg B < c.lo) :
    ∃ C ∈ filteredFrom E cfg c blocks, C.parent = B := by
  obtain ⟨-, hF, hZ, W, hW, hBW, hlo⟩ := (mem_filteredFrom E cfg c blocks B).1 hB
  have hne : B ≠ W := by
    rintro rfl
    simp only [Height] at *
    omega
  obtain ⟨C, hCp, hCg, hCW⟩ := child_toward hBW hne
  have hBC : FGBlock.Preceq B C := by
    cases C with
    | genesis => exact absurd rfl hCg
    | node p s r_s r rs =>
        simp only [FGBlock.parent] at hCp
        subst hCp
        exact preceq_parent_node p s r_s r rs
  exact ⟨C, (mem_filteredFrom E cfg c blocks C).2
    ⟨hclosed W hW C hCW, preceq_trans hF hBC, preceq_trans hZ hBC, W, hW, hCW, hlo⟩, hCp⟩

/-- [pin fg.frameCompat.v1] (part (ii); was `fBasis_lexMax`) If the block set
holds a block whose J extends F, the selected pair extends F and is at least
that block's pair: the `(0, genesis)` fallback is not used. -/
theorem lexMax_of_candidate (F : FGBlock V) (Vw : View V) (hinj : ViewRootInj Vw)
    (K : FGBlock V) (hK : K ∈ Vw) (hFK : FGBlock.Preceq F (derive E cfg K).J) :
    FGBlock.Preceq F (fjControls E cfg F Vw).J ∧
      lexKey ((derive E cfg K).h_j, (derive E cfg K).J) ≤
        lexKey ((fjControls E cfg F Vw).j, (fjControls E cfg F Vw).J) := by
  obtain ⟨K', -, hFK', hlex, hmax⟩ := lexMax_spec E cfg F Vw hinj ⟨K, hK, hFK⟩
  have hJ : (fjControls E cfg F Vw).J = (derive E cfg K').J := by
    change (lexMax E cfg F Vw).2 = _
    rw [hlex]
  have hj : (fjControls E cfg F Vw).j = (derive E cfg K').h_j := by
    change (lexMax E cfg F Vw).1 = _
    rw [hlex]
  rw [hJ, hj]
  exact ⟨hFK', hmax K hK hFK⟩

-- The pinned statement keeps `hinj` and `hKF`; this proof does not need them.
set_option linter.unusedVariables false in
/-- [pin fj.frameFeasible.v1] (2) (fjFrame special case) D is not empty when
(a) the set holds a block K whose chain finalizes F, and (b) every block of the
set above `h_F(K)` extends F (pure fg.finalLock.v1, r148 fj-redteam.md:222–230). -/
theorem fjFrame_D_nonempty (F : FGBlock V) (Vw : View V) (hinj : ViewRootInj Vw)
    (K : FGBlock V) (hK : K ∈ Vw) (hKF : (derive E cfg K).F = F)
    (hext : ∀ W ∈ Vw, (derive E cfg K).h_F < hOf E cfg W → FGBlock.Preceq F W) :
    (fjFrame E cfg F Vw).D.Nonempty := by
  -- The frontier block `W` has height `H ≥ h(K) > h_F(K)`, so it extends F.
  -- The root test uses the contest bit only, so no collision freedom is needed.
  obtain ⟨W, hW, hWH⟩ := exists_frontier E cfg Vw ⟨K, hK⟩
  have hKH := le_frontier E cfg hK
  have hFh := finalized_below_height E cfg K
  have hFW : FGBlock.Preceq F W := by
    apply hext W hW
    rw [hWH]
    unfold hOf at hKH
    simp only [Height] at *
    omega
  refine ⟨W, ?_⟩
  rw [fjFrame_D, mem_filteredFrom]
  refine ⟨hW, hFW, ?_, W, hW, preceq_refl W, ?_⟩
  · unfold Controls.Z
    split_ifs with hr
    · exact fjControls_J_preceq_of_rootIsJ E cfg F Vw hr W hW hWH
    · exact hFW
  · rw [hWH]
    exact Controls.lo_le_H _

/-- [pin fj.frameFeasible.v1] (3) (fjFrame special case) Z ∈ D under (a) and
(b) of part (2), in an ancestor-closed set. -/
theorem fjFrame_Z_mem_D (F : FGBlock V) (Vw : View V) (hinj : ViewRootInj Vw)
    (hclosed : ∀ B ∈ Vw, ∀ A, FGBlock.Preceq A B → A ∈ Vw)
    (K : FGBlock V) (hK : K ∈ Vw) (hKF : (derive E cfg K).F = F)
    (hext : ∀ W ∈ Vw, (derive E cfg K).h_F < hOf E cfg W → FGBlock.Preceq F W) :
    (fjFrame E cfg F Vw).Z ∈ (fjFrame E cfg F Vw).D := by
  have hFZ : FGBlock.Preceq (fjControls E cfg F Vw).F (fjControls E cfg F Vw).Z := by
    unfold Controls.Z
    split_ifs
    · exact (lexMax_of_candidate E cfg F Vw hinj K hK
        (hKF ▸ derive_F_preceq_J E cfg K)).1
    · exact preceq_refl _
  have hne := fjFrame_D_nonempty E cfg F Vw hinj K hK hKF hext
  rw [fjFrame_D] at hne ⊢
  exact filteredFrom_Z_mem E cfg _ Vw hclosed hFZ hne

/-- [pin fj.frameFeasible.v1] (2) and (3), ALFS store form: with the store
controls on the full admitted tree, the filtered tree is not empty and holds Z.
(a) is `StoreInv.Fcar`; (b) is the hypothesis. -/
theorem storeFrame_feasible (st : Store V) (h : StoreInv E cfg st) (hinj : ViewRootInj st.TF)
    (hext : ∀ K ∈ st.TF, (derive E cfg K).F = st.F →
      ∀ W ∈ st.TF, (derive E cfg K).h_F < hOf E cfg W → FGBlock.Preceq st.F W) :
    (storeFrame E cfg st st.TF).Nonempty ∧
      (storeControls E cfg st).Z ∈ storeFrame E cfg st st.TF := by
  obtain ⟨K, hK, hKF⟩ := h.Fcar
  have hcl := ancestor_closed_of_parent_closed st.TF h.closed
  have hZ : (storeControls E cfg st).Z = (fjFrame E cfg st.F st.TF).Z := by
    rw [storeControls_eq_fjControls E cfg st h]
    rfl
  rw [storeFrame_full E cfg st h, hZ]
  exact ⟨fjFrame_D_nonempty E cfg st.F st.TF hinj K hK hKF (hext K hK hKF),
    fjFrame_Z_mem_D E cfg st.F st.TF hinj hcl K hK hKF (hext K hK hKF)⟩

/-! ## Acceptance viability and frame viability -/

-- The pinned statement keeps `h`; this proof does not need it.
set_option linter.unusedVariables false in
/-- [pin fj.frame.v4] (viable_tree; store form, full tree) The ALFS filtered
tree is inside DC's acceptance viability. -/
theorem frameViable_subset_accept (st : Store V) (h : StoreInv E cfg st) :
    storeFrame E cfg st st.TF ⊆ acceptViable E cfg st := by
  intro B hB
  obtain ⟨hBT, hF, -, W, hW, hBW, hlo⟩ :=
    (mem_filteredFrom E cfg (storeControls E cfg st) st.TF B).1 hB
  have hlo' : st.h_max - 1 ≤ hOf E cfg W :=
    le_trans (Controls.H_sub_one_le_lo (storeControls E cfg st)) hlo
  simp only [acceptViable, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hBT, hF, W, hW, hBW, hlo'⟩

-- The pinned statement keeps `h`; this proof does not need it.
set_option linter.unusedVariables false in
/-- [helper] (store form, full tree) Without a contest and with root F, they are
equal. -/
theorem frameViable_eq_accept_of_noContest (st : Store V) (h : StoreInv E cfg st)
    (hnc : (storeControls E cfg st).contest = false)
    (hZ : (storeControls E cfg st).rootIsJ = false) :
    storeFrame E cfg st st.TF = acceptViable E cfg st := by
  have hZF : (storeControls E cfg st).Z = st.F := by
    unfold Controls.Z
    rw [hZ]
    rfl
  have hlo : (storeControls E cfg st).lo = st.h_max - 1 := by
    unfold Controls.lo
    rw [hnc]
    rfl
  ext B
  rw [storeFrame, mem_filteredFrom, hZF, hlo]
  simp only [acceptViable, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hBT, hF, -, hw⟩
    exact ⟨hBT, hF, hw⟩
  · rintro ⟨hBT, hF, hw⟩
    exact ⟨hBT, hF, hF, hw⟩

-- The pinned statement keeps `h`; this proof does not need it.
set_option linter.unusedVariables false in
/-- [helper] (store form, full tree) Without a contest and with root J, the
filtered tree is acceptance viability cut at J. -/
theorem frameViable_eq_accept_cut (st : Store V) (h : StoreInv E cfg st)
    (hZ : (storeControls E cfg st).rootIsJ = true) :
    storeFrame E cfg st st.TF =
      (acceptViable E cfg st).filter (fun B => FGBlock.preceq st.J B) := by
  have hnc : (storeControls E cfg st).contest = false := by
    unfold Controls.rootIsJ at hZ
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hZ
    exact hZ.2
  have hZJ : (storeControls E cfg st).Z = st.J := by
    unfold Controls.Z
    rw [hZ]
    rfl
  have hlo : (storeControls E cfg st).lo = st.h_max - 1 := by
    unfold Controls.lo
    rw [hnc]
    rfl
  ext B
  rw [storeFrame, mem_filteredFrom, hZJ, hlo]
  simp only [acceptViable, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
  simp only [FGBlock.Preceq]
  constructor
  · rintro ⟨hBT, hF, hJ, hw⟩
    exact ⟨⟨hBT, hF, hw⟩, hJ⟩
  · rintro ⟨⟨hBT, hF, hw⟩, hJ⟩
    exact ⟨hBT, hF, hJ, hw⟩

/-! ## G18: frame facts from the live caches -/

/-- [pin fj.frame.v1] [GLY G18] R10 at a store read (S1b:566–570).
The table and band bounds use the live caches. The finality clauses hold for
each held carrier of F; `StoreInv.Fcar` supplies such a carrier. Its `h_F` is
the certificate height, not the state height of F. No run premise is needed.
The last disjunction does not assert that every held block at `lo` extends F:
in the top-J case, a stale branch can remain in the cumulative tree. -/
theorem frame_facts (st : Store V) (h : StoreInv E cfg st)
    (hinj : ViewRootInj st.TF) :
    let c := storeControls E cfg st
    c.j < c.H ∧
      (c.Z, c.lo) =
        (if c.H = c.j + 1 ∧ c.contest = false then (c.J, c.H - 1)
         else if c.contest then (st.F, c.H) else (st.F, c.H - 1)) ∧
      (c.lo = c.H - 1 ∨ c.lo = c.H) ∧
      (c.rootIsJ = true ↔ c.H = c.j + 1 ∧ c.contest = false) ∧
      ∀ K ∈ st.TF, (derive E cfg K).F = st.F →
        (derive E cfg K).h_F ≤ c.j ∧
          ((derive E cfg K).h_F < c.lo ∨
            (c.Z = c.J ∧ c.lo = c.j ∧ c.j = c.H - 1 ∧
              c.j + 1 = c.H ∧ FGBlock.Preceq st.F c.J)) := by
  let c := storeControls E cfg st
  obtain ⟨K₀, hK₀, hK₀F⟩ := h.Fcar
  obtain ⟨L, hL, -, hp, hmax⟩ := lexMax_spec E cfg st.F st.TF
    hinj ⟨K₀, hK₀, hK₀F ▸ derive_F_preceq_J E cfg K₀⟩
  have hj : c.j = (derive E cfg L).h_j := congrArg Prod.fst (h.pair.trans hp)
  have hjH : c.j < c.H := by
    rw [hj]
    exact lt_of_lt_of_le (justified_below_height E cfg L)
      (show (derive E cfg L).h ≤ st.h_max by
        rw [h.hmax]
        exact le_frontier E cfg hL)
  have hFj : ∀ K ∈ st.TF, (derive E cfg K).F = st.F →
      (derive E cfg K).h_F ≤ c.j := by
    intro K hK hKF
    rw [hj]
    exact le_trans (heights_ordered E cfg K)
      (fst_le_of_lexKey_le (hmax K hK (hKF ▸ derive_F_preceq_J E cfg K)))
  have hroot : c.rootIsJ = true ↔ c.H = c.j + 1 ∧ c.contest = false := by
    unfold Controls.rootIsJ
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
  have htable : (c.Z, c.lo) =
      (if c.H = c.j + 1 ∧ c.contest = false then (c.J, c.H - 1)
       else if c.contest then (st.F, c.H) else (st.F, c.H - 1)) := by
    have hF : c.F = st.F := rfl
    unfold Controls.Z Controls.lo Controls.rootIsJ
    by_cases hc : c.contest = true
    · simp [hc, hF]
    · have hc : c.contest = false := Bool.eq_false_iff.mpr hc
      by_cases htop : c.H = c.j + 1 <;>
        simp [hc, htop, hF]
  refine ⟨hjH, htable, ?_, hroot, ?_⟩
  · unfold Controls.lo
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · intro K hK hKF
    have hle := hFj K hK hKF
    refine ⟨hle, ?_⟩
    by_cases hlt : (derive E cfg K).h_F < c.lo
    · exact Or.inl hlt
    · have hc : c.contest = false := by
        cases heq : c.contest with
        | false => rfl
        | true =>
            have hlo : c.lo = c.H := by unfold Controls.lo; rw [heq]; rfl
            rw [hlo] at hlt
            exact False.elim (hlt (lt_of_le_of_lt hle hjH))
      have hlo : c.lo = c.H - 1 := by unfold Controls.lo; rw [hc]; rfl
      have htop : c.H = c.j + 1 := by
        simp only [Height] at *
        omega
      have hZ : c.Z = c.J := by
        unfold Controls.Z
        rw [hroot.mpr ⟨htop, hc⟩]
        rfl
      have hjH₁ : c.j = c.H - 1 := by rw [htop, Nat.add_sub_cancel]
      exact Or.inr ⟨hZ, hlo.trans hjH₁.symm, hjH₁, htop.symm, h.FJ⟩

end AvailableChain.KitFG
end
