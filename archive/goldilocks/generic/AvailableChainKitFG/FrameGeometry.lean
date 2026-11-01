module
public import AvailableChainKitFG.FrameBridge
public import AvailableChainKitFG.StoreSafetyDef
public import AvailableChainKitFG.FrameSelection
public import AvailableChainKitFG.JustificationLawsDef

public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

variable {V : Type} [DecidableEq V]

/-- The filter contains exactly the blocks above both anchors with a height witness. -/
theorem mem_filteredFromView (H : FGHeightView V) (c : Controls V)
    (blocks : Finset (FGBlock V)) (B : FGBlock V) :
    B ∈ filteredFromView H c blocks ↔ B ∈ blocks ∧ FGBlock.Preceq c.F B ∧
      FGBlock.Preceq c.Z B ∧ ∃ W ∈ blocks, FGBlock.Preceq B W ∧ c.lo ≤ (H W).h := by
  rw [filteredFromView_def]
  simp only [Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
  simp only [FGBlock.Preceq, and_assoc]

variable [Fintype V] [RowCodec V]

/-- The old filter membership test reads view heights through the bridge. -/
theorem mem_filteredFrom_of_bridge (E : Electorate V) (cfg : FGConfig)
    (H : FGHeightView V) (hb : HeightBridge E cfg H) (c : Controls V)
    (blocks : Finset (FGBlock V)) (B : FGBlock V) :
    B ∈ filteredFrom E cfg c blocks ↔ B ∈ blocks ∧ FGBlock.Preceq c.F B ∧
      FGBlock.Preceq c.Z B ∧ ∃ W ∈ blocks, FGBlock.Preceq B W ∧ c.lo ≤ (H W).h := by
  rw [filteredFrom_of_bridge E cfg H hb]
  exact mem_filteredFromView H c blocks B

/-- [ROOT-DIGEST W1; DC RootInjectiveOnAncestors] Candidate J values are ancestors. -/
theorem candidateJ_rootInj_of_viewRootInj (E : Electorate V) (H : FGHeightView V)
    (hH : FGHeightLaws E H) (T : View V) (hinj : ViewRootInj T) :
    ∀ A ∈ T, ∀ B ∈ T, (H A).J.root = (H B).J.root → (H A).J = (H B).J := by
  intro A hA B hB hr
  exact hinj _ _
    ⟨A, hA, preceq_trans (hH.justified_preceq_entry A) (hH.entry_preceq A)⟩
    ⟨B, hB, preceq_trans (hH.justified_preceq_entry B) (hH.entry_preceq B)⟩ hr

omit [Fintype V] in
/-- The structural pair fields select the same pair as the view selector. -/
private theorem frameGeometry_lexMax_of_inv (H : FGHeightView V) (f : FGFinalityView V)
    (st : Store V) (hI : FGStoreInvariant H f st)
    (hroots : ∀ A ∈ st.TF, ∀ B ∈ st.TF,
      (H A).J.root = (H B).J.root → (H A).J = (H B).J) :
    lexMaxView H st.F st.TF = (st.h_j, st.J) := by
  rw [lexMaxView_def]
  dsimp only
  let candidates := (st.TF.filter (fun W => FGBlock.preceq st.F (H W).J)).image
    (fun W => ((H W).h_j, (H W).J))
  have hmem : ∀ q, q ∈ candidates ↔
      ∃ W ∈ st.TF, FGBlock.Preceq st.F (H W).J ∧ ((H W).h_j, (H W).J) = q := by
    intro q
    simp only [candidates, Finset.mem_image, Finset.mem_filter, FGBlock.Preceq, and_assoc]
  obtain ⟨C, hC, hFC, hj, hJ⟩ := hI.pair.1
  have hp : (st.h_j, st.J) ∈ candidates :=
    (hmem _).2 ⟨C, hC, hFC, by rw [hj, hJ]⟩
  have hsup : candidates.sup lexKey = lexKey (st.h_j, st.J) := by
    apply le_antisymm
    · apply Finset.sup_le
      intro q hq
      obtain ⟨W, hW, hFW, rfl⟩ := (hmem q).1 hq
      exact hI.pair.2 W hW hFW
    · exact Finset.le_sup hp
  change (pickPair candidates (fun p => decide (lexKey p = candidates.sup lexKey))).getD
    (0, .genesis) = _
  rw [hsup, pickPair_eq_of_unique _ _ _ hp (by simp)]
  · rfl
  · intro q hq hk
    obtain ⟨W, hW, _, rfl⟩ := (hmem q).1 hq
    have hk' : ((H W).h_j, (H W).J.root.value) = (st.h_j, st.J.root.value) :=
      toLex.injective (show lexKey ((H W).h_j, (H W).J) = lexKey (st.h_j, st.J) from
        of_decide_eq_true hk)
    exact Prod.ext (Prod.mk.inj hk').1
      (by
        rw [hJ] at hk' ⊢
        exact hroots W hW C hC (BlockId.ext (Prod.mk.inj hk').2))

omit [Fintype V] in
/-- The structural invariant makes the store controls equal to the full-tree controls. -/
theorem storeControlsView_eq_fjControlsView_of_inv
    (H : FGHeightView V) (f : FGFinalityView V)
    (st : Store V) (hI : FGStoreInvariant H f st)
    (hroots : ∀ A ∈ st.TF, ∀ B ∈ st.TF,
      (H A).J.root = (H B).J.root → (H A).J = (H B).J) :
    storeControlsView H st = fjControlsView H st.F st.TF := by
  rw [storeControlsView_def, fjControlsView_def, frontierView_def,
    frameGeometry_lexMax_of_inv H f st hI hroots, ← hI.hmax]

omit [Fintype V] in
/-- The store frame on the full tree is the domain of its FJ frame. -/
theorem storeFrameView_full_of_inv (H : FGHeightView V) (f : FGFinalityView V)
    (st : Store V) (hI : FGStoreInvariant H f st)
    (hroots : ∀ A ∈ st.TF, ∀ B ∈ st.TF,
      (H A).J.root = (H B).J.root → (H A).J = (H B).J) :
    storeFrameView H st st.TF = (fjFrameView H st.F st.TF).D := by
  rw [storeFrameView_def, fjFrameView_def,
    storeControlsView_eq_fjControlsView_of_inv H f st hI hroots]

/-- Crossed entries below a block bound the floor of an uncontested frame. -/
theorem storeFrameView_height_of_crossed_prefix_of_inv
    (E : Electorate V) (H : FGHeightView V) (hH : FGHeightLaws E H)
    (f : FGFinalityView V) (st : Store V) (hI : FGStoreInvariant H f st)
    (B : FGBlock V) (hn : (storeControlsView H st).contest = false)
    (hc : ∀ W ∈ st.TF, ∀ U, FGBlock.Preceq U W → (H U).h < (H W).h →
      FGBlock.Preceq (H U).T_h B) :
    (storeControlsView H st).lo ≤ (H B).h := by
  have hlo : (storeControlsView H st).lo = st.h_max - 1 := by
    change (if (storeControlsView H st).contest then _ else _) = _
    rw [hn]
    rfl
  rw [hlo]
  by_cases hh : st.h_max ≤ 1
  · exact (Nat.sub_eq_zero_of_le hh) ▸ Nat.zero_le _
  obtain ⟨W, hW, hsup⟩ :=
    Finset.exists_mem_eq_sup st.TF ⟨_, hI.gen⟩ (fun W => (H W).h)
  have hw : (H W).h = st.h_max := by
    have hm := hI.hmax
    rw [hsup] at hm
    simp only [Height] at *
    omega
  obtain ⟨U, hU, hu, _⟩ := hH.height_crossing W (st.h_max - 1)
    (by simp only [Height] at *; omega) (by simp only [Height] at *; omega)
  have hm := hH.h_mono (hc W hW U hU (by simp only [Height] at *; omega))
  rw [hH.entry_same_height, hu] at hm
  exact hm

/-- The height bridge supplies the three laws for the justified entry. -/
theorem FGJustificationLaws.of_bridge {E : Electorate V} {cfg : FGConfig}
    {v : FGHeightView V} (hb : HeightBridge E cfg v) : FGJustificationLaws v := by
  have heq : v = simplexHeightView E cfg := funext hb
  rw [heq]
  exact ⟨J_is_entry E cfg, entry_height E cfg, justified_zero_is_genesis E cfg⟩

/-- A contest has a crossed entry that is incompatible with the stored J. -/
private theorem frameGeometry_contest_crossing_of_inv
    (E : Electorate V) (H : FGHeightView V) (hH : FGHeightLaws E H)
    (f : FGFinalityView V) (st : Store V) (hI : FGStoreInvariant H f st)
    (hJ : FGJustificationLaws H) (htop : st.h_max = st.h_j + 1)
    (W : FGBlock V) (hW : (H W).h = st.h_max) (hn : ¬ FGBlock.Preceq st.J W) :
    ∃ U, FGBlock.Preceq U W ∧ (H U).h < (H W).h ∧
      ¬ (FGBlock.Preceq st.J (H U).T_h ∨ FGBlock.Preceq (H U).T_h st.J) := by
  obtain ⟨K, _, _, hj, hJK⟩ := hI.pair.1
  have hnz : st.h_j ≠ 0 := by
    intro hz
    exact hn (hJK ▸ hJ.J_zero K (hj.symm.trans hz) ▸ genesis_preceq W)
  obtain ⟨U, hU, hh, _⟩ := hH.height_crossing W st.h_j
    (Nat.one_le_iff_ne_zero.mpr hnz)
    (by rw [hW, htop]; exact Nat.lt_succ_self _)
  refine ⟨U, hU, by rw [hh, hW, htop]; exact Nat.lt_succ_self _, ?_⟩
  intro hc
  have hJW : FGBlock.Preceq (H U).T_h W := preceq_trans (hH.entry_preceq U) hU
  have hhJ : (H st.J).h = (H U).h := by
    rw [hJK, hJ.J_height K (fun hz => hnz (hj.trans hz))]
    exact hj.symm.trans hh.symm
  have heJ : (H st.J).T_h = st.J := hJK ▸ hJ.J_entry K
  rcases hc with hc | hc
  · exact hn (preceq_trans hc hJW)
  · have he : (H U).T_h = st.J := by
      have hp := hH.entry_plateau hc ((hH.entry_same_height U).trans hhJ.symm)
      rw [hH.entry_idem, heJ] at hp
      exact hp
    exact hn (he ▸ hJW)

/-- Compatible crossed entries exclude a contest in the view frame. -/
theorem storeFrameView_noContest_of_crossed_of_inv
    (E : Electorate V) (H : FGHeightView V) (hH : FGHeightLaws E H)
    (f : FGFinalityView V) (st : Store V) (hI : FGStoreInvariant H f st)
    (hJ : FGJustificationLaws H)
    (hc : ∀ W ∈ st.TF, ∀ U, FGBlock.Preceq U W → (H U).h < (H W).h →
      FGBlock.Preceq st.J (H U).T_h ∨ FGBlock.Preceq (H U).T_h st.J) :
    (storeControlsView H st).contest = false := by
  apply Bool.eq_false_iff.mpr
  intro ht
  change (decide (st.h_max = st.h_j + 1) && decide _) = true at ht
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at ht
  obtain ⟨htop, W, hW, hh, hn⟩ := ht
  obtain ⟨U, hU, hlt, hbad⟩ :=
    frameGeometry_contest_crossing_of_inv E H hH f st hI hJ htop W hh hn
  exact hbad (hc W hW U hU hlt)

/-- A block compatible with J and crossed entries precedes every contest witness. -/
theorem storeFrameView_contest_of_compatible_of_inv
    (E : Electorate V) (H : FGHeightView V) (hH : FGHeightLaws E H)
    (f : FGFinalityView V) (st : Store V) (hI : FGStoreInvariant H f st)
    (hJ : FGJustificationLaws H) (B : FGBlock V)
    (hJB : FGBlock.Preceq st.J B ∨ FGBlock.Preceq B st.J)
    (hc : ∀ W ∈ st.TF, ∀ U, FGBlock.Preceq U W → (H U).h < (H W).h →
      FGBlock.Preceq (H U).T_h B ∨ FGBlock.Preceq B (H U).T_h)
    (ht : (storeControlsView H st).contest = true) :
    FGBlock.Preceq B st.J ∧ ∀ W ∈ st.TF, (H W).h = st.h_max →
      ¬ FGBlock.Preceq st.J W → FGBlock.Preceq B W := by
  have ht' := ht
  change (decide (st.h_max = st.h_j + 1) && decide _) = true at ht'
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at ht'
  obtain ⟨htop, W₀, hW₀, hh₀, hn₀⟩ := ht'
  have step : ∀ W ∈ st.TF, (H W).h = st.h_max → ¬ FGBlock.Preceq st.J W →
      FGBlock.Preceq B st.J ∧ FGBlock.Preceq B W := by
    intro W hW hh hn
    obtain ⟨U, hU, hlt, hbad⟩ :=
      frameGeometry_contest_crossing_of_inv E H hH f st hI hJ htop W hh hn
    have hBW : FGBlock.Preceq B (H U).T_h := by
      rcases hc W hW U hU hlt with hu | hu
      · rcases hJB with hj | hj
        · exact (hbad (preceq_total_of_common hj hu)).elim
        · exact (hbad (Or.inr (preceq_trans hu hj))).elim
      · exact hu
    have hBJ : FGBlock.Preceq B st.J := by
      rcases hJB with hj | hj
      · exact (hbad (Or.inl (preceq_trans hj hBW))).elim
      · exact hj
    exact ⟨hBJ, preceq_trans hBW (preceq_trans (hH.entry_preceq U) hU)⟩
  exact ⟨(step W₀ hW₀ hh₀ hn₀).1, fun W hW hh hn => (step W hW hh hn).2⟩

/-- Compatibility retains a stored block above F unless the frame anchor covers it. -/
theorem storeFrameView_retention_of_compatible_of_inv
    (E : Electorate V) (H : FGHeightView V) (hH : FGHeightLaws E H)
    (f : FGFinalityView V) (st : Store V) (hI : FGStoreInvariant H f st)
    (hJ : FGJustificationLaws H) (B : FGBlock V)
    (hB : B ∈ st.TF) (hFB : FGBlock.Preceq st.F B)
    (hJB : FGBlock.Preceq st.J B ∨ FGBlock.Preceq B st.J)
    (hc : ∀ W ∈ st.TF, ∀ U, FGBlock.Preceq U W → (H U).h < (H W).h →
      FGBlock.Preceq (H U).T_h B ∨ FGBlock.Preceq B (H U).T_h) :
    FGBlock.Preceq B (storeControlsView H st).Z ∨
      B ∈ filteredFromView H (storeControlsView H st) st.TF := by
  let c := storeControlsView H st
  by_cases hBZ : FGBlock.Preceq B c.Z
  · exact Or.inl hBZ
  right
  have hZB : FGBlock.Preceq c.Z B := by
    change FGBlock.Preceq (if c.rootIsJ then st.J else st.F) B
    cases hr : c.rootIsJ
    · exact hFB
    · rcases hJB with hj | hj
      · exact hj
      · exact (hBZ (by
          change FGBlock.Preceq B (if c.rootIsJ then st.J else st.F)
          rw [hr]; exact hj)).elim
  apply (mem_filteredFromView H c st.TF B).2
  refine ⟨hB, hFB, hZB, ?_⟩
  cases ht : c.contest with
  | true =>
    have hx := storeFrameView_contest_of_compatible_of_inv E H hH f st hI hJ B hJB hc ht
    have ht' := ht
    change (decide (st.h_max = st.h_j + 1) && decide _) = true at ht'
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at ht'
    obtain ⟨_, W, hW, hh, hn⟩ := ht'
    exact ⟨W, hW, hx.2 W hW hh hn, hh ▸ Controls.lo_le_H c⟩
  | false =>
    have hlo : c.lo = st.h_max - 1 := by
      change (if c.contest then _ else _) = _
      rw [ht]
      rfl
    by_cases hsmall : st.h_max ≤ 1
    · exact ⟨B, hB, preceq_refl B, by rw [hlo]; simp only [Height] at *; omega⟩
    obtain ⟨W, hW, hsup⟩ :=
      Finset.exists_mem_eq_sup st.TF ⟨_, hI.gen⟩ (fun W => (H W).h)
    have hw : (H W).h = st.h_max := by
      have hm := hI.hmax
      rw [hsup] at hm
      simp only [Height] at *
      omega
    obtain ⟨U, hU, hu, _⟩ := hH.height_crossing W (st.h_max - 1)
      (by simp only [Height] at *; omega) (by simp only [Height] at *; omega)
    rcases hc W hW U hU (by simp only [Height] at *; omega) with heB | hBe
    · refine ⟨B, hB, preceq_refl B, ?_⟩
      have hm := hH.h_mono heB
      rw [hH.entry_same_height] at hm
      exact hlo.trans hu.symm ▸ hm
    · exact ⟨W, hW, preceq_trans hBe (preceq_trans (hH.entry_preceq U) hU),
        by rw [hlo, hw]; simp only [Height] at *; omega⟩

end AvailableChain.KitFG
end
