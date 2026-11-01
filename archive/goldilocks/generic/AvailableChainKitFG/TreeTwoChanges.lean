module
public import AvailableChainKitFG.TreeCorrespondence
public import AvailableChainKitFG.TwoChanges

public section

namespace AvailableChain.KitFG
open AvailableChain.SimplexFG

local macro "homega" : tactic => `(tactic| ((try simp only [Height] at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]
variable {E : Electorate V} (v : FGHeightView V) (hL : FGHeightLaws E v)
variable {F : FGBlock V} {Vw : View V} {m : Height} {Jm : FGBlock V}

omit [Fintype V] [RowCodec V] [DecidableEq V] in
/-- Repairs `le_frontier` for the supplied height view. -/
theorem treeLe_frontier {W : FGBlock V} (hW : W ∈ Vw) :
    (v W).h ≤ frontierView v Vw :=
  (Finset.le_sup (f := fun B => (v B).h) hW).trans (Nat.le_max_left _ _)

/-- Repairs `phaseOf` for the guarded tree frame. The FJ phase of a view: no top J, top J
uncontested, or top J contested. -/
def treePhaseOf (F : FGBlock V) (Vw : View V) : Phase :=
  let c := treeFjControlsView v F Vw
  if c.H = c.j + 1 then (if c.contest then .contested else .uncontested) else .gap

/-- Repairs `EJ` for the guarded tree frame. E_J: the view holds a carrier of the pair `(m−1,
Jm)`. -/
def treeEJ (m : Height) (Jm : FGBlock V) (Vw : View V) : Prop :=
  ∃ K ∈ Vw, (v K).h_j = m - 1 ∧ (v K).J = Jm

omit [Fintype V] [RowCodec V] [DecidableEq V] in
/-- Repairs the `EJ` evidence API for a supplied height view. -/
theorem treeEJ_def (m : Height) (Jm : FGBlock V) (Vw : View V) :
    treeEJ v m Jm Vw = (∃ K ∈ Vw, (v K).h_j = m - 1 ∧ (v K).J = Jm) := by rfl

/-- Repairs `nFrame` for the guarded tree frame. The normalized frame of a view: `(H, lo, Ẑ)`.
-/
def treeNFrame (F : FGBlock V) (Vw : View V) : NFrame V :=
  let c := treeFjControlsView v F Vw
  ⟨c.H, c.lo, if c.rootIsJ then some c.J else none⟩

/-! ## The phase and the normalized frame of the controls -/

omit [Fintype V] in
/-- Repairs `phaseOf_eq` for the guarded tree frame. `treePhaseOf` reads H, j and the contest
bit of `fjControls`. -/
theorem treePhaseOf_eq (F : FGBlock V) (Vw : View V) :
    treePhaseOf v F Vw =
      if (treeFjControlsView v F Vw).H = (treeFjControlsView v F Vw).j + 1 then
        (if (treeFjControlsView v F Vw).contest then .contested else .uncontested)
      else .gap := by rfl

omit [Fintype V] in
/-- Repairs `nFrame_eq` for the guarded tree frame. `treeNFrame` reads H, lo, the root test and
J of `fjControls`. -/
theorem treeNFrame_eq (F : FGBlock V) (Vw : View V) :
    treeNFrame v F Vw = ⟨(treeFjControlsView v F Vw).H, (treeFjControlsView v F Vw).lo,
      if (treeFjControlsView v F Vw).rootIsJ
        then some (treeFjControlsView v F Vw).J else none⟩ := by rfl

omit [Fintype V] in
/-- Repairs `fjControls_contest` for the guarded tree frame. The contest bit of `fjControls`. -/
theorem treeFjControls_contest (F : FGBlock V) (Vw : View V) :
    (treeFjControlsView v F Vw).contest =
      (decide ((treeFjControlsView v F Vw).H = (treeFjControlsView v F Vw).j + 1) &&
        decide (∃ W ∈ Vw, FGBlock.Preceq F W ∧ (v W).h = (treeFjControlsView v F Vw).H ∧
          ¬ FGBlock.Preceq (treeFjControlsView v F Vw).J W)) := by rfl

omit [Fintype V] in
/-- Repairs `gap_of_ne` for the guarded tree frame. The gap phase: `H ≠ j + 1`. There is no
contest, the root is F, and `lo = H − 1`. -/
theorem treeGap_of_ne (F : FGBlock V) (Vw : View V)
    (hne : ¬ (treeFjControlsView v F Vw).H = (treeFjControlsView v F Vw).j + 1) :
    (treeFjControlsView v F Vw).contest = false ∧ (treeFjControlsView v F Vw).rootIsJ = false ∧
      treePhaseOf v F Vw = .gap ∧
      treeNFrame v F Vw =
        ⟨(treeFjControlsView v F Vw).H, (treeFjControlsView v F Vw).H - 1, none⟩ := by
  have hc : (treeFjControlsView v F Vw).contest = false := by
    rw [treeFjControls_contest, decide_eq_false hne, Bool.false_and]
  have hr : (treeFjControlsView v F Vw).rootIsJ = false := by
    unfold Controls.rootIsJ
    rw [decide_eq_false hne, Bool.false_and]
  refine ⟨hc, hr, ?_, ?_⟩
  · rw [treePhaseOf_eq, ite_eq_right hne]
  · rw [treeNFrame_eq, hr, ite_eq_right Bool.false_ne_true]
    unfold Controls.lo
    rw [hc, ite_eq_right Bool.false_ne_true]

omit [Fintype V] in
/-- Repairs `top_contest` for the guarded tree frame. At `H = j + 1`, the contest bit is the
contest test alone. -/
theorem treeTop_contest (F : FGBlock V) (Vw : View V)
    (htop : (treeFjControlsView v F Vw).H = (treeFjControlsView v F Vw).j + 1) :
    (treeFjControlsView v F Vw).contest =
      decide (∃ W ∈ Vw, FGBlock.Preceq F W ∧ (v W).h = (treeFjControlsView v F Vw).H ∧
        ¬ FGBlock.Preceq (treeFjControlsView v F Vw).J W) := by
  rw [treeFjControls_contest, decide_eq_true htop, Bool.true_and]

omit [Fintype V] in
/-- Repairs `top_uncontested` for the guarded tree frame. At `H = j + 1` with no contest: the
uncontested phase, root J, `lo = H − 1`. -/
theorem treeTop_uncontested (F : FGBlock V) (Vw : View V)
    (htop : (treeFjControlsView v F Vw).H = (treeFjControlsView v F Vw).j + 1)
    (hc : (treeFjControlsView v F Vw).contest = false) :
    treePhaseOf v F Vw = .uncontested ∧ (treeFjControlsView v F Vw).rootIsJ = true ∧
      treeNFrame v F Vw = ⟨(treeFjControlsView v F Vw).H, (treeFjControlsView v F Vw).H - 1,
        some (treeFjControlsView v F Vw).J⟩ := by
  have hr : (treeFjControlsView v F Vw).rootIsJ = true := by
    unfold Controls.rootIsJ
    rw [decide_eq_true htop, hc]
    rfl
  refine ⟨?_, hr, ?_⟩
  · rw [treePhaseOf_eq, ite_eq_left htop, hc, ite_eq_right Bool.false_ne_true]
  · rw [treeNFrame_eq, hr, ite_eq_left rfl]
    unfold Controls.lo
    rw [hc, ite_eq_right Bool.false_ne_true]

omit [Fintype V] in
/-- Repairs `top_contested` for the guarded tree frame. At `H = j + 1` with a contest: the
contested phase, root F, `lo = H`. -/
theorem treeTop_contested (F : FGBlock V) (Vw : View V)
    (htop : (treeFjControlsView v F Vw).H = (treeFjControlsView v F Vw).j + 1)
    (hc : (treeFjControlsView v F Vw).contest = true) :
    treePhaseOf v F Vw = .contested ∧ (treeFjControlsView v F Vw).rootIsJ = false ∧
      treeNFrame v F Vw = ⟨(treeFjControlsView v F Vw).H, (treeFjControlsView v F Vw).H, none⟩ := by
  have hr : (treeFjControlsView v F Vw).rootIsJ = false := by
    unfold Controls.rootIsJ
    rw [decide_eq_true htop, hc]
    rfl
  refine ⟨?_, hr, ?_⟩
  · rw [treePhaseOf_eq, ite_eq_left htop, hc, ite_eq_left rfl]
  · rw [treeNFrame_eq, hr, ite_eq_right Bool.false_ne_true]
    unfold Controls.lo
    rw [hc, ite_eq_left rfl]

omit [Fintype V] in
/-- Repairs `rootIsJ_iff` for the guarded tree frame. The root is J exactly in the uncontested
phase. -/
theorem treeRootIsJ_iff (F : FGBlock V) (Vw : View V) :
    (treeFjControlsView v F Vw).rootIsJ = true ↔ treePhaseOf v F Vw = .uncontested := by
  by_cases htop : (treeFjControlsView v F Vw).H = (treeFjControlsView v F Vw).j + 1
  · cases hc : (treeFjControlsView v F Vw).contest
    · obtain ⟨hp, hr, -⟩ := treeTop_uncontested v F Vw htop hc
      rw [hp, hr]
      simp
    · obtain ⟨hp, hr, -⟩ := treeTop_contested v F Vw htop hc
      rw [hp, hr]
      simp
  · obtain ⟨-, hr, hp, -⟩ := treeGap_of_ne v F Vw htop
    rw [hp, hr]
    simp

/-! ## The selected pair at the top of the band -/

omit [Fintype V] [RowCodec V] [DecidableEq V] in
/-- Repairs `one_le_frontier` for the guarded tree frame. The frontier is at least 1. -/
theorem treeOne_le_frontier (Vw : View V) : 1 ≤ frontierView v Vw := by
  unfold frontierView
  exact le_sup_right

include hL in
/-- Repairs `lexMax_fst_lt` for the guarded tree frame, including ambiguous selection. -/
theorem treeLexMax_fst_lt (G : FGBlock V) (Vw : View V) :
    (lexMaxView v G Vw).1 < frontierView v Vw := by
  rcases treeLexMax_spec v G Vw with hf | ⟨K, hK, -, hlex, -⟩
  · rw [hf]
    exact lt_of_lt_of_le Nat.zero_lt_one (treeOne_le_frontier v Vw)
  · rw [hlex]
    exact lt_of_lt_of_le (hL.justified_below_height K) (treeLe_frontier v hK)

include hL in
/-- Repairs `lexMax_top_of_carrier`: a carrier at `m − 1` selects its pair when all pairs
at that height name its J. Lower pairs need no collision-freedom premise. -/
theorem treeLexMax_top_of_carrier (G : FGBlock V) (Vw : View V)
    (hfront : frontierView v Vw = m) (K : FGBlock V) (hK : K ∈ Vw)
    (hKj : (v K).h_j = m - 1) (hGK : FGBlock.Preceq G (v K).J)
    (huniq : ∀ W ∈ Vw, (v W).h_j = m - 1 → (v W).J = (v K).J) :
    (lexMaxView v G Vw).1 = m - 1 := by
  have hlex := treeLexMax_eq_of_greatest v G Vw K hK hGK (by
    intro W hW _ hne
    have hlt := hL.justified_below_height W
    have hWH := treeLe_frontier v hW
    rw [hfront] at hWH
    have hh : (v W).h_j < (v K).h_j := by
      by_contra hn
      have heq : (v W).h_j = m - 1 := by homega
      exact hne (Prod.ext (heq.trans hKj.symm) (huniq W hW heq))
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hh))
  rw [hlex]
  exact hKj

omit [Fintype V] in
/-- Repairs `lexMax_carrier_of_top`: at `m ≥ 2` a selected height `m − 1` excludes the
fallback, including an ambiguous maximum. No height laws or root injectivity are needed. -/
theorem treeLexMax_carrier_of_top (G : FGBlock V) (Vw : View V) (hm : 2 ≤ m)
    (htop : (lexMaxView v G Vw).1 = m - 1) :
    ∃ K ∈ Vw, (v K).h_j = m - 1 ∧ FGBlock.Preceq G (v K).J ∧
      lexMaxView v G Vw = ((v K).h_j, (v K).J) := by
  rcases treeLexMax_spec v G Vw with hf | ⟨K, hK, hGK, hlex, -⟩
  · rw [hf] at htop
    dsimp only at htop
    homega
  · refine ⟨K, hK, ?_, hGK, hlex⟩
    rw [hlex] at htop
    exact htop

omit [Fintype V] in
/-- Repairs `EC` extraction from `fjControls_contest`: the witness must extend F. -/
theorem treeECView_of_contest (F : FGBlock V) (Vw : View V)
    (hc : (treeFjControlsView v F Vw).contest = true) :
    treeECView v F (frontierView v Vw) (lexMaxView v F Vw).2 Vw :=
  ((treeFjControlsView_contest_iff v F Vw).mp hc).2

omit [Fintype V] [RowCodec V] in
/-- Repairs the EC part of `evidence_mono` when F changes: require destination retention. -/
theorem treeECView_mono_of_retained {F' : FGBlock V} {S : View V}
    (hsub : Vw ⊆ S)
    (hretain : ∀ W ∈ S, (v W).h = m → FGBlock.Preceq F' W)
    (hc : treeECView v F m Jm Vw) : treeECView v F' m Jm S := by
  obtain ⟨W, hW, _, hh, hn⟩ := hc
  exact ⟨W, hsub hW, hretain W (hsub hW) hh, hh, hn⟩

/-! ## Items 1 and 2 -/

omit [Fintype V] [RowCodec V] in
/-- Repairs `evidence_mono` for the guarded tree frame. (item 2, first sentence) Views are
subsets of stores: a bit that is true in a view is true in every larger set. -/
theorem treeEvidence_mono {Vw S : View V} (h : Vw ⊆ S) :
    (treeEJ v m Jm Vw → treeEJ v m Jm S) ∧ (treeECView v F m Jm Vw → treeECView v F m Jm S) :=
  ⟨fun ⟨K, hK, hKj⟩ => ⟨K, h hK, hKj⟩, fun ⟨W, hW, hWm⟩ => ⟨W, h hW, hWm⟩⟩

include hL in
/-- Repairs `effFrame_of_bits` for the guarded tree frame. (item 1) At frontier m ≥ 2, when
every pair at m−1 in the view names Jm and F ⪯ Jm when E_J holds, the phase is given by the
bits, and the normalized frame is: gap (m, m−1, ◇); uncontested (m, m−1, Jm); contested (m, m,
◇). -/
theorem treeEffFrame_of_bits (hm : 2 ≤ m)
    (hfront : frontierView v Vw = m)
    (huniq : ∀ K ∈ Vw, (v K).h_j = m - 1 → (v K).J = Jm)
    (hFJ : treeEJ v m Jm Vw → FGBlock.Preceq F Jm) :
    (¬ treeEJ v m Jm Vw →
        treePhaseOf v F Vw = .gap ∧ treeNFrame v F Vw = ⟨m, m - 1, none⟩) ∧
      (treeEJ v m Jm Vw → ¬ treeECView v F m Jm Vw →
        treePhaseOf v F Vw = .uncontested ∧ treeNFrame v F Vw = ⟨m, m - 1, some Jm⟩) ∧
      (treeEJ v m Jm Vw → treeECView v F m Jm Vw →
        treePhaseOf v F Vw = .contested ∧ treeNFrame v F Vw = ⟨m, m, none⟩) := by
  have hH : (treeFjControlsView v F Vw).H = m := hfront
  have hlt : (treeFjControlsView v F Vw).j < m := by
    have := treeLexMax_fst_lt v hL F Vw
    rw [hfront] at this
    exact this
  -- With E_J, the selected pair is `(m − 1, Jm)`.
  have htopJ : treeEJ v m Jm Vw →
      (treeFjControlsView v F Vw).j = m - 1 ∧ (treeFjControlsView v F Vw).J = Jm := by
    intro hJ
    obtain ⟨K, hK, hKj, hKJ⟩ := hJ
    have htop := treeLexMax_top_of_carrier v hL F Vw hfront K hK hKj
      (by rw [hKJ]; exact hFJ ⟨K, hK, hKj, hKJ⟩)
      (fun W hW hh => (huniq W hW hh).trans hKJ.symm)
    obtain ⟨K', hK', hK'j, -, hlex⟩ := treeLexMax_carrier_of_top v F Vw hm htop
    refine ⟨htop, ?_⟩
    change (lexMaxView v F Vw).2 = Jm
    rw [hlex]
    exact huniq K' hK' hK'j
  -- Without E_J, no pair at `m − 1` is selected.
  have hnotop : ¬ treeEJ v m Jm Vw → (treeFjControlsView v F Vw).j ≠ m - 1 := by
    intro hn htop
    obtain ⟨K, hK, hKj, -, -⟩ := treeLexMax_carrier_of_top v F Vw hm htop
    exact hn ⟨K, hK, hKj, huniq K hK hKj⟩
  -- With E_J, the contest test is E_C.
  have hcont : treeEJ v m Jm Vw →
      ((treeFjControlsView v F Vw).contest = true ↔ treeECView v F m Jm Vw) := by
    intro hJ
    obtain ⟨hj, hJm⟩ := htopJ hJ
    have htop : (treeFjControlsView v F Vw).H = (treeFjControlsView v F Vw).j + 1 := by homega
    rw [treeTop_contest v F Vw htop, hH, hJm, decide_eq_true_iff]
    rfl
  refine ⟨fun hn => ?_, fun hJ hC => ?_, fun hJ hC => ?_⟩
  · have hne : ¬ (treeFjControlsView v F Vw).H = (treeFjControlsView v F Vw).j + 1 := by
      have := hnotop hn
      homega
    obtain ⟨-, -, hp, hf⟩ := treeGap_of_ne v F Vw hne
    rw [hp, hf, hH]
    exact ⟨rfl, rfl⟩
  · obtain ⟨hj, hJm⟩ := htopJ hJ
    have htop : (treeFjControlsView v F Vw).H = (treeFjControlsView v F Vw).j + 1 := by homega
    have hc : (treeFjControlsView v F Vw).contest = false := by
      cases h : (treeFjControlsView v F Vw).contest
      · rfl
      · exact absurd ((hcont hJ).1 h) hC
    obtain ⟨hp, -, hf⟩ := treeTop_uncontested v F Vw htop hc
    rw [hp, hf, hH, hJm]
    exact ⟨rfl, rfl⟩
  · obtain ⟨hj, -⟩ := htopJ hJ
    have htop : (treeFjControlsView v F Vw).H = (treeFjControlsView v F Vw).j + 1 := by homega
    obtain ⟨hp, -, hf⟩ := treeTop_contested v F Vw htop ((hcont hJ).2 hC)
    rw [hp, hf, hH]
    exact ⟨rfl, rfl⟩

include hL in
/-- Repairs `nFrame_eq_phaseFrame` for the guarded tree frame. Under the hypotheses of
`treeEffFrame_of_bits`, the normalized frame is the frame of the phase. -/
theorem treeNFrame_eq_phaseFrame (hm : 2 ≤ m)
    (hfront : frontierView v Vw = m)
    (huniq : ∀ K ∈ Vw, (v K).h_j = m - 1 → (v K).J = Jm)
    (hFJ : treeEJ v m Jm Vw → FGBlock.Preceq F Jm) :
    treeNFrame v F Vw = phaseFrame m Jm (treePhaseOf v F Vw) := by
  have h := treeEffFrame_of_bits v hL hm hfront huniq hFJ
  by_cases hJ : treeEJ v m Jm Vw
  · by_cases hC : treeECView v F m Jm Vw
    · obtain ⟨hp, hf⟩ := h.2.2 hJ hC
      rw [hp, hf]
      rfl
    · obtain ⟨hp, hf⟩ := h.2.1 hJ hC
      rw [hp, hf]
      rfl
  · obtain ⟨hp, hf⟩ := h.1 hJ
    rw [hp, hf]
    rfl

include hL in
/-- Repairs `twoChanges` for the guarded tree frame. (item 2) Along any sequence of duty views
at frontier m, each with its own F, if each evidence bit persists once true, the phase rank
never decreases, and two duties in one phase have the same normalized frame. The views need not
be nested. -/
theorem treeTwoChanges (Fs : ℕ → FGBlock V) (Vs : ℕ → View V) (hm : 2 ≤ m)
    (hfront : ∀ k, frontierView v (Vs k) = m)
    (huniq : ∀ k, ∀ K ∈ Vs k, (v K).h_j = m - 1 → (v K).J = Jm)
    (hFJ : ∀ k, treeEJ v m Jm (Vs k) → FGBlock.Preceq (Fs k) Jm)
    (hJ : ∀ k k', k ≤ k' → treeEJ v m Jm (Vs k) → treeEJ v m Jm (Vs k'))
    (hC : ∀ k k', k ≤ k' → treeECView v (Fs k) m Jm (Vs k) → treeECView v (Fs k') m Jm (Vs k')) :
    Monotone (fun k => (treePhaseOf v (Fs k) (Vs k)).rank) ∧
      ∀ k k', treePhaseOf v (Fs k) (Vs k) = treePhaseOf v (Fs k') (Vs k') →
        treeNFrame v (Fs k) (Vs k) = treeNFrame v (Fs k') (Vs k') := by
  refine ⟨fun k k' hkk' => ?_, fun k k' hp => ?_⟩
  · have e := treeEffFrame_of_bits v hL hm (hfront k) (huniq k) (hFJ k)
    have e' := treeEffFrame_of_bits v hL hm (hfront k') (huniq k') (hFJ k')
    dsimp only
    by_cases hJk : treeEJ v m Jm (Vs k)
    · have hJk' := hJ k k' hkk' hJk
      by_cases hCk : treeECView v (Fs k) m Jm (Vs k)
      · rw [(e.2.2 hJk hCk).1, (e'.2.2 hJk' (hC k k' hkk' hCk)).1]
      · rw [(e.2.1 hJk hCk).1]
        by_cases hCk' : treeECView v (Fs k') m Jm (Vs k')
        · rw [(e'.2.2 hJk' hCk').1]
          decide
        · rw [(e'.2.1 hJk' hCk').1]
    · rw [(e.1 hJk).1]
      exact Nat.zero_le _
  · rw [treeNFrame_eq_phaseFrame v hL hm (hfront k) (huniq k) (hFJ k),
      treeNFrame_eq_phaseFrame v hL hm (hfront k') (huniq k') (hFJ k'), hp]

include hL in
/-- Repairs `twoChanges_count` for the guarded tree frame. (item 2, the count) Under the
hypotheses of `treeTwoChanges`, the normalized frame changes at most twice in any prefix. -/
theorem treeTwoChanges_count (Fs : ℕ → FGBlock V) (Vs : ℕ → View V) (hm : 2 ≤ m)
    (hfront : ∀ k, frontierView v (Vs k) = m)
    (huniq : ∀ k, ∀ K ∈ Vs k, (v K).h_j = m - 1 → (v K).J = Jm)
    (hFJ : ∀ k, treeEJ v m Jm (Vs k) → FGBlock.Preceq (Fs k) Jm)
    (hJ : ∀ k k', k ≤ k' → treeEJ v m Jm (Vs k) → treeEJ v m Jm (Vs k'))
    (hC : ∀ k k', k ≤ k' → treeECView v (Fs k) m Jm (Vs k) →
      treeECView v (Fs k') m Jm (Vs k')) (n : ℕ) :
    ((List.range n).filter (fun k =>
      decide (treeNFrame v (Fs (k + 1)) (Vs (k + 1)) ≠ treeNFrame v (Fs k) (Vs k)))).length
        ≤ 2 := by
  obtain ⟨hmono, hsame⟩ := treeTwoChanges v hL Fs Vs hm hfront huniq hFJ hJ hC
  -- A change of the normalized frame is a strict rise of the phase rank.
  have hstep : ∀ k, treeNFrame v (Fs (k + 1)) (Vs (k + 1)) ≠ treeNFrame v (Fs k) (Vs k) →
      (treePhaseOf v (Fs k) (Vs k)).rank < (treePhaseOf v (Fs (k + 1)) (Vs (k + 1))).rank := by
    intro k hne
    have hle : (treePhaseOf v (Fs k) (Vs k)).rank ≤
        (treePhaseOf v (Fs (k + 1)) (Vs (k + 1))).rank := hmono (Nat.le_succ k)
    exact lt_of_le_of_ne hle
      (fun heq => hne (hsame (k + 1) k (Phase.rank_injective heq).symm))
  -- The number of changes plus the first rank is at most the last rank.
  have hcount : ∀ n, ((List.range n).filter (fun k =>
      decide (treeNFrame v (Fs (k + 1)) (Vs (k + 1)) ≠ treeNFrame v (Fs k) (Vs k)))).length +
        (treePhaseOf v (Fs 0) (Vs 0)).rank ≤ (treePhaseOf v (Fs n) (Vs n)).rank := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.filter_append, List.length_append]
      have hle : (treePhaseOf v (Fs n) (Vs n)).rank ≤
          (treePhaseOf v (Fs (n + 1)) (Vs (n + 1))).rank := hmono (Nat.le_succ n)
      by_cases hne : treeNFrame v (Fs (n + 1)) (Vs (n + 1)) ≠ treeNFrame v (Fs n) (Vs n)
      · have hlt := hstep n hne
        have hl : ([n].filter (fun k => decide (treeNFrame v (Fs (k + 1)) (Vs (k + 1)) ≠
            treeNFrame v (Fs k) (Vs k)))).length = 1 := by
          simp [hne]
        homega
      · have hl : ([n].filter (fun k => decide (treeNFrame v (Fs (k + 1)) (Vs (k + 1)) ≠
            treeNFrame v (Fs k) (Vs k)))).length = 0 := by
          simp only [ne_eq, not_not] at hne
          simp [hne]
        homega
  have h1 := hcount n
  have h2 := Phase.rank_le_two (treePhaseOf v (Fs n) (Vs n))
  homega

include hL in
/-- Repairs `twoChanges_nested` for the guarded tree frame. (partial: nested views only; Astra
G07) Nested views keep both bits (`treeEvidence_mono`), so `treeTwoChanges` applies. The trees
of different nodes need not be nested. -/
theorem treeTwoChanges_nested (F : FGBlock V) (Vs : ℕ → View V) (hmono : Monotone Vs)
    (hm : 2 ≤ m) (hfront : ∀ k, frontierView v (Vs k) = m)
    (huniq : ∀ k, ∀ K ∈ Vs k, (v K).h_j = m - 1 → (v K).J = Jm)
    (hFJ : ∀ k, treeEJ v m Jm (Vs k) → FGBlock.Preceq F Jm) :
    Monotone (fun k => (treePhaseOf v F (Vs k)).rank) :=
  (treeTwoChanges v hL (fun _ => F) Vs hm hfront huniq hFJ
    (fun _ _ h => (treeEvidence_mono v (F := F) (hmono h)).1)
    (fun _ _ h => (treeEvidence_mono v (F := F) (hmono h)).2)).1

end AvailableChain.KitFG
end
