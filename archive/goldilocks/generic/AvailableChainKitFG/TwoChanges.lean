module
public import AvailableChainSimplexFG
public import AvailableChainKitFG.Correspondence
public import AvailableChainKitFG.LowerFDomainDef

@[expose] public section

namespace AvailableChain.KitFG

open AvailableChain.SimplexFG

/-! # `fj.twoChanges.core.v1`: FJ phases at a fixed frontier (pure core)

r148 (`fj-redteam.md`, lines 764–773 and 778–789), with the registry's
formal reading of item 3 (Astra G02). The count is for SETTLED phases: the
theorem is stated over the two evidence bits `E_J` and `E_C` of a view, with
the hypothesis that each bit persists once true. Successive duty views need not
be nested: the count for raw successive duty frames is REFUTED (r148 lines
737–760).

Frame forms (ALFS):
- `phaseOf`, `EJ`, `EC`, `nFrame`, `effFrame_of_bits`, `twoChanges`,
  `twoChanges_count`, `twoChanges_nested`, `Fmove_atFrontier`: the controls
  `fjControls F V` of a block set V. In ALFS, V is a node's tree `Σ.T` (Lean
  `st.TF`), and `storeControls_eq_fjControls` makes these the live controls.
- `Fmove_filtered`: `filteredFrom` with any block set, under fixed controls in
  which only F moves (ldp §9.3 (1), claim C1).
- `Fmove_below`, `Fmove_atTop`: the `fjFrame` special case, where the controls
  are recomputed from the same set under F and under F′. -/

/-- [helper] The three FJ phases at one frontier. -/
inductive Phase where
  | gap | uncontested | contested
  deriving DecidableEq, Repr

/-- [helper] The order of the phases: gap, then uncontested, then contested. -/
def Phase.rank : Phase → Nat
  | .gap => 0 | .uncontested => 1 | .contested => 2

/-- [helper] The rank identifies the phase. -/
theorem Phase.rank_injective : Function.Injective Phase.rank := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- [helper] The rank is at most 2. -/
theorem Phase.rank_le_two (p : Phase) : p.rank ≤ 2 := by
  cases p <;> decide

/-- [helper] The normalized (effective) frame of `fj.twoChanges.core.v1` item 1:
H, lo and the root Ẑ, with Ẑ = ◇ (`none`) in the F-root phases. -/
structure NFrame (V : Type) where
  H : Height
  lo : Height
  root : Option (FGBlock V)
  deriving DecidableEq

/-- [helper] The normalized frame of each phase at frontier m (item 1). -/
def phaseFrame {V : Type} (m : Height) (Jm : FGBlock V) : Phase → NFrame V
  | .gap => ⟨m, m - 1, none⟩
  | .uncontested => ⟨m, m - 1, some Jm⟩
  | .contested => ⟨m, m, none⟩

/-- [helper] `omega` after `Height` is unfolded (`omega` does not see through the
abbreviation). -/
local macro "homega" : tactic => `(tactic| ((try simp only [Height] at *) <;> omega))

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V] (E : Electorate V)
  (cfg : FGConfig)
variable {F F' : FGBlock V} {Vw : View V} {m : Height} {Jm : FGBlock V}

/-- The FJ phase of a view: no top J, top J uncontested, or top J contested. -/
def phaseOf (F : FGBlock V) (Vw : View V) : Phase :=
  let c := fjControls E cfg F Vw
  if c.H = c.j + 1 then (if c.contest then .contested else .uncontested) else .gap

/-- E_J: the view holds a carrier of the pair `(m−1, Jm)`. -/
def EJ (m : Height) (Jm : FGBlock V) (Vw : View V) : Prop :=
  ∃ K ∈ Vw, (derive E cfg K).h_j = m - 1 ∧ (derive E cfg K).J = Jm

/-- E_C: the view holds a block of height m that does not extend Jm. -/
def EC (m : Height) (Jm : FGBlock V) (Vw : View V) : Prop :=
  ∃ W ∈ Vw, hOf E cfg W = m ∧ ¬ FGBlock.Preceq Jm W

/-- The normalized frame of a view: `(H, lo, Ẑ)`. -/
def nFrame (F : FGBlock V) (Vw : View V) : NFrame V :=
  let c := fjControls E cfg F Vw
  ⟨c.H, c.lo, if c.rootIsJ then some c.J else none⟩

/-! ## The phase and the normalized frame of the controls -/

/-- [helper] `phaseOf` reads H, j and the contest bit of `fjControls`. -/
theorem phaseOf_eq (F : FGBlock V) (Vw : View V) :
    phaseOf E cfg F Vw =
      if (fjControls E cfg F Vw).H = (fjControls E cfg F Vw).j + 1 then
        (if (fjControls E cfg F Vw).contest then .contested else .uncontested)
      else .gap := rfl

/-- [helper] `nFrame` reads H, lo, the root test and J of `fjControls`. -/
theorem nFrame_eq (F : FGBlock V) (Vw : View V) :
    nFrame E cfg F Vw = ⟨(fjControls E cfg F Vw).H, (fjControls E cfg F Vw).lo,
      if (fjControls E cfg F Vw).rootIsJ then some (fjControls E cfg F Vw).J else none⟩ := rfl

/-- [helper] The contest bit of `fjControls`. -/
theorem fjControls_contest (F : FGBlock V) (Vw : View V) :
    (fjControls E cfg F Vw).contest =
      (decide ((fjControls E cfg F Vw).H = (fjControls E cfg F Vw).j + 1) &&
        decide (∃ W ∈ Vw, hOf E cfg W = (fjControls E cfg F Vw).H ∧
          ¬ FGBlock.Preceq (fjControls E cfg F Vw).J W)) := rfl

/-- [helper] The gap phase: `H ≠ j + 1`. There is no contest, the root is F, and
`lo = H − 1`. -/
theorem gap_of_ne (F : FGBlock V) (Vw : View V)
    (hne : ¬ (fjControls E cfg F Vw).H = (fjControls E cfg F Vw).j + 1) :
    (fjControls E cfg F Vw).contest = false ∧ (fjControls E cfg F Vw).rootIsJ = false ∧
      phaseOf E cfg F Vw = .gap ∧
      nFrame E cfg F Vw = ⟨(fjControls E cfg F Vw).H, (fjControls E cfg F Vw).H - 1, none⟩ := by
  have hc : (fjControls E cfg F Vw).contest = false := by
    rw [fjControls_contest, decide_eq_false hne, Bool.false_and]
  have hr : (fjControls E cfg F Vw).rootIsJ = false := by
    unfold Controls.rootIsJ
    rw [decide_eq_false hne, Bool.false_and]
  refine ⟨hc, hr, ?_, ?_⟩
  · rw [phaseOf_eq, ite_eq_right hne]
  · rw [nFrame_eq, hr, ite_eq_right Bool.false_ne_true]
    unfold Controls.lo
    rw [hc, ite_eq_right Bool.false_ne_true]

/-- [helper] At `H = j + 1`, the contest bit is the contest test alone. -/
theorem top_contest (F : FGBlock V) (Vw : View V)
    (htop : (fjControls E cfg F Vw).H = (fjControls E cfg F Vw).j + 1) :
    (fjControls E cfg F Vw).contest =
      decide (∃ W ∈ Vw, hOf E cfg W = (fjControls E cfg F Vw).H ∧
        ¬ FGBlock.Preceq (fjControls E cfg F Vw).J W) := by
  rw [fjControls_contest, decide_eq_true htop, Bool.true_and]

/-- [helper] At `H = j + 1` with no contest: the uncontested phase, root J,
`lo = H − 1`. -/
theorem top_uncontested (F : FGBlock V) (Vw : View V)
    (htop : (fjControls E cfg F Vw).H = (fjControls E cfg F Vw).j + 1)
    (hc : (fjControls E cfg F Vw).contest = false) :
    phaseOf E cfg F Vw = .uncontested ∧ (fjControls E cfg F Vw).rootIsJ = true ∧
      nFrame E cfg F Vw = ⟨(fjControls E cfg F Vw).H, (fjControls E cfg F Vw).H - 1,
        some (fjControls E cfg F Vw).J⟩ := by
  have hr : (fjControls E cfg F Vw).rootIsJ = true := by
    unfold Controls.rootIsJ
    rw [decide_eq_true htop, hc]
    rfl
  refine ⟨?_, hr, ?_⟩
  · rw [phaseOf_eq, ite_eq_left htop, hc, ite_eq_right Bool.false_ne_true]
  · rw [nFrame_eq, hr, ite_eq_left rfl]
    unfold Controls.lo
    rw [hc, ite_eq_right Bool.false_ne_true]

/-- [helper] At `H = j + 1` with a contest: the contested phase, root F, `lo = H`. -/
theorem top_contested (F : FGBlock V) (Vw : View V)
    (htop : (fjControls E cfg F Vw).H = (fjControls E cfg F Vw).j + 1)
    (hc : (fjControls E cfg F Vw).contest = true) :
    phaseOf E cfg F Vw = .contested ∧ (fjControls E cfg F Vw).rootIsJ = false ∧
      nFrame E cfg F Vw = ⟨(fjControls E cfg F Vw).H, (fjControls E cfg F Vw).H, none⟩ := by
  have hr : (fjControls E cfg F Vw).rootIsJ = false := by
    unfold Controls.rootIsJ
    rw [decide_eq_true htop, hc]
    rfl
  refine ⟨?_, hr, ?_⟩
  · rw [phaseOf_eq, ite_eq_left htop, hc, ite_eq_left rfl]
  · rw [nFrame_eq, hr, ite_eq_right Bool.false_ne_true]
    unfold Controls.lo
    rw [hc, ite_eq_left rfl]

/-- [helper] The root is J exactly in the uncontested phase. -/
theorem rootIsJ_iff (F : FGBlock V) (Vw : View V) :
    (fjControls E cfg F Vw).rootIsJ = true ↔ phaseOf E cfg F Vw = .uncontested := by
  by_cases htop : (fjControls E cfg F Vw).H = (fjControls E cfg F Vw).j + 1
  · cases hc : (fjControls E cfg F Vw).contest
    · obtain ⟨hp, hr, -⟩ := top_uncontested E cfg F Vw htop hc
      rw [hp, hr]
      simp
    · obtain ⟨hp, hr, -⟩ := top_contested E cfg F Vw htop hc
      rw [hp, hr]
      simp
  · obtain ⟨-, hr, hp, -⟩ := gap_of_ne E cfg F Vw htop
    rw [hp, hr]
    simp

/-! ## The selected pair at the top of the band -/

/-- [helper] The frontier is at least 1. -/
theorem one_le_frontier (Vw : View V) : 1 ≤ frontier E cfg Vw := by
  unfold SimplexFG.frontier
  exact le_sup_right

/-- [helper] The selected height is below the frontier. -/
theorem lexMax_fst_lt (G : FGBlock V) (Vw : View V) (hinj : ViewRootInj Vw) :
    (lexMax E cfg G Vw).1 < frontier E cfg Vw := by
  by_cases hne : ∃ K ∈ Vw, FGBlock.Preceq G (derive E cfg K).J
  · obtain ⟨K, hK, -, hlex, -⟩ := lexMax_spec E cfg G Vw hinj hne
    rw [hlex]
    exact lt_of_lt_of_le (justified_below_height E cfg K) (le_frontier E cfg hK)
  · push Not at hne
    rw [lexMax_of_none E cfg G Vw hne]
    exact lt_of_lt_of_le Nat.zero_lt_one (one_le_frontier E cfg Vw)

/-- [helper] At frontier m, a block of the view with a pair at `m − 1` whose J
extends G makes the selected height `m − 1`. -/
theorem lexMax_top_of_carrier (G : FGBlock V) (Vw : View V) (hinj : ViewRootInj Vw)
    (hfront : frontier E cfg Vw = m) (K : FGBlock V) (hK : K ∈ Vw)
    (hKj : (derive E cfg K).h_j = m - 1) (hGK : FGBlock.Preceq G (derive E cfg K).J) :
    (lexMax E cfg G Vw).1 = m - 1 := by
  obtain ⟨K', hK', -, hlex, hmax⟩ := lexMax_spec E cfg G Vw hinj ⟨K, hK, hGK⟩
  have hle := fst_le_of_lexKey_le (hmax K hK hGK)
  have hlt := justified_below_height E cfg K'
  have hK'H := le_frontier E cfg hK'
  rw [hlex]
  unfold hOf at hK'H
  rw [hfront] at hK'H
  dsimp only at hle ⊢
  homega

/-- [helper] With `m ≥ 2`, a selected height `m − 1` is not the fallback: it is
the pair of a block of the view whose J extends G. -/
theorem lexMax_carrier_of_top (G : FGBlock V) (Vw : View V) (hm : 2 ≤ m)
    (hinj : ViewRootInj Vw) (htop : (lexMax E cfg G Vw).1 = m - 1) :
    ∃ K ∈ Vw, (derive E cfg K).h_j = m - 1 ∧ FGBlock.Preceq G (derive E cfg K).J ∧
      lexMax E cfg G Vw = ((derive E cfg K).h_j, (derive E cfg K).J) := by
  by_cases hne : ∃ K ∈ Vw, FGBlock.Preceq G (derive E cfg K).J
  · obtain ⟨K, hK, hGK, hlex, -⟩ := lexMax_spec E cfg G Vw hinj hne
    refine ⟨K, hK, ?_, hGK, hlex⟩
    rw [hlex] at htop
    exact htop
  · push Not at hne
    rw [lexMax_of_none E cfg G Vw hne] at htop
    dsimp only at htop
    homega

/-! ## Items 1 and 2 -/

/-- [pin fj.twoChanges.core.v1] (item 2, first sentence) Views are subsets of
stores: a bit that is true in a view is true in every larger set. -/
theorem evidence_mono {Vw S : View V} (h : Vw ⊆ S) :
    (EJ E cfg m Jm Vw → EJ E cfg m Jm S) ∧ (EC E cfg m Jm Vw → EC E cfg m Jm S) :=
  ⟨fun ⟨K, hK, hKj⟩ => ⟨K, h hK, hKj⟩, fun ⟨W, hW, hWm⟩ => ⟨W, h hW, hWm⟩⟩

/-- [pin fj.twoChanges.core.v1] (item 1) At frontier m ≥ 2, when every pair at
m−1 in the view names Jm and F ⪯ Jm when E_J holds, the phase is given by the
bits, and the normalized frame is: gap (m, m−1, ◇); uncontested (m, m−1, Jm);
contested (m, m, ◇). -/
theorem effFrame_of_bits (hm : 2 ≤ m) (hinj : ViewRootInj Vw)
    (hfront : frontier E cfg Vw = m)
    (huniq : ∀ K ∈ Vw, (derive E cfg K).h_j = m - 1 → (derive E cfg K).J = Jm)
    (hFJ : EJ E cfg m Jm Vw → FGBlock.Preceq F Jm) :
    (¬ EJ E cfg m Jm Vw →
        phaseOf E cfg F Vw = .gap ∧ nFrame E cfg F Vw = ⟨m, m - 1, none⟩) ∧
      (EJ E cfg m Jm Vw → ¬ EC E cfg m Jm Vw →
        phaseOf E cfg F Vw = .uncontested ∧ nFrame E cfg F Vw = ⟨m, m - 1, some Jm⟩) ∧
      (EJ E cfg m Jm Vw → EC E cfg m Jm Vw →
        phaseOf E cfg F Vw = .contested ∧ nFrame E cfg F Vw = ⟨m, m, none⟩) := by
  have hH : (fjControls E cfg F Vw).H = m := hfront
  have hlt : (fjControls E cfg F Vw).j < m := by
    have := lexMax_fst_lt E cfg F Vw hinj
    rw [hfront] at this
    exact this
  -- With E_J, the selected pair is `(m − 1, Jm)`.
  have htopJ : EJ E cfg m Jm Vw →
      (fjControls E cfg F Vw).j = m - 1 ∧ (fjControls E cfg F Vw).J = Jm := by
    intro hJ
    obtain ⟨K, hK, hKj, hKJ⟩ := hJ
    have htop := lexMax_top_of_carrier E cfg F Vw hinj hfront K hK hKj
      (by rw [hKJ]; exact hFJ ⟨K, hK, hKj, hKJ⟩)
    obtain ⟨K', hK', hK'j, -, hlex⟩ := lexMax_carrier_of_top E cfg F Vw hm hinj htop
    refine ⟨htop, ?_⟩
    change (lexMax E cfg F Vw).2 = Jm
    rw [hlex]
    exact huniq K' hK' hK'j
  -- Without E_J, no pair at `m − 1` is selected.
  have hnotop : ¬ EJ E cfg m Jm Vw → (fjControls E cfg F Vw).j ≠ m - 1 := by
    intro hn htop
    obtain ⟨K, hK, hKj, -, -⟩ := lexMax_carrier_of_top E cfg F Vw hm hinj htop
    exact hn ⟨K, hK, hKj, huniq K hK hKj⟩
  -- With E_J, the contest test is E_C.
  have hcont : EJ E cfg m Jm Vw →
      ((fjControls E cfg F Vw).contest = true ↔ EC E cfg m Jm Vw) := by
    intro hJ
    obtain ⟨hj, hJm⟩ := htopJ hJ
    have htop : (fjControls E cfg F Vw).H = (fjControls E cfg F Vw).j + 1 := by homega
    rw [top_contest E cfg F Vw htop, hH, hJm, decide_eq_true_iff]
    rfl
  refine ⟨fun hn => ?_, fun hJ hC => ?_, fun hJ hC => ?_⟩
  · have hne : ¬ (fjControls E cfg F Vw).H = (fjControls E cfg F Vw).j + 1 := by
      have := hnotop hn
      homega
    obtain ⟨-, -, hp, hf⟩ := gap_of_ne E cfg F Vw hne
    rw [hp, hf, hH]
    exact ⟨rfl, rfl⟩
  · obtain ⟨hj, hJm⟩ := htopJ hJ
    have htop : (fjControls E cfg F Vw).H = (fjControls E cfg F Vw).j + 1 := by homega
    have hc : (fjControls E cfg F Vw).contest = false := by
      cases h : (fjControls E cfg F Vw).contest
      · rfl
      · exact absurd ((hcont hJ).1 h) hC
    obtain ⟨hp, -, hf⟩ := top_uncontested E cfg F Vw htop hc
    rw [hp, hf, hH, hJm]
    exact ⟨rfl, rfl⟩
  · obtain ⟨hj, -⟩ := htopJ hJ
    have htop : (fjControls E cfg F Vw).H = (fjControls E cfg F Vw).j + 1 := by homega
    obtain ⟨hp, -, hf⟩ := top_contested E cfg F Vw htop ((hcont hJ).2 hC)
    rw [hp, hf, hH]
    exact ⟨rfl, rfl⟩

/-- [helper] Under the hypotheses of `effFrame_of_bits`, the normalized frame is
the frame of the phase. -/
theorem nFrame_eq_phaseFrame (hm : 2 ≤ m) (hinj : ViewRootInj Vw)
    (hfront : frontier E cfg Vw = m)
    (huniq : ∀ K ∈ Vw, (derive E cfg K).h_j = m - 1 → (derive E cfg K).J = Jm)
    (hFJ : EJ E cfg m Jm Vw → FGBlock.Preceq F Jm) :
    nFrame E cfg F Vw = phaseFrame m Jm (phaseOf E cfg F Vw) := by
  have h := effFrame_of_bits E cfg hm hinj hfront huniq hFJ
  by_cases hJ : EJ E cfg m Jm Vw
  · by_cases hC : EC E cfg m Jm Vw
    · obtain ⟨hp, hf⟩ := h.2.2 hJ hC
      rw [hp, hf]
      rfl
    · obtain ⟨hp, hf⟩ := h.2.1 hJ hC
      rw [hp, hf]
      rfl
  · obtain ⟨hp, hf⟩ := h.1 hJ
    rw [hp, hf]
    rfl

/-- [pin fj.twoChanges.core.v1] (item 2) Along any sequence of duty views at
frontier m, each with its own F, if each evidence bit persists once true, the
phase rank never decreases, and two duties in one phase have the same
normalized frame. The views need not be nested. -/
theorem twoChanges (Fs : ℕ → FGBlock V) (Vs : ℕ → View V) (hm : 2 ≤ m)
    (hinj : ∀ k, ViewRootInj (Vs k)) (hfront : ∀ k, frontier E cfg (Vs k) = m)
    (huniq : ∀ k, ∀ K ∈ Vs k, (derive E cfg K).h_j = m - 1 → (derive E cfg K).J = Jm)
    (hFJ : ∀ k, EJ E cfg m Jm (Vs k) → FGBlock.Preceq (Fs k) Jm)
    (hJ : ∀ k k', k ≤ k' → EJ E cfg m Jm (Vs k) → EJ E cfg m Jm (Vs k'))
    (hC : ∀ k k', k ≤ k' → EC E cfg m Jm (Vs k) → EC E cfg m Jm (Vs k')) :
    Monotone (fun k => (phaseOf E cfg (Fs k) (Vs k)).rank) ∧
      ∀ k k', phaseOf E cfg (Fs k) (Vs k) = phaseOf E cfg (Fs k') (Vs k') →
        nFrame E cfg (Fs k) (Vs k) = nFrame E cfg (Fs k') (Vs k') := by
  refine ⟨fun k k' hkk' => ?_, fun k k' hp => ?_⟩
  · have e := effFrame_of_bits E cfg hm (hinj k) (hfront k) (huniq k) (hFJ k)
    have e' := effFrame_of_bits E cfg hm (hinj k') (hfront k') (huniq k') (hFJ k')
    dsimp only
    by_cases hJk : EJ E cfg m Jm (Vs k)
    · have hJk' := hJ k k' hkk' hJk
      by_cases hCk : EC E cfg m Jm (Vs k)
      · rw [(e.2.2 hJk hCk).1, (e'.2.2 hJk' (hC k k' hkk' hCk)).1]
      · rw [(e.2.1 hJk hCk).1]
        by_cases hCk' : EC E cfg m Jm (Vs k')
        · rw [(e'.2.2 hJk' hCk').1]
          decide
        · rw [(e'.2.1 hJk' hCk').1]
    · rw [(e.1 hJk).1]
      exact Nat.zero_le _
  · rw [nFrame_eq_phaseFrame E cfg hm (hinj k) (hfront k) (huniq k) (hFJ k),
      nFrame_eq_phaseFrame E cfg hm (hinj k') (hfront k') (huniq k') (hFJ k'), hp]

/-- [pin fj.twoChanges.core.v1] (item 2, the count) Under the hypotheses of
`twoChanges`, the normalized frame changes at most twice in any prefix. -/
theorem twoChanges_count (Fs : ℕ → FGBlock V) (Vs : ℕ → View V) (hm : 2 ≤ m)
    (hinj : ∀ k, ViewRootInj (Vs k)) (hfront : ∀ k, frontier E cfg (Vs k) = m)
    (huniq : ∀ k, ∀ K ∈ Vs k, (derive E cfg K).h_j = m - 1 → (derive E cfg K).J = Jm)
    (hFJ : ∀ k, EJ E cfg m Jm (Vs k) → FGBlock.Preceq (Fs k) Jm)
    (hJ : ∀ k k', k ≤ k' → EJ E cfg m Jm (Vs k) → EJ E cfg m Jm (Vs k'))
    (hC : ∀ k k', k ≤ k' → EC E cfg m Jm (Vs k) → EC E cfg m Jm (Vs k')) (n : ℕ) :
    ((List.range n).filter (fun k =>
      decide (nFrame E cfg (Fs (k + 1)) (Vs (k + 1)) ≠ nFrame E cfg (Fs k) (Vs k)))).length
        ≤ 2 := by
  obtain ⟨hmono, hsame⟩ := twoChanges E cfg Fs Vs hm hinj hfront huniq hFJ hJ hC
  -- A change of the normalized frame is a strict rise of the phase rank.
  have hstep : ∀ k, nFrame E cfg (Fs (k + 1)) (Vs (k + 1)) ≠ nFrame E cfg (Fs k) (Vs k) →
      (phaseOf E cfg (Fs k) (Vs k)).rank < (phaseOf E cfg (Fs (k + 1)) (Vs (k + 1))).rank := by
    intro k hne
    have hle : (phaseOf E cfg (Fs k) (Vs k)).rank ≤
        (phaseOf E cfg (Fs (k + 1)) (Vs (k + 1))).rank := hmono (Nat.le_succ k)
    exact lt_of_le_of_ne hle
      (fun heq => hne (hsame (k + 1) k (Phase.rank_injective heq).symm))
  -- The number of changes plus the first rank is at most the last rank.
  have hcount : ∀ n, ((List.range n).filter (fun k =>
      decide (nFrame E cfg (Fs (k + 1)) (Vs (k + 1)) ≠ nFrame E cfg (Fs k) (Vs k)))).length +
        (phaseOf E cfg (Fs 0) (Vs 0)).rank ≤ (phaseOf E cfg (Fs n) (Vs n)).rank := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.filter_append, List.length_append]
      have hle : (phaseOf E cfg (Fs n) (Vs n)).rank ≤
          (phaseOf E cfg (Fs (n + 1)) (Vs (n + 1))).rank := hmono (Nat.le_succ n)
      by_cases hne : nFrame E cfg (Fs (n + 1)) (Vs (n + 1)) ≠ nFrame E cfg (Fs n) (Vs n)
      · have hlt := hstep n hne
        have hl : ([n].filter (fun k => decide (nFrame E cfg (Fs (k + 1)) (Vs (k + 1)) ≠
            nFrame E cfg (Fs k) (Vs k)))).length = 1 := by
          simp [hne]
        homega
      · have hl : ([n].filter (fun k => decide (nFrame E cfg (Fs (k + 1)) (Vs (k + 1)) ≠
            nFrame E cfg (Fs k) (Vs k)))).length = 0 := by
          simp only [ne_eq, not_not] at hne
          simp [hne]
        homega
  have h1 := hcount n
  have h2 := Phase.rank_le_two (phaseOf E cfg (Fs n) (Vs n))
  homega

/-- [helper] (partial: nested views only; Astra G07) Nested views keep both bits
(`evidence_mono`), so `twoChanges` applies. The trees of different nodes need not be
nested. -/
theorem twoChanges_nested (F : FGBlock V) (Vs : ℕ → View V) (hmono : Monotone Vs)
    (hm : 2 ≤ m) (hinj : ∀ k, ViewRootInj (Vs k)) (hfront : ∀ k, frontier E cfg (Vs k) = m)
    (huniq : ∀ k, ∀ K ∈ Vs k, (derive E cfg K).h_j = m - 1 → (derive E cfg K).J = Jm)
    (hFJ : ∀ k, EJ E cfg m Jm (Vs k) → FGBlock.Preceq F Jm) :
    Monotone (fun k => (phaseOf E cfg F (Vs k)).rank) :=
  (twoChanges E cfg (fun _ => F) Vs hm hinj hfront huniq hFJ
    (fun _ _ h => (evidence_mono E cfg (hmono h)).1)
    (fun _ _ h => (evidence_mono E cfg (hmono h)).2)).1

/-! ## Item 3: finalizations add no change -/

/-- [helper] Only F, Z and lo of the controls enter the filtered tree. -/
theorem filteredFrom_congr (c c' : Controls V) (blocks : Finset (FGBlock V))
    (hF : c.F = c'.F) (hZ : c.Z = c'.Z) (hlo : c.lo = c'.lo) :
    filteredFrom E cfg c blocks = filteredFrom E cfg c' blocks := by
  ext B
  rw [mem_filteredFrom, mem_filteredFrom, hF, hZ, hlo]

/-- [helper] (item 3 (i), the equality) Under fixed controls, an F move to
`F′ ⪰ F` cuts the filtered tree at F′. -/
theorem filteredFrom_move (c : Controls V) (F' : FGBlock V) (blocks : Finset (FGBlock V))
    (hFF' : FGBlock.Preceq c.F F') :
    filteredFrom E cfg { c with F := F' } blocks =
      (filteredFrom E cfg c blocks).filter (fun B => FGBlock.preceq F' B) := by
  have hZ' : ({ c with F := F' } : Controls V).Z = if c.rootIsJ then c.J else F' := rfl
  have hlo' : ({ c with F := F' } : Controls V).lo = c.lo := rfl
  ext B
  rw [Finset.mem_filter, mem_filteredFrom, mem_filteredFrom, hZ', hlo']
  unfold Controls.Z
  constructor
  · rintro ⟨hB, hF'B, hZB, hw⟩
    refine ⟨⟨hB, preceq_trans hFF' hF'B, ?_, hw⟩, hF'B⟩
    split_ifs at hZB ⊢
    · exact hZB
    · exact preceq_trans hFF' hF'B
  · rintro ⟨⟨hB, -, hZB, hw⟩, hF'B⟩
    refine ⟨hB, hF'B, ?_, hw⟩
    split_ifs at hZB ⊢
    · exact hZB
    · exact hF'B

/-- [pin fj.twoChanges.core.v1] (item 3 (i); filteredFrom, ANY block set; ldp
§9.3 C1) Under fixed controls in which only F moves to F′ ⪰ F: the filtered
tree is cut at F′. If F′ is below the band in the F-root phases, and, in the J-root
phase, the root J extends F′, and every block of the set above h(F′) extends F′ (pure
fg.finalLock.v1), then every removed block is an ancestor of F′; in the J-root
phase nothing is removed. -/
theorem Fmove_filtered (c : Controls V) (F' : FGBlock V) (blocks : Finset (FGBlock V))
    (hFF' : FGBlock.Preceq c.F F')
    (hband : c.rootIsJ = false → hOf E cfg F' < c.lo)
    (hroot : c.rootIsJ = true → FGBlock.Preceq F' c.J)
    (hext : ∀ W ∈ blocks, hOf E cfg F' < hOf E cfg W → FGBlock.Preceq F' W) :
    filteredFrom E cfg { c with F := F' } blocks =
        (filteredFrom E cfg c blocks).filter (fun B => FGBlock.preceq F' B) ∧
      (∀ B ∈ filteredFrom E cfg c blocks, B ∉ filteredFrom E cfg { c with F := F' } blocks →
        FGBlock.Preceq B F') ∧
      (c.rootIsJ = true →
        filteredFrom E cfg { c with F := F' } blocks = filteredFrom E cfg c blocks) := by
  have heq := filteredFrom_move E cfg c F' blocks hFF'
  have hZJ : c.rootIsJ = true → c.Z = c.J := by
    intro hr
    unfold Controls.Z
    rw [ite_eq_left hr]
  refine ⟨heq, ?_, ?_⟩
  · intro B hB hB'
    rw [heq, Finset.mem_filter] at hB'
    have hnF' : ¬ FGBlock.Preceq F' B := fun h => hB' ⟨hB, h⟩
    obtain ⟨-, -, hZB, W, hW, hBW, hlo⟩ := (mem_filteredFrom E cfg c blocks B).1 hB
    cases hr : c.rootIsJ
    · -- F-root: the witness W is above the band floor, so above F′.
      have hF'W : FGBlock.Preceq F' W := hext W hW (lt_of_lt_of_le (hband hr) hlo)
      rcases preceq_total_of_common hBW hF'W with h | h
      · exact h
      · exact absurd h hnF'
    · -- J-root: `F′ ⪯ J ⪯ B`, so B is not removed.
      rw [hZJ hr] at hZB
      exact absurd (preceq_trans (hroot hr) hZB) hnF'
  · intro hr
    rw [heq]
    apply Finset.filter_true_of_mem
    intro B hB
    obtain ⟨-, -, hZB, -⟩ := (mem_filteredFrom E cfg c blocks B).1 hB
    rw [hZJ hr] at hZB
    exact preceq_trans (hroot hr) hZB

/-- [helper] Below `m − 1`: if `h(F′) < m − 1` and every block of the view above
h(F′) extends F′, every pair at `m − 1` in the view has `F′ ⪯ J`. -/
theorem top_J_extends (hlow : hOf E cfg F' < m - 1)
    (hext : ∀ W ∈ Vw, hOf E cfg F' < hOf E cfg W → FGBlock.Preceq F' W)
    (K : FGBlock V) (hK : K ∈ Vw) (hKj : (derive E cfg K).h_j = m - 1) :
    FGBlock.Preceq F' (derive E cfg K).J := by
  have hjh := justified_below_height E cfg K
  unfold hOf at hlow hext
  have hJh := entry_height E cfg K (by homega)
  have hF'K : FGBlock.Preceq F' K := hext K hK (by homega)
  rcases preceq_total_of_common hF'K (derive_anchors_preceq E cfg K).2 with h | h
  · exact h
  · have := h_mono E cfg h
    homega

/-- [helper] (item 3 (i), fjFrame special case: the controls are recomputed
from the set under F and under F′) An F move F → F′ below m−1 at one
view, when every view block above h(F′) extends F′ (fg.finalLock.v1, pure
form): the phase and lo do not change; Z changes only from F to F′; (j, J) does
not change if j = m−1; and D is cut at F′: every removed block is an ancestor
of F′. Here h(F′) is the state height of F′. It is the checkpoint height of F′ by
`entry_height` only when some block K has `σ[K].J = F′` with `h_j(K) ≠ 0`; the
statement does not assume such a carrier. -/
theorem Fmove_below (hinj : ViewRootInj Vw) (hfront : frontier E cfg Vw = m)
    (hFF' : FGBlock.Preceq F F') (hlow : hOf E cfg F' < m - 1)
    (hext : ∀ W ∈ Vw, hOf E cfg F' < hOf E cfg W → FGBlock.Preceq F' W) :
    phaseOf E cfg F Vw = phaseOf E cfg F' Vw ∧
      (fjFrame E cfg F' Vw).lo = (fjFrame E cfg F Vw).lo ∧
      (phaseOf E cfg F Vw = .uncontested →
        (fjFrame E cfg F' Vw).Z = (fjFrame E cfg F Vw).Z) ∧
      (phaseOf E cfg F Vw ≠ .uncontested →
        (fjFrame E cfg F Vw).Z = F ∧ (fjFrame E cfg F' Vw).Z = F') ∧
      ((fjFrame E cfg F Vw).j = m - 1 →
        (fjFrame E cfg F' Vw).j = (fjFrame E cfg F Vw).j ∧
          (fjFrame E cfg F' Vw).J = (fjFrame E cfg F Vw).J) ∧
      (fjFrame E cfg F' Vw).D = (fjFrame E cfg F Vw).D.filter (fun B => FGBlock.preceq F' B) ∧
      ∀ B ∈ (fjFrame E cfg F Vw).D, B ∉ (fjFrame E cfg F' Vw).D → FGBlock.Preceq B F' := by
  have hm : 2 ≤ m := by
    have := one_le_h E cfg F'
    unfold hOf at hlow
    homega
  have hH : (fjControls E cfg F Vw).H = m := hfront
  have hHeq : (fjControls E cfg F' Vw).H = (fjControls E cfg F Vw).H := rfl
  have hlt : (fjControls E cfg F Vw).j < m := by
    have := lexMax_fst_lt E cfg F Vw hinj
    rw [hfront] at this
    exact this
  have hlt' : (fjControls E cfg F' Vw).j < m := by
    have := lexMax_fst_lt E cfg F' Vw hinj
    rw [hfront] at this
    exact this
  -- Step 1: the pairs at `m − 1` extend F′, so they are candidates for F′
  -- exactly when they are candidates for F.
  have hJext := top_J_extends E cfg hlow hext
  have hiff : (fjControls E cfg F Vw).j = m - 1 → (fjControls E cfg F' Vw).j = m - 1 ∧
      lexMax E cfg F' Vw = lexMax E cfg F Vw := by
    intro htop
    obtain ⟨K, hK, hKj, hFK, hlex⟩ := lexMax_carrier_of_top E cfg F Vw hm hinj htop
    have hadv : lexMax E cfg F' Vw = lexMax E cfg F Vw := by
      refine lexMax_of_advance E cfg F F' Vw hinj ⟨K, hK, hFK⟩ hFF' ?_
      rw [hlex]
      exact hJext K hK hKj
    refine ⟨?_, hadv⟩
    change (lexMax E cfg F' Vw).1 = m - 1
    rw [hadv]
    exact htop
  have hiff' : (fjControls E cfg F' Vw).j = m - 1 → (fjControls E cfg F Vw).j = m - 1 := by
    intro htop
    obtain ⟨K, hK, hKj, hF'K, -⟩ := lexMax_carrier_of_top E cfg F' Vw hm hinj htop
    exact lexMax_top_of_carrier E cfg F Vw hinj hfront K hK hKj (preceq_trans hFF' hF'K)
  -- Step 2: the phase, lo and the root test agree; J agrees when the root is J.
  have hctl : phaseOf E cfg F Vw = phaseOf E cfg F' Vw ∧
      (fjControls E cfg F' Vw).lo = (fjControls E cfg F Vw).lo ∧
      (fjControls E cfg F' Vw).rootIsJ = (fjControls E cfg F Vw).rootIsJ ∧
      ((fjControls E cfg F Vw).rootIsJ = true →
        (fjControls E cfg F' Vw).J = (fjControls E cfg F Vw).J ∧
          FGBlock.Preceq F' (fjControls E cfg F Vw).J) := by
    by_cases htop : (fjControls E cfg F Vw).j = m - 1
    · obtain ⟨-, hadv⟩ := hiff htop
      have hj : (fjControls E cfg F' Vw).j = (fjControls E cfg F Vw).j := by
        change (lexMax E cfg F' Vw).1 = (lexMax E cfg F Vw).1
        rw [hadv]
      have hJ : (fjControls E cfg F' Vw).J = (fjControls E cfg F Vw).J := by
        change (lexMax E cfg F' Vw).2 = (lexMax E cfg F Vw).2
        rw [hadv]
      have hc : (fjControls E cfg F' Vw).contest = (fjControls E cfg F Vw).contest := by
        rw [fjControls_contest, fjControls_contest E cfg F, hHeq, hj, hJ]
      refine ⟨?_, ?_, ?_, fun _ => ⟨hJ, ?_⟩⟩
      · rw [phaseOf_eq, phaseOf_eq E cfg F', hHeq, hj, hc]
      · unfold Controls.lo
        rw [hc, hHeq]
      · unfold Controls.rootIsJ
        rw [hc, hHeq, hj]
      · obtain ⟨K, hK, hKj, -, hlex⟩ := lexMax_carrier_of_top E cfg F Vw hm hinj htop
        change FGBlock.Preceq F' (lexMax E cfg F Vw).2
        rw [hlex]
        exact hJext K hK hKj
    · have htop' : ¬ (fjControls E cfg F' Vw).j = m - 1 := fun h => htop (hiff' h)
      have hne : ¬ (fjControls E cfg F Vw).H = (fjControls E cfg F Vw).j + 1 := by homega
      have hne' : ¬ (fjControls E cfg F' Vw).H = (fjControls E cfg F' Vw).j + 1 := by
        rw [hHeq]
        homega
      obtain ⟨hc, hr, hp, -⟩ := gap_of_ne E cfg F Vw hne
      obtain ⟨hc', hr', hp', -⟩ := gap_of_ne E cfg F' Vw hne'
      refine ⟨by rw [hp, hp'], ?_, by rw [hr, hr'], fun h => absurd (hr ▸ h) (by simp)⟩
      unfold Controls.lo
      rw [hc, hc', hHeq]
  obtain ⟨hph, hlo, hrj, hJ⟩ := hctl
  -- Step 3: Z of F′ is Z of the controls of F with F replaced by F′.
  have hZ' : (fjControls E cfg F' Vw).Z =
      if (fjControls E cfg F Vw).rootIsJ then (fjControls E cfg F Vw).J else F' := by
    unfold Controls.Z
    rw [hrj]
    cases hr : (fjControls E cfg F Vw).rootIsJ
    · rfl
    · rw [ite_eq_left rfl, ite_eq_left rfl]
      exact (hJ hr).1
  have hFm := Fmove_filtered E cfg (fjControls E cfg F Vw) F' Vw hFF'
    (fun _ => by
      have := Controls.H_sub_one_le_lo (fjControls E cfg F Vw)
      rw [hH] at this
      homega)
    (fun hr => (hJ hr).2) hext
  have hD : filteredFrom E cfg (fjControls E cfg F' Vw) Vw =
      filteredFrom E cfg { fjControls E cfg F Vw with F := F' } Vw :=
    filteredFrom_congr E cfg _ _ Vw rfl hZ' hlo
  refine ⟨hph, hlo, ?_, ?_, ?_, ?_, ?_⟩
  · intro hu
    have hr := (rootIsJ_iff E cfg F Vw).2 hu
    change (fjControls E cfg F' Vw).Z = (fjControls E cfg F Vw).Z
    rw [hZ', hr, ite_eq_left rfl]
    unfold Controls.Z
    rw [hr, ite_eq_left rfl]
  · intro hu
    have hr : (fjControls E cfg F Vw).rootIsJ = false := by
      cases h : (fjControls E cfg F Vw).rootIsJ
      · rfl
      · exact absurd ((rootIsJ_iff E cfg F Vw).1 h) hu
    constructor
    · change (fjControls E cfg F Vw).Z = F
      unfold Controls.Z
      rw [hr, ite_eq_right Bool.false_ne_true]
      rfl
    · change (fjControls E cfg F' Vw).Z = F'
      rw [hZ', hr, ite_eq_right Bool.false_ne_true]
  · intro htop
    obtain ⟨-, hadv⟩ := hiff htop
    change (lexMax E cfg F' Vw).1 = (lexMax E cfg F Vw).1 ∧
      (lexMax E cfg F' Vw).2 = (lexMax E cfg F Vw).2
    rw [hadv]
    exact ⟨rfl, rfl⟩
  · exact hD.trans hFm.1
  · intro B hB hB'
    change B ∉ filteredFrom E cfg (fjControls E cfg F' Vw) Vw at hB'
    rw [hD] at hB'
    exact hFm.2.1 B hB hB'

/-- [pin fj.twoChanges.core.v1] (item 3 (ii)) An F move to F′ at m−1, when the
view holds a block K whose chain finalizes F′ at m−1, the pairs at m−1 in the
view are unique, and every view block above m−1 extends F′: both frames are
uncontested with Z = F′ and lo = m−1, and D does not change. -/
theorem Fmove_atTop (hm : 2 ≤ m) (hinj : ViewRootInj Vw) (hfront : frontier E cfg Vw = m)
    (hFF' : FGBlock.Preceq F F')
    (K : FGBlock V) (hK : K ∈ Vw) (hKF : (derive E cfg K).F = F')
    (hKh : (derive E cfg K).h_F = m - 1)
    (huniq : ∀ K₁ ∈ Vw, ∀ K₂ ∈ Vw, (derive E cfg K₁).h_j = m - 1 →
      (derive E cfg K₂).h_j = m - 1 → (derive E cfg K₁).J = (derive E cfg K₂).J)
    (hext : ∀ W ∈ Vw, m - 1 < hOf E cfg W → FGBlock.Preceq F' W) :
    phaseOf E cfg F Vw = .uncontested ∧ phaseOf E cfg F' Vw = .uncontested ∧
      (fjFrame E cfg F Vw).Z = F' ∧ (fjFrame E cfg F' Vw).Z = F' ∧
      (fjFrame E cfg F Vw).lo = m - 1 ∧ (fjFrame E cfg F' Vw).lo = m - 1 ∧
      (fjFrame E cfg F' Vw).D = (fjFrame E cfg F Vw).D := by
  -- K carries the pair `(m − 1, F′)`: `h_F(K) = m−1 ≤ h_j(K) < h(K) ≤ m`.
  have hKH := le_frontier E cfg hK
  unfold hOf at hKH
  rw [hfront] at hKH
  have hFj := heights_ordered E cfg K
  have hjh := justified_below_height E cfg K
  have hKj : (derive E cfg K).h_j = m - 1 := by homega
  have hKJ : (derive E cfg K).J = F' :=
    (F_eq_J_of_heights E cfg K (hKh.trans hKj.symm)).symm.trans hKF
  -- For every G ⪯ F′, the controls select `(m − 1, F′)`, with no contest.
  have hctl : ∀ G, FGBlock.Preceq G F' →
      phaseOf E cfg G Vw = .uncontested ∧ (fjControls E cfg G Vw).Z = F' ∧
        (fjControls E cfg G Vw).lo = m - 1 := by
    intro G hG
    have htop := lexMax_top_of_carrier E cfg G Vw hinj hfront K hK hKj
      (by rw [hKJ]; exact hG)
    obtain ⟨K', hK', hK'j, -, hlex⟩ := lexMax_carrier_of_top E cfg G Vw hm hinj htop
    have hJ : (fjControls E cfg G Vw).J = F' := by
      change (lexMax E cfg G Vw).2 = F'
      rw [hlex]
      exact (huniq K' hK' K hK hK'j hKj).trans hKJ
    have hHG : (fjControls E cfg G Vw).H = m := hfront
    have hjG : (fjControls E cfg G Vw).j = m - 1 := htop
    have htopG : (fjControls E cfg G Vw).H = (fjControls E cfg G Vw).j + 1 := by homega
    have hc : (fjControls E cfg G Vw).contest = false := by
      rw [top_contest E cfg G Vw htopG, decide_eq_false_iff_not]
      rintro ⟨W, hW, hWh, hn⟩
      apply hn
      rw [hJ]
      apply hext W hW
      rw [hWh, hHG]
      homega
    obtain ⟨hp, hr, -⟩ := top_uncontested E cfg G Vw htopG hc
    refine ⟨hp, ?_, ?_⟩
    · unfold Controls.Z
      rw [hr, ite_eq_left rfl, hJ]
    · unfold Controls.lo
      rw [hc, ite_eq_right Bool.false_ne_true, hHG]
  obtain ⟨hp, hZ, hlo⟩ := hctl F hFF'
  obtain ⟨hp', hZ', hlo'⟩ := hctl F' (preceq_refl F')
  refine ⟨hp, hp', hZ, hZ', hlo, hlo', ?_⟩
  change filteredFrom E cfg (fjControls E cfg F' Vw) Vw =
    filteredFrom E cfg (fjControls E cfg F Vw) Vw
  ext B
  rw [mem_filteredFrom, mem_filteredFrom, hZ, hZ', hlo, hlo']
  constructor
  · rintro ⟨hB, -, hZB, hw⟩
    exact ⟨hB, preceq_trans hFF' hZB, hZB, hw⟩
  · rintro ⟨hB, -, hZB, hw⟩
    exact ⟨hB, hZB, hZB, hw⟩

/-- [pin fj.twoChanges.core.v1] (item 3 (iii)) A finalization at m or above
needs a carrier above m, so it ends the no-rise interval at m. -/
theorem Fmove_atFrontier (K : FGBlock V) (hK : K ∈ Vw) (hKh : m ≤ (derive E cfg K).h_F) :
    m < frontier E cfg Vw := by
  have h1 := finalized_below_height E cfg K
  have h2 := le_frontier E cfg hK
  unfold hOf at h2
  homega

/-! ### Review Focus 6: an F move does not keep D (Astra G02)

`B1`, `B2`, `B3` are the G02 chain of `Store.lean`: `B1` (slot 1) justifies
genesis at height 1 (state height 2); `B2` (slot 2) justifies `B1` at height 2
(state height 3); `B3` (slot 3) carries three timeouts for `(3, B2)` with the
finality pair `(2, B1)`: state height 4, and it finalizes `B1`. In the view
`{genesis, B1, B2, B3}` (`m = 4`) the top pair is `(2, B1)`, below `m − 1 = 3`:
both frames are gap frames with `lo = 3`. The move F = genesis → F′ = B1 is case
(i) of item 3 (`h(B1) = 2 < m − 1`): D is cut at B1, and genesis, an ancestor of
B1, leaves D. -/

/-- The G02 view: frontier 4, `h(B1) = 2`, top pair `(2, B1)` below `m − 1 = 3`. -/
example : frontier E4 cfg1 {.genesis, B1, B2, B3} = 4 ∧ hOf E4 cfg1 B1 = 2 ∧
    (fjFrame E4 cfg1 .genesis {.genesis, B1, B2, B3}).j = 2 ∧
    (fjFrame E4 cfg1 .genesis {.genesis, B1, B2, B3}).J = B1 := by
  decide +kernel

/-- Both frames are gap frames with `lo = 3`; the normalized frame is the same. -/
example : phaseOf E4 cfg1 .genesis {.genesis, B1, B2, B3} = .gap ∧
    phaseOf E4 cfg1 B1 {.genesis, B1, B2, B3} = .gap ∧
    (fjFrame E4 cfg1 .genesis {.genesis, B1, B2, B3}).lo = 3 ∧
    (fjFrame E4 cfg1 B1 {.genesis, B1, B2, B3}).lo = 3 ∧
    nFrame E4 cfg1 .genesis {.genesis, B1, B2, B3} = nFrame E4 cfg1 B1 {.genesis, B1, B2, B3} := by
  decide +kernel

/-- The old D holds genesis; the new D does not: D is cut at F′ = B1. -/
example : FGBlock.genesis ∈ (fjFrame E4 cfg1 .genesis {.genesis, B1, B2, B3}).D ∧
    FGBlock.genesis ∉ (fjFrame E4 cfg1 B1 {.genesis, B1, B2, B3}).D ∧
    (fjFrame E4 cfg1 .genesis {.genesis, B1, B2, B3}).D = {.genesis, B1, B2, B3} ∧
    (fjFrame E4 cfg1 B1 {.genesis, B1, B2, B3}).D = {B1, B2, B3} := by
  decide +kernel

/-! ### `Fmove_atTop`: the hypotheses are satisfiable

`K3` is a child of `B2` (slot 3) with three rows that carry only the finality
pair `(2, B1)`. It finalizes `B1` at height 2 and stays at state height 3. In
the view `{genesis, B1, B2, K3}` (`m = 3`), the move F = genesis → F′ = B1 is
case (ii) of item 3. `K3` has body 0, as every block of the G02 chain. The
hypothesis `ViewRootInj` holds on this finite view (`K3_roots`). -/

/-- [helper] A row with no height pair and the finality pair `(2, B1)`. -/
def rowK3 (i : Fin 4) : Row (Fin 4) := ⟨i, .empty, some ⟨2, B1.root⟩⟩

def K3 : FGBlock (Fin 4) := .node B2 3 ⟨16⟩ 0 [rowK3 0, rowK3 1, rowK3
  2]

/-- The decidable hypotheses of `Fmove_atTop` hold with `K = K3`, `F = genesis`,
`F′ = B1`, `m = 3`. -/
example : frontier E4 cfg1 {.genesis, B1, B2, K3} = 3 ∧
    FGBlock.Preceq (FGBlock.genesis : FGBlock (Fin 4)) B1 ∧
    hOf E4 cfg1 K3 = 3 ∧ (derive E4 cfg1 K3).F = B1 ∧ (derive E4 cfg1 K3).h_F = 2 ∧
    (∀ K₁ ∈ ({.genesis, B1, B2, K3} : View (Fin 4)),
      ∀ K₂ ∈ ({.genesis, B1, B2, K3} : View (Fin 4)),
        (derive E4 cfg1 K₁).h_j = 2 → (derive E4 cfg1 K₂).h_j = 2 →
          (derive E4 cfg1 K₁).J = (derive E4 cfg1 K₂).J) ∧
    (∀ W ∈ ({.genesis, B1, B2, K3} : View (Fin 4)), 2 < hOf E4 cfg1 W →
      FGBlock.Preceq B1 W) := by
  decide +kernel

/-- The conclusions of `Fmove_atTop`: both phases are uncontested, Z = B1,
lo = 2, and D does not change. -/
example : phaseOf E4 cfg1 .genesis {.genesis, B1, B2, K3} = .uncontested ∧
    phaseOf E4 cfg1 B1 {.genesis, B1, B2, K3} = .uncontested ∧
    (fjFrame E4 cfg1 .genesis {.genesis, B1, B2, K3}).Z = B1 ∧
    (fjFrame E4 cfg1 B1 {.genesis, B1, B2, K3}).Z = B1 ∧
    (fjFrame E4 cfg1 .genesis {.genesis, B1, B2, K3}).lo = 2 ∧
    (fjFrame E4 cfg1 B1 {.genesis, B1, B2, K3}).lo = 2 ∧
    (fjFrame E4 cfg1 B1 {.genesis, B1, B2, K3}).D =
      (fjFrame E4 cfg1 .genesis {.genesis, B1, B2, K3}).D := by
  decide +kernel

/-- [ROOT-DIGEST W1; DC RootInjectiveOnAncestors] The finite K3 scope has distinct roots. -/
private theorem K3_roots : ViewRootInj ({.genesis, B1, B2, K3} : View (Fin 4)) := by
  intro A B hA hB hr
  simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp,
    exists_eq_left, FGBlock.Preceq, FGBlock.preceq, B1, B2, K3, Bool.or_eq_true,
    decide_eq_true_eq, or_assoc] at hA hB
  rcases hA with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    rcases hB with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
    first | rfl | simp only [FGBlock.root, genesisRoot, BlockId.mk.injEq,
      Nat.reduceEqDiff] at hr

/-- [ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
`Fmove_atTop` applies to `K3`: `K3_roots` gives its root hypothesis,
and each other hypothesis is decided. -/
example : (fjFrame E4 cfg1 B1 {.genesis, B1, B2, K3}).D =
    (fjFrame E4 cfg1 .genesis {.genesis, B1, B2, K3}).D :=
  (Fmove_atTop E4 cfg1 (m := 3) (F := .genesis) (F' := B1) (by decide) K3_roots
    (by decide +kernel) (by decide) K3 (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)).2.2.2.2.2.2

/-- Reuse the cut equation and top-J equality from `Fmove_filtered`.
Reflexivity retains F′; ancestry antisymmetry excludes each strict ancestor.
DC: none; INTENTIONAL addition: FJ phase-dependent domain; record
blueprint/21-healing.md:691–694, 2579–2581. -/
theorem lowerF_domain_identity : LowerFDomainIdentityStatement := by
  intro V _ _ _ E cfg c F' blocks hFF' hband hroot hext
  obtain ⟨hcut, hancestor, htop⟩ := Fmove_filtered E cfg c F' blocks hFF' hband hroot hext
  dsimp only
  refine ⟨hcut, ?_, htop⟩
  intro B hB
  constructor
  · intro hremoved
    refine ⟨hancestor B hB hremoved, ?_⟩
    intro hEq
    subst B
    apply hremoved
    rw [hcut, Finset.mem_filter]
    exact ⟨hB, preceq_refl F'⟩
  · rintro ⟨hBF', hne⟩ hnew
    rw [hcut, Finset.mem_filter] at hnew
    exact hne (preceq_antisymm hBF' hnew.2)

end AvailableChain.KitFG
end
