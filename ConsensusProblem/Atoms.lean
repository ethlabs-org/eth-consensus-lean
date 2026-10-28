module
public import ConsensusProblem.Premise

@[expose] public section

/-! # Environment atoms: monotonicity and counting (layer 0)

Facts about the participation and fault-bound vocabulary of `Basic`: each
threshold is monotone in its fraction; two standard fractions as integer
inequalities; an inclusive `ReadyOfAllAtLeast 1` forces an empty faulty set
(why inclusive fractions must stay below 1); and the counting step from
"more than half of all validators ready" to the FG-SA outage bound. -/

namespace Consensus

namespace EnvPoint

variable {V : Type} [Fintype V] [DecidableEq V] (p : EnvPoint V)

/-- `ReadyAbove ½` is "more ready than faulty". -/
theorem readyAbove_half_iff (c t : Time) : p.ReadyAbove (1 / 2) c t ↔ p.ReadyMajority c t := by
  unfold ReadyAbove ReadyMajority
  constructor <;> intro h
  · exact_mod_cast (show (p.faulty.card : ℚ) < (p.readyAt c t).card by linarith)
  · have h' : (p.faulty.card : ℚ) < (p.readyAt c t).card := by exact_mod_cast h
    linarith

/-- Fewer than a third faulty, as an integer inequality. -/
theorem faultsBelow_third_iff : p.FaultsBelow (1 / 3) ↔ 3 * p.faulty.card < Fintype.card V := by
  unfold FaultsBelow
  constructor <;> intro h
  · exact_mod_cast (show (3 : ℚ) * p.faulty.card < Fintype.card V by linarith)
  · have h' : (3 : ℚ) * p.faulty.card < Fintype.card V := by exact_mod_cast h
    linarith

/-- Fewer than a quarter faulty, as an integer inequality. -/
theorem faultsBelow_quarter_iff : p.FaultsBelow (1 / 4) ↔ 4 * p.faulty.card < Fintype.card V := by
  unfold FaultsBelow
  constructor <;> intro h
  · exact_mod_cast (show (4 : ℚ) * p.faulty.card < Fintype.card V by linarith)
  · have h' : (4 : ℚ) * p.faulty.card < Fintype.card V := by exact_mod_cast h
    linarith

/-- A smaller ready fraction is weaker. -/
theorem ReadyAbove.mono {θ θ' : ℚ} {c t : Time} (h : p.ReadyAbove θ' c t)
    (hle : θ ≤ θ') : p.ReadyAbove θ c t :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle (by positivity)) h

/-- A larger fault bound is weaker. -/
theorem FaultsBelow.mono {β β' : ℚ} (h : p.FaultsBelow β') (hle : β' ≤ β) : p.FaultsBelow β :=
  lt_of_lt_of_le h (mul_le_mul_of_nonneg_right hle (by positivity))

omit [DecidableEq V] in
/-- A smaller fraction of all validators is weaker. -/
theorem ReadyOfAll.mono {φ φ' : ℚ} {c t : Time} (h : p.ReadyOfAll φ' c t)
    (hle : φ ≤ φ') : p.ReadyOfAll φ c t :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle (by positivity)) h

omit [DecidableEq V] in
/-- A smaller inclusive fraction of all validators is weaker. -/
theorem ReadyOfAllAtLeast.mono {φ φ' : ℚ} {c t : Time} (h : p.ReadyOfAllAtLeast φ' c t)
    (hle : φ ≤ φ') : p.ReadyOfAllAtLeast φ c t :=
  le_trans (mul_le_mul_of_nonneg_right hle (by positivity)) h

/-- A smaller fraction and a shorter look-back are weaker. -/
theorem EtaSleepy.mono {θ θ' : ℚ} {η η' c t : Time} (h : p.EtaSleepy θ' η' c t)
    (h0 : 0 ≤ θ) (hθ : θ ≤ θ') (hη : η ≤ η') : p.EtaSleepy θ η c t := by
  classical
  have hsub : p.awakeIn (t - η) t ∪ p.faulty ⊆ p.awakeIn (t - η') t ∪ p.faulty := by
    apply Finset.union_subset_union _ (Finset.Subset.refl _)
    intro v hv
    obtain ⟨hv, u, ha, hb, hw⟩ := Finset.mem_filter.mp hv
    apply Finset.mem_filter.mpr
    exact ⟨hv, u, by dsimp only [Time] at *; omega, hb, hw⟩
  have hc : ((p.awakeIn (t - η) t ∪ p.faulty).card : ℚ) ≤
      (p.awakeIn (t - η') t ∪ p.faulty).card := by exact_mod_cast Finset.card_le_card hsub
  exact lt_of_le_of_lt
    ((mul_le_mul_of_nonneg_left hc h0).trans
      (mul_le_mul_of_nonneg_right hθ (by positivity))) h

/-- All validators ready (inclusive fraction 1) forces an empty faulty set: this is
why inclusive fractions are well-formed only below 1. -/
theorem readyOfAllAtLeast_one_faulty_empty {c t : Time} (h : p.ReadyOfAllAtLeast 1 c t) :
    p.faulty = ∅ := by
  classical
  have hr : p.readyAt c t ⊆ p.honest := Finset.filter_subset _ _
  have hc := Finset.card_le_card hr
  have hn : Fintype.card V ≤ (p.readyAt c t).card := by
    unfold ReadyOfAllAtLeast at h
    exact_mod_cast (by simpa using h : (Fintype.card V : ℚ) ≤ (p.readyAt c t).card)
  have heq : p.honest = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simpa using (hn.trans hc))
  simp [EnvPoint.faulty, heq]

/-- If every validator ready at `t` is in an honest set `C`, and `W` avoids
`C`, then more than half of all validators ready gives `2·|faulty ∪ W| < n`
(the FG-SA `OutageE1` shape, for `C` = covered, `W` = uncovered outage
wakers). -/
theorem two_mul_card_faulty_union_lt {c t : Time} {C W : Finset V}
    (hR : p.readyAt c t ⊆ C) (hC : C ⊆ p.honest) (hW : Disjoint W C)
    (h : p.ReadyOfAll (1 / 2) c t) : 2 * (p.faulty ∪ W).card < Fintype.card V := by
  have hdis : Disjoint (p.faulty ∪ W) C := by
    refine Finset.disjoint_union_left.mpr ⟨?_, hW⟩
    refine Finset.disjoint_left.mpr fun v hv hvC => ?_
    exact (Finset.mem_sdiff.mp hv).2 (hC hvC)
  have hsum : (p.faulty ∪ W).card + C.card ≤ Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hdis]
    exact Finset.card_le_univ _
  have hRC : (p.readyAt c t).card ≤ C.card := Finset.card_le_card hR
  have h' : (Fintype.card V : ℚ) < 2 * (p.readyAt c t).card := by
    unfold ReadyOfAll at h; linarith
  have h'' : Fintype.card V < 2 * (p.readyAt c t).card := by exact_mod_cast h'
  omega

end EnvPoint

end Consensus

end
