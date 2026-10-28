module
public import ConsensusProblem.Properties
public import Mathlib.Tactic

@[expose] public section

/-! # Environment atoms: monotonicity and counting (L0)

Facts about the participation and fault-bound vocabulary of `Basic`: each
threshold is monotone in its parameter, and a counting step from "more than
half of all validators ready" to a bound on the faulty validators together
with an honest set that avoids the ready ones. -/

namespace Consensus

namespace EnvPoint

variable {V : Type} [Fintype V] [DecidableEq V] (p : EnvPoint V)

/-- A smaller ready fraction is weaker. -/
theorem ReadyAbove.mono {θ θ' : ℚ} {c t : Time} (h : p.ReadyAbove θ' c t)
    (hle : θ ≤ θ') : p.ReadyAbove θ c t :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle (by positivity)) h

/-- With look-back `0`, η-sleepy is plain sleepy (by definition). -/
theorem etaReadyAbove_zero (θ : ℚ) (c t : Time) :
    p.EtaReadyAbove θ 0 c t ↔ p.ReadyAbove θ c t := by
  rw [EtaReadyAbove, ite_eq_left_of_eq_true _ _ (eq_true le_rfl)]

/-- Plain sleepy as a count over `ready ∪ faulty` (the two are disjoint). -/
theorem readyAbove_iff_union (θ : ℚ) (c t : Time) :
    p.ReadyAbove θ c t ↔ θ * ((p.readyAt c t ∪ p.faulty).card : ℚ) < (p.readyAt c t).card := by
  classical
  have hdis : Disjoint (p.readyAt c t) p.faulty := by
    refine Finset.disjoint_left.mpr fun v hv hf => ?_
    unfold readyAt at hv
    exact (Finset.mem_sdiff.mp hf).2 (Finset.mem_filter.mp hv).1
  unfold ReadyAbove
  rw [Finset.card_union_of_disjoint hdis]
  push_cast
  rfl

/-- The η-sleepy count set grows with the look-back window. -/
theorem etaSet_mono {η η' c t : Time} (hη : η ≤ η') :
    p.readyAt c t ∪ p.awakeIn (max 0 (t - η)) t ∪ p.faulty ⊆
      p.readyAt c t ∪ p.awakeIn (max 0 (t - η')) t ∪ p.faulty := by
  classical
  refine Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) ?_)
    (Finset.Subset.refl _)
  intro v hv
  simp only [awakeIn, Finset.mem_filter] at hv ⊢
  obtain ⟨hv, u, h1, h2, ha⟩ := hv
  exact ⟨hv, u, le_trans (max_le_max le_rfl (by linarith)) h1, h2, ha⟩

/-- η-sleepy (`θ ≥ 0`) implies plain sleepy. -/
theorem EtaReadyAbove.readyAbove {θ : ℚ} {η c t : Time} (h : p.EtaReadyAbove θ η c t)
    (h0 : 0 ≤ θ) : p.ReadyAbove θ c t := by
  classical
  unfold EtaReadyAbove at h
  split_ifs at h with hη
  · exact h
  rw [readyAbove_iff_union]
  have hsub : p.readyAt c t ∪ p.faulty ⊆ p.readyAt c t ∪ p.awakeIn (max 0 (t - η)) t ∪ p.faulty :=
    Finset.union_subset_union Finset.subset_union_left (Finset.Subset.refl _)
  have hc : ((p.readyAt c t ∪ p.faulty).card : ℚ) ≤
      (p.readyAt c t ∪ p.awakeIn (max 0 (t - η)) t ∪ p.faulty).card := by
    exact_mod_cast Finset.card_le_card hsub
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hc h0) h

/-- A smaller fraction (`θ ≥ 0`) and a shorter look-back are weaker. -/
theorem EtaReadyAbove.mono {θ θ' : ℚ} {η η' c t : Time} (h : p.EtaReadyAbove θ' η' c t)
    (h0 : 0 ≤ θ) (hθ : θ ≤ θ') (hη : η ≤ η') : p.EtaReadyAbove θ η c t := by
  classical
  by_cases hη0 : η ≤ 0
  · rw [EtaReadyAbove, ite_eq_left_of_eq_true _ _ (eq_true hη0)]
    exact (h.readyAbove p (h0.trans hθ)).mono p hθ
  have hη0' : ¬ η' ≤ 0 := fun h' => hη0 (hη.trans h')
  rw [EtaReadyAbove, ite_eq_right_of_eq_false _ _ (eq_false hη0)]
  rw [EtaReadyAbove, ite_eq_right_of_eq_false _ _ (eq_false hη0')] at h
  have hc : ((p.readyAt c t ∪ p.awakeIn (max 0 (t - η)) t ∪ p.faulty).card : ℚ) ≤
      (p.readyAt c t ∪ p.awakeIn (max 0 (t - η')) t ∪ p.faulty).card := by
    exact_mod_cast Finset.card_le_card (p.etaSet_mono hη)
  exact lt_of_le_of_lt
    ((mul_le_mul_of_nonneg_left hc h0).trans
      (mul_le_mul_of_nonneg_right hθ (by positivity))) h

omit [Fintype V] [DecidableEq V] in
/-- A ready validator (catch-up `c ≥ 0`) at `t ≥ 0` is awake at `t`. -/
theorem readyAt_subset_awakeAt {c t : Time} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    p.readyAt c t ⊆ p.awakeAt t := by
  classical
  intro v hv
  simp only [readyAt, awakeAt, Finset.mem_filter] at hv ⊢
  exact ⟨hv.1, hv.2.2 t (max_le ht (by linarith)) le_rfl⟩

/-- With positive look-back, η-sleepy (`θ ≥ 0`, catch-up `c ≥ 0`, `t ≥ 0`) implies the
awake-count form: the honest validators awake at `t` exceed fraction `θ` of
those awake at some time in `[max 0 (t − η), t]` together with the faulty
ones. -/
theorem EtaReadyAbove.awakeForm {θ : ℚ} {η c t : Time} (h : p.EtaReadyAbove θ η c t)
    (h0 : 0 ≤ θ) (hη : 0 < η) (hc0 : 0 ≤ c) (ht : 0 ≤ t) :
    θ * ((p.awakeIn (max 0 (t - η)) t ∪ p.faulty).card : ℚ) < (p.awakeAt t).card := by
  classical
  rw [EtaReadyAbove, ite_eq_right_of_eq_false _ _ (eq_false (not_le.mpr hη))] at h
  have hsub : p.awakeIn (max 0 (t - η)) t ∪ p.faulty ⊆
      p.readyAt c t ∪ p.awakeIn (max 0 (t - η)) t ∪ p.faulty :=
    Finset.union_subset_union Finset.subset_union_right (Finset.Subset.refl _)
  have hc : ((p.awakeIn (max 0 (t - η)) t ∪ p.faulty).card : ℚ) ≤
      (p.readyAt c t ∪ p.awakeIn (max 0 (t - η)) t ∪ p.faulty).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hr : ((p.readyAt c t).card : ℚ) ≤ (p.awakeAt t).card := by
    exact_mod_cast Finset.card_le_card (p.readyAt_subset_awakeAt hc0 ht)
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hc h0) (lt_of_lt_of_le h hr)

/-- A larger absolute fault bound is weaker. -/
theorem FaultsAtMost.mono {m m' : Nat} (h : p.FaultsAtMost m') (hle : m' ≤ m) : p.FaultsAtMost m :=
  le_trans h hle

/-- A larger fault bound is weaker. -/
theorem FaultsBelow.mono {β β' : ℚ} (h : p.FaultsBelow β') (hle : β' ≤ β) : p.FaultsBelow β :=
  lt_of_lt_of_le h (mul_le_mul_of_nonneg_right hle (by positivity))

omit [DecidableEq V] in
/-- A smaller fraction of all validators is weaker. -/
theorem ReadyOfAll.mono {φ φ' : ℚ} {c t : Time} (h : p.ReadyOfAll φ' c t)
    (hle : φ ≤ φ') : p.ReadyOfAll φ c t :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle (by positivity)) h

omit [DecidableEq V] in
/-- A smaller fraction of all validators honest and awake is weaker. -/
theorem AwakeOfAll.mono {φ φ' : ℚ} {t : Time} (h : p.AwakeOfAll φ' t) (hle : φ ≤ φ') :
    p.AwakeOfAll φ t :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle (by positivity)) h

end EnvPoint

end Consensus

end
