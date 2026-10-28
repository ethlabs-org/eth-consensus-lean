module
public import ConsensusProblem.Properties
public import Mathlib.Tactic

@[expose] public section

/-! # Environment atoms: monotonicity and counting (layer 0)

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

/-- With look-back `0`, η-sleepy is plain sleepy: the validators ready at
some time in `[t, t]` are those ready at `t`, all honest, so disjoint from
the faulty ones. -/
theorem etaReadyAbove_zero (θ : ℚ) (c t : Time) :
    p.EtaReadyAbove θ 0 c t ↔ p.ReadyAbove θ c t := by
  classical
  have hin : p.readyIn c (t - 0) t = p.readyAt c t := by
    ext v
    simp only [readyIn, readyAt, Finset.mem_filter, sub_zero]
    constructor
    · rintro ⟨hv, u, h1, h2, hr⟩
      exact ⟨hv, (le_antisymm h2 h1) ▸ hr⟩
    · rintro ⟨hv, hr⟩
      exact ⟨hv, t, le_rfl, le_rfl, hr⟩
  have hdis : Disjoint (p.readyAt c t) p.faulty := by
    refine Finset.disjoint_left.mpr fun v hv hf => ?_
    unfold readyAt at hv
    exact (Finset.mem_sdiff.mp hf).2 (Finset.mem_filter.mp hv).1
  unfold EtaReadyAbove ReadyAbove
  rw [hin, Finset.card_union_of_disjoint hdis]
  push_cast
  rfl

/-- η-sleepy (`η ≥ 0`, `θ ≥ 0`) implies plain sleepy. -/
theorem EtaReadyAbove.readyAbove {θ : ℚ} {η c t : Time} (h : p.EtaReadyAbove θ η c t)
    (h0 : 0 ≤ θ) (hη : 0 ≤ η) : p.ReadyAbove θ c t := by
  classical
  rw [← etaReadyAbove_zero]
  unfold EtaReadyAbove at h ⊢
  have hsub : p.readyIn c (t - 0) t ∪ p.faulty ⊆ p.readyIn c (t - η) t ∪ p.faulty := by
    apply Finset.union_subset_union _ (Finset.Subset.refl _)
    intro v hv
    simp only [readyIn, Finset.mem_filter, sub_zero] at hv ⊢
    obtain ⟨hv, u, h1, h2, hr⟩ := hv
    exact ⟨hv, u, by linarith, h2, hr⟩
  have hc : ((p.readyIn c (t - 0) t ∪ p.faulty).card : ℚ) ≤
      (p.readyIn c (t - η) t ∪ p.faulty).card := by exact_mod_cast Finset.card_le_card hsub
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hc h0) h

/-- A smaller fraction (`θ ≥ 0`) and a shorter look-back are weaker. -/
theorem EtaReadyAbove.mono {θ θ' : ℚ} {η η' c t : Time} (h : p.EtaReadyAbove θ' η' c t)
    (h0 : 0 ≤ θ) (hθ : θ ≤ θ') (hη : η ≤ η') : p.EtaReadyAbove θ η c t := by
  classical
  unfold EtaReadyAbove at h ⊢
  have hsub : p.readyIn c (t - η) t ∪ p.faulty ⊆ p.readyIn c (t - η') t ∪ p.faulty := by
    apply Finset.union_subset_union _ (Finset.Subset.refl _)
    intro v hv
    simp only [readyIn, Finset.mem_filter] at hv ⊢
    obtain ⟨hv, u, h1, h2, hr⟩ := hv
    exact ⟨hv, u, by linarith, h2, hr⟩
  have hc : ((p.readyIn c (t - η) t ∪ p.faulty).card : ℚ) ≤
      (p.readyIn c (t - η') t ∪ p.faulty).card := by exact_mod_cast Finset.card_le_card hsub
  exact lt_of_le_of_lt
    ((mul_le_mul_of_nonneg_left hc h0).trans
      (mul_le_mul_of_nonneg_right hθ (by positivity))) h

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

/-- If every validator ready at `t` is in an honest set `C`, and `W` avoids
`C`, then more than half of all validators ready gives `2·|faulty ∪ W| < n`
(the outage regime's cover at `b₀` with `cover = ½`). -/
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
