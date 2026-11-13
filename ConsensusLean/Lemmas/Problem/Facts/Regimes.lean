module
public import ConsensusLean.Lemmas.Problem.DerivedFacts
public import ConsensusLean.Spec.Problem.Regimes
import ConsensusLean.Lemmas.Problem.Facts.Atoms
public import Mathlib.Tactic.NormNum
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Numbers and regimes (L0 facts)

The standard thresholds are admissible; the healthy regime bounds the faults. -/

namespace Consensus

namespace Params

variable {Idx : Type}

/-- The standard thresholds are admissible. -/
theorem standard_admissible {catchUp lag budget : Nat} {heal latency : Capability → Idx → Nat}
    (h : 1 ≤ catchUp) (hb : 1 ≤ budget) :
    (standard catchUp lag budget heal latency).Admissible :=
  ⟨h, by norm_num [standard], by norm_num [standard], by norm_num [standard],
    by norm_num [standard], hb⟩

end Params

namespace EnvPoint

variable {V : Type} [Fintype V] [DecidableEq V] {p : EnvPoint V}

omit [DecidableEq V] in
/-- Healthy bounds the faults below `β`. -/
theorem HealthyOn.faultsBelow {β : ℚ} {g : Time} (h : p.HealthyOn β g p.horizon) :
    p.FaultsBelow β :=
  faultsBelow_iff.mpr h.1

/-- The outage cohort count bounds the opponents by half of all validators:
the faulty validators, the late wakers and the honest validators awake at `a`
are disjoint, so `2·|faulty ∪ late| < |faulty ∪ late| + |awake a| ≤ n`. -/
theorem CohortOn.two_mul_lt {a b : Time} (h : p.CohortOn a b)
    (hab : p.faultyAt b ⊆ p.faultyAt a) :
    2 * (p.faultyAt b ∪ p.lateWakers a b).card < Fintype.card V := by
  classical
  have hdisj : Disjoint (p.faultyAt b ∪ p.lateWakers a b) (p.awakeAt a) := by
    rw [Finset.disjoint_left]
    intro v hv ha
    have hah : v ∉ p.faultyAt a := (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha).1).2
    rcases Finset.mem_union.mp hv with hf | hl
    · exact hah (hab hf)
    · exact (Finset.mem_sdiff.mp hl).2 ha
  have hcard := Finset.card_union_of_disjoint hdisj
  have hle := Finset.card_le_univ ((p.faultyAt b ∪ p.lateWakers a b) ∪ p.awakeAt a)
  unfold CohortOn at h
  omega

/-- η-sleepy (`θ ≥ 0`) implies plain sleepy. -/
theorem EtaReadyAbove.readyAbove {θ : ℚ} {η c t : Time} (h : p.EtaReadyAbove θ η c t)
    (h0 : 0 ≤ θ) : p.ReadyAbove θ c t := by
  classical
  unfold EtaReadyAbove at h
  split_ifs at h with hη
  · exact h
  rw [readyAbove_iff_union]
  have hsub : p.readyAt c t ∪ p.faultyAt t ⊆
      p.readyAt c t ∪ p.awakeIn (max 0 (t - η)) t ∪ p.faultyAt t :=
    Finset.union_subset_union Finset.subset_union_left (Finset.Subset.refl _)
  have hc : ((p.readyAt c t ∪ p.faultyAt t).card : ℚ) ≤
      (p.readyAt c t ∪ p.awakeIn (max 0 (t - η)) t ∪ p.faultyAt t).card := by
    exact_mod_cast Finset.card_le_card hsub
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hc h0) h

omit [DecidableEq V] in
/-- Retaining through an earlier time weakens the sleepy budget: fewer faults
are charged and more ready validators survive. -/
theorem ReadyAbove.retain_mono {θ : ℚ} {c t d e : Time}
    (h : (p.retain e).ReadyAbove θ c t) (hde : d ≤ e) (hθ : θ ≤ 1) (h0 : 0 ≤ θ) :
    (p.retain d).ReadyAbove θ c t := by
  classical
  have hr : (p.retain e).readyAt c t ⊆ (p.retain d).readyAt c t := by
    intro v hv
    simp only [readyAt, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact ⟨fun hf => hv.1 (p.faultyAt_mono hde hf), hv.2⟩
  have hrc : ((p.retain e).readyAt c t).card ≤ ((p.retain d).readyAt c t).card :=
    Finset.card_le_card hr
  have hfc : (p.faultyAt d).card ≤ (p.faultyAt e).card :=
    Finset.card_le_card (p.faultyAt_mono hde)
  have hrq : (((p.retain e).readyAt c t).card : ℚ) ≤
      ((p.retain d).readyAt c t).card := by exact_mod_cast hrc
  have hfq : ((p.faultyAt d).card : ℚ) ≤ (p.faultyAt e).card := by exact_mod_cast hfc
  have hmul := mul_le_mul_of_nonneg_left hfq h0
  have hdiff := mul_nonneg (sub_nonneg.mpr hθ) (sub_nonneg.mpr hrq)
  change θ * (((p.retain e).readyAt c t).card + (p.faultyAt e).card : ℚ) <
    ((p.retain e).readyAt c t).card at h
  change θ * (((p.retain d).readyAt c t).card + (p.faultyAt d).card : ℚ) <
    ((p.retain d).readyAt c t).card
  linarith

omit [DecidableEq V] in
/-- A full-run sleepy premise remains valid when its look-ahead is clamped
at an earlier prefix horizon. -/
theorem SleepyOn.prefix {θ : ℚ} {c W a b : Time} (h : p.SleepyOn θ c W a b)
    (hb : b ≤ p.horizon) (hθ : θ ≤ 1) (h0 : 0 ≤ θ) :
    ({ p with horizon := b } : EnvPoint V).SleepyOn θ c W a b := by
  intro t hat htb
  exact (h t hat htb).retain_mono (min_le_min_left _ hb) hθ h0

/-- The identity-sensitive sleepy budget also weakens at an earlier retention
time: any lost honest support is included among the later faults. -/
theorem EtaReadyAbove.retain_mono {θ : ℚ} {η c t d e : Time}
    (h : (p.retain e).EtaReadyAbove θ η c t) (hde : d ≤ e)
    (hθ : θ ≤ 1) (h0 : 0 ≤ θ) : (p.retain d).EtaReadyAbove θ η c t := by
  classical
  unfold EtaReadyAbove at h ⊢
  split_ifs at h ⊢ with hη
  · exact h.retain_mono hde hθ h0
  have hr : (p.retain e).readyAt c t ⊆ (p.retain d).readyAt c t := by
    intro v hv
    simp only [readyAt, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact ⟨fun hf => hv.1 (p.faultyAt_mono hde hf), hv.2⟩
  have hs : (p.retain d).readyAt c t ∪ (p.retain d).awakeIn (max 0 (t - η)) t ∪
      p.faultyAt d ⊆ (p.retain e).readyAt c t ∪ (p.retain e).awakeIn (max 0 (t - η)) t ∪
      p.faultyAt e := by
    intro v hv
    by_cases hf : v ∈ p.faultyAt e
    · exact Finset.mem_union_right _ hf
    apply Finset.mem_union_left
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_union.mp hv with hv | hv
      · apply Finset.mem_union_left
        simp only [readyAt, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        exact ⟨hf, hv.2⟩
      · apply Finset.mem_union_right
        simp only [awakeIn, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        obtain ⟨u, hau, hut, -, haw⟩ := hv
        exact ⟨u, hau, hut, hf, haw⟩
    · exact False.elim (hf (p.faultyAt_mono hde hv))
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by
    exact_mod_cast Finset.card_le_card hs) h0)
    (lt_of_lt_of_le h (by exact_mod_cast Finset.card_le_card hr))

/-- Clamp an η-sleepy premise at the prefix horizon. -/
theorem EtaSleepyOn.prefix {θ : ℚ} {η c W a b : Time} (h : p.EtaSleepyOn θ η c W a b)
    (hb : b ≤ p.horizon) (hθ : θ ≤ 1) (h0 : 0 ≤ θ) :
    ({ p with horizon := b } : EnvPoint V).EtaSleepyOn θ η c W a b := by
  intro t hat htb
  exact (h t hat htb).retain_mono (min_le_min_left _ hb) hθ h0

/-- Full committees recover the population η-sleepy predicate. -/
theorem committeeSleepyOn_univ_iff [Nonempty V] {θ : ℚ} {η c W a b : Time} :
    p.CommitteeSleepyOn (fun _ => Finset.univ) θ η c W a b ↔
      p.EtaSleepyOn θ η c W a b := by
  simp [CommitteeSleepyOn, EtaSleepyOn, EtaReadyAbove, ReadyAbove, faultCount]

/-- A population premise implies full-committee participation at an earlier look-ahead. -/
theorem EtaSleepyOn.committee_univ {θ : ℚ} {η c W W' a b : Time}
    (h : p.EtaSleepyOn θ η c W a b) (hW : W' ≤ W) (hθ : θ ≤ 1) (h0 : 0 ≤ θ) :
    p.CommitteeSleepyOn (fun _ => Finset.univ) θ η c W' a b := by
  intro t hat htb _
  have ht := (h t hat htb).retain_mono
    (min_le_min_right _ (show t + W' ≤ t + W by linarith)) hθ h0
  simpa [lookAhead, EtaReadyAbove, ReadyAbove, faultCount] using ht

/-- At each band time, a full committee asks for exactly the stock cohort inequality. -/
theorem committeeCohortOn_univ_iff [Nonempty V] {a z lo hi : Time} :
    p.CommitteeCohortOn (fun _ => Finset.univ) a z lo hi ↔
      ∀ t, max 0 lo ≤ t → t ≤ hi → t ≤ p.horizon → p.CohortOn a z := by
  simp only [CommitteeCohortOn, CohortOn, Finset.inter_univ, Finset.univ_nonempty,
    true_implies]

/-- A population cohort satisfies every full-committee band, including an empty band. -/
theorem CohortOn.committee_univ {a z lo hi : Time} (h : p.CohortOn a z) :
    p.CommitteeCohortOn (fun _ => Finset.univ) a z lo hi := by
  intro _ _ _ _ _
  simpa only [CohortOn, Finset.inter_univ] using h

end EnvPoint

namespace System.Outage

variable {V : Type} [Fintype V] [DecidableEq V] {S : System V} {Prog : Type}
  {X : External S} {K : Contract Prog} {T b₀ b₁ : Time} {r : S.Run}

theorem times (h : S.Outage X K T b₀ b₁ r) :
    OutageTimes K.params (S.pt r).env.ΔAC T b₀ b₁ := h.1

theorem net (h : S.Outage X K T b₀ b₁ r) :
    (S.log r).OutageNet (S.pt r) b₀ b₁ := h.2.1

theorem etaSleepy (h : S.Outage X K T b₀ b₁ r) :
    (S.pt r).EtaSleepyOn K.params.θ ((K.params.η : Time) * (S.pt r).env.ΔAC)
      (S.cDur K r) (S.aheadDur K r) 0 (S.pt r).horizon := h.2.2.1

theorem noSleep (h : S.Outage X K T b₀ b₁ r) :
    ((S.pt r).retain (S.cohortAt K b₁ r)).NoSleepOn
      (S.outageStart K b₀ r) (S.outageEnd K b₁ r) := h.2.2.2.1

theorem cohort (h : S.Outage X K T b₀ b₁ r) :
    ((S.pt r).retain (S.cohortAt K b₁ r)).CohortOn
      (S.outageStart K b₀ r) (S.outageEnd K b₁ r) := h.2.2.2.2.1

theorem committeeCohort (h : S.Outage X K T b₀ b₁ r) :
    ((S.pt r).retain (S.cohortAt K b₁ r)).CommitteeCohortOn
      (X.selected (S.pt r).env (X.ext r)) (S.outageStart K b₀ r) (S.outageEnd K b₁ r)
      (S.bandStart K b₀ r) (S.bandEnd K b₀ r) := h.2.2.2.2.2.1

theorem committeeSleepy (h : S.Outage X K T b₀ b₁ r) :
    (S.pt r).CommitteeSleepyOn (X.selected (S.pt r).env (X.ext r)) K.params.θ
      ((K.params.η : Time) * (S.pt r).env.ΔAC) (S.cDur K r) (S.committeeAheadDur K r)
      0 (S.pt r).horizon := h.2.2.2.2.2.2

end System.Outage

end Consensus

end
