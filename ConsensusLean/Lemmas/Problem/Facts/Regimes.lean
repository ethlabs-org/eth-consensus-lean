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

/-- At zero look-back, η-readiness is plain readiness. -/
theorem etaReadyAbove_zero_iff {θ : ℚ} {c t : Time} :
    p.EtaReadyAbove θ 0 c t ↔ p.ReadyAbove θ c t := by
  unfold EtaReadyAbove
  simp only [le_refl, ↓reduceIte]

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

/-- A population premise implies full-committee participation at an earlier look-ahead. -/
theorem EtaSleepyOn.committee_univ {θ : ℚ} {η c W W' a b : Time}
    (h : p.EtaSleepyOn θ η c W a b) (hW : W' ≤ W) (hθ : θ ≤ 1) (h0 : 0 ≤ θ) :
    p.CommitteeSleepyOn (fun _ => Finset.univ) θ η c W' a b := by
  intro t hat htb _
  have ht := (h t hat htb).retain_mono
    (min_le_min_right _ (show t + W' ≤ t + W by linarith)) hθ h0
  simpa [lookAhead, EtaReadyAbove, ReadyAbove, faultCount] using ht

/-- **The opponents of the ready validators** inside a set `K`, from a half-threshold look-back
count on the view retained through `e`: on the view retained through any `d ≤ e`, the validators
seen awake in `[max 0 (t − η), t]` but not ready, together with those compromised by `d`, are fewer
than the ready ones. Ready validators are honest, so they are disjoint from the compromised ones;
retaining through an earlier time keeps every ready validator and charges fewer faults. -/
theorem opponents_inter_lt_of_retain {η c t d e : Time} (K : Finset V) (hde : d ≤ e)
    (h : (1 / 2 : ℚ) * ((((p.retain e).readyAt c t ∪ (p.retain e).awakeIn (max 0 (t - η)) t ∪
      (p.retain e).faultyAt t) ∩ K).card : ℚ) < (((p.retain e).readyAt c t ∩ K).card : ℚ)) :
    ((((p.retain d).awakeIn (max 0 (t - η)) t \ (p.retain d).readyAt c t) ∪
      (p.retain d).faultyAt t) ∩ K).card < ((p.retain d).readyAt c t ∩ K).card := by
  classical
  have hRF : ∀ v ∈ (p.retain e).readyAt c t, v ∉ (p.retain e).faultyAt t :=
    fun v hv => (Finset.mem_filter.mp hv).2.1
  have hR : (p.retain e).readyAt c t ⊆ (p.retain d).readyAt c t := by
    intro v hv
    simp only [readyAt, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact ⟨fun hf => hv.1 (p.faultyAt_mono hde hf), hv.2⟩
  have hopp : ((p.retain d).awakeIn (max 0 (t - η)) t \ (p.retain d).readyAt c t) ∪
      (p.retain d).faultyAt t ⊆ ((p.retain e).awakeIn (max 0 (t - η)) t \
        (p.retain e).readyAt c t) ∪ (p.retain e).faultyAt t := by
    intro v hv
    by_cases hf : v ∈ (p.retain e).faultyAt t
    · exact Finset.mem_union_right _ hf
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨hi, hr⟩ := Finset.mem_sdiff.mp hv
      refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨?_, fun h => hr (hR h)⟩)
      simp only [awakeIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      obtain ⟨u, hau, hut, -, haw⟩ := hi
      exact ⟨u, hau, hut, hf, haw⟩
    · exact Finset.mem_union_right _ (p.faultyAt_mono hde hv)
  set R := (p.retain e).readyAt c t
  set I := (p.retain e).awakeIn (max 0 (t - η)) t
  set F := (p.retain e).faultyAt t
  have heq : (R ∪ I ∪ F) ∩ K = (R ∩ K) ∪ (((I \ R) ∪ F) ∩ K) := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    tauto
  have hdisj : Disjoint (R ∩ K) (((I \ R) ∪ F) ∩ K) := by
    refine Finset.disjoint_left.mpr fun v hv hw => ?_
    rcases Finset.mem_union.mp (Finset.mem_inter.mp hw).1 with hi | hf
    · exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_inter.mp hv).1
    · exact hRF v (Finset.mem_inter.mp hv).1 hf
  rw [heq, Finset.card_union_of_disjoint hdisj] at h
  have he : (((I \ R) ∪ F) ∩ K).card < (R ∩ K).card := by
    have hq : ((((I \ R) ∪ F) ∩ K).card : ℚ) < (R ∩ K).card := by
      push_cast at h
      linarith
    exact_mod_cast hq
  calc ((((p.retain d).awakeIn (max 0 (t - η)) t \ (p.retain d).readyAt c t) ∪
        (p.retain d).faultyAt t) ∩ K).card
      ≤ (((I \ R) ∪ F) ∩ K).card :=
        Finset.card_le_card (Finset.inter_subset_inter hopp (Finset.Subset.refl _))
    _ < (R ∩ K).card := he
    _ ≤ ((p.retain d).readyAt c t ∩ K).card :=
        Finset.card_le_card (Finset.inter_subset_inter hR (Finset.Subset.refl _))

end EnvPoint

namespace System.Outage

variable {V : Type} [Fintype V] [DecidableEq V] {S : System V} {Prog : Type}
  {X : External S} {K : Contract Prog} {T b₀ b₁ : Time} {r : S.Run}

/-- An outage run satisfies the timing conjunct `OutageTimes`. -/
theorem times (h : S.Outage X K T b₀ b₁ r) :
    OutageTimes K.params (S.pt r).env.ΔAC T b₀ b₁ := h.1

/-- An outage run satisfies the network conjunct `OutageNet`. -/
theorem net (h : S.Outage X K T b₀ b₁ r) :
    (S.log r).OutageNet (S.pt r) b₀ b₁ := h.2.1

/-- An outage run satisfies the population η-sleepy conjunct `EtaSleepyOn` on the horizon. -/
theorem etaSleepy (h : S.Outage X K T b₀ b₁ r) :
    (S.pt r).EtaSleepyOn K.params.θ ((K.params.η : Time) * (S.pt r).env.ΔAC)
      (max (S.cDur K r) ((K.params.η : Time) * (S.pt r).env.ΔAC - 1))
      (S.aheadDur K r) 0 (S.pt r).horizon := h.2.2.1

/-- An outage run satisfies the look-back committee η-sleepy conjunct `CommitteeSleepyOn` on the
horizon, for each look-back `δ ∈ [0, η·ΔAC]` (selection at `max 0 (t − δ)`). -/
theorem committeeSleepy (h : S.Outage X K T b₀ b₁ r) {δ : Time} (h0 : 0 ≤ δ)
    (hδ : δ ≤ (K.params.η : Time) * (S.pt r).env.ΔAC) :
    (S.pt r).CommitteeSleepyOn (fun t => X.selected (S.pt r).env (X.ext r) (max 0 (t - δ)))
      K.params.θ ((K.params.η : Time) * (S.pt r).env.ΔAC)
      (max (S.cDur K r) ((K.params.η : Time) * (S.pt r).env.ΔAC - 1))
      (S.committeeAheadDur K r) 0 (S.pt r).horizon := h.2.2.2 δ h0 hδ

end System.Outage

end Consensus

end
