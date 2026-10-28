module
public import ConsensusShape.Problem
public import Mathlib.Tactic
@[expose] public section
namespace Consensus.Shape
open Model Run
variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] {F : Family} {E : Env V}

/-- Standard assumptions retain the instance's named timing and η thresholds. -/
abbrev standard := Assumptions.standard

variable (r : Model.Run (compiled F) E) (c eta lag fastLag budget : Nat)
    (θ θrec : ℚ) (full : Bool)

local notation "A" => standard c eta lag fastLag budget θ θrec full

theorem sleepy_standard_iff : Sleepy r A ↔
    r.ExecutionValid ∧ r.PartialSynchrony ∧ E.gst = 0 ∧
      ∀ t, 0 ≤ t → t ≤ r.horizon → r.point.ReadyMajority ((c : Time) * E.Δ) t := by
  constructor
  · intro h; exact ⟨h.valid, h.sync, h.gst_zero,
      fun t ht hh => (EnvPoint.readyAbove_half_iff _ _ _).mp (h.participation t ht hh)⟩
  · rintro ⟨hv, hs, hg, hp⟩
    exact ⟨hv, hs, hg, fun t ht hh => (EnvPoint.readyAbove_half_iff _ _ _).mpr (hp t ht hh)⟩

theorem stableSleepy_standard_iff : StableSleepy r A ↔ Sleepy r A ∧
    ∀ t, 0 ≤ t → t ≤ r.horizon →
      r.point.EtaSleepy θ ((eta : Time) * E.Δ) ((c : Time) * E.Δ) t :=
  ⟨fun h => ⟨h.toSleepy, h.etaSleepy⟩, fun h => ⟨h.1, h.2⟩⟩

theorem fast_standard_iff : Fast r A ↔ Sleepy r A ∧ r.point.FullParticipation 0 ∧
    4 * r.point.faulty.card < Fintype.card V := by
  constructor
  · intro h; exact ⟨h.toSleepy, h.full, (EnvPoint.faultsBelow_quarter_iff _).mp h.belowQuarter⟩
  · rintro ⟨hs, hf, hb⟩
    exact ⟨hs, hf, (EnvPoint.faultsBelow_quarter_iff _).mpr hb⟩

theorem live_standard_iff (k : Nat) : LiveSleepy r A k ↔ Sleepy r A ∧
    Recurrence r ((c : Time) * E.Δ) 0 k :=
  ⟨fun h => ⟨h.toSleepy, h.recurrence⟩, fun h => ⟨h.1, h.2⟩⟩

theorem outage_standard_iff (T b₀ b₁ : Time) : Outage r A T b₀ b₁ ↔
    r.ExecutionValid ∧ r.HealthyPrefixDelivery b₀ ∧
    (0 ≤ T ∧ T ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ r.horizon) ∧
    T + (lag : Time) * E.Δ ≤ b₀ ∧ b₁ - b₀ ≤ (budget : Time) * E.Δ ∧
    (∀ t, 0 ≤ t → t < b₀ → r.point.ReadyMajority ((c : Time) * E.Δ) t) ∧
    (∀ t, 0 ≤ t → t < b₀ → r.point.EtaSleepy θ ((eta : Time) * E.Δ) ((c : Time) * E.Δ) t) := by
  constructor
  · intro h
    exact ⟨h.valid, h.healthy, h.interval, h.armed, h.withinBudget,
      fun t ht hh => (EnvPoint.readyAbove_half_iff _ _ _).mp (h.readyBefore t ht hh), h.etaSleepyBefore⟩
  · rintro ⟨hv, hh, hi, ha, hb, hr, he⟩
    exact ⟨hv, hh, hi, ha, hb,
      fun t ht hh => (EnvPoint.readyAbove_half_iff _ _ _).mpr (hr t ht hh), he⟩

/-- The inclusive half threshold preserves iteration 3's ceiling for odd n. -/
theorem readyAtLeast_half_iff (p : EnvPoint V) (c t : Time) :
    p.ReadyOfAllAtLeast (1/2) c t ↔
      (Fintype.card V + 1) / 2 ≤ (p.readyAt c t).card := by
  unfold EnvPoint.ReadyOfAllAtLeast
  have hiff : (1/2 : ℚ) * Fintype.card V ≤ (p.readyAt c t).card ↔
      Fintype.card V ≤ 2 * (p.readyAt c t).card := by
    constructor <;> intro h
    · exact_mod_cast (show (Fintype.card V : ℚ) ≤ 2 * (p.readyAt c t).card by linarith)
    · have : (Fintype.card V : ℚ) ≤ 2 * (p.readyAt c t).card := by exact_mod_cast h
      linarith
  rw [hiff]
  omega

theorem fastOutage_standard_iff (T b₀ b₁ : Time) : FastOutage r A T b₀ b₁ ↔
    OutageWith r A fastLag T b₀ b₁ ∧
      ∀ t, 0 ≤ t → t < b₀ →
        (Fintype.card V + 1) / 2 ≤ (r.point.readyAt ((c : Time) * E.Δ) t).card := by
  constructor
  · intro h
    exact ⟨h.toOutageWith, fun t ht hh =>
      (readyAtLeast_half_iff _ _ _).mp (h.highParticipation t ht hh)⟩
  · rintro ⟨h, hp⟩
    exact ⟨h, fun t ht hh => (readyAtLeast_half_iff _ _ _).mpr (hp t ht hh)⟩

theorem twoThirdsReady_iff (p : EnvPoint V) (c t : Time) :
    p.TwoThirdsReady c t ↔ 2 * Fintype.card V < 3 * (p.readyAt c t).card := by
  unfold EnvPoint.TwoThirdsReady EnvPoint.ReadyOfAll
  constructor <;> intro h
  · exact_mod_cast (show (2 : ℚ) * Fintype.card V < 3 * (p.readyAt c t).card by linarith)
  · have : (2 : ℚ) * Fintype.card V < 3 * (p.readyAt c t).card := by exact_mod_cast h
    linarith
/-- Standard finality participation implies its fault cap without a separate
fault premise. -/
theorem belowOneThird_of_twoThirdsReady (p : EnvPoint V) (c t : Time)
    (h : p.TwoThirdsReady c t) : p.BelowOneThird := by
  classical
  have hr := Finset.card_le_card (Finset.filter_subset
    (fun v => p.Ready c v t) p.honest)
  have hf : p.faulty.card + p.honest.card = Fintype.card V := by
    simpa [EnvPoint.faulty] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ p.honest)
  apply (EnvPoint.faultsBelow_third_iff p).mpr
  have hp := (twoThirdsReady_iff p c t).mp h
  change (p.readyAt c t).card ≤ p.honest.card at hr
  omega
end Consensus.Shape
end
