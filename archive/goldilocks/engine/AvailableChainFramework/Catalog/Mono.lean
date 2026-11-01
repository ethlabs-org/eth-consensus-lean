module
public import Mathlib.Tactic.Linarith
public import AvailableChainStatements.Generic.Claims

@[expose] public section

/-! Monotonicity lemmas for the catalog claims (L3). A `transport` proof of a
claim uses them to move a run from the regime at a weaker constant to the
regime at a stronger constant, and the conclusion in the other direction. -/

namespace AvailableChain.Framework.Catalog

open AvailableChain AvailableChain.Generic AvailableChain.Statements.Generic

/-- All time constants zero except `proposerGap = 1`, `θ = θrec = 1/2`,
`recoveryFull = false`. A claim sets only the fields that it reads. -/
def zeroConstants : Constants where
  η := 0
  D_c := 0
  D_s := 0
  D_f := 0
  armingLag := 0
  fastArmingLag := 0
  budget := 0
  recoveryBound := 0
  proposerGap := 1
  θ := 1 / 2
  θrec := 1 / 2
  recoveryFull := false

/-- A larger θ or η makes the η-sleepy inequality harder. -/
theorem etaSleepy_mono {V : Type} [DecidableEq V] [Fintype V] {n : Nat}
    {P : ProtocolSpec n} {E : Env V} {C C' : Constants} {rho : Run V P} {t : Time}
    (hθ : C.θ ≤ C'.θ) (hη : C.η ≤ C'.η) (hθ0 : 0 ≤ C.θ)
    (h : EtaSleepy E C' rho t) : EtaSleepy E C rho t := by
  unfold EtaSleepy at h ⊢
  have hsub : awakeInClosed E rho.honest (t - C.η) t ⊆
      awakeInClosed E rho.honest (t - C'.η) t := by
    classical
    intro v hv
    simp only [awakeInClosed, Finset.mem_filter] at hv ⊢
    obtain ⟨hv, u, hu₀, hu₁, hu⟩ := hv
    exact ⟨hv, u, by linarith, hu₁, hu⟩
  have hcard : ((awakeInClosed E rho.honest (t - C.η) t ∪ faulty rho).card : ℚ) ≤
      ((awakeInClosed E rho.honest (t - C'.η) t ∪ faulty rho).card : ℚ) := by
    exact_mod_cast Finset.card_le_card (Finset.union_subset_union hsub subset_rfl)
  have hnn : (0 : ℚ) ≤
      ((awakeInClosed E rho.honest (t - C'.η) t ∪ faulty rho).card : ℚ) := by positivity
  calc C.θ * ((awakeInClosed E rho.honest (t - C.η) t ∪ faulty rho).card : ℚ)
      ≤ C.θ * ((awakeInClosed E rho.honest (t - C'.η) t ∪ faulty rho).card : ℚ) :=
        mul_le_mul_of_nonneg_left hcard hθ0
    _ ≤ C'.θ * ((awakeInClosed E rho.honest (t - C'.η) t ∪ faulty rho).card : ℚ) :=
        mul_le_mul_of_nonneg_right hθ hnn
    _ < _ := h

/-- A smaller gap makes the recurrence premise harder. -/
theorem recurrence_mono {V : Type} {n : Nat} {P : ProtocolSpec n}
    {E : Env V} {I : Interface P} {rho : Run V P} {start g g' : Time}
    (hg : g' ≤ g) (h : HonestProposerRecurrence E I rho start g') :
    HonestProposerRecurrence E I rho start g := by
  intro t ht hH
  obtain ⟨s, hs₀, hs₁, hop, hp⟩ := h t ht (by linarith)
  exact ⟨s, hs₀, by linarith, hop, hp⟩

/-- Safety from a later time. -/
theorem safeFrom_mono {V : Type} [DecidableEq V] {n : Nat} {P : ProtocolSpec n}
    {rho : Run V P} {g : Output P} {t₀ t₁ : Time} (ht : t₀ ≤ t₁)
    (h : SafeFrom P rho g t₀) : SafeFrom P rho g t₁ where
  agree := fun u hu v hv t t' h₀ h₁ h₀' h₁' =>
    h.agree u hu v hv t t' (le_trans ht h₀) h₁ (le_trans ht h₀') h₁'
  monotone := fun v hv t t' h₀ h₁ h₂ => h.monotone v hv t t' (le_trans ht h₀) h₁ h₂

/-- Inclusion from a later time. -/
theorem includedFrom_mono {V : Type} [DecidableEq V] {n : Nat} {P : ProtocolSpec n}
    {E : Env V} {I : Interface P} {rho : Run V P} {g : Output P} {t₀ t₁ D : Time}
    (ht : t₀ ≤ t₁) (h : IncludedFrom P E I rho g t₀ D) : IncludedFrom P E I rho g t₁ D :=
  fun s hs hp hH => h s (lt_of_le_of_lt ht hs) hp hH

/-- The Stable Sleepy regime at a weaker constant is in the regime at a
stronger constant. -/
theorem stableSleepyRegime_mono {V : Type} [DecidableEq V] [Fintype V] {n : Nat}
    {P : ProtocolSpec n} {E : Env V} {I : Interface P} {C C' : Constants}
    {rho : Run V P} {t₀ : Time}
    (hθ : C.θ ≤ C'.θ) (hη : C.η ≤ C'.η) (hθ0 : 0 ≤ C.θ)
    (h : StableSleepyRegime P E I C' rho t₀) : StableSleepyRegime P E I C rho t₀ where
  toSleepyRegime := h.toSleepyRegime
  etaSleepy := fun t h₀ h₁ => etaSleepy_mono hθ hη hθ0 (h.etaSleepy t h₀ h₁)

/-- The Outage regime at a smaller η, θ and arming lag, and a larger budget,
contains the regime at the other constant. -/
theorem outageRegime_mono {V : Type} [DecidableEq V] [Fintype V] {n : Nat}
    {P : ProtocolSpec n} {E : Env V} {I : Interface P} {C C' : Constants}
    {rho : Run V P} {T b₀ b₁ : Time}
    (hθ : C.θ ≤ C'.θ) (hη : C.η ≤ C'.η) (hθ0 : 0 ≤ C.θ)
    (hA : C.armingLag ≤ C'.armingLag) (hB : C'.budget ≤ C.budget)
    (h : OutageRegime P E I C' rho T b₀ b₁) : OutageRegime P E I C rho T b₀ b₁ where
  execution := h.execution
  rootInjective := h.rootInjective
  healthy := h.healthy
  interval := h.interval
  armed := by have := h.armed; linarith
  withinBudget := by have := h.withinBudget; linarith
  sleepyBefore := h.sleepyBefore
  etaSleepyBefore := fun t h₀ h₁ => etaSleepy_mono hθ hη hθ0 (h.etaSleepyBefore t h₀ h₁)

/-- The Fast Outage regime, as `outageRegime_mono` with the fast arming lag. -/
theorem fastOutageRegime_mono {V : Type} [DecidableEq V] [Fintype V] {n : Nat}
    {P : ProtocolSpec n} {E : Env V} {I : Interface P} {C C' : Constants}
    {rho : Run V P} {T b₀ b₁ : Time}
    (hθ : C.θ ≤ C'.θ) (hη : C.η ≤ C'.η) (hθ0 : 0 ≤ C.θ)
    (hA : C.fastArmingLag ≤ C'.fastArmingLag) (hB : C'.budget ≤ C.budget)
    (h : FastOutageRegime P E I C' rho T b₀ b₁) : FastOutageRegime P E I C rho T b₀ b₁ where
  toOutageRegime :=
    outageRegime_mono (C' := { C' with armingLag := C'.fastArmingLag })
      hθ hη hθ0 hA hB h.toOutageRegime
  highParticipation := h.highParticipation

/-- The Recovery regime at a smaller θrec, a larger gap, a smaller bound, and
`recoveryFull` false where the other is false, contains the regime at the
other constant. -/
theorem recoveryRegime_mono {V : Type} [DecidableEq V] [Fintype V] {n : Nat}
    {P : ProtocolSpec n} {E : Env V} {I : Interface P} {C C' : Constants}
    {rho : Run V P}
    (hθ : C.θrec ≤ C'.θrec) (hfull : C.recoveryFull = true → C'.recoveryFull = true)
    (hG : C'.proposerGap ≤ C.proposerGap) (hρ : C.recoveryBound ≤ C'.recoveryBound)
    (h : RecoveryRegime P E I C' rho) : RecoveryRegime P E I C rho where
  execution := h.execution
  rootInjective := h.rootInjective
  partialSynchrony := h.partialSynchrony
  participation := fun t h₀ h₁ => by
    have hp := h.participation t h₀ h₁
    have hnn : (0 : ℚ) ≤
        ((awakeAt E rho.honest t).card + (faulty rho).card : ℚ) := by positivity
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hθ hnn) hp
  full := fun hf => h.full (hfull hf)
  recurrence := recurrence_mono hG h.recurrence
  horizon := by have := h.horizon; linarith

/-- The recovered conclusions from a later time, at the same delays. -/
theorem recoveredAt_mono {V : Type} [DecidableEq V] {n : Nat}
    {P : ProtocolSpec n} {E : Env V} {I : Interface P} {C C' : Constants}
    {rho : Run V P} {t₀ t₁ : Time} (ht : t₀ ≤ t₁)
    (hc : C.D_c = C'.D_c) (hs : C.D_s = C'.D_s)
    (h : RecoveredAt P E I C rho t₀) : RecoveredAt P E I C' rho t₁ where
  confirmedSafe := safeFrom_mono ht h.confirmedSafe
  stableSafe := safeFrom_mono ht h.stableSafe
  confirmedIncluded := hc ▸ includedFrom_mono ht h.confirmedIncluded
  stableIncluded := hs ▸ includedFrom_mono ht h.stableIncluded

end AvailableChain.Framework.Catalog

end
