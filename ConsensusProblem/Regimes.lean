module
public import ConsensusProblem.Network
public import ConsensusProblem.Atoms
public import Mathlib.Tactic

@[expose] public section

/-! # Numbers and regimes (L0)

A protocol's contract supplies only numbers (`Params`): thresholds, a
catch-up, an arming lag, an outage budget and an outage look-back `η`, and
per capability and index a heal point and a latency. Every duration is a
coefficient of `Δ`. `Params.standard` names the standard thresholds (½
sleepy, ⅔ healthy, ½ cover, ⅓ accountable, look-back `0`);
`Params.Admissible` requires the thresholds to be no stronger than the
standard ones (and `1 − φ ≤ α`), so a contract cannot buy its claims with a
stronger environment. The look-back `η` is an instance number like the lag
and the budget: it is not bounded (any `η` is realizable, `Shape.outage_witness`).

The regimes are fixed here, over an environment point and a communication log:

* **sleepy**: synchrony (`PSync 0`) and, at every time, the ready honest
  validators exceed fraction `θ` of the ready and faulty ones;
* **healthy from GST `g`**: partial synchrony with GST `g`, and one fixed set
  of honest validators, more than fraction `φ` of all validators, each awake
  throughout `[max g 0, horizon]` (no churn: the same validators stay awake,
  so certificates are formable; awake, not ready: readiness restricts readers
  and progress only);
* **outage `[b₀, b₁)` armed at `T`**: synchronous before `b₀`, partially
  synchronous with GST `b₁`, η-sleepy throughout (look-back `η·Δ`; `η = 0` is
  plain sleepy, `EnvPoint.etaSleepyOn_zero`, `Regime.outage_eta_zero`), more
  than fraction `cover` ready at `b₀`; `T` is at least `lag·Δ` before `b₀`,
  and the window is at most `budget·Δ` long.

The GST is a parameter of the regimes, not of the environment. A run after an
outage is a partially synchronous run with GST `b₁`: the healthy regime with
`g = b₁` applies to it by definition. -/

namespace Consensus

/-- The numbers of a protocol. Durations are `Δ`-coefficients. -/
structure Params (Idx : Type) where
  /-- Readers' catch-up `c`: a reader is ready after `c·Δ` awake. -/
  catchUp : Nat
  /-- Sleepy threshold: `θ·(|ready| + |faulty|) < |ready|`. -/
  θ : ℚ
  /-- Healthy threshold: `φ·n < |honest and awake|`. -/
  φ : ℚ
  /-- Caught up at the outage start: `cover·n < |ready b₀|`. -/
  cover : ℚ
  /-- Accountable fraction of the final output. -/
  α : ℚ
  /-- Arming lag: `T + lag·Δ ≤ b₀`. -/
  lag : Nat
  /-- Outage budget: `b₁ ≤ b₀ + budget·Δ`. -/
  budget : Nat
  /-- Outage look-back: the outage regime is η-sleepy with look-back `η·Δ`
  (`0`: plain sleepy). -/
  η : Nat
  /-- Heal point after GST, per capability and index (from `max g 0`; for
  final, the first finality). -/
  heal : Capability → Idx → Nat
  /-- Transaction latency per capability and index. -/
  latency : Capability → Idx → Nat

namespace Params

variable {Idx : Type}

/-- The standard thresholds: `θ = ½`, `φ = ⅔`, `cover = ½`, `α = ⅓`, and
look-back `η = 0` (plain sleepy outage participation); an instance with a
look-back sets `η` (`{ standard … with η := k }`). -/
def standard (catchUp lag budget : Nat) (heal latency : Capability → Idx → Nat) :
    Params Idx :=
  ⟨catchUp, 1 / 2, 2 / 3, 1 / 2, 1 / 3, lag, budget, 0, heal, latency⟩

/-- Admissible numbers: thresholds no stronger than standard, `1 − φ ≤ α`
(so the healthy regime implies faults below the accountable fraction), a
positive catch-up and a positive budget. -/
structure Admissible (P : Params Idx) : Prop where
  catchUp_pos : 1 ≤ P.catchUp
  θ_range : 0 ≤ P.θ ∧ P.θ ≤ 1 / 2
  φ_range : 0 ≤ P.φ ∧ P.φ ≤ 2 / 3
  cover_range : 0 ≤ P.cover ∧ P.cover ≤ 1 / 2
  α_range : 1 - P.φ ≤ P.α ∧ P.α ≤ 1
  budget_pos : 1 ≤ P.budget

/-- The standard thresholds are admissible. -/
theorem standard_admissible {catchUp lag budget : Nat} {heal latency : Capability → Idx → Nat}
    (h : 1 ≤ catchUp) (hb : 1 ≤ budget) :
    (standard catchUp lag budget heal latency).Admissible :=
  ⟨h, by norm_num [standard], by norm_num [standard], by norm_num [standard],
    by norm_num [standard], hb⟩

/-- The catch-up duration `catchUp·Δ`. -/
def cDur (P : Params Idx) (Δ : Time) : Time := (P.catchUp : Time) * Δ

/-- The outage look-back duration `η·Δ`. -/
def ηDur (P : Params Idx) (Δ : Time) : Time := (P.η : Time) * Δ

/-- The heal point of `cap` at index `i` after GST `g`: `max g 0 + heal·Δ`
(catch-up is inside `heal`). -/
def healPoint (P : Params Idx) (Δ : Time) (cap : Capability) (i : Idx) (g : Time) : Time :=
  max g 0 + (P.heal cap i : Time) * Δ

/-- The latency duration `latency·Δ`. -/
def latDur (P : Params Idx) (Δ : Time) (cap : Capability) (i : Idx) : Time :=
  (P.latency cap i : Time) * Δ

end Params

/-- First time from which a node awake since `g` is ready: `max g 0 + c + 1`.
Used only for the start of progress windows. -/
def readyFrom (c g : Time) : Time := max g 0 + c + 1

namespace EnvPoint

variable {V : Type} [Fintype V] [DecidableEq V] (p : EnvPoint V)

/-- Sleepy participation on `[a, b]`. -/
def SleepyOn (θ : ℚ) (c a b : Time) : Prop := ∀ t, a ≤ t → t ≤ b → p.ReadyAbove θ c t

/-- Sleepy participation throughout the run. -/
def Sleepy (θ : ℚ) (c : Time) : Prop := p.SleepyOn θ c 0 p.horizon

/-- η-sleepy participation (look-back `η`, a duration) on `[a, b]`. -/
def EtaSleepyOn (θ : ℚ) (η c a b : Time) : Prop :=
  ∀ t, a ≤ t → t ≤ b → p.EtaReadyAbove θ η c t

/-- η-sleepy participation throughout the run. -/
def EtaSleepy (θ : ℚ) (η c : Time) : Prop := p.EtaSleepyOn θ η c 0 p.horizon

/-- Healthy on `[max g 0, b]`: one fixed set `H` of honest validators, more
than `φ·n`, each awake throughout `[max g 0, b]` (the same validators at every
time: no churn). Readiness is not required: it restricts readers and progress
only. -/
def HealthyOn (φ : ℚ) (g b : Time) : Prop :=
  ∃ H ⊆ p.honest, φ * Fintype.card V < (H.card : ℚ) ∧ ∀ v ∈ H, p.AwakeOnClosed v (max g 0) b

/-- Healthy from `g` to the horizon. -/
def HealthyFrom (φ : ℚ) (g : Time) : Prop := p.HealthyOn φ g p.horizon

variable {p}

/-- A smaller fraction is weaker. -/
theorem SleepyOn.mono {θ θ' : ℚ} {c a b : Time} (h : p.SleepyOn θ' c a b) (hle : θ ≤ θ') :
    p.SleepyOn θ c a b :=
  fun t ha hb => (h t ha hb).mono p hle

/-- With look-back `0`, η-sleepy is plain sleepy. -/
theorem etaSleepyOn_zero (θ : ℚ) (c a b : Time) :
    p.EtaSleepyOn θ 0 c a b ↔ p.SleepyOn θ c a b :=
  forall_congr' fun t => imp_congr_right fun _ => imp_congr_right fun _ =>
    p.etaReadyAbove_zero θ c t

/-- η-sleepy (`η ≥ 0`, `θ ≥ 0`) implies plain sleepy. -/
theorem EtaSleepyOn.sleepyOn {θ : ℚ} {η c a b : Time} (h : p.EtaSleepyOn θ η c a b)
    (h0 : 0 ≤ θ) (hη : 0 ≤ η) : p.SleepyOn θ c a b :=
  fun t ha hb => (h t ha hb).readyAbove p h0 hη

/-- A smaller fraction (`θ ≥ 0`) and a shorter look-back are weaker. -/
theorem EtaSleepyOn.mono {θ θ' : ℚ} {η η' c a b : Time} (h : p.EtaSleepyOn θ' η' c a b)
    (h0 : 0 ≤ θ) (hθ : θ ≤ θ') (hη : η ≤ η') : p.EtaSleepyOn θ η c a b :=
  fun t ha hb => (h t ha hb).mono p h0 hθ hη

omit [DecidableEq V] in
/-- A smaller fraction is weaker. -/
theorem HealthyOn.mono {φ φ' : ℚ} {g b : Time} (h : p.HealthyOn φ' g b) (hle : φ ≤ φ') :
    p.HealthyOn φ g b := by
  obtain ⟨H, hH, hc, ha⟩ := h
  exact ⟨H, hH, lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle (by positivity)) hc, ha⟩

omit [DecidableEq V] in
/-- Healthy on `[max g 0, b]` gives more than `φ·n` honest and awake at every
time in it. -/
theorem HealthyOn.awakeOfAll {φ : ℚ} {g b t : Time} (h : p.HealthyOn φ g b)
    (ht : max g 0 ≤ t) (htb : t ≤ b) : p.AwakeOfAll φ t := by
  classical
  obtain ⟨H, hH, hc, ha⟩ := h
  have hsub : H ⊆ p.awakeAt t := by
    intro v hv
    unfold awakeAt
    exact Finset.mem_filter.mpr ⟨hH hv, ha v hv t ht htb⟩
  have : (H.card : ℚ) ≤ (p.awakeAt t).card := by exact_mod_cast Finset.card_le_card hsub
  unfold AwakeOfAll
  linarith

/-- Healthy bounds the faults: a set of more than `φ·n` honest validators
leaves fewer than `(1 − φ)·n` faulty. -/
theorem HealthyOn.faultsBelow {φ : ℚ} {g b : Time} (h : p.HealthyOn φ g b) :
    p.FaultsBelow (1 - φ) := by
  classical
  obtain ⟨H, hsub, ha, -⟩ := h
  have hc : H.card ≤ p.honest.card := Finset.card_le_card hsub
  have hsum : p.faulty.card + p.honest.card = Fintype.card V := by
    unfold faulty
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    have := Finset.card_le_univ p.honest
    omega
  have hc' : (H.card : ℚ) ≤ p.honest.card := by exact_mod_cast hc
  have hsum' : (p.faulty.card : ℚ) + p.honest.card = Fintype.card V := by exact_mod_cast hsum
  unfold FaultsBelow
  linarith

end EnvPoint

/-- The outage times: armed at `T ≥ 0` at least `lag·Δ` before the window
`[b₀, b₁)`, which lasts at most `budget·Δ`. -/
def OutageTimes {Idx : Type} (P : Params Idx) (Δ T b₀ b₁ : Time) : Prop :=
  0 ≤ T ∧ T + (P.lag : Time) * Δ ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ b₀ + (P.budget : Time) * Δ

namespace Regime

variable {V M Idx : Type} [Fintype V] [DecidableEq V]
  (P : Params Idx) (p : EnvPoint V) (L : CommLog V M)

/-- The sleepy regime: synchrony and sleepy participation throughout. -/
def Sleepy : Prop := L.PSync p 0 ∧ p.Sleepy P.θ (P.cDur p.env.Δ)

/-- The healthy regime from GST `g`: partial synchrony with GST `g`, and more
than `φ·n` honest and awake from `max g 0` on. -/
def Healthy (g : Time) : Prop := L.PSync p g ∧ p.HealthyFrom P.φ g

/-- The outage regime: outage times, synchronous before `b₀` and partially
synchronous with GST `b₁`, η-sleepy throughout (look-back `η·Δ`), more than
`cover·n` ready at `b₀`. -/
def Outage (T b₀ b₁ : Time) : Prop :=
  OutageTimes P p.env.Δ T b₀ b₁ ∧ L.OutageNet p b₀ b₁ ∧
    p.EtaSleepy P.θ (P.ηDur p.env.Δ) (P.cDur p.env.Δ) ∧
    p.ReadyOfAll P.cover (P.cDur p.env.Δ) b₀

variable {P p L}

/-- With look-back `η = 0`, the outage regime's participation is plain
sleepy throughout. -/
theorem outage_eta_zero (hη : P.η = 0) {T b₀ b₁ : Time} :
    Outage P p L T b₀ b₁ ↔ OutageTimes P p.env.Δ T b₀ b₁ ∧ L.OutageNet p b₀ b₁ ∧
      p.Sleepy P.θ (P.cDur p.env.Δ) ∧ p.ReadyOfAll P.cover (P.cDur p.env.Δ) b₀ := by
  unfold Outage EnvPoint.EtaSleepy EnvPoint.Sleepy
  rw [show P.ηDur p.env.Δ = 0 by simp [Params.ηDur, hη], EnvPoint.etaSleepyOn_zero]

/-- Weaker thresholds (same catch-up) keep the sleepy regime. -/
theorem Sleepy.of_le {P' : Params Idx} (hc : P'.catchUp = P.catchUp) (hθ : P'.θ ≤ P.θ)
    (h : Sleepy P p L) : Sleepy P' p L := by
  refine ⟨h.1, ?_⟩
  unfold Params.cDur; rw [hc]
  exact EnvPoint.SleepyOn.mono h.2 hθ

omit [DecidableEq V] in
/-- Weaker thresholds keep the healthy regime. -/
theorem Healthy.of_le {P' : Params Idx} {g : Time} (hφ : P'.φ ≤ P.φ) (h : Healthy P p L g) :
    Healthy P' p L g :=
  ⟨h.1, EnvPoint.HealthyOn.mono h.2 hφ⟩

/-- Weaker thresholds (`θ' ≥ 0`), a shorter look-back, a shorter lag and a
larger budget (same catch-up) keep the outage regime. -/
theorem Outage.of_le {P' : Params Idx} {T b₀ b₁ : Time} (hc : P'.catchUp = P.catchUp)
    (h0 : 0 ≤ P'.θ) (hθ : P'.θ ≤ P.θ) (hη : P'.η ≤ P.η) (hcov : P'.cover ≤ P.cover)
    (hl : P'.lag ≤ P.lag) (hb : P.budget ≤ P'.budget) (h : Outage P p L T b₀ b₁) :
    Outage P' p L T b₀ b₁ := by
  obtain ⟨⟨hT, hlag, h01, hbud⟩, hn, hs, hr⟩ := h
  have hΔ : (0 : Time) ≤ p.env.Δ := p.env.Δ_pos.le
  have hl' : ((P'.lag : Nat) : Time) ≤ (P.lag : Time) := by exact_mod_cast hl
  have hb' : ((P.budget : Nat) : Time) ≤ (P'.budget : Time) := by exact_mod_cast hb
  refine ⟨⟨hT, ?_, h01, ?_⟩, hn, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · unfold Params.cDur; rw [hc]
    have hη' : ((P'.η : Nat) : Time) ≤ (P.η : Time) := by exact_mod_cast hη
    exact EnvPoint.EtaSleepyOn.mono hs h0 hθ (by unfold Params.ηDur; nlinarith)
  · unfold Params.cDur; rw [hc]
    exact hr.mono p hcov

end Regime

end Consensus

end
