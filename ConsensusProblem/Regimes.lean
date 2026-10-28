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
standard ones (and `1 − φ ≤ α`), so a contract cannot buy its claims with
stronger thresholds. The other numbers (catch-up, lag, budget, look-back `η`,
heal points, latencies) are instance numbers that the reviewer reads: larger
values strengthen premises or weaken claims, and they are not bounded (any
`η` is realizable, `Shape.outage_witness`).

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
  plain sleepy, `EnvPoint.etaSleepyOn_zero`, `Regime.outage_eta_zero` (tests); for
  `η > 0` the ready validators exceed fraction `θ` of those awake at some time
  in the window `[max 0 (t − η·Δ), t]` plus the faulty ones, which implies
  the awake-count form, `EnvPoint.EtaReadyAbove.awakeForm`, tests), more
  than fraction `cover` ready at `b₀`; `T` is at least `lag·Δ` before `b₀`,
  and the window is at most `budget·Δ` long.

The GST is a parameter of the regimes, not of the environment. An outage run
is partially synchronous with GST `b₁`, so the after-GST rows apply with
`g = b₁` when their other premises hold. -/

namespace Consensus

/-- The numbers of a protocol. Durations are `Δ`-coefficients. -/
structure Params (Idx : Type) where
  /-- Readers' catch-up `c`: a reader is ready after `c·Δ` awake. -/
  catchUp : Nat
  /-- Sleepy threshold: `θ·(|ready| + |faulty|) < |ready|`. -/
  θ : ℚ
  /-- Healthy threshold: a fixed set of more than `φ·n` honest validators,
  awake throughout from `max g 0`. -/
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

/-- The healthy regime from GST `g`: partial synchrony with GST `g`, and one
fixed set of more than `φ·n` honest validators, each awake throughout
`[max g 0, horizon]` (no churn). -/
def Healthy (g : Time) : Prop := L.PSync p g ∧ p.HealthyFrom P.φ g

/-- The outage regime: outage times, synchronous before `b₀` and partially
synchronous with GST `b₁`, η-sleepy throughout (look-back `η·Δ`), more than
`cover·n` ready at `b₀`. -/
def Outage (T b₀ b₁ : Time) : Prop :=
  OutageTimes P p.env.Δ T b₀ b₁ ∧ L.OutageNet p b₀ b₁ ∧
    p.EtaSleepy P.θ (P.ηDur p.env.Δ) (P.cDur p.env.Δ) ∧
    p.ReadyOfAll P.cover (P.cDur p.env.Δ) b₀

end Regime

end Consensus

end
