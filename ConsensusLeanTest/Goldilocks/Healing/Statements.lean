module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Run
public import ConsensusLeanTest.Goldilocks.Run.Statements
public import Mathlib.Tactic.Ring
@[expose] public section

/-! # Witnesses for Goldilocks run-level healing premises and constants

Labelled by kind (CONTRIBUTING "Statements"):

* (a) `oneTickRun_catch_noRestart`: the one-tick run of
  `ConsensusLeanTest/Goldilocks/Run/Statements` is a `Node.LocalRun` that satisfies `CatchRun` (for
  every `g`, `κ`; vacuously: no acceptance) and `NoRestartAfter` (for every time), over `idleAC`,
  not the Goldilocks AC.
* (a) `periodicRun_healthy_catch_noRestart`: the infinite periodic run of
  `ConsensusLeanTest/Goldilocks/Run/Statements` satisfies `Healthy(0)`, `CatchRun` (vacuously: no
  acceptance) and `NoRestartAfter` with the run laws: the generic `RunTrace` premises hold together
  on an infinite run over `idleAC`; `GoldilocksRun`, `HSShared` and `PropPlus` are witnessed on the
  Goldilocks tick run instead (`ConsensusLeanTest/Goldilocks/Runs/OneValidator/Premises`).
* Arithmetic check (no witness kind): `C_HS_closed_form`, `bound_closed_form`,
  `T_heal_closed_form` and `T_heal_closed_form_off`, the closed forms of `C_HS`, of
  `ḡ + 24Δ + 12C_HS` (HR.3 (c)) and of `T_heal` (H.4) with the optimistic confirmation on and
  off, hold at every parameter (a check of the transcription of the constants);
  `theta_of_optimistic` and `theta_of_not_optimistic` give `Θ` in each case.

**Elsewhere.** The premise witnesses over a Goldilocks trace are on the one-validator tick run:
`ConsensusLeanTest/Goldilocks/Runs/OneValidator/Premises` gives `GoldilocksRun`, `Healthy(g)`,
`HSShared` and `Prop⁺(G_p)` (`tickRun_goldilocksRun`, `tickRun_healthy`, `tickRun_hsShared`,
`tickRun_propPlus`), and `ConsensusLeanTest/Goldilocks/Runs/OneValidator/Run` the reset
(`tickRun_isReset`). `Healthy(g)` keeps every
honest validator awake from `ḡ` on, and a run's awake function is clamped to its horizon
(`Node.LocalRun.awake_in_horizon`), so every run satisfying `Healthy(g)` is infinite, as the
periodic run above and the tick run are.

**Not provided** (a follow-up): a non-vacuous run witness (kind (b)) for HR.1, HR.3 and HR.4,
which would apply those premise witnesses together. -/

namespace Consensus.Goldilocks.Healing.Test

/-- (a) The one-tick run is a `Node.LocalRun` with `CatchRun` and `NoRestartAfter`: it accepts no
block and has no restart (its cuts are `ac_on_tick` and `ac_to_fg`). -/
theorem oneTickRun_catch_noRestart (sg : Compose.Test.rootAC.Msg → Fin Compose.Test.P₁.n)
    (g κ t : Time) :
    Node.LocalRun (fun _ => Compose.Test.v₀) Compose.Test.dg₁ Set.univ sg Compose.Test.oneTickRun ∧
      CatchRun Compose.Test.oneTickRun Set.univ g κ ∧
      NoRestartAfter Compose.Test.oneTickRun Set.univ t := by
  refine ⟨Compose.Test.oneTickRun_localRun sg, ?_, ?_⟩
  · intro x _ i B hB
    obtain ⟨_, hℓ, -⟩ := Compose.Test.oneTickRun_label_ac hB.2
    cases hℓ
  · intro y _ k hk
    obtain ⟨ℓ, hc, hr⟩ := hk
    obtain ⟨ℓ', hℓ', hcall⟩ := Compose.Test.oneTickRun_label_ac hc.2
    cases hℓ'
    rcases hcall with h | h <;> rw [h] at hr <;> cases hr

/-- Every labelled cut of the periodic run is an AC call: a tick, a proposal or `ac_to_fg`. -/
theorem periodicRun_label_ac {i : Nat} {c : Cut Compose.Test.idleAC}
    (h : Compose.Test.periodicRun.label i = some c) :
    ∃ ℓ : ACLabel Compose.Test.idleAC, c = .ac ℓ ∧
      (ℓ.call = .tick ∨ ℓ.call = .proposal ∨ ℓ.call = .toFG) := by
  have hm : c ∈ Compose.Test.idleTickCuts ((i / 3 : Nat) : Int) :=
    List.mem_of_getElem? h
  obtain ⟨ℓ, hc, -, -, hcall⟩ := Compose.Test.idleTickCuts_mem (Int.natCast_nonneg _) hm
  exact ⟨ℓ, hc, hcall⟩

/-- (a) The infinite periodic run of `ConsensusLeanTest/Goldilocks/Run/Statements` (one honest
validator ticking at every time) satisfies `Healthy(0)` (with `Δ_F = 1`), `CatchRun` (for every `κ`)
and `NoRestartAfter` (for every time) together with the run laws, on an infinite run over `idleAC`
(`CatchRun` vacuously: no block is accepted). `GoldilocksRun`, `HSShared` and `Prop⁺` need the
Goldilocks AC: a follow-up. -/
theorem periodicRun_healthy_catch_noRestart
    (sg : Compose.Test.idleAC.Msg → Fin Compose.Test.P₁.n) (κ t : Time) :
    Node.LocalRun (fun _ => Compose.Test.v₀) Compose.Test.dg₁ Set.univ sg Compose.Test.periodicRun ∧
      Compose.Test.periodicRun.HealthyRun Set.univ 1 0 ∧
      CatchRun Compose.Test.periodicRun Set.univ 0 κ ∧
      NoRestartAfter Compose.Test.periodicRun Set.univ t := by
  refine ⟨Compose.Test.periodicRun_localRun sg, Compose.Test.periodicRun_healthy, ?_, ?_⟩
  · intro x _ i B hB
    obtain ⟨_, hℓ, -⟩ := periodicRun_label_ac hB.2
    cases hℓ
  · intro y _ k hk
    obtain ⟨ℓ, hc, hr⟩ := hk
    obtain ⟨ℓ', hℓ', hcall⟩ := periodicRun_label_ac hc.2
    cases hℓ'
    rcases hcall with h | h | h <;> rw [h] at hr <;> cases hr

/-- Arithmetic check: `C_HS = (8k + 49 + 4δ_t)Δ + Δ_F + 3G` (claims HR.3 (c)). -/
theorem C_HS_closed_form (sp : AC.ACParams) (ΔF G : Time) :
    C_HS sp ΔF G = (8 * (sp.k : Time) + 49 + 4 * (sp.toParams.δt : Time)) * sp.Δ + ΔF + 3 * G := by
  simp only [C_HS, D_HS]; ring

/-- Arithmetic check: `ḡ + 24Δ + 12C_HS = ḡ + (96k + 612 + 48δ_t)Δ + 12Δ_F + 36G` (claims
HR.3 (c)). -/
theorem bound_closed_form (sp : AC.ACParams) (g ΔF G : Time) :
    AC.gbar g + 24 * sp.Δ + 12 * C_HS sp ΔF G =
      AC.gbar g + (96 * (sp.k : Time) + 612 + 48 * (sp.toParams.δt : Time)) * sp.Δ + 12 * ΔF +
        36 * G := by
  simp only [C_HS, D_HS]; ring

/-- With the optimistic confirmation on, `Θ = 4(k + 1)Δ`. -/
theorem theta_of_optimistic (sp : AC.ACParams) (h : sp.optimistic = true) :
    AC.Θ sp = 4 * ((sp.k : Time) + 1) * sp.Δ := by
  simp only [AC.Θ, h, ↓reduceIte]

/-- With the optimistic confirmation off, `Θ = (4k − 2)Δ`. -/
theorem theta_of_not_optimistic (sp : AC.ACParams) (h : sp.optimistic = false) :
    AC.Θ sp = (4 * (sp.k : Time) - 2) * sp.Δ := by
  simp only [AC.Θ, h, Bool.false_eq_true, ↓reduceIte]

/-- Arithmetic check, optimistic confirmation on:
`T_heal = ḡ + (104k + 628 + 48δ_t)Δ + 12Δ_F + 36G + T_b` (claims H.4). -/
theorem T_heal_closed_form (sp : AC.ACParams) (h : sp.optimistic = true)
    (g ΔF G Tb : Time) :
    T_heal sp g ΔF G Tb =
      AC.gbar g + (104 * (sp.k : Time) + 628 + 48 * (sp.toParams.δt : Time)) * sp.Δ + 12 * ΔF +
        36 * G + Tb := by
  simp only [T_heal, C_HS, D_HS, theta_of_optimistic sp h]; ring

/-- Arithmetic check, optimistic confirmation off:
`T_heal = ḡ + (104k + 616 + 48δ_t)Δ + 12Δ_F + 36G + T_b` (claims H.4). -/
theorem T_heal_closed_form_off (sp : AC.ACParams) (h : sp.optimistic = false)
    (g ΔF G Tb : Time) :
    T_heal sp g ΔF G Tb =
      AC.gbar g + (104 * (sp.k : Time) + 616 + 48 * (sp.toParams.δt : Time)) * sp.Δ + 12 * ΔF +
        36 * G + Tb := by
  simp only [T_heal, C_HS, D_HS, theta_of_not_optimistic sp h]; ring

end Consensus.Goldilocks.Healing.Test

end
