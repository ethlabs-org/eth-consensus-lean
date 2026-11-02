module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ResetOfDrain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ResetCoefficients
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyGap
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthyQueryShared

public section

/-! # Goldilocks Refinement: the reset envelope (E) of a healthy preparation query (#136, S5)

workbench `healing_supply_repair_contracts.md` S5. For a `HealthyPreparationQuery` with nonfinal
progress on `[ready, heal]` and `heal ≤ horizon`: a delay `Δ_F` and a reset `a` with
`ResetPremisesUpTo … Q.gst Δ_F a horizon` and `a ≤ ready + R·Δ + r`, where `R = healthyResetCoeff`
and `r = healthyResetSlack` are the named parameter-only coefficients (`ResetCoefficients`).

It is the instance of `exists_reset_of_drain_awake` at `λ = 2Δ`, the ready scalar `ready`
(`ready ≥ 1`, so `max ready 0 = ready`), the gap `G = X` (`hgp_of_healthyQuery`) and the drain
length `L_drain = healthyDrainLen`, with `Δ_F = Δ`. The run premises come from
`hsSharedUpTo_of_le`; the whole-run no-restart premise from the bounded one, since a restart is a
labelled call at a time `≤ horizon`; Catch from `healthy_repair_catch`; the snapshot call condition
from `cutZ_fit_of_catchUp`. The kernel's frame ends before `B = ready + R·Δ`, so the gap is needed
only up to heal, given the fit `ready + R·Δ + r ≤ heal`. This module stays upstream of
`FinalWindowDefs` and `HealedSafety`.

The fit `hfit` of `healthy_reset_envelope_of_fit` is the window fit of the heal coefficient,
`healthy_reset_fit` (S6), so `healthy_reset_envelope_of_drain` takes only the drain at
`healthyDrainLen`. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape
open SA (gbar)

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The reset envelope from the drain and the fit before heal.** With the drain at the engine
horizon (`DrainOutputs`, gap `X`, length `healthyDrainLen`) and the fit
`ready + R·Δ + r ≤ heal`: a reset with its premises through the horizon at `Δ_F = Δ`, and
`a ≤ ready + R·Δ + r`. -/
theorem healthy_reset_envelope_of_fit (Q : HealthyPreparationQuery S A V)
    (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A)
      Q.cap Q.index Q.ready Q.heal Q.run)
    (hfit : Q.ready + (healthyResetCoeff S Q.index : Time) * Q.params.Δ +
      (healthyResetSlack S Q.index : Time) ≤ Q.heal)
    (hdrain : DrainOutputs Q.trace (runProposer S Q.run.2 Q.hn) (honestKeys S Q.run.2) Q.gst
      (Q.index : Nat) (healthyDrainLen S Q.index) Q.run.2.horizon) :
    ∃ ΔF a, Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
        (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst ΔF a Q.run.2.horizon ∧
      a ≤ Q.ready + (healthyResetCoeff S Q.index : Time) * Q.params.Δ +
        (healthyResetSlack S Q.index : Time) := by
  classical
  have hΔ : 0 < Q.params.Δ := Q.params.toParams.hΔ
  have hδ6 : 6 ≤ S.δt := A.timeout
  have hδeq : Q.params.toParams.fg.δt = S.δt := rfl
  have hs := Q.hsSharedUpTo_of_le Q.params.Δ le_rfl (by
    have : (6 : Time) ≤ S.δt := by exact_mod_cast hδ6
    nlinarith)
  have hrun := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  -- the ready scalar
  have hready : Q.ready = max Q.gst 0 + (Sys (family S) V).cDur (K S A) Q.run + 1 := rfl
  have hcDur : 0 ≤ (Sys (family S) V).cDur (K S A) Q.run :=
    mul_nonneg (Int.natCast_nonneg _) Q.run.1.Δ_pos.le
  have hr0 : 0 ≤ Q.ready := by rw [hready]; linarith [le_max_right Q.gst 0]
  have hgr : gbar Q.gst ≤ Q.ready := by
    change max Q.gst 0 ≤ Q.ready
    rw [hready]; linarith
  have hcz := cutZ_fit_of_catchUp A V (accepted_coefficients S A)
    (by rw [accepted_coefficients_catchUp]; exact accepted_catchUp_ge_sleepy S A) Q.run Q.hn Q.gst
  change Healing.cutZ Q.params.toParams Q.gst + Q.params.Δ + 1 ≤ max Q.ready 0 + 4 * Q.params.Δ
    at hcz
  rw [max_eq_left hr0] at hcz
  -- the whole-run no-restart premise: a restart is a labelled call, at a time `≤ horizon`
  have hnr : Healing.NoRestartAfter Q.trace (honestKeys S Q.run.2) (gbar Q.gst) :=
    fun y hy k hk => hs.noRestart y hy k hk
      (healthy_query_call_time_le S A V Q (by obtain ⟨ℓ, hc, -⟩ := hk; exact ⟨_, hc⟩))
  -- an honest node exists
  have hH : (honestKeys S Q.run.2).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hf := hs.faults
    rw [hne, Set.compl_empty, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hf
    have hn := Q.params.toParams.hn
    change 0 < Q.params.n at hn
    have hf' : 3 * Q.params.n ≤ Q.params.n - 1 := hf
    omega
  -- the reset bound `B = ready + R·Δ`
  have hBeq : resetBound Q.ready Q.params.Δ (2 * Q.params.Δ) Q.params.toParams.fg.δt
      (Q.index : Nat) (healthyDrainLen S Q.index) =
      Q.ready + (healthyResetCoeff S Q.index : Time) * Q.params.Δ := by
    rw [resetBound_eq, healthyResetCoeff_val, hδeq]; push_cast; ring
  have hR : (28 : Time) ≤ healthyResetCoeff S Q.index := by
    rw [healthyResetCoeff_val]; push_cast
    linarith [Nat.cast_nonneg (α := Time) (healthyDrainLen S Q.index)]
  have hr : (0 : Time) ≤ healthyResetSlack S Q.index := Nat.cast_nonneg _
  have hBh : resetBound Q.ready Q.params.Δ (2 * Q.params.Δ) Q.params.toParams.fg.δt
      (Q.index : Nat) (healthyDrainLen S Q.index) ≤ Q.heal := by
    rw [hBeq]; linarith
  have h4B : Q.ready + 4 * Q.params.Δ ≤ Q.heal := by
    have := mul_le_mul_of_nonneg_right hR hΔ.le
    linarith
  -- the kernel
  obtain ⟨a, ha, hab⟩ := exists_reset_of_drain_awake hrun hs.noColl hs.faults hs.sync hs.awake
    (healthy_repair_catch S A V Q) hnr hH (by rw [hδeq]; omega)
    (by rw [hδeq]; exact hs.timeoutDelay)
    hr0 hgr Q.index.pos hcz (hBh.trans hb)
    (fun s₀ N hs₀ hN => hgp_of_healthyQuery S A V Q hb hp (by rw [max_eq_left hr0]; exact hs₀)
      (by linarith))
    hdrain
  obtain ⟨j, hj, hjt⟩ := Healing.snapshot_of_awake hrun hs.awake hH (b := Q.run.2.horizon)
    (by linarith)
  refine ⟨Q.params.Δ, a, reset_premises_of_healthy_query S A V Q hs.sync ha
    (by linarith) ⟨j, hj, hjt⟩, ?_⟩
  rw [hBeq] at hab
  linarith

/-- **The window fit before heal** (S6): `ready + R·Δ + r ≤ heal` at every query, from the
coefficient inequality `accepted_heal_ge_reset` alone. With engine delay `d ≥ 1`, `Δ = d + 1`,
`ready = g₀ + C·d + 1` and `heal = g₀ + H·d`, `H ≥ C + 2R + r + 3` gives
`heal − ready − R·Δ − r ≥ (R + r)(d − 1) + 3d − 1 ≥ 0`. -/
theorem healthy_reset_fit (Q : HealthyPreparationQuery S A V) :
    Q.ready + (healthyResetCoeff S Q.index : Time) * Q.params.Δ +
      (healthyResetSlack S Q.index : Time) ≤ Q.heal := by
  have hd : (1 : Time) ≤ Q.run.1.Δ := Q.run.1.Δ_pos
  have hready : Q.ready = max Q.gst 0 + ((accepted_catchUp S A : Nat) : Time) * Q.run.1.Δ + 1 := by
    change max Q.gst 0 + (((accepted_coefficients S A).catchUp : Nat) : Time) * Q.run.1.Δ + 1 = _
    rw [accepted_coefficients_catchUp]
  have hheal : Q.heal = max Q.gst 0 + (accepted_heal S A Q.cap Q.index : Time) * Q.run.1.Δ := by
    change max Q.gst 0 + ((accepted_coefficients S A).heal Q.cap Q.index : Time) * Q.run.1.Δ = _
    rw [accepted_coefficients_heal]
  have hΔ : Q.params.Δ = Q.run.1.Δ + 1 := rfl
  have hH : ((accepted_catchUp S A : Nat) : Time) + 2 * (healthyResetCoeff S Q.index : Time) +
      (healthyResetSlack S Q.index : Time) + 3 ≤ (accepted_heal S A Q.cap Q.index : Time) := by
    have := accepted_heal_ge_reset S A Q.cap Q.index
    exact_mod_cast (show _ ≤ _ by omega)
  have hR0 : (0 : Time) ≤ healthyResetCoeff S Q.index := Nat.cast_nonneg _
  have hr0 : (0 : Time) ≤ healthyResetSlack S Q.index := Nat.cast_nonneg _
  rw [hready, hheal, hΔ]
  nlinarith [mul_le_mul_of_nonneg_right hH (by linarith : (0 : Time) ≤ Q.run.1.Δ),
    mul_nonneg hR0 (by linarith : (0 : Time) ≤ Q.run.1.Δ - 1),
    mul_nonneg hr0 (by linarith : (0 : Time) ≤ Q.run.1.Δ - 1)]

/-- **The reset envelope (E) from the drain.** `healthy_reset_envelope_of_fit` with the window fit
`healthy_reset_fit`: the drain at `healthyDrainLen` is the only remaining input. -/
theorem healthy_reset_envelope_of_drain (Q : HealthyPreparationQuery S A V)
    (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A)
      Q.cap Q.index Q.ready Q.heal Q.run)
    (hdrain : DrainOutputs Q.trace (runProposer S Q.run.2 Q.hn) (honestKeys S Q.run.2) Q.gst
      (Q.index : Nat) (healthyDrainLen S Q.index) Q.run.2.horizon) :
    ∃ ΔF a, Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
        (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst ΔF a Q.run.2.horizon ∧
      a ≤ Q.ready + (healthyResetCoeff S Q.index : Time) * Q.params.Δ +
        (healthyResetSlack S Q.index : Time) :=
  healthy_reset_envelope_of_fit S A V Q hb hp (healthy_reset_fit S A V Q) hdrain

end Consensus.Goldilocks.Refinement

end
