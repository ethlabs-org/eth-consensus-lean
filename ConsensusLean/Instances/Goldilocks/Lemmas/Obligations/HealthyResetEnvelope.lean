module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ResetOfDrainRounds
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ResetCoefficients
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyGap
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyQueryShared
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.DrainWarm
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyPreparationTiming
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HonestNonempty
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Obligations: the reset envelope of a healthy preparation query

For a `HealthyPreparationQuery` with nonfinal
progress on `[ready, heal]` and `heal ≤ horizon`: a delay `Δ_F` and a reset `a` with
`ResetPremisesUpTo … Q.gst Δ_F a horizon` and `a ≤ ready + R·Δ + ρ`, where `R = healthyResetCoeff`
and `ρ = healthyResetSlack`, the literal slack `0` (not an FG delay bound), are the named
parameter-only coefficients (`ResetCoefficients`).

It is the instance of `exists_reset_of_drain_rounds_awake` (the rise-round route) at `λ = 2Δ`, the
ready scalar `ready` (`ready ≥ 1`, so `max ready 0 = ready`), the gap `G = X`
(`hgp_of_healthyQuery`) and the drain length `L_drain = healthyDrainLen`, with the protocol FG
delay `Δ_F = protoFGDelay`. The run premises come from `hsSharedUpTo_of_le`; the whole-run
no-restart premise from the bounded one, since a restart is a labelled call at a time `≤ horizon`;
Catch from
`healthy_repair_catch`; the snapshot call condition from `cutZ_fit_of_catchUp`. The kernel's frame
ends before `B = ready + R·Δ`, so the gap is needed only up to heal, given the fit
`ready + R·Δ + ρ ≤ heal`. This module stays upstream of `FinalWindowDefs` and `HealedSafety`.

The fit `hfit` of `healthy_reset_envelope_of_fit` is the window fit of the heal coefficient,
`healthy_reset_fit`, so `healthy_reset_envelope_of_drain` takes only the drain at
`healthyDrainLen`, and the leaf form `healthy_reset_envelope` takes the drain from
`drainOutputs_of_service` (`DrainWarm`). -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open Blocks Shape
open SA (gbar)

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- The shared HS premises of the query through the horizon at the protocol FG delay
`Δ_F,p = protoFGDelay` (`6Δ + Δ_F,p ≤ 4Δ·fgSlots ≤ 4Δ·δ_t`, `protoFGDelay_timeout_of_fgDelay`). -/
private theorem healthy_hsShared (Q : HealthyPreparationQuery S A V) :
    Healing.HSSharedUpTo Q.trace (honestKeys S Q.run.2) (digestOf S Q.run.2) Q.gst
      (protoFGDelay (Model.pubOf Q.run.1)) Q.run.2.horizon :=
  Q.hsSharedUpTo_of_le _ le_rfl (protoFGDelay_timeout_of_fgDelay S A V Q.run Q.hn Q.healthy.2.2)

/-- The whole-run no-restart premise: a restart is a labelled call, at a time `≤ horizon`, so
the bounded one of `healthy_hsShared` covers it. -/
private theorem healthy_noRestartAfter (Q : HealthyPreparationQuery S A V) :
    Healing.NoRestartAfter Q.trace (honestKeys S Q.run.2) (gbar Q.gst) :=
  fun y hy k hk => (healthy_hsShared S A V Q).noRestart y hy k hk
    (healthy_query_call_time_le S A V Q (by obtain ⟨ℓ, hc, -⟩ := hk; exact ⟨_, hc⟩))

/-- **The reset envelope from the drain and the fit before heal.** With the drain at the engine
horizon (`DrainOutputs`, gap `X`, length `healthyDrainLen`) and the fit
`ready + R·Δ + r ≤ heal`: a reset with its premises through the horizon at the protocol attestation
delay `Δ_F = protoFGDelay`, and
`a ≤ ready + R·Δ + r`. -/
theorem healthy_reset_envelope_of_fit (Q : HealthyPreparationQuery S A V)
    (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A)
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
  have hδ6 : 6 ≤ S.δt := A.six_le_δt
  have hδeq : Q.params.toParams.fg.δt = S.δt := rfl
  have hs := healthy_hsShared S A V Q
  have hrun := simTrace_goldilocksRun S Q.run.2 Q.hn Q.constant Q.valid
  -- the ready scalar
  have hready : Q.ready = max Q.gst 0 + (Sys (goldilocks S) V).cDur (K S A) Q.run + 1 := rfl
  have hcDur : 0 ≤ (Sys (goldilocks S) V).cDur (K S A) Q.run :=
    mul_nonneg (Int.natCast_nonneg _) Q.run.1.ΔAC_pos.le
  have hr0 : 0 ≤ Q.ready := by rw [hready]; linarith only [le_max_right Q.gst 0, hcDur]
  have hgr : gbar Q.gst ≤ Q.ready := by
    change max Q.gst 0 ≤ Q.ready
    rw [hready]; linarith only [hcDur]
  have hcz := cutZ_fit_of_catchUp A V (contract_coefficients S A)
    (by rw [contract_coefficients_catchUp]; exact contract_catchUp_ge_sleepy S A) Q.run Q.hn Q.gst
  change Healing.cutZ Q.params.toParams Q.gst + Q.params.Δ + 1 ≤ max Q.ready 0 + 4 * Q.params.Δ
    at hcz
  rw [max_eq_left hr0] at hcz
  have hnr := healthy_noRestartAfter S A V Q
  have hH : (honestKeys S Q.run.2).Nonempty :=
    nonempty_of_fault_bound hs.faults Q.params.toParams.hn
  -- the reset bound `B = ready + R·Δ`
  have hBeq : resetBoundRounds Q.ready Q.params.Δ (2 * Q.params.Δ) Q.params.toParams.fg.δt
      (Q.index : Nat) (healthyDrainLen S Q.index) =
      Q.ready + (healthyResetCoeff S Q.index : Time) * Q.params.Δ := by
    rw [resetBoundRounds_eq, healthyResetCoeff_val, hδeq]; push_cast; ring
  have hR : (24 : Time) ≤ healthyResetCoeff S Q.index := by
    rw [healthyResetCoeff_val]; push_cast
    linarith only [Nat.cast_nonneg (α := Time) (healthyDrainLen S Q.index)]
  have hr : (0 : Time) ≤ healthyResetSlack S Q.index := Nat.cast_nonneg _
  have hBh : resetBoundRounds Q.ready Q.params.Δ (2 * Q.params.Δ) Q.params.toParams.fg.δt
      (Q.index : Nat) (healthyDrainLen S Q.index) ≤ Q.heal := by
    rw [hBeq]; linarith only [hfit, hr]
  have h4B : Q.ready + 4 * Q.params.Δ ≤ Q.heal := by
    have := mul_le_mul_of_nonneg_right hR hΔ.le
    linarith only [this, hfit, hr, hΔ]
  -- the kernel
  obtain ⟨a, ha, hab⟩ := exists_reset_of_drain_rounds_awake hrun hs.noColl hs.faults hs.sync
    hs.awake (healthy_repair_catch S A V Q) hnr hH (by rw [hδeq]; omega)
    (by rw [hδeq]; exact hs.timeoutDelay)
    hr0 hgr Q.index.pos hcz (hBh.trans hb)
    (fun s₀ N hs₀ hN => hgp_of_healthyQuery S A V Q hb hp (by rw [max_eq_left hr0]; exact hs₀)
      (by linarith only [hN, hBh, hΔ]))
    hdrain
  obtain ⟨j, hj, hjt⟩ := Healing.snapshot_of_awake hrun hs.awake hH (b := Q.run.2.horizon)
    (by linarith only [hcz, h4B, hb])
  refine ⟨protoFGDelay (Model.pubOf Q.run.1), a, reset_premises_of_healthy_query S A V Q hs.sync ha
    (by linarith only [hab, hBh, hb]) ⟨j, hj, hjt⟩, ?_⟩
  rw [hBeq] at hab
  linarith only [hab, hr]

/-- **The window fit before heal**: `ready + R·Δ + r ≤ heal` at every query, from the
coefficient inequality `contract_heal_ge_reset` alone. It gives `H ≥ C + (R + r) + 3`, so
`healthy_heal_margin` gives `ready + (R + r)·Δ + 2 ≤ heal`, and `r ≤ r·Δ` at `Δ ≥ 1`. -/
theorem healthy_reset_fit (Q : HealthyPreparationQuery S A V) :
    Q.ready + (healthyResetCoeff S Q.index : Time) * Q.params.Δ +
      (healthyResetSlack S Q.index : Time) ≤ Q.heal := by
  have h := healthy_heal_margin S A V Q.run Q.hn Q.cap Q.index Q.gst
    (M := healthyResetCoeff S Q.index + healthyResetSlack S Q.index)
    (by have := contract_heal_ge_reset S A Q.cap Q.index; omega)
  have hd : (1 : Time) ≤ Q.params.Δ := Q.run.1.ΔAC_pos
  have hr0 : (0 : Time) ≤ healthyResetSlack S Q.index := Nat.cast_nonneg _
  push_cast at h
  linarith only [h, mul_nonneg hr0 (sub_nonneg.mpr hd)]

/-- **The reset envelope from the drain.** `healthy_reset_envelope_of_fit` with the window fit
`healthy_reset_fit`: the drain at `healthyDrainLen` is the only remaining input. -/
theorem healthy_reset_envelope_of_drain (Q : HealthyPreparationQuery S A V)
    (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A)
      Q.cap Q.index Q.ready Q.heal Q.run)
    (hdrain : DrainOutputs Q.trace (runProposer S Q.run.2 Q.hn) (honestKeys S Q.run.2) Q.gst
      (Q.index : Nat) (healthyDrainLen S Q.index) Q.run.2.horizon) :
    ∃ ΔF a, Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
        (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst ΔF a Q.run.2.horizon ∧
      a ≤ Q.ready + (healthyResetCoeff S Q.index : Time) * Q.params.Δ +
        (healthyResetSlack S Q.index : Time) :=
  healthy_reset_envelope_of_fit S A V Q hb hp (healthy_reset_fit S A V Q) hdrain

/-- **The reset envelope of a healthy preparation query**: from the query, `heal ≤ horizon`
and nonfinal progress on `[ready, heal]` alone, a delay `Δ_F` and a reset `a` with its premises
through the horizon and `a ≤ ready + R·Δ + r`, `R = healthyResetCoeff`, `r = healthyResetSlack`.
The drain is `drainOutputs_of_service` at `L_drain = healthyDrainLen = 2k + X`, which pays its
guard `2k + X ≤ L_drain + 1`; the fit is `healthy_reset_fit`. -/
theorem healthy_reset_envelope (Q : HealthyPreparationQuery S A V)
    (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A)
      Q.cap Q.index Q.ready Q.heal Q.run) :
    ∃ ΔF a, Healing.ResetPremisesUpTo Q.trace (honestKeys S Q.run.2)
        (runProposer S Q.run.2 Q.hn) (digestOf S Q.run.2) Q.gst ΔF a Q.run.2.horizon ∧
      a ≤ Q.ready + (healthyResetCoeff S Q.index : Time) * Q.params.Δ +
        (healthyResetSlack S Q.index : Time) := by
  have hs := healthy_hsShared S A V Q
  refine healthy_reset_envelope_of_drain S A V Q hb hp
    (drainOutputs_of_service (simTrace_goldilocksRun S Q.run.2 Q.hn Q.constant Q.valid)
      hs.noColl hs.sync hs.awake hs.faults (healthy_repair_catch S A V Q)
      (healthy_noRestartAfter S A V Q) ?_)
  rw [healthyDrainLen_val]
  change 2 * S.k + (Q.index : Nat) ≤ 2 * S.k + (Q.index : Nat) + 1
  omega

set_option linter.unusedVariables false in
/-- **The joint preparation tuple (E)**: base timing and a finite preparation schedule (an actual
reset with service through the horizon, its seed, and a query with the lower bound and the strict
reserve). It replaces, as (R0), the former
`healthy_old_inventory_initialize`: no old-entry inventory is produced or required. The reset is
`healthy_reset_envelope` (`Δ_F = protoFGDelay`, `a ≤ ready + R·Δ`), the seed
`ResetPremisesUpTo.reset_seed`, the base slot `slot(ready) + 1` and the query the maximum of the
lower bound. Every timing bound is one step from the coefficient inequality
`contract_heal_ge_reset`: with `B = R + 8k + 4X + 26`, `ready + B·Δ + 2 ≤ heal`, which covers
the query `≤ ready + (R + 8k + 20)Δ` plus the reserve `(4X + 6)Δ` and the base timing
`t_w + max(14, 4k)Δ ≤ ready + (4k + 18)Δ`. No new Healthy premise, whole-run progress, or
prefix-causal coverage is asserted. `h0` is kept for the consumer's interface; `heal > 0` follows
from the coefficient. -/
theorem healthy_preparation_initialize (Q : HealthyPreparationQuery S A V)
    (h0 : 0 ≤ Q.heal) (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) Q.cap Q.index
      Q.ready Q.heal Q.run) :
    ∃ W : HealthyBaseTiming S A V Q, Nonempty (HealthyPreparationSchedule S A V Q W) := by
  obtain ⟨ΔF, a, hreset, ha⟩ := healthy_reset_envelope S A V Q hb hp
  obtain ⟨v, r, l, O, hO, hra, hla⟩ := hreset.reset_seed
  obtain ⟨⟨_, _, k, _, -, -, hka⟩, -⟩ := hreset.reset
  have ha0 : 0 ≤ a := hka ▸ hreset.run.time_nonneg k
  -- the reserve bound `ready + B·Δ + 2 ≤ heal`, `B = R + 8k + 4X + 26`, from (★) alone
  have hB := healthy_heal_margin S A V Q.run Q.hn Q.cap Q.index Q.gst
    (M := healthyResetCoeff S Q.index + 8 * S.k + 4 * (Q.index : Nat) + 26)
    (by have := contract_heal_ge_reset S A Q.cap Q.index; omega)
  push_cast at hB
  obtain ⟨w, hw, hq⟩ := healthy_preparation_timing S A V Q.run Q.hn Q.cap Q.index Q.gst hB
  exact ⟨⟨w, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2⟩,
    ⟨⟨a, ΔF, hreset, v, r, l, O, hO, hra, hla, _, le_rfl,
      by linarith only [hq a l ha0 ha hla, hB]⟩⟩⟩

end Consensus.Goldilocks.Obligations

end
