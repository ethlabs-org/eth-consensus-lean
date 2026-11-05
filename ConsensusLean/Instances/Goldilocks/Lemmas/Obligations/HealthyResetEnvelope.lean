module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ResetOfDrainRounds
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ResetCoefficients
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyGap
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyQueryShared
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.DrainWarm
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
`Δ_F,p = protoFGDelay` (`6Δ + Δ_F,p ≤ 4Δ·fgSlots ≤ 4Δ·δ_t`, `protoFGDelay_timeout_of_healthy`). -/
private theorem healthy_hsShared (Q : HealthyPreparationQuery S A V) :
    Healing.HSSharedUpTo Q.trace (honestKeys S Q.run.2) (digestOf S Q.run.2) Q.gst
      (protoFGDelay (Model.pubOf Q.run.1)) Q.run.2.horizon :=
  Q.hsSharedUpTo_of_le _ le_rfl (protoFGDelay_timeout_of_healthy S A V Q.run Q.hn Q.healthy)

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
  have hrun := simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid
  -- the ready scalar
  have hready : Q.ready = max Q.gst 0 + (Sys (goldilocks S) V).cDur (K S A) Q.run + 1 := rfl
  have hcDur : 0 ≤ (Sys (goldilocks S) V).cDur (K S A) Q.run :=
    mul_nonneg (Int.natCast_nonneg _) Q.run.1.ΔAC_pos.le
  have hr0 : 0 ≤ Q.ready := by rw [hready]; linarith [le_max_right Q.gst 0]
  have hgr : gbar Q.gst ≤ Q.ready := by
    change max Q.gst 0 ≤ Q.ready
    rw [hready]; linarith
  have hcz := cutZ_fit_of_catchUp A V (contract_coefficients S A)
    (by rw [contract_coefficients_catchUp]; exact contract_catchUp_ge_sleepy S A) Q.run Q.hn Q.gst
  change Healing.cutZ Q.params.toParams Q.gst + Q.params.Δ + 1 ≤ max Q.ready 0 + 4 * Q.params.Δ
    at hcz
  rw [max_eq_left hr0] at hcz
  have hnr := healthy_noRestartAfter S A V Q
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
  have hBeq : resetBoundRounds Q.ready Q.params.Δ (2 * Q.params.Δ) Q.params.toParams.fg.δt
      (Q.index : Nat) (healthyDrainLen S Q.index) =
      Q.ready + (healthyResetCoeff S Q.index : Time) * Q.params.Δ := by
    rw [resetBoundRounds_eq, healthyResetCoeff_val, hδeq]; push_cast; ring
  have hR : (24 : Time) ≤ healthyResetCoeff S Q.index := by
    rw [healthyResetCoeff_val]; push_cast
    linarith [Nat.cast_nonneg (α := Time) (healthyDrainLen S Q.index)]
  have hr : (0 : Time) ≤ healthyResetSlack S Q.index := Nat.cast_nonneg _
  have hBh : resetBoundRounds Q.ready Q.params.Δ (2 * Q.params.Δ) Q.params.toParams.fg.δt
      (Q.index : Nat) (healthyDrainLen S Q.index) ≤ Q.heal := by
    rw [hBeq]; linarith
  have h4B : Q.ready + 4 * Q.params.Δ ≤ Q.heal := by
    have := mul_le_mul_of_nonneg_right hR hΔ.le
    linarith
  -- the kernel
  obtain ⟨a, ha, hab⟩ := exists_reset_of_drain_rounds_awake hrun hs.noColl hs.faults hs.sync
    hs.awake (healthy_repair_catch S A V Q) hnr hH (by rw [hδeq]; omega)
    (by rw [hδeq]; exact hs.timeoutDelay)
    hr0 hgr Q.index.pos hcz (hBh.trans hb)
    (fun s₀ N hs₀ hN => hgp_of_healthyQuery S A V Q hb hp (by rw [max_eq_left hr0]; exact hs₀)
      (by linarith))
    hdrain
  obtain ⟨j, hj, hjt⟩ := Healing.snapshot_of_awake hrun hs.awake hH (b := Q.run.2.horizon)
    (by linarith)
  refine ⟨protoFGDelay (Model.pubOf Q.run.1), a, reset_premises_of_healthy_query S A V Q hs.sync ha
    (by linarith) ⟨j, hj, hjt⟩, ?_⟩
  rw [hBeq] at hab
  linarith

/-- **The window fit before heal**: `ready + R·Δ + r ≤ heal` at every query, from the
coefficient inequality `contract_heal_ge_reset` alone. With engine delay `d ≥ 1`, `Δ = d`,
`ready = g₀ + C·d + 1` and `heal = g₀ + H·d`, `H ≥ C + R + r + 1` gives
`heal − ready − R·Δ − r ≥ r(d − 1) + d − 1 ≥ 0`. -/
theorem healthy_reset_fit (Q : HealthyPreparationQuery S A V) :
    Q.ready + (healthyResetCoeff S Q.index : Time) * Q.params.Δ +
      (healthyResetSlack S Q.index : Time) ≤ Q.heal := by
  have hd : (1 : Time) ≤ Q.run.1.ΔAC := Q.run.1.ΔAC_pos
  have hready :
      Q.ready = max Q.gst 0 + ((contract_catchUp S A : Nat) : Time) * Q.run.1.ΔAC + 1 := by
    change max Q.gst 0 + (((contract_coefficients S A).catchUp : Nat) : Time) * Q.run.1.ΔAC + 1 = _
    rw [contract_coefficients_catchUp]
  have hheal : Q.heal = max Q.gst 0 + (contract_heal S A Q.cap Q.index : Time) * Q.run.1.ΔAC := by
    change max Q.gst 0 + ((contract_coefficients S A).heal Q.cap Q.index : Time) * Q.run.1.ΔAC = _
    rw [contract_coefficients_heal]
  have hΔ : Q.params.Δ = Q.run.1.ΔAC := rfl
  have hH : ((contract_catchUp S A : Nat) : Time) + (healthyResetCoeff S Q.index : Time) +
      (healthyResetSlack S Q.index : Time) + 1 ≤ (contract_heal S A Q.cap Q.index : Time) := by
    have := contract_heal_ge_reset S A Q.cap Q.index
    exact_mod_cast (show _ ≤ _ by omega)
  have hr0 : (0 : Time) ≤ healthyResetSlack S Q.index := Nat.cast_nonneg _
  rw [hready, hheal, hΔ]
  linarith [mul_le_mul_of_nonneg_right hH (by linarith : (0 : Time) ≤ Q.run.1.ΔAC),
    mul_nonneg hr0 (by linarith : (0 : Time) ≤ Q.run.1.ΔAC - 1)]

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
    (drainOutputs_of_service (simTrace_goldilocksRun S Q.run.2 Q.hn Q.valid) hs.noColl hs.sync
      hs.awake hs.faults (healthy_repair_catch S A V Q) (healthy_noRestartAfter S A V Q) ?_)
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
  -- the scalars
  have hd : (1 : Time) ≤ Q.run.1.ΔAC := Q.run.1.ΔAC_pos
  have hΔ : Q.params.Δ = Q.run.1.ΔAC := rfl
  have hready :
      Q.ready = max Q.gst 0 + ((contract_catchUp S A : Nat) : Time) * Q.run.1.ΔAC + 1 := by
    change max Q.gst 0 + (((contract_coefficients S A).catchUp : Nat) : Time) * Q.run.1.ΔAC + 1 = _
    rw [contract_coefficients_catchUp]
  have hheal : Q.heal = max Q.gst 0 + (contract_heal S A Q.cap Q.index : Time) * Q.run.1.ΔAC := by
    change max Q.gst 0 + ((contract_coefficients S A).heal Q.cap Q.index : Time) * Q.run.1.ΔAC = _
    rw [contract_coefficients_heal]
  have hC : (19 : Time) ≤ (contract_catchUp S A : Nat) := by
    exact_mod_cast contract_catchUp_ge_sleepy S A
  have hk : (2 : Time) ≤ (S.k : Time) := by exact_mod_cast S.two_le_k
  have hkk : (Q.params.k : Time) = S.k := rfl
  rw [healthyResetSlack_val] at ha
  push_cast at ha
  -- the reserve bound `ready + B·Δ + 2 ≤ heal`, `B = R + 8k + 4X + 26`, from (★) alone
  set B : Time := (healthyResetCoeff S Q.index : Time) + 8 * (S.k : Time) +
    4 * ((Q.index : Nat) : Time) + 26 with hBdef
  have hB : Q.ready + B * Q.params.Δ + 2 ≤ Q.heal := by
    have hH : ((contract_catchUp S A : Nat) : Time) + B + 3 ≤
        (contract_heal S A Q.cap Q.index : Time) := by
      have h1 := (Nat.cast_le (α := Time)).mpr (contract_heal_ge_reset S A Q.cap Q.index)
      rw [healthyResetSlack_val] at h1
      push_cast at h1
      rw [hBdef]
      linarith
    rw [hready, hheal, hΔ]
    linarith [mul_le_mul_of_nonneg_right hH (by linarith : (0 : Time) ≤ Q.run.1.ΔAC)]
  have hR0 : (24 : Time) ≤ healthyResetCoeff S Q.index := by
    rw [healthyResetCoeff_val]; push_cast
    linarith [Nat.cast_nonneg (α := Time) (healthyDrainLen S Q.index)]
  have hX0 : (0 : Time) ≤ ((Q.index : Nat) : Time) := Nat.cast_nonneg _
  have hr0 : 0 ≤ Q.ready := by rw [hready]; positivity
  have hgr : SA.gbar Q.gst + 4 * Q.params.Δ ≤ Q.ready := by
    change max Q.gst 0 + _ ≤ _
    rw [hready, hΔ]; nlinarith
  -- the base slot `w = slot(ready) + 1`: `ready < t_w ≤ ready + 4Δ`
  have hts (s j : Nat) : Q.params.ts (s + j : Nat) = Q.params.ts s + 4 * Q.params.Δ * j := by
    simp only [SA.SAParams.ts]; push_cast; ring
  set w : Nat := Q.params.slot Q.ready + 1 with hw
  have hw0 : Q.params.ts (Q.params.slot Q.ready : Nat) ≤ Q.ready :=
    (SA.ts_le_iff_le_slot Q.params hr0 _).mpr le_rfl
  have hw1 : Q.ready < Q.params.ts w := by
    have h := (SA.ts_le_iff_le_slot Q.params hr0 (w : Int)).not.mpr (by rw [hw]; push_cast; omega)
    exact lt_of_not_ge h
  have hw2 : Q.params.ts w ≤ Q.ready + 4 * Q.params.Δ := by
    rw [hw, hts]; push_cast; linarith
  have hkB : (4 * (S.k : Time) + 18) * Q.params.Δ ≤ B * Q.params.Δ :=
    mul_le_mul_of_nonneg_right (by rw [hBdef]; linarith) (by linarith)
  -- the reset, its drain and its seed
  obtain ⟨⟨_, _, k, _, -, -, hka⟩, -⟩ := hreset.reset
  have ha0 : 0 ≤ a := hka ▸ hreset.run.time_nonneg k
  have hsa : Q.params.ts (Q.params.slot a : Nat) ≤ a :=
    (SA.ts_le_iff_le_slot Q.params ha0 _).mpr le_rfl
  have hkD : (0 : Time) ≤ (S.k : Time) * Q.params.Δ := by positivity
  have hdrain : Healing.drainTime Q.params a ≤ a + (8 * (S.k : Time) + 20) * Q.params.Δ := by
    rw [Healing.drainTime_eq, show Q.params.slot a + 2 * Q.params.k + 5 =
      Q.params.slot a + (2 * S.k + 5) from rfl, hts]
    push_cast; linarith
  have hla' : l ≤ Q.params.slot a := hla
  have hseed : Q.params.ts (l + 1 : Nat) ≤ a + 4 * Q.params.Δ := by
    have hl : ((l + 1 : Nat) : Int) ≤ (Q.params.slot a : Int) + 1 := by push_cast; omega
    have := mul_le_mul_of_nonneg_left hl (by linarith : (0 : Time) ≤ 4 * Q.params.Δ)
    simp only [SA.SAParams.ts] at hsa ⊢
    linarith
  have hRD := mul_le_mul_of_nonneg_right hR0 (by linarith : (0 : Time) ≤ Q.params.Δ)
  have hq : max Q.ready (max (Healing.drainTime Q.params a) (max (Q.params.ts w)
      (max (SA.gbar Q.gst + 4 * Q.params.Δ) (max 0 (Q.params.ts (l + 1 : Nat)))))) ≤
      Q.ready + ((healthyResetCoeff S Q.index : Time) + 8 * (S.k : Time) + 20) * Q.params.Δ :=
    max_le (by linarith) (max_le (by linarith) (max_le (by linarith)
      (max_le (by linarith) (max_le (by linarith) (by linarith)))))
  have hXD : (0 : Time) ≤ ((Q.index : Nat) : Time) * Q.params.Δ := by positivity
  rw [hBdef] at hB
  refine ⟨⟨w, hw1.le, by linarith, by rw [hts]; push_cast; linarith,
    by rw [hts, hkk]; linarith, by rw [hts]; push_cast; linarith⟩, ⟨?_⟩⟩
  exact ⟨a, ΔF, hreset, v, r, l, O, hO, hra, hla, _, le_rfl, by linarith⟩

end Consensus.Goldilocks.Obligations

end
