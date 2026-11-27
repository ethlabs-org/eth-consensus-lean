module
public import ConsensusLeanTest.Goldilocks.Refinement.Final
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Queries.Confirmed
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationReset
public import ConsensusLean.Proofs.RegimesRealizable.Main
import ConsensusLean.Lemmas.Tactic.Linarith
@[expose] public section

/-! # Witnesses: the healthy-nonfinal and outage queries are inhabited at the obligations contract

Kinds (a) and (r) (CONTRIBUTING "Statements") for three engine queries of the growing endpoint,
at the population binding `Ss S = { S with vote := AsChainShape.stock }`:
`Growing.ConfirmedQueryAt` (Healthy branch; the Sleepy branch's fields are
`GoldilocksSleepyWitness.sleepyQuery_fields`), `Growing.HealthyPreparationQueryAt` (at bound
`horizon`) and `Growing.OutageQueryAt`. Unlike the field witnesses of `Goldilocks/Refinement/Sleepy`
and `Goldilocks/Refinement/Final`, these inhabit the structures at `K (Ss S) (As S A)` itself: the
coefficients are defined, so no coefficient record is abstracted.

The queries are over engine runs (`(Sys (goldilocks (Ss S)) V).Run`), so the node-level tick run of
`Goldilocks/Runs/OneValidator/Run` does not apply; the runs are the existing engine witnesses: the
two-validator run of `Goldilocks/Refinement/Sleepy` (`healthy_run`, Healthy from GST 0) and the
outage witness of `Shape.regimes_realizable` at `K (Ss S) (As S A)` on five validators.

* (a) `confirmedQuery_healthy`, `healthyPreparationQuery_witness`, `outageQuery_witness`: each
  query is inhabited.
* (a) non-vacuous conclusions of proved consumers on them: `confirmedQuery_producer`
  (`confirmed_query_slot_at` gives a producer slot), `healthyPreparation_fit`
  (`healthy_preparation_reset_fit_at`, with `ready < heal` strictly), `outageQuery_lag`
  (`outageQuery_node_lag`).
* (r) `no_confirmedQuery_short`: a valid, collision-free, Healthy run with nonfinal progress whose
  horizon is below the latency deadline is the run of no `ConfirmedQueryAt` (the `bounded` field
  is a real constraint); `outageQuery_start_ge`: no outage query starts before the arming lag
  `(4k + 6)Δ`; `healthyPreparationQuery_not_final`: the `nonfinal` guard excludes `.final`.
* `*_applies`: the hypotheses of the healthy-liveness, healed-safety and persistence claims
  build the query with exactly those run, capability, index, GST and times, so the witnesses
  above are instances of those claims' hypotheses. -/

namespace Consensus.Goldilocks.Obligations.Test.NonfinalQueryWitness
open AsChainShape Simulation
open Consensus.Goldilocks.Obligations.Growing

open Shape Blocks SleepyWitness FinalWitness
open Consensus.Model (pubOf)

variable (S : Setup) (A : ContractAssumptions S)

/-- The population binding of `S`, at which the witness runs are built. -/
abbrev Ss : Setup := { S with vote := AsChainShape.stock }

/-- The contract assumptions of `S`, at its population binding. -/
abbrev As : ContractAssumptions (Ss S) :=
  ⟨A.fgSlots, A.two_le_fgSlots, A.signGap, A.sign_liveness,
    A.releaseGap, A.release_liveness, A.timeout, A.deep_final⟩

/-! ## Fidelity: the endpoint hypotheses build the queries -/

theorem confirmedQuery_applies {V : Type} [Fintype V] [DecidableEq V]
    (r : (Sys (goldilocks (Ss S)) V).Run)
    (hn : 1 ≤ Fintype.card V) (cap : Capability)
    (hcap : cap = .available ∨ cap = .stable) (idx : (K (Ss S) (As S A)).Idx) (gst t : Time)
    (hv : (Sys (goldilocks (Ss S)) V).Valid r)
    (hc : ¬ r.2.HashCollision)
    (hh : (Sys (goldilocks (Ss S)) V).Healthy
      (shapeProgress (goldilocks (Ss S)) V).toExternal (K (Ss S) (As S A)) gst r)
    (hp : (Sys (goldilocks (Ss S)) V).prog
      (shapeProgress (goldilocks (Ss S)) V) (K (Ss S) (As S A)) cap idx
      ((Sys (goldilocks (Ss S)) V).ready (K (Ss S) (As S A)) gst r) r.2.horizon r)
    (ht : (Sys (goldilocks (Ss S)) V).heal (K (Ss S) (As S A)) cap idx gst r ≤ t)
    (hb : t + ((K (Ss S) (As S A)).params.latency cap idx : Time) * r.1.ΔAC ≤ r.2.horizon)
    (hr : ∃ v, r.2.point.Ready ((Sys (goldilocks (Ss S)) V).cDur (K (Ss S) (As S A)) r) v
      (t + ((K (Ss S) (As S A)).params.latency cap idx : Time) * r.1.ΔAC)) :
    ∃ Q : ConfirmedQueryAt (Ss S) (As S A) V, Q.run = r ∧ Q.cap = cap ∧ Q.index = idx ∧
      Q.gst = gst ∧ Q.query = t :=
  ⟨⟨r, hn, cap, hcap, idx, gst, t, hv, hc, Or.inr (Or.inl ⟨hh, hp, ht⟩), hb, hr⟩,
    rfl, rfl, rfl, rfl, rfl⟩

theorem healthyPreparationQuery_applies {V : Type} [Fintype V] [DecidableEq V]
    (r : (Sys (goldilocks (Ss S)) V).Run)
    (hn : 1 ≤ Fintype.card V) (cap : Capability)
    (hcap : cap = .available ∨ cap = .stable) (idx : (K (Ss S) (As S A)).Idx) (gst : Time)
    (hv : (Sys (goldilocks (Ss S)) V).Valid r)
    (hc : ¬ r.2.HashCollision)
    (hh : (Sys (goldilocks (Ss S)) V).Healthy
        (shapeProgress (goldilocks (Ss S)) V).toExternal (K (Ss S) (As S A)) gst r) :
    ∃ Q : HealthyPreparationQueryAt (Ss S) (As S A) V, Q.run = r ∧ Q.cap = cap ∧
      Q.index = idx ∧ Q.gst = gst ∧ Q.bound = r.2.horizon :=
  ⟨⟨r, hn, cap, hcap, idx, gst, r.2.horizon, hv, hc, le_rfl, ⟨hh.1, hh.2.1, hh.2.2.1⟩,
    hh.2.2.2⟩, rfl, rfl, rfl, rfl, rfl⟩

theorem outageQuery_applies {V : Type} [Fintype V] [DecidableEq V]
    (r : (Sys (goldilocks (Ss S)) V).Run)
    (hn : 1 ≤ Fintype.card V) (T b₀ b₁ : Time)
    (hv : (Sys (goldilocks (Ss S)) V).Valid r)
    (hc : ¬ r.2.HashCollision)
    (ho : (Sys (goldilocks (Ss S)) V).Outage
      (shapeProgress (goldilocks (Ss S)) V).toExternal (K (Ss S) (As S A)) T b₀ b₁ r) :
    ∃ Q : OutageQueryAt (Ss S) (As S A) V, Q.run = r ∧ Q.T = T ∧ Q.start = b₀ ∧ Q.stop = b₁ :=
  ⟨⟨r, hn, T, b₀, b₁, hv, hc, ho⟩, rfl, rfl, rfl, rfl⟩

/-! ## The two-validator healthy run at `K (Ss S) (As S A)` -/

/-- The heal point of `.available` at index 1, GST 0, engine `Δ = 2`. -/
noncomputable abbrev healT : Time :=
  ((K (Ss S) (As S A)).params.heal .available ⟨1, (As S A).deepAdmits_one⟩ : Time) * 2

/-- The latency deadline after `healT`. -/
noncomputable abbrev horizonT : Time :=
  healT S A + ((K (Ss S) (As S A)).params.latency
    .available ⟨1, (As S A).deepAdmits_one⟩ : Time) * 2

theorem horizonT_nonneg : 0 ≤ horizonT S A := by positivity

/-- The two-validator run of `healthy_run` at the contract `K (Ss S) (As S A)`. -/
theorem healthy_run_K (H : Time) (hH : 0 ≤ H) :
    ∃ r : (Sys (goldilocks (Ss S)) (Fin 2)).Run,
      r.1 = (point H).env ∧ r.2.point = point H ∧ r.2.sel = sel S H ∧
      (Sys (goldilocks (Ss S)) (Fin 2)).Valid r ∧ ¬ r.2.HashCollision ∧
      (Sys (goldilocks (Ss S)) (Fin 2)).Healthy
          (shapeProgress (goldilocks (Ss S)) (Fin 2)).toExternal (K (Ss S) (As S A)) 0 r := by
  obtain ⟨r, hE, hp, hs, -, hv, hc, hh⟩ := healthy_run S A (contract_coefficients S A) H hH
  exact ⟨r, hE, hp, hs, hv, hc, hh⟩

/-- Nonfinal (`.available`) progress at index 1 holds on every interval of the run. -/
theorem healthy_run_prog {H : Time}
    {r : (Sys (goldilocks (Ss S)) (Fin 2)).Run}
    (hp : r.2.point = point H) (hs : r.2.sel = sel S H) (a b : Time) :
    (Sys (goldilocks (Ss S)) (Fin 2)).prog
      (shapeProgress (goldilocks (Ss S)) (Fin 2)) (K (Ss S) (As S A)) .available
      ⟨1, (As S A).deepAdmits_one⟩ a b r := by
  change PatternRecurrence r.2.point r.2.key (fun s => r.2.sel (ShapeRole.proposer s)) _ _ _ _ _
  apply patternRecurrence_of_all
  intro s j _
  rw [hs, hp]
  exact ⟨⟨_, Finset.mem_singleton_self _⟩, fun _ _ =>
    ⟨point_ready H _ _ _, by simp [EnvPoint.HonestAt, point]⟩⟩

/-- (a) A `HealthyPreparationQueryAt` at `K (Ss S) (As S A)`: the two-validator run,
`.available`, index 1, GST 0, bound at the horizon. -/
theorem healthyPreparationQuery_witness (H : Time) (hH : 0 ≤ H) :
    ∃ Q : HealthyPreparationQueryAt (Ss S) (As S A) (Fin 2), Q.run.2.point = point H ∧
      Q.run.2.sel = sel S H ∧ Q.run.1 = (point H).env := by
  obtain ⟨r, hE, hp, hs, hv, hc, hh⟩ := healthy_run_K S A H hH
  obtain ⟨Q, hQ, -⟩ := healthyPreparationQuery_applies S A r one_le_card .available
    (Or.inl rfl) ⟨1, (As S A).deepAdmits_one⟩ 0 hv hc hh
  exact ⟨Q, hQ ▸ hp, hQ ▸ hs, hQ ▸ hE⟩

/-- (a) The reset fit of `healthy_preparation_reset_fit_at` on that query, with `ready < heal`
strictly. -/
theorem healthyPreparation_fit (H : Time) (hH : 0 ≤ H) :
    ∃ Q : HealthyPreparationQueryAt (Ss S) (As S A) (Fin 2),
      Q.ready + (healthyResetCoeff (Ss S) Q.index : Time) * Q.params.Δ +
        (healthyResetSlack (Ss S) Q.index : Time) ≤ Q.heal ∧ Q.ready < Q.heal := by
  obtain ⟨Q, -, -, -⟩ := healthyPreparationQuery_witness S A H hH
  refine ⟨Q, healthy_preparation_reset_fit_at (Ss S) (As S A) (Fin 2) Q, ?_⟩
  have hfit := healthy_preparation_reset_fit_at (Ss S) (As S A) (Fin 2) Q
  have hR : (0 : Time) < healthyResetCoeff (Ss S) Q.index := by
    rw [healthyResetCoeff_val]; positivity
  have hΔ : (0 : Time) < Q.params.Δ := Q.params.toParams.hΔ
  have hr : (0 : Time) ≤ healthyResetSlack (Ss S) Q.index := Nat.cast_nonneg _
  nlinarith

/-- (a) A `ConfirmedQueryAt` at `K (Ss S) (As S A)` on the Healthy branch: the two-validator run
with horizon `healT + latency·Δ`, `.available`, index 1, GST 0, query time `healT` (the heal
point). -/
theorem confirmedQuery_healthy :
    ∃ Q : ConfirmedQueryAt (Ss S) (As S A) (Fin 2), Q.run.1 = (point (horizonT S A)).env ∧
      Q.run.2.point = point (horizonT S A) ∧ Q.run.2.sel = sel S (horizonT S A) ∧
      Q.cap = .available ∧ Q.index
        = ⟨1, (As S A).deepAdmits_one⟩ ∧ Q.gst = 0 ∧ Q.query = healT S A ∧
      (Sys (goldilocks (Ss S)) (Fin 2)).Healthy
          (shapeProgress (goldilocks (Ss S)) (Fin 2)).toExternal
          (K (Ss S) (As S A)) 0 Q.run := by
  obtain ⟨⟨E, rho⟩, hE, hp, hs, hv, hc, hh⟩ :=
    healthy_run_K S A (horizonT S A) (horizonT_nonneg S A)
  subst hE
  have hhor : rho.horizon = horizonT S A := congrArg EnvPoint.horizon hp
  let Q : ConfirmedQueryAt (Ss S) (As S A) (Fin 2) := ⟨⟨_, rho⟩, one_le_card, .available,
    Or.inl rfl, ⟨1, (As S A).deepAdmits_one⟩, 0, healT S A, hv, hc,
    Or.inr (Or.inl ⟨hh, healthy_run_prog S A hp hs _ _,
      by change max (0 : Time) 0 + _ * 2 ≤ healT S A; simp⟩),
    by rw [hhor]; change healT S A + _ * 2 ≤ horizonT S A; exact le_rfl,
    ⟨0, by change rho.point.Ready _ _ _; rw [hp]; exact point_ready _ _ _ _⟩⟩
  exact ⟨Q, rfl, hp, hs, rfl, rfl, rfl, rfl, hh⟩

/-- (a) Non-vacuous: on that query `confirmed_query_slot_at` gives a producer slot (a ready
proposer with its duty in the window after the query, still honest through its hold). The
readiness start is the Healthy `ready`, before the query by the reset fit. -/
theorem confirmedQuery_producer :
    ∃ Q : ConfirmedQueryAt (Ss S) (As S A) (Fin 2),
      Nonempty (ConfirmedProducerSlotAt (Ss S) (As S A) (Fin 2) Q) := by
  obtain ⟨Q, hE, hp, hs, hc, hi, hg, hq, hh⟩ := confirmedQuery_healthy S A
  obtain ⟨P, hPr, -, hPi, hPg, -⟩ := healthyPreparationQuery_applies S A Q.run Q.hn .available
    (Or.inl rfl) ⟨1, (As S A).deepAdmits_one⟩ 0 Q.valid Q.noCollision hh
  have hfit := healthy_preparation_reset_fit_at (Ss S) (As S A) (Fin 2) P
  have hR : (0 : Time) ≤ healthyResetCoeff (Ss S) P.index := Nat.cast_nonneg _
  have hΔ : (0 : Time) < P.params.Δ := P.params.toParams.hΔ
  have hr : (0 : Time) ≤ healthyResetSlack (Ss S) P.index := Nat.cast_nonneg _
  have hlt : P.ready ≤ P.heal := by nlinarith
  have hready : P.ready = (Sys (goldilocks (Ss S)) (Fin 2)).ready
      (K (Ss S) (As S A)) 0 Q.run := by
    change (Sys (goldilocks (Ss S)) (Fin 2)).ready (K (Ss S) (As S A)) P.gst P.run = _
    rw [hPg, hPr]
  have hheal : P.heal = healT S A := by
    change (Sys (goldilocks (Ss S)) (Fin 2)).heal (K (Ss S) (As S A)) P.cap P.index P.gst P.run = _
    rw [hPi, hPg, hPr]
    change max (0 : Time) 0 +
      ((K (Ss S) (As S A)).params.heal
        .available ⟨1, (As S A).deepAdmits_one⟩ : Time) * Q.run.1.ΔAC = _
    rw [hE]; simp only [max_self, zero_add]; rfl
  have h0 : 0 ≤ (Sys (goldilocks (Ss S)) (Fin 2)).ready (K (Ss S) (As S A)) 0 Q.run := by
    change 0 ≤ max (0 : Time) 0 +
      (Sys (goldilocks (Ss S)) (Fin 2)).cDur (K (Ss S) (As S A)) Q.run + 1
    have : (0 : Time) ≤ (Sys (goldilocks (Ss S)) (Fin 2)).cDur (K (Ss S) (As S A)) Q.run := by
      change (0 : Time) ≤ ((K (Ss S) (As S A)).params.catchUp : Time) * Q.run.1.ΔAC
      have := Q.run.1.ΔAC_pos; positivity
    simp only [max_self]; linarith
  refine ⟨Q, confirmed_query_slot_at (Ss S) (As S A) (Fin 2) Q
    (ready := (Sys (goldilocks (Ss S)) (Fin 2)).ready (K (Ss S) (As S A)) 0 Q.run) ?_ ?_⟩
  · rw [hc, hi]; exact healthy_run_prog S A hp hs _ _
  · rw [max_eq_left h0, hq, ← hheal, ← hready]; exact hlt

/-- (r) The latency deadline is a real constraint: the two-validator Healthy run with nonfinal
progress whose horizon is the heal point `healT` (below the deadline `healT + latency·Δ`) is the
run of no `ConfirmedQueryAt` at `.available`, index 1, with a query at or after `healT`. -/
theorem no_confirmedQuery_short :
    ∃ r : (Sys (goldilocks (Ss S)) (Fin 2)).Run,
      (Sys (goldilocks (Ss S)) (Fin 2)).Valid r ∧ ¬ r.2.HashCollision ∧
      (Sys (goldilocks (Ss S)) (Fin 2)).Healthy
          (shapeProgress (goldilocks (Ss S)) (Fin 2)).toExternal (K (Ss S) (As S A)) 0 r ∧
      (Sys (goldilocks (Ss S)) (Fin 2)).prog
        (shapeProgress (goldilocks (Ss S)) (Fin 2)) (K (Ss S) (As S A)) .available
        ⟨1, (As S A).deepAdmits_one⟩
        ((Sys (goldilocks (Ss S)) (Fin 2)).ready (K (Ss S) (As S A)) 0 r)
        r.2.horizon r ∧
      ∀ Q : ConfirmedQueryAt (Ss S) (As S A) (Fin 2), Q.run = r → Q.cap = .available →
        Q.index = ⟨1, (As S A).deepAdmits_one⟩ → healT S A ≤ Q.query → False := by
  have hH : 0 ≤ healT S A := by positivity
  obtain ⟨⟨E, rho⟩, hE, hp, hs, hv, hc, hh⟩ := healthy_run_K S A (healT S A) hH
  subst hE
  have hhor : rho.horizon = healT S A := congrArg EnvPoint.horizon hp
  refine ⟨⟨_, rho⟩, hv, hc, hh, healthy_run_prog S A hp hs _ _, fun Q hQ hc hi hq => ?_⟩
  have hb := Q.bounded
  rw [hc, hi, hQ] at hb
  change _ + ((contract_latency S A .available 1 : Nat) : Time) * 2 ≤ rho.horizon at hb
  rw [contract_latency_available, hhor] at hb
  push_cast at hb
  linarith

/-- (r) The `nonfinal` guard: no `HealthyPreparationQueryAt` is at `.final`. -/
theorem healthyPreparationQuery_not_final {V : Type} [Fintype V] [DecidableEq V]
    (Q : HealthyPreparationQueryAt (Ss S) (As S A) V) : Q.cap ≠ .final := by
  rcases Q.nonfinal with h | h <;> rw [h] <;> decide

/-! ## The outage witness of `regimes_realizable` at `K (Ss S) (As S A)` -/

/-- (a) An `OutageQueryAt` at `K (Ss S) (As S A)`: the outage witness of
`Shape.regimes_realizable` for the obligations contract on five validators, at `Δ = ΔF = 2`,
armed at `T ≥ 0`. -/
theorem outageQuery_witness : ∃ Q : OutageQueryAt (Ss S) (As S A) (Fin 5), 0 ≤ Q.T := by
  obtain ⟨r, T, b₀, b₁, ⟨⟨hv, hc, -, -, -⟩, -, -⟩, ho, -, -⟩ :=
    (Shape.regimes_realizable (goldilocks (Ss S)) (K (Ss S) (As S A))
      (meetsObligations_admissible (Ss S) (As S A))
      (meetsObligations_progressFits (Ss S) (As S A))
      (meetsObligations_progressTolerant (Ss S) (As S A)) (Fin 5)
      (((meetsObligations_optimalFaultTolerance (Ss S) (As S A)).room_iff _).mpr
        (by decide))).outage
      2 2 0 (by decide) (by decide)
  obtain ⟨Q, -, hT, -, -⟩ := outageQuery_applies S A r (by decide) T b₀ b₁ hv hc ho
  exact ⟨Q, hT ▸ Q.outage.1.1⟩

/-- The lag `4k + 6` of an outage query is the node lag `(4k + 6)Δ`. -/
theorem outageQuery_node_lag {V : Type} [Fintype V] [DecidableEq V]
    (Q : OutageQueryAt (Ss S) (As S A) V) :
    Q.T + (4 * Q.params.k + 6) * Q.params.Δ ≤ Q.start := by
  obtain ⟨⟨-, hlag, -, -⟩, -⟩ := Q.outage
  change Q.T + ((4 * S.k + 6 : Nat) : Int) * Q.run.1.ΔAC ≤ Q.start at hlag
  change Q.T + (4 * (S.k : Int) + 6) * Q.run.1.ΔAC ≤ Q.start
  push_cast at hlag
  linarith

/-- (a) Non-vacuous: `outageQuery_node_lag` on that query, `T + (4k + 6)Δ ≤ b₀`. -/
theorem outageQuery_lag : ∃ Q : OutageQueryAt (Ss S) (As S A) (Fin 5),
    Q.T + (4 * Q.params.k + 6) * Q.params.Δ ≤ Q.start := by
  obtain ⟨Q, -⟩ := outageQuery_witness S A
  exact ⟨Q, outageQuery_node_lag S A Q⟩

/-- (r) No outage query starts before the arming lag: every `OutageQueryAt` has
`(4k + 6)Δ ≤ b₀` (`T ≥ 0`), so a run whose outage starts earlier is the run of none. -/
theorem outageQuery_start_ge {V : Type} [Fintype V] [DecidableEq V]
    (Q : OutageQueryAt (Ss S) (As S A) V) :
    (4 * Q.params.k + 6) * Q.params.Δ ≤ Q.start := by
  have h := outageQuery_node_lag S A Q
  have hT : 0 ≤ Q.T := Q.outage.1.1
  linarith

end Consensus.Goldilocks.Obligations.Test.NonfinalQueryWitness

end
