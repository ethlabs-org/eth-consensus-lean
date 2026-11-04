module
public import ConsensusLeanTest.GoldilocksFinalWitness
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.NonfinalSuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyGap
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.HealthyResetEnvelope
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OutageArming
public import ConsensusLean.Proofs.RegimesRealizable.Main
import ConsensusLean.Lemmas.Tactic.Linarith
@[expose] public section

/-! # Witnesses: the healthy-nonfinal and outage queries are inhabited at the Accepted contract

Kinds (a) and (r) (CONTRIBUTING "Statements") for the three engine queries that the nonfinal
endpoints of `Lemmas/Obligations/Concrete` build: `ConfirmedQuery` (Healthy branch; the Sleepy
branch's fields are `GoldilocksSleepyWitness.sleepyQuery_fields`), `HealthyPreparationQuery` and
`OutageQuery`. Unlike the field witnesses of `GoldilocksSleepyWitness` and
`GoldilocksFinalWitness`, these inhabit the structures at `K S A` itself: the coefficients are
defined, so no coefficient record is abstracted.

The queries are over engine runs (`(Sys (goldilocks S) V).Run`), so the node-level tick run of
`GoldilocksWitnessRun` does not apply; the runs are the existing engine witnesses: the
two-validator run of `GoldilocksSleepyWitness` (`healthy_run`, Healthy from GST 0) and the outage
witness of `Shape.regimes_realizable` at `K S A` on five validators.

* (a) `confirmedQuery_healthy`, `healthyPreparationQuery_witness`, `outageQuery_witness`: each
  query is inhabited.
* (a) non-vacuous conclusions of proved consumers on them: `confirmedQuery_producer`
  (`healthy_query_slot` gives a producer slot), `healthyPreparation_fit`
  (`healthy_reset_fit`, with `ready < heal` strictly), `outageQuery_lag` (`outage_node_lag`).
* (r) `no_confirmedQuery_short`: a valid, collision-free, Healthy run with nonfinal progress whose
  horizon is below the latency deadline is the run of no `ConfirmedQuery` (the `bounded` field
  is a real constraint); `outageQuery_start_ge`: no outage query starts before the arming lag
  `(4k + 6)Δ`; `healthyPreparationQuery_not_final`: the `nonfinal` guard excludes `.final`.
* `*_applies`: the endpoint hypotheses of `accepted_healthyLive`, `accepted_healedSafe` and
  `accepted_persists` build the query with exactly those run, capability, index, GST and times
  (as `Concrete.lean` does), so the witnesses above are instances of what the endpoints use. -/

namespace Consensus.Goldilocks.Obligations.Test.NonfinalQueryWitness
open AsChainShape Simulation

open Shape Blocks SleepyWitness FinalWitness
open Consensus.Model (pubOf)

variable (S : Setup) (A : ContractAssumptions S)

/-! ## Fidelity: the endpoint hypotheses build the queries -/

theorem confirmedQuery_applies {V : Type} [Fintype V] [DecidableEq V]
    (r : (Sys (goldilocks S) V).Run) (hn : 1 ≤ Fintype.card V) (cap : Capability)
    (hcap : cap = .available ∨ cap = .stable) (idx : (K S A).Idx) (gst t : Time)
    (hv : (Sys (goldilocks S) V).Valid r) (hc : ¬ r.2.HashCollision)
    (hh : (Sys (goldilocks S) V).Healthy (K S A) gst r)
    (hp : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) cap idx
      ((Sys (goldilocks S) V).ready (K S A) gst r) r.2.horizon r)
    (ht : (Sys (goldilocks S) V).heal (K S A) cap idx gst r ≤ t)
    (hb : t + ((K S A).params.latency cap idx : Time) * r.1.ΔAC ≤ r.2.horizon)
    (hr : ∃ v, r.2.point.Ready ((Sys (goldilocks S) V).cDur (K S A) r) v
      (t + ((K S A).params.latency cap idx : Time) * r.1.ΔAC)) :
    ∃ Q : ConfirmedQuery S A V, Q.run = r ∧ Q.cap = cap ∧ Q.index = idx ∧ Q.gst = gst ∧
      Q.query = t :=
  ⟨⟨r, hn, cap, hcap, idx, gst, t, hv, hc, Or.inr ⟨hh, hp, ht⟩, hb, hr⟩,
    rfl, rfl, rfl, rfl, rfl⟩

theorem healthyPreparationQuery_applies {V : Type} [Fintype V] [DecidableEq V]
    (r : (Sys (goldilocks S) V).Run) (hn : 1 ≤ Fintype.card V) (cap : Capability)
    (hcap : cap = .available ∨ cap = .stable) (idx : (K S A).Idx) (gst : Time)
    (hv : (Sys (goldilocks S) V).Valid r) (hc : ¬ r.2.HashCollision)
    (hh : (Sys (goldilocks S) V).Healthy (K S A) gst r) :
    ∃ Q : HealthyPreparationQuery S A V, Q.run = r ∧ Q.cap = cap ∧ Q.index = idx ∧
      Q.gst = gst :=
  ⟨⟨r, hn, cap, hcap, idx, gst, hv, hc, hh⟩, rfl, rfl, rfl, rfl⟩

theorem outageQuery_applies {V : Type} [Fintype V] [DecidableEq V]
    (r : (Sys (goldilocks S) V).Run) (hn : 1 ≤ Fintype.card V) (T b₀ b₁ : Time)
    (hv : (Sys (goldilocks S) V).Valid r) (hc : ¬ r.2.HashCollision)
    (ho : (Sys (goldilocks S) V).Outage (K S A) T b₀ b₁ r) :
    ∃ Q : OutageQuery S A V, Q.run = r ∧ Q.T = T ∧ Q.start = b₀ ∧ Q.stop = b₁ :=
  ⟨⟨r, hn, T, b₀, b₁, hv, hc, ho⟩, rfl, rfl, rfl, rfl⟩

/-! ## The two-validator healthy run at `K S A` -/

/-- The heal point of `.available` at index 1, GST 0, engine `Δ = 2`. -/
noncomputable abbrev healT : Time := ((K S A).params.heal .available (1 : ℕ+) : Time) * 2

/-- The latency deadline after `healT`. -/
noncomputable abbrev horizonT : Time :=
  healT S A + ((K S A).params.latency .available (1 : ℕ+) : Time) * 2

theorem horizonT_nonneg : 0 ≤ horizonT S A := by positivity

/-- Nonfinal (`.available`) progress at index 1 holds on every interval of the run. -/
theorem healthy_run_prog {H : Time} {r : (Sys (goldilocks S) (Fin 2)).Run}
    (hp : r.2.point = point H) (hs : r.2.sel = sel S H) (a b : Time) :
    (Sys (goldilocks S) (Fin 2)).prog (shapeProgress (goldilocks S) (Fin 2)) (K S A) .available
      (1 : ℕ+) a b r := by
  change PatternRecurrence r.2.point r.2.key (fun s => r.2.sel (ShapeRole.proposer s)) _ _ _ _ _
  apply patternRecurrence_of_all
  intro s j _
  rw [hs, hp]
  exact ⟨⟨_, Finset.mem_singleton_self _⟩, fun _ _ => point_ready H _ _ _⟩

/-- (a) A `HealthyPreparationQuery` at `K S A`: the two-validator run, `.available`, index 1,
GST 0. -/
theorem healthyPreparationQuery_witness (H : Time) (hH : 0 ≤ H) :
    ∃ Q : HealthyPreparationQuery S A (Fin 2), Q.run.2.point = point H ∧
      Q.run.2.sel = sel S H ∧ Q.run.1 = (point H).env := by
  obtain ⟨r, hE, hp, hs, -, hv, hc, hh⟩ := healthy_run S A (contract_coefficients S A) H hH
  obtain ⟨Q, hQ, -⟩ := healthyPreparationQuery_applies S A r one_le_card .available
    (Or.inl rfl) (1 : ℕ+) 0 hv hc hh
  exact ⟨Q, hQ ▸ hp, hQ ▸ hs, hQ ▸ hE⟩

/-- (a) The reset fit of `healthy_reset_fit` on that query, with `ready < heal` strictly. -/
theorem healthyPreparation_fit (H : Time) (hH : 0 ≤ H) :
    ∃ Q : HealthyPreparationQuery S A (Fin 2),
      Q.ready + (healthyResetCoeff S Q.index : Time) * Q.params.Δ +
        (healthyResetSlack S Q.index : Time) ≤ Q.heal ∧ Q.ready < Q.heal := by
  obtain ⟨Q, -, -, -⟩ := healthyPreparationQuery_witness S A H hH
  refine ⟨Q, healthy_reset_fit S A (Fin 2) Q, ?_⟩
  have hfit := healthy_reset_fit S A (Fin 2) Q
  have hR : (0 : Time) < healthyResetCoeff S Q.index := by
    rw [healthyResetCoeff_val]; positivity
  have hΔ : (0 : Time) < Q.params.Δ := Q.params.toParams.hΔ
  have hr : (0 : Time) ≤ healthyResetSlack S Q.index := Nat.cast_nonneg _
  nlinarith

/-- (a) A `ConfirmedQuery` at `K S A` on the Healthy branch: the two-validator run with horizon
`healT + latency·Δ`, `.available`, index 1, GST 0, query time `healT` (the heal point). -/
theorem confirmedQuery_healthy :
    ∃ Q : ConfirmedQuery S A (Fin 2), Q.run.1 = (point (horizonT S A)).env ∧
      Q.run.2.point = point (horizonT S A) ∧ Q.run.2.sel = sel S (horizonT S A) ∧
      Q.cap = .available ∧ Q.index = (1 : ℕ+) ∧ Q.gst = 0 ∧ Q.query = healT S A ∧
      (Sys (goldilocks S) (Fin 2)).Healthy (K S A) 0 Q.run := by
  obtain ⟨⟨E, rho⟩, hE, hp, hs, -, hv, hc, hh⟩ :=
    healthy_run S A (contract_coefficients S A) (horizonT S A) (horizonT_nonneg S A)
  subst hE
  have hhor : rho.horizon = horizonT S A := congrArg EnvPoint.horizon hp
  let Q : ConfirmedQuery S A (Fin 2) := ⟨⟨_, rho⟩, one_le_card, .available, Or.inl rfl,
    (1 : ℕ+), 0, healT S A, hv, hc,
    Or.inr ⟨hh, healthy_run_prog S A hp hs _ _,
      by change max (0 : Time) 0 + _ * 2 ≤ healT S A; simp⟩,
    by rw [hhor]; change healT S A + _ * 2 ≤ horizonT S A; exact le_rfl,
    ⟨0, by rw [hp]; exact point_ready _ _ _ _⟩⟩
  exact ⟨Q, rfl, hp, hs, rfl, rfl, rfl, rfl, hh⟩

/-- (a) Non-vacuous: on that query `healthy_query_slot` gives a producer slot (an honest ready
proposer with its duty in the window after the query). The readiness start is the Healthy
`ready`, before the query by the reset fit. -/
theorem confirmedQuery_producer :
    ∃ Q : ConfirmedQuery S A (Fin 2), Nonempty (ConfirmedProducerSlot S A (Fin 2) Q) := by
  obtain ⟨Q, hE, hp, hs, hc, hi, hg, hq, hh⟩ := confirmedQuery_healthy S A
  let P : HealthyPreparationQuery S A (Fin 2) :=
    ⟨Q.run, Q.hn, .available, Or.inl rfl, (1 : ℕ+), 0, Q.valid, Q.noCollision, hh⟩
  have hfit := healthy_reset_fit S A (Fin 2) P
  have hR : (0 : Time) ≤ healthyResetCoeff S P.index := Nat.cast_nonneg _
  have hΔ : (0 : Time) < P.params.Δ := P.params.toParams.hΔ
  have hr : (0 : Time) ≤ healthyResetSlack S P.index := Nat.cast_nonneg _
  have hlt : P.ready ≤ P.heal := by nlinarith
  have hready : P.ready = (Sys (goldilocks S) (Fin 2)).ready (K S A) 0 Q.run := rfl
  have hheal : P.heal = healT S A := by
    change max (0 : Time) 0 + ((K S A).params.heal .available (1 : ℕ+) : Time) * Q.run.1.ΔAC = _
    rw [hE]; simp only [max_self, zero_add]; rfl
  have h0 : 0 ≤ (Sys (goldilocks S) (Fin 2)).ready (K S A) 0 Q.run := by
    change 0 ≤ max (0 : Time) 0 + (Sys (goldilocks S) (Fin 2)).cDur (K S A) Q.run + 1
    have : (0 : Time) ≤ (Sys (goldilocks S) (Fin 2)).cDur (K S A) Q.run := by
      change (0 : Time) ≤ ((K S A).params.catchUp : Time) * Q.run.1.ΔAC
      have := Q.run.1.ΔAC_pos; positivity
    simp only [max_self]; linarith
  refine ⟨Q, healthy_query_slot S A (Fin 2) Q (ready := (Sys (goldilocks S) (Fin 2)).ready
    (K S A) 0 Q.run) ?_ ?_⟩
  · rw [hc, hi]; exact healthy_run_prog S A hp hs _ _
  · rw [max_eq_left h0, hq, ← hheal, ← hready]; exact hlt

/-- (r) The latency deadline is a real constraint: the two-validator Healthy run with nonfinal
progress whose horizon is the heal point `healT` (below the deadline `healT + latency·Δ`) is the
run of no `ConfirmedQuery` at `.available`, index 1, with a query at or after `healT`. -/
theorem no_confirmedQuery_short :
    ∃ r : (Sys (goldilocks S) (Fin 2)).Run, (Sys (goldilocks S) (Fin 2)).Valid r ∧
        ¬ r.2.HashCollision ∧
      (Sys (goldilocks S) (Fin 2)).Healthy (K S A) 0 r ∧
      (Sys (goldilocks S) (Fin 2)).prog (shapeProgress (goldilocks S) (Fin 2)) (K S A) .available
        (1 : ℕ+) ((Sys (goldilocks S) (Fin 2)).ready (K S A) 0 r) r.2.horizon r ∧
      ∀ Q : ConfirmedQuery S A (Fin 2), Q.run = r → Q.cap = .available → Q.index = (1 : ℕ+) →
        healT S A ≤ Q.query → False := by
  have hH : 0 ≤ healT S A := by positivity
  obtain ⟨⟨E, rho⟩, hE, hp, hs, -, hv, hc, hh⟩ :=
    healthy_run S A (contract_coefficients S A) (healT S A) hH
  subst hE
  have hhor : rho.horizon = healT S A := congrArg EnvPoint.horizon hp
  refine ⟨⟨_, rho⟩, hv, hc, hh, healthy_run_prog S A hp hs _ _, fun Q hQ hc hi hq => ?_⟩
  have hb := Q.bounded
  rw [hc, hi, hQ] at hb
  change _ + ((contract_latency S A .available 1 : Nat) : Time) * 2 ≤ rho.horizon at hb
  rw [contract_latency_available, hhor] at hb
  push_cast at hb
  linarith

/-- (r) The `nonfinal` guard: no `HealthyPreparationQuery` is at `.final`. -/
theorem healthyPreparationQuery_not_final {V : Type} [Fintype V] [DecidableEq V]
    (Q : HealthyPreparationQuery S A V) : Q.cap ≠ .final := by
  rcases Q.nonfinal with h | h <;> rw [h] <;> decide

/-! ## The outage witness of `regimes_realizable` at `K S A` -/

/-- (a) An `OutageQuery` at `K S A`: the outage witness of `Shape.regimes_realizable` for the
Accepted contract on five validators, at `Δ = ΔF = 2`, armed at `T ≥ 0`. -/
theorem outageQuery_witness : ∃ Q : OutageQuery S A (Fin 5), 0 ≤ Q.T := by
  obtain ⟨r, T, b₀, b₁, ⟨⟨hv, hc, -, -⟩, -, -⟩, ho, -, -⟩ :=
    (Shape.regimes_realizable (goldilocks S) (K S A) (accepted_admissible S A)
      (accepted_progressFits S A) (accepted_progressTolerant S A) (Fin 5) (by decide)).outage
      2 2 0 (by decide) (by decide)
  obtain ⟨Q, -, hT, -, -⟩ := outageQuery_applies S A r (by decide) T b₀ b₁ hv hc ho
  exact ⟨Q, hT ▸ Q.outage.1.1⟩

/-- (a) Non-vacuous: `outage_node_lag` on that query, `T + (4k + 6)Δ ≤ b₀`. -/
theorem outageQuery_lag : ∃ Q : OutageQuery S A (Fin 5),
    Q.T + (4 * Q.params.k + 6) * Q.params.Δ ≤ Q.start := by
  obtain ⟨Q, -⟩ := outageQuery_witness S A
  exact ⟨Q, outage_node_lag S A (Fin 5) Q⟩

/-- (r) No outage query starts before the arming lag: every `OutageQuery` has
`(4k + 6)Δ ≤ b₀` (`T ≥ 0`), so a run whose outage starts earlier is the run of none. -/
theorem outageQuery_start_ge {V : Type} [Fintype V] [DecidableEq V] (Q : OutageQuery S A V) :
    (4 * Q.params.k + 6) * Q.params.Δ ≤ Q.start := by
  have h := outage_node_lag S A V Q
  have hT : 0 ≤ Q.T := Q.outage.1.1
  linarith

end Consensus.Goldilocks.Obligations.Test.NonfinalQueryWitness

end
