module
public import ConsensusLeanTest.GoldilocksSleepyWitness
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Accepted
@[expose] public section

/-! # Witness: the final liveness query's hypotheses are jointly satisfiable

Kind (a), joint satisfiability (CONTRIBUTING "Statements"), for the fields of `FinalQuery`, the
hypotheses of `accepted_healthyLive_final`. `FinalQuery` fixes the contract to `K S A`; the
theorem below states the same fields over `acceptanceContract A C` for every coefficient record
`C`. At
`C = accepted_coefficients S A` they are the structure's fields, since `K S A` is that
abbreviation.

* `healthy_run`: the two-validator run of `GoldilocksSleepyWitness` (everyone awake and honest,
  engine `Δ = 1`) is Healthy from GST 0 for every `acceptanceContract A C`.
* `finalQuery_fields`: on that run with horizon `H = heal + latency` (at `.final`, index 1), the
  `FinalQuery` fields hold with GST 0 and query time `heal`: validity, no collision, Healthy,
  final progress (the four-anchor `finalWindow`) on `[ready, H]`, maturity, the latency deadline
  inside the horizon, and a ready reader at the deadline. -/

namespace Consensus.Goldilocks.Refinement.Test.FinalWitness

open Shape Blocks SleepyWitness
open Consensus.Model (pubOf)

variable (S : Setup)

/-- The run of `Shape.coverage` at `point H` is Healthy from GST 0 for every contract
`acceptanceContract A C`. -/
theorem healthy_run (A : AcceptanceAssumptions S) (C : AcceptanceCoefficients) (H : Time)
    (hH : 0 ≤ H) :
    ∃ r : (Sys (family S) (Fin 2)).Run, r.1 = (point H).env ∧ r.2.point = point H ∧
      r.2.sel = sel S H ∧ r.2.key = Equiv.refl _ ∧
      (Sys (family S) (Fin 2)).Valid r ∧ ¬ r.2.HashCollision ∧
      (Sys (family S) (Fin 2)).Healthy (acceptanceContract A C) 0 r := by
  obtain ⟨rho, hp, hk, hs, hv, hc, -, he⟩ := Shape.coverage (family S) (point H) hH
    (by exact Equiv.refl _) (sel S H) (sel_admits S H) 0
  refine ⟨⟨(point H).env, rho⟩, rfl, hp, hs, hk, hv, hc, ?_, ?_, ?_⟩
  · exact (Model.sysOf_delivers_iff rho _ _).mpr (he.psync le_rfl)
  · change ((rho.point.faulty.card : ℚ)) < _ * _
    rw [hp, point_faulty]
    norm_num [Params.standard]
  · exact fun _ _ _ _ _ => rfl

/-- (a) The `FinalQuery` fields, over `acceptanceContract A C`, are jointly satisfiable: index 1,
GST 0, query time `heal`, horizon `heal + latency` (engine `Δ = 1`). -/
theorem finalQuery_fields (A : AcceptanceAssumptions S) (C : AcceptanceCoefficients) :
    ∃ r : (Sys (family S) (Fin 2)).Run, ∃ query : Time, 1 ≤ Fintype.card (Fin 2) ∧
      (Sys (family S) (Fin 2)).Valid r ∧ ¬ r.2.HashCollision ∧
      (Sys (family S) (Fin 2)).Healthy (acceptanceContract A C) 0 r ∧
      (Sys (family S) (Fin 2)).prog (shapeProgress (family S) (Fin 2)) (acceptanceContract A C)
        .final (1 : ℕ+) ((Sys (family S) (Fin 2)).ready (acceptanceContract A C) 0 r)
        r.2.horizon r ∧
      (Sys (family S) (Fin 2)).heal (acceptanceContract A C) .final (1 : ℕ+) 0 r ≤ query ∧
      query + ((acceptanceContract A C).params.latency .final (1 : ℕ+) : Time) * r.1.Δ ≤
        r.2.horizon ∧
      ∃ v, r.2.point.Ready ((Sys (family S) (Fin 2)).cDur (acceptanceContract A C) r) v
        (query + ((acceptanceContract A C).params.latency .final (1 : ℕ+) : Time) * r.1.Δ) := by
  let H : Time := (C.heal .final 1 : Time) + (C.latency .final 1 : Time)
  have hH0 : 0 ≤ H := by positivity
  obtain ⟨⟨E, rho⟩, hE, hp, hs, hk, hv, hc, hhl⟩ := healthy_run S A C H hH0
  subst hE
  have hhor : rho.horizon = H := congrArg EnvPoint.horizon hp
  refine ⟨⟨_, rho⟩, (C.heal .final 1 : Time), one_le_card, hv, hc, hhl, ?_, ?_, ?_, 0, ?_⟩
  · change PatternRecurrence rho.point rho.key (fun s => rho.sel (ShapeRole.proposer s)) _ _ _ _ _
    apply patternRecurrence_of_all
    intro s j _
    rw [hs, hp]
    exact ⟨⟨_, Finset.mem_singleton_self _⟩, fun _ _ => point_ready H _ _ _⟩
  · change max (0 : Time) 0 + (C.heal .final 1 : Time) * 1 ≤ (C.heal .final 1 : Time)
    simp
  · rw [hhor]
    change (C.heal .final 1 : Time) + (C.latency .final 1 : Time) * 1 ≤ H
    rw [mul_one]
  · rw [hp]
    exact point_ready H _ _ _

end Consensus.Goldilocks.Refinement.Test.FinalWitness
