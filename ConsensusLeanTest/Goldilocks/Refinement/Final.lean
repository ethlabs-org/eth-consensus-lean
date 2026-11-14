module
public import ConsensusLeanTest.Goldilocks.Refinement.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Concrete.Final
@[expose] public section

/-! # Witness: the final liveness query's hypotheses are jointly satisfiable

Kind (a), joint satisfiability (CONTRIBUTING "Statements"), for the fields of the final liveness
query, the hypotheses of `Growing.meetsObligations_healthyLive_final_growing`, stated over
`goldilocksContract A C` for every coefficient record `C` (at `C = contract_coefficients S A`,
the contract `K S A`).

* `healthy_run`: the two-validator run of `Goldilocks/Refinement/Sleepy` (everyone awake and honest,
  engine `Δ = 2`) is Healthy from GST 0 for every `goldilocksContract A C`.
* `finalQuery_fields`: on that run with horizon `H = (heal + latency)·Δ` (at `.final`, index 1),
  the final query's fields hold with GST 0 and query time `heal·Δ`: validity, no collision, Healthy,
  final progress (the four-anchor `finalWindow`) on `[ready, H]`, maturity, the latency deadline
  inside the horizon, and a ready reader at the deadline. -/

namespace Consensus.Goldilocks.Obligations.Test.FinalWitness
open AsChainShape Simulation

open Shape Blocks SleepyWitness
open Consensus.Model (pubOf)

variable (S : Setup)

/-- The run of `Shape.coverage` at `point H` is Healthy from GST 0 for every contract
`goldilocksContract A C`. -/
theorem healthy_run (A : ContractAssumptions S) (C : ContractCoefficients) (H : Time)
    (hH : 0 ≤ H) :
    ∃ r : (Sys (goldilocks S) (Fin 2)).Run, r.1 = (point H).env ∧ r.2.point = point H ∧
      r.2.sel = sel S H ∧ r.2.key = Equiv.refl _ ∧
      (Sys (goldilocks S) (Fin 2)).Valid r ∧ ¬ r.2.HashCollision ∧
      (Sys (goldilocks S) (Fin 2)).Healthy (goldilocksContract A C) 0 r := by
  obtain ⟨rho, hp, hk, hs, hv, hc, -, he⟩ := Shape.coverage (goldilocks S) (point H) hH
    (by exact Equiv.refl _) (sel S H) (sel_admits S H) 0
  refine ⟨⟨(point H).env, rho⟩, rfl, hp, hs, hk, hv, hc, ?_, ⟨?_, ?_⟩, ?_⟩
  · exact (Model.sysOf_delivers_iff rho _ _ _).mpr
      (he.psync le_rfl (show (1 : Time) < 2 by decide) (show (1 : Time) < 2 by decide))
  · change ((rho.point.faultyAt rho.point.horizon).card : ℚ) < _ * _
    rw [hp, point_faulty]
    norm_num [Params.standard]
  · exact fun _ _ _ _ _ => rfl
  · exact le_mul_of_one_le_left zero_le_two
      (by exact_mod_cast (goldilocksContract A C).params.fgDelay.pos)

/-- (a) The final query's fields, over `goldilocksContract A C`, are jointly satisfiable: index 1,
GST 0, query time `heal·Δ`, horizon `(heal + latency)·Δ` (engine `Δ = 2`). -/
theorem finalQuery_fields (A : ContractAssumptions S) (C : ContractCoefficients) :
    ∃ r : (Sys (goldilocks S) (Fin 2)).Run, ∃ query : Time, 1 ≤ Fintype.card (Fin 2) ∧
      (Sys (goldilocks S) (Fin 2)).Valid r ∧ ¬ r.2.HashCollision ∧
      (Sys (goldilocks S) (Fin 2)).Healthy (goldilocksContract A C) 0 r ∧
      (Sys (goldilocks S) (Fin 2)).prog (shapeProgress (goldilocks S) (Fin 2))
          (goldilocksContract A C)
        .final (1 : ℕ+) ((Sys (goldilocks S) (Fin 2)).ready (goldilocksContract A C) 0 r)
        r.2.horizon r ∧
      (Sys (goldilocks S) (Fin 2)).heal (goldilocksContract A C) .final (1 : ℕ+) 0 r ≤ query ∧
      query + ((goldilocksContract A C).params.latency .final (1 : ℕ+) : Time) * r.1.ΔAC ≤
        r.2.horizon ∧
      ∃ v, r.2.point.Ready ((Sys (goldilocks S) (Fin 2)).cDur (goldilocksContract A C) r) v
        (query + ((goldilocksContract A C).params.latency .final (1 : ℕ+) : Time) * r.1.ΔAC) := by
  let H : Time := (C.heal .final 1 : Time) * 2 + (C.latency .final 1 : Time) * 2
  have hH0 : 0 ≤ H := by positivity
  obtain ⟨⟨E, rho⟩, hE, hp, hs, hk, hv, hc, hhl⟩ := healthy_run S A C H hH0
  subst hE
  have hhor : rho.horizon = H := congrArg EnvPoint.horizon hp
  refine ⟨⟨_, rho⟩, (C.heal .final 1 : Time) * 2, one_le_card, hv, hc, hhl, ?_, ?_, ?_, 0, ?_⟩
  · change PatternRecurrence rho.point rho.key (fun s => rho.sel (ShapeRole.proposer s)) _ _ _ _ _
    apply patternRecurrence_of_all
    intro s j _
    rw [hs, hp]
    exact ⟨⟨_, Finset.mem_singleton_self _⟩, fun _ _ =>
      ⟨point_ready H _ _ _, by simp [EnvPoint.HonestAt, point]⟩⟩
  · change max (0 : Time) 0 + (C.heal .final 1 : Time) * 2 ≤ (C.heal .final 1 : Time) * 2
    simp
  · rw [hhor]
    change (C.heal .final 1 : Time) * 2 + (C.latency .final 1 : Time) * 2 ≤ H
    exact le_rfl
  · rw [hp]
    exact point_ready H _ _ _

end Consensus.Goldilocks.Obligations.Test.FinalWitness
