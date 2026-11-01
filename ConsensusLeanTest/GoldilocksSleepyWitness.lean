module
public import ConsensusLeanTest.GoldilocksRefinement
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.NonfinalEndpoints
@[expose] public section

/-! # Witnesses: the Sleepy leaves' hypotheses are jointly satisfiable

Kind (a), joint satisfiability (CONTRIBUTING "Statements"), for the hypotheses of
`sleepy_safety_inputs` (`SleepySafetyQuery`) and of `sleepy_query_sync` (`ConfirmedQuery`,
Sleepy branch). Both structures fix the contract to `K S A`, whose heal coefficient
`accepted_heal` is still open, so a test cannot build them. The theorems below state the same
fields over `acceptanceContract A C` for every coefficient record `C`; at
`C = accepted_coefficients S A` they are the structures' fields, since `K S A` is that
abbreviation.

* `sleepySafety_fields`: a valid, collision-free Sleepy run of `family S` on two validators,
  with any horizon `H ≥ 0`.
* `sleepyQuery_fields`: the same run with Sleepy progress at `.available`, index 1, on
  `[0, H]`, query time 0, the latency deadline inside the horizon, and a ready reader at the
  deadline, for every `H ≥ latency`. -/

namespace Consensus.Goldilocks.Refinement.Test.SleepyWitness

open Shape Blocks
open Consensus.Model (pubOf)

/-- Two validators, always awake and honest, engine `Δ = 1`, horizon `H`, no submissions. -/
def point (H : Time) : EnvPoint (Fin 2) :=
  ⟨⟨1, by decide, fun _ _ => true⟩, Finset.univ, H, fun _ _ => []⟩

theorem one_le_card : 1 ≤ Fintype.card (Fin 2) := by decide

variable (S : Setup)

/-- Validator `0` proposes every slot; everyone polls. -/
def sel (H : Time) :
    (Model.protoOf (compiled (family S)) (point H).env).Role → Finset (Fin (Fintype.card (Fin 2)))
  | .proposer _ => {⟨0, one_le_card⟩}
  | .duty _ k => k.elim
  | .poll => Finset.univ

theorem sel_admits (H : Time) :
    (Model.protoOf (compiled (family S)) (point H).env).SelAdmits (sel S H) := by
  intro r
  cases r with
  | proposer s =>
    change ((family S (pubOf (point H).env)).skel.proposerSel s).Admits _
    rw [Test.skeleton_proposerSel S s]
    change ({(⟨0, one_le_card⟩ : Fin (Fintype.card (Fin 2)))} : Finset _).card =
      min 1 (Fintype.card (Fin 2))
    simp
  | duty _ k => exact k.elim
  | poll => rfl

/-- Every validator is ready at every time and duration. -/
theorem point_ready (H c t : Time) (v : Fin 2) : (point H).Ready c v t :=
  ⟨Finset.mem_univ _, fun _ _ _ => rfl⟩

theorem point_readyAt (H c t : Time) : (point H).readyAt c t = Finset.univ := by
  ext v
  simp only [EnvPoint.readyAt, Finset.mem_filter, Finset.mem_univ, iff_true]
  exact ⟨Finset.mem_univ v, point_ready H c t v⟩

theorem point_faulty (H : Time) : (point H).faulty = ∅ := by
  simp [EnvPoint.faulty, point]

/-- The run of `Shape.coverage` at `point H`: valid, collision-free and Sleepy for every contract
`acceptanceContract A C`. -/
theorem sleepy_run (A : AcceptanceAssumptions S) (C : AcceptanceCoefficients) (H : Time)
    (hH : 0 ≤ H) :
    ∃ r : (Sys (family S) (Fin 2)).Run, r.1 = (point H).env ∧ r.2.point = point H ∧
      r.2.sel = sel S H ∧ r.2.key = Equiv.refl _ ∧
      (Sys (family S) (Fin 2)).Valid r ∧ ¬ r.2.HashCollision ∧
      (Sys (family S) (Fin 2)).Sleepy (acceptanceContract A C) r := by
  obtain ⟨rho, hp, hk, hs, hv, hc, -, he⟩ := Shape.coverage (family S) (point H) hH
    (by exact Equiv.refl _) (sel S H) (sel_admits S H) 0
  refine ⟨⟨(point H).env, rho⟩, rfl, hp, hs, hk, hv, hc, ?_, ?_⟩
  · exact (Model.sysOf_delivers_iff rho _ _).mpr (he.psync le_rfl)
  · intro t _ _
    change rho.point.ReadyAbove (1 / 2) _ t
    unfold EnvPoint.ReadyAbove
    rw [hp, point_readyAt, point_faulty]
    norm_num

/-- (a) The `SleepySafetyQuery` fields, over `acceptanceContract A C`, are jointly satisfiable at
every horizon `H ≥ 0`. -/
theorem sleepySafety_fields (A : AcceptanceAssumptions S) (C : AcceptanceCoefficients)
    (H : Time) (hH : 0 ≤ H) :
    ∃ r : (Sys (family S) (Fin 2)).Run, 1 ≤ Fintype.card (Fin 2) ∧ r.2.horizon = H ∧
      (Sys (family S) (Fin 2)).Valid r ∧ ¬ r.2.HashCollision ∧
      (Sys (family S) (Fin 2)).Sleepy (acceptanceContract A C) r := by
  obtain ⟨r, -, hp, -, -, hv, hc, hs⟩ := sleepy_run S A C H hH
  exact ⟨r, one_le_card, congrArg EnvPoint.horizon hp, hv, hc, hs⟩

/-- (a) The `ConfirmedQuery` fields on the Sleepy branch, over `acceptanceContract A C`, are jointly
satisfiable: capability `.available`, index 1, query time 0, at every horizon covering the latency
deadline (`Δ = 1`). -/
theorem sleepyQuery_fields (A : AcceptanceAssumptions S) (C : AcceptanceCoefficients)
    (H : Time) (hH : (C.latency .available 1 : Time) ≤ H) :
    ∃ r : (Sys (family S) (Fin 2)).Run, 1 ≤ Fintype.card (Fin 2) ∧ r.2.horizon = H ∧
      (Sys (family S) (Fin 2)).Valid r ∧ ¬ r.2.HashCollision ∧
      ((Sys (family S) (Fin 2)).Sleepy (acceptanceContract A C) r ∧
        (Sys (family S) (Fin 2)).prog (shapeProgress (family S) (Fin 2)) (acceptanceContract A C)
          .available (1 : ℕ+) 0 r.2.horizon r ∧ (0 : Time) ≤ 0) ∧
      (0 : Time) + ((acceptanceContract A C).params.latency .available (1 : ℕ+) : Time) * r.1.Δ ≤
        r.2.horizon ∧
      ∃ v, r.2.point.Ready ((Sys (family S) (Fin 2)).cDur (acceptanceContract A C) r) v
        ((0 : Time) + ((acceptanceContract A C).params.latency .available (1 : ℕ+) : Time) *
          r.1.Δ) := by
  have hH0 : 0 ≤ H := le_trans (Int.natCast_nonneg _) hH
  obtain ⟨⟨E, rho⟩, hE, hp, hs, hk, hv, hc, hsl⟩ := sleepy_run S A C H hH0
  subst hE
  have hhor : rho.horizon = H := congrArg EnvPoint.horizon hp
  refine ⟨⟨_, rho⟩, one_le_card, hhor, hv, hc, ⟨hsl, ?_, le_rfl⟩, ?_, 0, ?_⟩
  · change PatternRecurrence rho.point rho.key (fun s => rho.sel (ShapeRole.proposer s)) _ _ _ _ _
    apply patternRecurrence_of_all
    intro s j _
    rw [hs, hp]
    exact ⟨⟨_, Finset.mem_singleton_self _⟩, fun _ _ => point_ready H _ _ _⟩
  · rw [hhor]
    change (0 : Time) + (C.latency .available 1 : Time) * 1 ≤ H
    rw [zero_add, mul_one]
    exact hH
  · rw [hp]
    exact point_ready H _ _ _

end Consensus.Goldilocks.Refinement.Test.SleepyWitness
