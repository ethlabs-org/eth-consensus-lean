module
public import ConsensusLean.Proofs.RegimesRealizable.Main
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.Concrete
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.OutageSupply
import ConsensusLean.Lemmas.Tactic.Linarith
@[expose] public section

/-! # Witness: the L9 endpoint and participation premises on a valid outage run

Kind (a), joint satisfiability, for the environmental part of the local premises of L9
(`ACCorrectLocal.outageProtected`, `OutageReadPoint.protection`): an endpoint and participation
witness. `outage_witness` at `goldilocksContract` gives a valid run of `goldilocks S` in `Outage`
with a ready source at `T` and a ready reader at a destination time `t` in `[recoveryAt, horizon]`
(`OutageActive`), on which the participation premises hold at the `System.Outage` endpoints
(`OutageTransport.participation_of_outage`): `a = outageStart`, `z = outageEnd`,
`retention = cohortAt`, the band ends `bandStart`/`bandEnd`, with `a ≤ b₀` and `b₁ ≤ z`. The local
trace premises (`Growing.LocalRun`, `RunPointBinding`, `NoCollRun`, the read point) are not
constructed here. -/

namespace Consensus.Goldilocks.Generic.Test.OutageTransport
open AsChainShape Shape Obligations

/-- An environmental endpoint and participation witness for L9, on `outage_witness` at
`goldilocksContract` (coefficients `contract_coefficients S A`): a valid run with a ready source at
the arming time `T`, a ready reader at a destination time `t` in `[recoveryAt, horizon]`, and the
participation premises of L9 at the `System.Outage` endpoints, through
`OutageTransport.participation_of_outage`. -/
theorem outage_witness_l9_premises (S : Setup) (A : ContractAssumptions S) :
    let Y := Sys (goldilocks S) (Fin 5)
    let X := (shapeProgress (goldilocks S) (Fin 5)).toExternal
    let K := goldilocksContract A (contract_coefficients S A)
    ∃ (r : Y.Run) (T b₀ b₁ t : Time) (u w : Fin 5),
      Y.Valid r ∧ Y.Outage X K T b₀ b₁ r ∧ Y.recoveryAt K b₁ r ≤ t ∧ t ≤ (Y.pt r).horizon ∧
      (Y.pt r).Ready (Y.cDur K r) u T ∧ (Y.pt r).Ready (Y.cDur K r) w t ∧
      0 ≤ T ∧ T ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ Y.recoveryAt K b₁ r ∧
      (Y.pt r).EtaSleepyOn (1 / 2) ((K.params.η : Time) * (Y.pt r).env.ΔAC) (Y.cDur K r)
        (Y.aheadDur K r) 0 (Y.pt r).horizon ∧
      ((Y.pt r).retain (Y.cohortAt K b₁ r)).NoSleepOn (Y.outageStart K b₀ r)
        (Y.outageEnd K b₁ r) ∧
      ((Y.pt r).retain (Y.cohortAt K b₁ r)).CohortOn (Y.outageStart K b₀ r)
        (Y.outageEnd K b₁ r) ∧
      (Y.pt r).CommitteeSleepyOn (X.selected (Y.pt r).env (X.ext r)) (1 / 2)
        ((K.params.η : Time) * (Y.pt r).env.ΔAC) (Y.cDur K r) (Y.committeeAheadDur K r)
        0 (Y.pt r).horizon ∧
      ((Y.pt r).retain (Y.cohortAt K b₁ r)).CommitteeCohortOn
        (X.selected (Y.pt r).env (X.ext r)) (Y.outageStart K b₀ r) (Y.outageEnd K b₁ r)
        (Y.bandStart K b₀ r) (Y.bandEnd K b₀ r) ∧
      Y.outageStart K b₀ r ≤ b₀ ∧ b₁ ≤ Y.outageEnd K b₁ r := by
  intro Y X K
  have ha := meetsObligations_admissible S A
  have hk := S.two_le_k
  let key : Fin (Fintype.card (Fin 5)) ≃ Fin 5 := finCongr (Fintype.card_fin 5)
  have hn : 5 ≤ Fintype.card (Fin 5) := by simp
  have hl : (0 : Time) ≤ (K.params.lag : Time) * 2 := by positivity
  have hr : (0 : Time) ≤ (K.params.recovery : Time) * 2 := by positivity
  let b₀ : Time := (K.params.lag : Time) * 2 + 1
  let b₁ : Time := b₀ + 2
  let H : Time := b₁ + (K.params.recovery : Time) * 2
  have hT : OutageTimes K.params 2 0 b₀ b₁ := by
    refine ⟨le_rfl, by simp [b₀], by simp [b₁], ?_⟩
    have : (3 : Time) ≤ (K.params.budget : Time) := by
      change (3 : Time) ≤ ((4 * S.k - 5 : Nat) : Time)
      have : 3 ≤ 4 * S.k - 5 := by omega
      exact_mod_cast this
    simp only [b₁]; linarith
  obtain ⟨rho, hp, hwit, ho, hact⟩ := outage_witness (F := goldilocks S) key hn (Δ := 2)
    (by decide) (ΔF := 2) (by decide) H ha (by decide) (by decide) hT (by simp [b₀]; positivity)
    (by simp [b₁]) le_rfl
  obtain ⟨-, -, -, ⟨u, hu⟩, -, w, t, hwt, htH, hw⟩ := hact
  have hH : (Y.pt ⟨_, rho⟩).horizon = H := by
    change rho.point.horizon = H
    rw [hp, realPoint_horizon]
  have hΔ : (Y.pt ⟨_, rho⟩).env.ΔAC = 2 := by
    change rho.point.env.ΔAC = 2
    rw [hp, realPoint_env]
  have hrec : Y.recoveryAt K b₁ ⟨_, rho⟩ = H := by
    simp only [System.recoveryAt, hΔ, H]
  have hnS : (0 : Time) ≤ (K.params.noSleep : Time) * 2 := by positivity
  obtain ⟨hη, hns, hco, hcs, hcc⟩ :=
    OutageTransport.participation_of_outage K rfl hwit.1 0 b₀ b₁ ho
  refine ⟨⟨_, rho⟩, 0, b₀, b₁, t, u, w, hwit.1, ho, hrec.le.trans hwt, htH, hu, hw, le_rfl,
    by simp only [b₀]; linarith, by simp only [b₁]; linarith,
    by rw [hrec]; simp only [H]; linarith, hη, hns, hco, hcs, hcc, ?_, ?_⟩
  · simp only [System.outageStart, hΔ]
    exact min_le_of_left_le (max_le (by simp only [b₀]; linarith) (by linarith))
  · simp only [System.outageEnd, hΔ, hH]
    exact le_min (by linarith) (by simp only [H]; linarith)

end Consensus.Goldilocks.Generic.Test.OutageTransport

end
