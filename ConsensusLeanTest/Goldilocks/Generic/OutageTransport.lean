module
public import ConsensusLean.Proofs.RegimesRealizable.Main
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.OutageSupply
import ConsensusLean.Lemmas.Tactic.Linarith
@[expose] public section

/-! # Witness: the L9 endpoint and participation premises on a valid outage run

Kind (a), joint satisfiability, for the environmental part of the local premises of L9
(`ACCorrectLocal.outageProtected`, `OutageReadPoint.protection`): an endpoint and participation
witness. `outage_witness` at `goldilocksContract` gives a valid run of `goldilocks S` in `Outage`
with a ready source at `T` and a ready reader at a destination time `t` in `[recoveryAt, horizon]`
(`OutageActive`), on which the participation premises hold at the contract's look-back `η·ΔAC`
(`OutageTransport.participation_of_outage`): population and look-back committee η-sleepy
participation with the outage catch-up `max cDur (η·ΔAC − 1)`. The local trace premises
(`Growing.LocalRun`, `RunPointBinding`, `NoCollRun`, the read point) are not constructed here. -/

namespace Consensus.Goldilocks.Generic.Test.OutageTransport
open AsChainShape Shape Obligations

/-- An environmental endpoint and participation witness for L9, on `outage_witness` at
`goldilocksContract` (coefficients `contract_coefficients S A`): a valid run with a ready source at
the arming time `T`, a ready reader at a destination time `t` in `[recoveryAt, horizon]`, and the
participation premises of L9 at the contract's look-back, through
`OutageTransport.participation_of_outage`. -/
theorem outage_witness_l9_premises (S : Setup) (A : ContractAssumptions S) :
    let Y := Sys (goldilocks S) (Fin 5)
    let X := (shapeProgress (goldilocks S) (Fin 5)).toExternal
    let K := goldilocksContract A (contract_coefficients S A)
    ∃ (r : Y.Run) (T b₀ b₁ t : Time) (u w : Fin 5),
      Y.Valid r ∧ Y.Outage X K T b₀ b₁ r ∧ Y.recoveryAt K b₁ r ≤ t ∧ t ≤ (Y.pt r).horizon ∧
      (Y.pt r).Ready (Y.cDur K r) u T ∧ (Y.pt r).Ready (Y.cDur K r) w t ∧
      0 ≤ T ∧ T ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ Y.recoveryAt K b₁ r ∧
      (Y.pt r).EtaSleepyOn (1 / 2) ((K.params.η : Time) * (Y.pt r).env.ΔAC)
        (max (Y.cDur K r) ((K.params.η : Time) * (Y.pt r).env.ΔAC - 1))
        (Y.aheadDur K r) 0 (Y.pt r).horizon ∧
      ∀ δ, 0 ≤ δ → δ ≤ (K.params.η : Time) * (Y.pt r).env.ΔAC →
        (Y.pt r).CommitteeSleepyOn
          (fun t => X.selected (Y.pt r).env (X.ext r) (max 0 (t - δ))) (1 / 2)
          ((K.params.η : Time) * (Y.pt r).env.ΔAC)
          (max (Y.cDur K r) ((K.params.η : Time) * (Y.pt r).env.ΔAC - 1))
          (Y.committeeAheadDur K r) 0 (Y.pt r).horizon := by
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
  have hΔ : (Y.pt ⟨_, rho⟩).env.ΔAC = 2 := by
    change rho.point.env.ΔAC = 2
    rw [hp, realPoint_env]
  have hrec : Y.recoveryAt K b₁ ⟨_, rho⟩ = H := by
    simp only [System.recoveryAt, hΔ, H]
  obtain ⟨hη, hcs⟩ := OutageTransport.participation_of_outage K rfl hwit.1 0 b₀ b₁ ho
  refine ⟨⟨_, rho⟩, 0, b₀, b₁, t, u, w, hwit.1, ho, hrec.le.trans hwt, htH, hu, hw, le_rfl,
    by simp only [b₀]; linarith, by simp only [b₁]; linarith,
    by rw [hrec]; simp only [H]; linarith, hη, hcs⟩

end Consensus.Goldilocks.Generic.Test.OutageTransport

end
