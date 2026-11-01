module
public import AvailableChainSA.Proofs.RecoverySupport
public import AvailableChainGridCO.Proofs.Recovery

@[expose] public section
namespace AvailableChain.SA
open AvailableChain.Generic AvailableChain.Statements.Generic
local instance saRecoveryLeasePolicy : GridCO.LeasePolicy := GridCO.slowLeasePolicy

/-- The SA recovery threshold is exactly the current honest majority. -/
theorem synchronousLabel_of_recovery {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sa p)) (G : Time)
    (hrec : RecoveryRegime (sa p) E (saInterface p) (saConstants p G) rho)
    (r : Slot) (hstart : E.t_GST ≤ proposalTime p r)
    (hh : gateTime p r ≤ rho.horizon) : GridCO.SynchronousLabel p.engine E rho r := by
  have hvstart : E.t_GST ≤ voteTime p r := by
    change E.t_GST ≤ proposalTime p r + p.Δ
    linarith [p.deltaPos]
  have hvend : voteTime p r ≤ rho.horizon := by
    change proposalTime p r + p.Δ ≤ rho.horizon
    change proposalTime p r + 6 * p.Δ ≤ rho.horizon at hh
    linarith [p.deltaPos]
  have hm := hrec.participation _ hvstart hvend
  change (1 / 2 : ℚ) * ((awakeAt E rho.honest (voteTime p r)).card + (faulty rho).card) <
    ((awakeAt E rho.honest (voteTime p r)).card : ℚ) at hm
  have hmaj : AwakeMajority E rho (voteTime p r) := by
    have hq : ((faulty rho).card : ℚ) < ((awakeAt E rho.honest (voteTime p r)).card : ℚ) := by
      linarith
    exact_mod_cast hq
  exact ⟨hrec.execution, hmaj, hh, Or.inl ⟨hstart, hrec.partialSynchrony⟩⟩

/-- SA recovers within 2L+G+8Δ with θrec = 1/2 and without full
participation. The source invariant survives release of its own lease. -/
theorem recovered_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sa p)) (hΔ : E.Δ = p.Δ) (G : Time)
    (hrec : RecoveryRegime (sa p) E (saInterface p) (saConstants p G) rho) :
    RecoveredAt (sa p) E (saInterface p) (saConstants p G) rho
      (E.t_GST + (saConstants p G).recoveryBound) := by
  obtain ⟨b, hbpos, hbstart, hbtime⟩ :=
    GridCO.exists_recovery_start p.engine E.t_GST E.t_GST_nonneg
  let finish := recoveryBoundary p b
  have hbfinish : b ≤ finish := Nat.le_add_right _ _
  have hseq : ∀ t, b ≤ t → gateTime p t ≤ rho.horizon →
      GridCO.SynchronousLabel p.engine E rho t := by
    intro t hbt hh
    exact synchronousLabel_of_recovery p E rho G hrec t
      (hbstart.le.trans ((GridCO.proposalTime_le_iff p.engine b t).mpr hbt)) hh
  have hsources := admitted_sources_after_two_leases p E rho hΔ b hseq
  have hrows := rows_supported_of_sources p E rho hrec.execution finish hsources
  apply GridCO.recovered_of_source_boundary p.engine E rho hΔ (saConstants p G) rfl rfl hrec
    finish (hbpos.trans_le hbfinish)
    (hbstart.le.trans ((GridCO.proposalTime_le_iff p.engine b finish).mpr hbfinish))
    (fun t hft hh => hseq t (hbfinish.trans hft) hh) hrows hsources
  change proposalTime p (recoveryBoundary p b) + G + 6 * p.Δ ≤
    E.t_GST + (2 * lifetime p + G + 8 * p.Δ)
  rw [recoveryBoundary_time]
  change proposalTime p b ≤ E.t_GST + 4 * p.Δ at hbtime
  linarith

end AvailableChain.SA
end
