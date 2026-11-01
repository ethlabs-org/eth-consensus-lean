module
public import AvailableChainGeneric.Proofs.Pure.KernelArithmetic
public import AvailableChainFGSARun.Model.Protocol
public import AvailableChainFGSAClaims.Statements.Bounds

public section

namespace AvailableChain.FGSA.Run

open Gen.Pure

/-- fgsa_grid_sa_proposalTime connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_sa_proposalTime (p : SA.Params) (s : Nat) :
    SlotGrid.t p.Δ s = SA.proposalTime p s := by rfl

/-- fgsa_grid_engine_proposalTime connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_engine_proposalTime (p : SA.Params) (s : Nat) :
    SlotGrid.t p.Δ s = GridCO.proposalTime p.engine s := by rfl

/-- fgsa_grid_gridco_proposalTime connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_gridco_proposalTime (p : GridCO.Params) (s : Nat) :
    SlotGrid.t p.Δ s = GridCO.proposalTime p s := by rfl

/-- fgsa_grid_sa_voteTime connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_sa_voteTime (p : SA.Params) (s : Nat) :
    SlotGrid.v p.Δ s = SA.voteTime p s := by rfl

/-- fgsa_grid_engine_voteTime connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_engine_voteTime (p : SA.Params) (s : Nat) :
    SlotGrid.v p.Δ s = GridCO.voteTime p.engine s := by rfl

/-- fgsa_grid_gridco_voteTime connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_gridco_voteTime (p : GridCO.Params) (s : Nat) :
    SlotGrid.v p.Δ s = GridCO.voteTime p s := by rfl

/-- fgsa_grid_sa_releaseTime connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_sa_releaseTime (p : SA.Params) (s : Nat) :
    SlotGrid.q p.Δ s = SA.releaseTime p s := by rfl

/-- fgsa_grid_engine_releaseTime connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_engine_releaseTime (p : SA.Params) (s : Nat) :
    SlotGrid.q p.Δ s = GridCO.releaseTime p.engine s := by rfl

/-- fgsa_grid_gridco_releaseTime connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_gridco_releaseTime (p : GridCO.Params) (s : Nat) :
    SlotGrid.q p.Δ s = GridCO.releaseTime p s := by rfl

/-- fgsa_grid_sa_earlyTime connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_sa_earlyTime (p : SA.Params) (s : Nat) :
    SlotGrid.e p.Δ s = SA.earlyTime p s := by rfl

/-- fgsa_grid_engine_earlyTime connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_engine_earlyTime (p : SA.Params) (s : Nat) :
    SlotGrid.e p.Δ s = GridCO.earlyTime p.engine s := by rfl

/-- fgsa_grid_gridco_earlyTime connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_gridco_earlyTime (p : GridCO.Params) (s : Nat) :
    SlotGrid.e p.Δ s = GridCO.earlyTime p s := by rfl

/-- fgsa_grid_sa_freezeTime connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_sa_freezeTime (p : SA.Params) (s : Nat) :
    SlotGrid.z p.Δ s = SA.freezeTime p s := by rfl

/-- fgsa_grid_engine_freezeTime connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_engine_freezeTime (p : SA.Params) (s : Nat) :
    SlotGrid.z p.Δ s = GridCO.freezeTime p.engine s := by rfl

/-- fgsa_grid_gridco_freezeTime connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_gridco_freezeTime (p : GridCO.Params) (s : Nat) :
    SlotGrid.z p.Δ s = GridCO.freezeTime p s := by rfl

/-- fgsa_grid_sa_gateTime connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_sa_gateTime (p : SA.Params) (s : Nat) :
    SlotGrid.d p.Δ s = SA.gateTime p s := by rfl

/-- fgsa_grid_engine_gateTime connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_engine_gateTime (p : SA.Params) (s : Nat) :
    SlotGrid.d p.Δ s = GridCO.gateTime p.engine s := by rfl

/-- fgsa_grid_gridco_gateTime connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_gridco_gateTime (p : GridCO.Params) (s : Nat) :
    SlotGrid.d p.Δ s = GridCO.gateTime p s := by rfl

/-- fgsa_grid_sa_lifetime connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_sa_lifetime (p : SA.Params) :
    SlotGrid.L p.Δ p.k = SA.lifetime p := by rfl

/-- fgsa_grid_engine_lifetime connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_engine_lifetime (p : SA.Params) :
    SlotGrid.L p.Δ p.k = GridCO.lifetime p.engine := by rfl

/-- fgsa_grid_gridco_lifetime connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_gridco_lifetime (p : GridCO.Params) :
    SlotGrid.L p.Δ p.m = GridCO.lifetime p := by rfl

/-- fgsa_grid_period connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_period (p : Params) :
    SlotGrid.P p.Δ p.R = P p := by rfl

/-- fgsa_grid_lease connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_lease (p : Params) :
    SlotGrid.L p.Δ p.k = L p := by rfl

/-- fgsa_grid_opening connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_opening (p : Params) (r : Nat) :
    SlotGrid.T p.Δ p.R r = SA.proposalTime p.toParams (r * p.R) := by rfl

/-- fgsa_grid_action_time connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_action_time (p : Params) (r : Nat) :
    SlotGrid.a p.Δ p.R r = p.actionTime r := by rfl

/-- fgsa_grid_action_gate connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_action_gate (p : Params) (r : Nat) :
    SlotGrid.a p.Δ p.R r = SA.gateTime p.toParams (r * p.R) := by rfl

/-- fgsa_grid_proposal_duty connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_proposal_duty (p : Params) (s : Nat) :
    SlotGrid.t p.Δ s = RunDuty.actTime p (.propAction s) := by rfl

/-- fgsa_grid_head_duty connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_head_duty (p : Params) (s : Nat) :
    SlotGrid.v p.Δ s = RunDuty.actTime p (.headAction s) := by rfl

/-- fgsa_grid_action_duty connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_action_duty (p : Params) (r : Nat) :
    SlotGrid.a p.Δ p.R r = RunDuty.actTime p (.fgAction r) := by rfl

/-- fgsa_grid_run_head_duty connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_run_head_duty (p : Params) (s : Nat) :
    SlotGrid.v p.Δ s = RunDuty.actTime p (.headAction s) := by rfl

/-- fgsa_grid_run_action_duty connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_run_action_duty (p : Params) (r : Nat) :
    SlotGrid.a p.Δ p.R r = RunDuty.actTime p (.fgAction r) := by rfl

/-- fgsa_grid_round_period connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_round_period (p : Params) (r : Nat) :
    SlotGrid.T p.Δ p.R r = (r : Time) * P p := by
  rw [SlotGrid.T_def, SlotGrid.t_def, slotLen_def]
  change 4 * p.Δ * ((r * p.R : Nat) : Time) =
    (r : Time) * (4 * (p.R : Time) * p.Δ)
  push_cast
  ring

/-- fgsa_grid_carrier_time2 connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_carrier_time2 (p : Params) (r : Nat) :
    SlotGrid.t p.Δ (r * p.R + 2) = carrierTime2 p r := by
  rw [SlotGrid.t_def, slotLen_def]
  change 4 * p.Δ * ((r * p.R + 2 : Nat) : Time) =
    (r : Time) * (4 * (p.R : Time) * p.Δ) + 8 * p.Δ
  push_cast
  ring

/-- fgsa_grid_kernel_deadline connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_kernel_deadline (p : Params) (r : Nat) :
    SlotGrid.T p.Δ p.R r + 9 * p.Δ = kernelDeadline p r := by
  rw [fgsa_grid_round_period]
  rfl

/-- fgsa_grid_kernel_before_next_action connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_kernel_before_next_action (p : Params) (r : Nat) :
    KernelBeforeNextAction p r := by
  change kernelDeadline p r < p.actionTime (r + 1)
  rw [← fgsa_grid_kernel_deadline, ← fgsa_grid_action_time]
  exact (kernel_arith p.Δ p.R r r p.deltaPos p.RLarge).1

/-- fgsa_grid_vote_before_action connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_vote_before_action (p : Params) (q : Nat) :
    VoteBeforeAction p q := by
  change SA.voteTime p.toParams (q * p.R + 1) < p.actionTime q
  simpa only [fgsa_grid_sa_voteTime, fgsa_grid_action_time] using
    (kernel_arith p.Δ p.R q q p.deltaPos p.RLarge).2.1

/-- fgsa_grid_gate_after_carrier2 connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_gate_after_carrier2 (p : Params) (q : Nat) :
    GateAfterCarrier2 p q := by
  change carrierTime2 p q < SA.gateTime p.toParams (q * p.R + 1)
  simpa only [fgsa_grid_carrier_time2, fgsa_grid_sa_gateTime] using
    (kernel_arith p.Δ p.R q q p.deltaPos p.RLarge).2.2.1

/-- fgsa_grid_action_delivery_bounds connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_action_delivery_bounds (p : Params) (r : Nat) :
    ActionDeliveryBounds p r := by
  have hc := action_carrier_arithmetic p.Δ p.R r p.deltaPos p.RLarge
  have hk := kernel_arith p.Δ p.R r r p.deltaPos p.RLarge
  change p.actionTime r + p.Δ = (r : Time) * P p + 7 * p.Δ ∧
    p.actionTime r + p.Δ < carrierTime2 p r ∧
    p.actionTime r + p.Δ < ((r : Time) + 1) * P p
  refine ⟨?_, ?_, ?_⟩
  · simpa only [fgsa_grid_action_time, fgsa_grid_round_period] using hc.1
  · change p.actionTime r + p.Δ < (r : Time) * P p + 8 * p.Δ
    simpa only [fgsa_grid_action_time, fgsa_grid_round_period] using hk.2.2.2
  · simpa only [fgsa_grid_action_time, fgsa_grid_round_period,
      Nat.cast_add, Nat.cast_one] using hc.2.2

/-- fgsa_grid_gate_action_order connects the scalar grid to the lane clock.
Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem fgsa_grid_gate_action_order (p : Params) (r c : Nat) :
    GateActionOrder p r c := by
  constructor
  · intro hc
    change SlotGrid.d p.Δ c ≤ SlotGrid.d p.Δ ((r + 2) * p.R)
    exact (grid_offset_order p.Δ (6 * p.Δ) c ((r + 2) * p.R) p.deltaPos).1.mpr hc
  · intro hc
    subst c
    change SlotGrid.d p.Δ ((r + 2) * p.R) < SlotGrid.d p.Δ ((r + 2) * p.R + 1)
    exact (grid_offset_order p.Δ (6 * p.Δ) ((r + 2) * p.R)
      ((r + 2) * p.R + 1) p.deltaPos).2.mpr (by omega)

end AvailableChain.FGSA.Run
