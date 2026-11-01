module
public import AvailableChainSAPC.Proofs.RecoveryPremise
public import AvailableChainSAPC.Proofs.Preservation

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- Every awake honest seat enters the actual late denominator. The duty
may be the first synchronous HEAD; no earlier proposal is required. -/
theorem awake_batch_late_count {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (net : PartialSynchrony (sapc p) E rho)
    (relay : AcceptedObjectRelay (sapc p) E rho) (r : Slot)
    (sync : E.t_GST ≤ voteTime p r) (horizon : earlyTime p r ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) :
    (awakeAt E rho.honest (voteTime p r)).card ≤ GridCO.voterCount (GridCO.lateVotes p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r) := by
  rw [← GridCO.lateSeats_card]
  apply Finset.card_le_card_of_injOn (rho.seatOf r).symm
  · intro u hu
    obtain ⟨honest, awake⟩ := Finset.mem_filter.mp hu
    have early := synchronous_head_in_earlyVotes p E rho hx hΔ net relay r sync horizon
      u v honest hv awake
    exact List.mem_toFinset.mpr (List.mem_dedup.mpr (List.mem_filterMap.mpr
      ⟨_, GridCO.earlyVotes_subset_lateVotes p.engine _ r _ early, rfl⟩))
  · intro u _ w _ eq
    exact (rho.seatOf r).symm.injective eq

/-- Full participation is a special case of the awake count. -/
theorem full_batch_late_count {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (net : PartialSynchrony (sapc p) E rho)
    (relay : AcceptedObjectRelay (sapc p) E rho) (r : Slot)
    (sync : E.t_GST ≤ voteTime p r) (horizon : earlyTime p r ≤ rho.horizon)
    (full : ∀ v ∈ rho.honest, E.awake v (voteTime p r) = true)
    (v : V) (hv : v ∈ rho.honest) :
    rho.honest.card ≤ GridCO.voterCount (GridCO.lateVotes p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r) := by
  have awake : awakeAt E rho.honest (voteTime p r) = rho.honest :=
    Finset.filter_eq_self.mpr full
  simpa only [awake] using awake_batch_late_count p E rho hx hΔ net relay r sync horizon v hv

/-- Every synchronous genuine prefix under Recovery has support above f.
The support can include faulty seats. Its bound comes from the awake late
denominator, the quorum count, and the raw majority test, before either PC gate guard. -/
theorem recovery_genuine_support_above_floor_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (_hG : 0 < G)
    (h : QuorumRecoveryRegime p G E rho)
    (r : Slot) (sync : E.t_GST ≤ voteTime p r) (horizon : earlyTime p r ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (B C : Block)
    (raw : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some C)
    (below : Block.Preceq B C) :
    pcFaultCap p < GridCO.prefixSupport p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r B := by
  have voteBound : voteTime p r ≤ rho.horizon := by
    apply le_trans _ horizon
    change 4 * p.Δ * (r : Time) + p.Δ ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
    linarith [p.deltaPos]
  have denominator := awake_batch_late_count p E rho h.execution hΔ h.partialSynchrony
    h.acceptedRelay r sync horizon v hv
  apply quorum_support_above_floor p (awakeAt E rho.honest (voteTime p r)).card _ _
    (h.quorumParticipation _ sync voteBound) denominator
  have majority := @GridCO.confirmation_majority GridCO.slowLeasePolicy p.engine p.n _ r C raw
  have mono := GridCO.prefixSupport_mono p.engine
    (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r B C below
  omega

/-- The original Draft 4.3 interface is retained. -/
theorem recovery_genuine_support_above_floor {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (r : Slot) (sync : E.t_GST ≤ voteTime p r) (horizon : earlyTime p r ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (B C : Block)
    (raw : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some C)
    (below : Block.Preceq B C) :
    pcFaultCap p < GridCO.prefixSupport p.engine
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r B :=
  recovery_genuine_support_above_floor_quorum p E rho hΔ G hG (recovery_to_quorum p G E rho hG h) r
    sync horizon v hv B C raw below

/-- Recovery removes the PC-compatibility premise from genuine transfer.
Only the finite-root obligation remains for fast-source release and
slow-window expiry. This does not assert those obligations or recovery. -/
theorem recovery_genuine_head_covers_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : QuorumRecoveryRegime p G E rho)
    (r : Slot) (sync : E.t_GST ≤ voteTime p r) (horizon : gateTime p r ≤ rho.horizon)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) (B C : Block)
    (raw : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some C)
    (below : Block.Preceq B C)
    (root : Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) w).base) B) :
    Block.Preceq B (headData p rho (r + 1) w).target := by
  have early : voteTime p r ≤ earlyTime p r ∧ earlyTime p r ≤ gateTime p r := by
    change 4 * p.Δ * (r : Time) + p.Δ ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ ∧
      4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
    constructor <;> linarith [p.deltaPos]
  exact synchronous_genuine_highSupport_head_covers p E rho h.execution hΔ h.acceptedRelay
    r (sync.trans early.1) horizon v w hv hw B C raw below
    (recovery_genuine_support_above_floor_quorum p E rho hΔ G hG h r sync (early.2.trans horizon)
      v hv B C raw below) root

/-- The original Draft 4.3 interface is retained. -/
theorem recovery_genuine_head_covers {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (r : Slot) (sync : E.t_GST ≤ voteTime p r) (horizon : gateTime p r ≤ rho.horizon)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) (B C : Block)
    (raw : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some C)
    (below : Block.Preceq B C)
    (root : Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) w).base) B) :
    Block.Preceq B (headData p rho (r + 1) w).target :=
  recovery_genuine_head_covers_quorum p E rho hΔ G hG (recovery_to_quorum p G E rho hG h) r sync
    horizon v w hv hw B C raw below root

end AvailableChain.SAPC
end
