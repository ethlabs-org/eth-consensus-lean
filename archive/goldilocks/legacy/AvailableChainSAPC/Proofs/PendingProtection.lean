module
public import AvailableChainSAPC.Proofs.HealthyBatch
public import AvailableChainSAPC.Proofs.LocalTransfer
public import AvailableChainSAPC.Proofs.SlowHistory

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- An awake honest majority puts all static faults below the SA release
threshold. This count needs no PC fault cap. -/
theorem faults_lt_releaseThreshold_of_awake {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (t : Time)
    (majority : AwakeMajority E rho t) : (faulty rho).card < releaseThreshold p := by
  have disjoint : Disjoint (awakeAt E rho.honest t) (faulty rho) := by
    apply Finset.disjoint_left.mpr
    intro v hv hf
    exact (Finset.mem_sdiff.mp hf).2 (Finset.mem_filter.mp hv).1
  have seats : Fintype.card V = p.n := by
    simpa using (Fintype.card_congr (rho.seatOf (0 : Slot))).symm
  apply SA.faults_lt_releaseThreshold p _ _ majority
  rw [← Finset.card_union_of_disjoint disjoint]
  exact (Finset.card_le_univ _).trans_eq seats

/-- The run-level pending-gate bridge. The healthy batch, actual SA
admission, finite guard, and prefix PC guard give the first lease.
Local transfer supplies the in-flight HEAD seed; shared first-loss
induction then retains the prefix until the new deadline.

This is a proof interface, not either contract P1 claim. The healthy
prefix induction must still supply the record and authority premises. -/
theorem pending_prefix_protection {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ) (cut : Time)
    (net : HealthyPrefixDelivery (sapc p) E rho cut)
    (relay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (r : Slot) (hearly : earlyTime p r ≤ cut) (hh : gateTime p r ≤ rho.horizon)
    (majority : AwakeMajority E rho (voteTime p r)) (B : Block) (nonzero : B ≠ .genesis)
    (heads : ∀ v ∈ rho.honest, Block.Preceq B (headData p rho r v).target)
    (old : ∀ v ∈ rho.honest, Block.Preceq B
      (stable (Run.stateBeforeTime (sapc p) rho (gateTime p r) v)))
    (admitted : ∀ v ∈ rho.honest, releaseThreshold p ∈
      @GridCO.admissionLevels GridCO.slowLeasePolicy p.engine p.n .block
        (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r B)
    (finite : ∀ v ∈ rho.honest, ∀ C,
      SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some C →
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base.obligations.any
        (fun (a, _, _) => !Block.compatible a C) = false)
    (gatePC : ∀ v ∈ rho.honest, pcOK
      (if capBroken p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v) then none
       else (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).bestPC) B = true)
    (root : ∀ v ∈ rho.honest,
      Block.Compatible (GridCO.liveRoot (headState p rho (r + 1) v).base) B)
    (headPC : ∀ v ∈ rho.honest, capBroken p (headState p rho (r + 1) v) = false →
      ∀ pc, selectedPC p (headState p rho (r + 1) v) (r + 1) = some pc →
        Block.Compatible pc.target B)
    (t : Time) (ht : gateTime p r ≤ t) (deadline : t < gateTime p r + lifetime p) :
    ∀ v ∈ rho.honest,
      GridCO.ProtectsUntil (Run.readAt (sapc p) rho t v).base B (releaseThreshold p)
        (gateTime p r + lifetime p) ∧ Block.Preceq B (stable (Run.readAt (sapc p) rho t v)) := by
  have earlyHorizon : earlyTime p r ≤ rho.horizon := by
    apply le_trans _ hh
    change 4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
    linarith [p.deltaPos]
  have freezeHorizon : freezeTime p r ≤ rho.horizon := by
    apply le_trans _ hh
    change 4 * p.Δ * (r : Time) + 3 * p.Δ ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
    linarith [p.deltaPos]
  have raw := healthy_preserve_from_heads p E rho hx hΔ cut net relay r hearly earlyHorizon
    majority B heads
  have base : ∀ v ∈ rho.honest,
      GridCO.ProtectsUntil (Run.readAt (sapc p) rho (gateTime p r) v).base B
        (releaseThreshold p) (gateTime p r + lifetime p) ∧
      Block.Preceq B (Run.readAt (sapc p) rho (gateTime p r) v).base.stableRecord := by
    intro v hv
    obtain ⟨C, result, below⟩ := raw v hv
    have count := healthy_prefixSupport_ge_awake p E rho hx hΔ cut net relay r
      hearly earlyHorizon B heads v hv
    have positive : 0 < GridCO.prefixSupport p.engine
        (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r B :=
      lt_of_lt_of_le (lt_of_le_of_lt (Nat.zero_le _) majority) count
    obtain ⟨target, stored, _, ancestor⟩ := GridCO.prefixSupport_target p.engine _ r B positive
    have storedB := (paths_at_fold p _ v).1 target stored B nonzero ancestor
    obtain ⟨row, record⟩ := read_gate_arms_prefix p E rho hx.toScheduleWellFormed hΔ r hh
      v hv B C (releaseThreshold p) result (finite v hv C result) storedB nonzero below
      (admitted v hv) (gatePC v hv) (old v hv)
    exact ⟨⟨_, le_refl _, row⟩, record⟩
  have nextHeads : ∀ v ∈ rho.honest, Block.Preceq B (headData p rho (r + 1) v).target := by
    intro v hv
    obtain ⟨C, result, below⟩ := raw v hv
    exact local_genuine_activePC_head_covers p E rho hx hΔ r v hv freezeHorizon B C result
      below (root v hv) (headPC v hv)
  exact protection_from_armed_read p E rho hx B (fun _ => releaseThreshold p)
    (gateTime p r) (gateTime p r + lifetime p)
    (fun _ _ => faults_lt_releaseThreshold_of_awake p E rho (voteTime p r) majority) base
    (armingHeadsCompatible_of_heads p E rho hx.toScheduleWellFormed r B nextHeads) t ht deadline

end AvailableChain.SAPC
end
