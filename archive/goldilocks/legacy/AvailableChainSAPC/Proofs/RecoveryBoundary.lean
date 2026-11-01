module
public import AvailableChainSAPC.Proofs.RecoverySupport
public import AvailableChainSA.Proofs.Recovery

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- Beyond the source boundary, each surviving row is covered by the
preceding honest HEAD batch. Its source lease may already be gone. -/
theorem recovery_rows_supported_at_head {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (boundary : Slot) (sources : RecoverySourcesSupported p rho boundary)
    (r : Slot) (start : boundary ≤ r) (horizon : voteTime p (r + 1) ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (B : Block) (g : Nat) (d : Time)
    (row : (B, g, d) ∈ (headState p rho (r + 1) v).base.obligations) :
    ∀ w ∈ rho.honest, Block.Preceq B (headData p rho r w).target := by
  obtain ⟨old, live, _⟩ := head_row_survives_release p rho r v B g d row
  obtain ⟨s, C, time, raw, below, admission, deadline⟩ := time_input_row_admitted_source
    p E rho hx.toScheduleWellFormed _ v B g d old
  have before : s < r := by
    by_contra hn
    have le := (GridCO.gateTime_le_iff p.engine r s).mpr (Nat.le_of_not_gt hn)
    change 4 * p.Δ * (s : Time) + 6 * p.Δ <
      4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ at time
    change 4 * p.Δ * (r : Time) + 6 * p.Δ ≤ 4 * p.Δ * (s : Time) + 6 * p.Δ at le
    push_cast at time
    linarith [p.deltaPos]
  have boundaryTime : voteTime p boundary ≤ voteTime p (r + 1) := by
    have cast : (boundary : Time) ≤ r + 1 := by exact_mod_cast start.trans (Nat.le_succ r)
    change 4 * p.Δ * (boundary : Time) + p.Δ ≤
      4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast
    nlinarith [p.deltaPos]
  have previousBound : gateTime p (r - 1) ≤ rho.horizon := by
    apply le_trans _ horizon
    have eq : r - 1 + 1 = r := Nat.sub_add_cancel (Nat.zero_le s |>.trans_lt before)
    have cast : ((r - 1 : Nat) : Time) + 1 = r := by exact_mod_cast eq
    change 4 * p.Δ * ((r - 1 : Nat) : Time) + 6 * p.Δ ≤
      4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast; nlinarith [p.deltaPos]
  have cover := (sources s (time.le.trans horizon)
    v hv B C g (deadline ▸ boundaryTime.trans_lt live) raw below admission (r - 1)
    (Nat.le_sub_one_of_lt before)
    previousBound).2
  have eq : r - 1 + 1 = r := Nat.sub_add_cancel (Nat.zero_le s |>.trans_lt before)
  simpa only [RecoveryHeadCovers, eq] using cover


/-- The complete-gate interface is retained. -/
theorem recovery_rows_supported {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (boundary : Slot) (sources : RecoverySourcesSupported p rho boundary)
    (r : Slot) (start : boundary ≤ r) (horizon : gateTime p r ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (B : Block) (g : Nat) (d : Time)
    (row : (B, g, d) ∈ (headState p rho (r + 1) v).base.obligations) :
    ∀ w ∈ rho.honest, Block.Preceq B (headData p rho r w).target := by
  apply recovery_rows_supported_at_head p E rho hx boundary sources r start _ v hv B g d row
  apply le_trans _ horizon
  change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
  push_cast; linarith [p.deltaPos]

/-- Every live root beyond the boundary is compatible with every raw
result at that label. Full honest coverage, not a relation to S, proves it. -/
theorem recovery_boundary_rows_compatible_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ) (G : Time)
    (h : QuorumRecoveryRegime p G E rho)
    (boundary : Slot) (sources : RecoverySourcesSupported p rho boundary)
    (r : Slot) (start : boundary ≤ r) (sync : E.t_GST ≤ voteTime p r)
    (horizon : gateTime p r ≤ rho.horizon) (source : V) (hs : source ∈ rho.honest)
    (B C : Block)
    (raw : SA.confirmation p
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r = some C)
    (below : Block.Preceq B C) : RecoveryRowsCompatible p rho r B := by
  have early : voteTime p r ≤ earlyTime p r ∧ earlyTime p r ≤ gateTime p r := by
    change 4 * p.Δ * (r : Time) + p.Δ ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ ∧
      4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
    constructor <;> linarith [p.deltaPos]
  intro v hv K g d row
  obtain ⟨D, rawD, belowD⟩ := preserve_from_heads p E rho h.execution hΔ h.partialSynchrony
    h.acceptedRelay r sync (early.2.trans horizon)
    (recovery_awake_majority_quorum p E rho G h _ sync (early.1.trans (early.2.trans horizon))) K
    (recovery_rows_supported p E rho h.execution boundary sources r start horizon v hv K g d row)
    source hs
  have eq : D = C := Option.some.inj (rawD.symm.trans raw)
  subst D
  exact GridCO.ancestors_compatible K B C belowD below

/-- The original Draft 4.3 interface is retained. -/
theorem recovery_boundary_rows_compatible {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ) (G : Time)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (boundary : Slot) (sources : RecoverySourcesSupported p rho boundary)
    (r : Slot) (start : boundary ≤ r) (sync : E.t_GST ≤ voteTime p r)
    (horizon : gateTime p r ≤ rho.horizon) (source : V) (hs : source ∈ rho.honest)
    (B C : Block)
    (raw : SA.confirmation p
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r = some C)
    (below : Block.Preceq B C) : RecoveryRowsCompatible p rho r B := by
  have early : voteTime p r ≤ earlyTime p r ∧ earlyTime p r ≤ gateTime p r := by
    change 4 * p.Δ * (r : Time) + p.Δ ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ ∧
      4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
    constructor <;> linarith [p.deltaPos]
  intro v hv K g d row
  obtain ⟨D, rawD, belowD⟩ := preserve_from_heads p E rho h.execution hΔ h.partialSynchrony
    h.acceptedRelay r sync (early.2.trans horizon)
    (recovery_awake_majority p E rho G h _ sync (early.1.trans (early.2.trans horizon))) K
    (recovery_rows_supported p E rho h.execution boundary sources r start horizon v hv K g d row)
    source hs
  have eq : D = C := Option.some.inj (rawD.symm.trans raw)
  subst D
  exact GridCO.ancestors_compatible K B C belowD below

/-- All raw results after the boundary transfer permanently through
actual SA-PC choices, for any frozen or carried PC. -/
theorem recovery_boundary_genuine_supported_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : QuorumRecoveryRegime p G E rho)
    (boundary : Slot) (sources : RecoverySourcesSupported p rho boundary)
    (r : Slot) (start : boundary ≤ r) (sync : E.t_GST ≤ voteTime p r)
    (horizon : gateTime p r ≤ rho.horizon) (source : V) (hs : source ∈ rho.honest)
    (B C : Block)
    (raw : SA.confirmation p
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r = some C)
    (below : Block.Preceq B C) :
    ∀ t, r ≤ t → gateTime p t ≤ rho.horizon →
      RecoveryRowsCompatible p rho t B ∧ RecoveryHeadCovers p rho t B ∧
      (r < t → ∀ v ∈ rho.honest, ∃ D,
        SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p t) v).base t = some D ∧
          Block.Preceq B D) :=
  recovery_permanent_support_quorum p E rho hΔ G hG h r sync horizon source hs B C raw below
    (recovery_boundary_rows_compatible_quorum p E rho hΔ G h boundary sources r start sync
      horizon source hs B C raw below)

/-- The original Draft 4.3 interface is retained. -/
theorem recovery_boundary_genuine_supported {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (boundary : Slot) (sources : RecoverySourcesSupported p rho boundary)
    (r : Slot) (start : boundary ≤ r) (sync : E.t_GST ≤ voteTime p r)
    (horizon : gateTime p r ≤ rho.horizon) (source : V) (hs : source ∈ rho.honest)
    (B C : Block)
    (raw : SA.confirmation p
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r = some C)
    (below : Block.Preceq B C) :
    ∀ t, r ≤ t → gateTime p t ≤ rho.horizon →
      RecoveryRowsCompatible p rho t B ∧ RecoveryHeadCovers p rho t B ∧
      (r < t → ∀ v ∈ rho.honest, ∃ D,
        SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p t) v).base t = some D ∧
          Block.Preceq B D) :=
  recovery_boundary_genuine_supported_quorum p E rho hΔ G hG (recovery_to_quorum p G E rho hG h)
    boundary sources r start sync horizon source hs B C raw below

/-- Raw genuine history is ordered after the two-lease boundary, even
before a fresh proposal repairs the public records. -/
theorem recovery_genuine_prefix_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : QuorumRecoveryRegime p G E rho)
    (boundary : Slot) (sources : RecoverySourcesSupported p rho boundary)
    (r s : Slot) (start : boundary ≤ r) (before : r < s) (sync : E.t_GST ≤ voteTime p r)
    (horizon : gateTime p s ≤ rho.horizon) (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (B C : Block)
    (rawB : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some B)
    (rawC : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) w).base s = some C) :
    Block.Preceq B C := by
  obtain ⟨D, rawD, below⟩ := (recovery_boundary_genuine_supported_quorum p E rho hΔ G hG h
    boundary sources r start sync
    (((GridCO.gateTime_le_iff p.engine r s).mpr before.le).trans horizon) v hv B B rawB
    (GridCO.block_preceq_self _) s before.le horizon).2.2 before w hw
  exact Option.some.inj (rawD.symm.trans rawC) ▸ below

/-- The original Draft 4.3 interface is retained. -/
theorem recovery_genuine_prefix {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (boundary : Slot) (sources : RecoverySourcesSupported p rho boundary)
    (r s : Slot) (start : boundary ≤ r) (before : r < s) (sync : E.t_GST ≤ voteTime p r)
    (horizon : gateTime p s ≤ rho.horizon) (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (B C : Block)
    (rawB : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some B)
    (rawC : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) w).base s = some C) :
    Block.Preceq B C :=
  recovery_genuine_prefix_quorum p E rho hΔ G hG (recovery_to_quorum p G E rho hG h) boundary
    sources r s start before sync horizon v w hv hw B C rawB rawC

/-- A supported boundary leaves the exact SA repair interval in the
requested 2L+G+8Δ budget. The start uses SA's proposal-time boundary. -/
theorem recovery_source_boundary_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : QuorumRecoveryRegime p G E rho) :
    ∃ boundary : Slot, 0 < boundary ∧ E.t_GST < proposalTime p boundary ∧
      RecoverySourcesSupported p rho boundary ∧
      proposalTime p boundary + G + 6 * p.Δ ≤
        E.t_GST + (sapcConstants p G).recoveryBound := by
  obtain ⟨b, positive, sync, time⟩ := GridCO.exists_recovery_start p.engine E.t_GST E.t_GST_nonneg
  have start : b ≤ SA.recoveryBoundary p b := Nat.le_add_right _ _
  have syncVote : E.t_GST ≤ voteTime p b := by
    change E.t_GST < 4 * p.Δ * (b : Time) at sync
    change E.t_GST ≤ 4 * p.Δ * (b : Time) + p.Δ
    linarith [p.deltaPos]
  refine ⟨SA.recoveryBoundary p b, positive.trans_le start,
    sync.trans_le ((GridCO.proposalTime_le_iff p.engine b _).mpr start),
    recovery_sources_after_two_leases_quorum p E rho hΔ G hG h b syncVote, ?_⟩
  change SA.proposalTime p (SA.recoveryBoundary p b) + G + 6 * p.Δ ≤
    E.t_GST + (2 * SA.lifetime p + G + 8 * p.Δ)
  rw [SA.recoveryBoundary_time]
  change SA.proposalTime p b ≤ E.t_GST + 4 * p.Δ at time
  linarith

/-- The original Draft 4.3 interface is retained. -/
theorem recovery_source_boundary {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho) :
    ∃ boundary : Slot, 0 < boundary ∧ E.t_GST < proposalTime p boundary ∧
      RecoverySourcesSupported p rho boundary ∧
      proposalTime p boundary + G + 6 * p.Δ ≤
        E.t_GST + (sapcConstants p G).recoveryBound :=
  recovery_source_boundary_quorum p E rho hΔ G hG (recovery_to_quorum p G E rho hG h)

end AvailableChain.SAPC
end
