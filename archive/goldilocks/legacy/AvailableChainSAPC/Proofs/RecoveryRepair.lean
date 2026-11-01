module
public import AvailableChainSAPC.Proofs.RecoveryGate

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- Equal-time receipts cannot replace the current-label PC by a later
rank: a later certificate needs an honest ack after this gate. -/
theorem installedPC_retained_at_gate {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (ha : (faulty rho).card < pcQuorum p) (s : Slot) (v : V) (c : PC p.n)
    (selected : (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).bestPC = some c)
    (slot : c.slot = s) : (Run.readAt (sapc p) rho (gateTime p s) v).bestPC = some c := by
  have input : Run.stateBeforeTime (sapc p) rho (gateTime p s) =
      Run.readAt (sapc p) rho (gateTime p s - 1) := by
    simp only [Run.stateBeforeTime, Run.readAt, ← Int.le_sub_one_iff]
  rw [input] at selected
  obtain ⟨d, next, rank⟩ := read_rank p E rho hx.toScheduleWellFormed v
    (gateTime p s - 1) (gateTime p s) (Int.sub_le_self _ (by norm_num)) c selected
  rcases rank with rfl | later
  · exact next
  · have bound := installedPC_time_le_read p E rho hx.toUnforgeableSignatures ha v
      (gateTime p s) d next
    have cast : (s : Time) + 1 ≤ d.slot := by rw [slot] at later; exact_mod_cast later
    change 4 * p.Δ * ((d.slot + 1 : Nat) : Time) + p.Δ ≤
      4 * p.Δ * (s : Time) + 6 * p.Δ at bound
    push_cast at bound
    nlinarith [p.deltaPos]

/-- Each honest opening after the supported boundary repairs both public
outputs and strong by 6Δ. The raw result is the same fresh block. -/
theorem recovery_proposal_after_sources_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : QuorumRecoveryRegime p G E rho)
    (boundary : Slot) (positive : 0 < boundary) (sync : E.t_GST ≤ proposalTime p boundary)
    (sources : RecoverySourcesSupported p rho boundary)
    (s : Slot) (start : proposalTime p boundary < proposalTime p s)
    (proposer : HonestAwakeProposer E rho s) (horizon : gateTime p s ≤ rho.horizon) :
    ∃ B, HonestProposalAt E (sapcInterface p).toInterface rho s B ∧
      (∀ v ∈ rho.honest, stable (Run.readAt (sapc p) rho (gateTime p s) v) = B ∧
        strong (Run.readAt (sapc p) rho (gateTime p s) v) = B) ∧
      ∀ v ∈ rho.honest,
        SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s = some B := by
  have later : boundary < s := by
    by_contra hn
    exact (not_lt.mpr ((GridCO.proposalTime_le_iff p.engine s boundary).mpr
      (Nat.le_of_not_gt hn))) start
  have pos : 0 < s := positive.trans later
  have proposalBound : proposalTime p s ≤ rho.horizon := by
    apply le_trans _ horizon
    change 4 * p.Δ * (s : Time) ≤ 4 * p.Δ * (s : Time) + 6 * p.Δ
    linarith [p.deltaPos]
  obtain ⟨B, proposal⟩ := honest_proposal_exists h.execution hΔ s pos proposer proposalBound
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt pos)
  have before : boundary ≤ r := Nat.le_of_lt_succ later
  have syncVote : E.t_GST ≤ voteTime p r := by
    have time := (GridCO.proposalTime_le_iff p.engine boundary r).mpr before
    apply sync.trans
    change 4 * p.Δ * (boundary : Time) ≤ 4 * p.Δ * (r : Time) + p.Δ
    change 4 * p.Δ * (boundary : Time) ≤ 4 * p.Δ * (r : Time) at time
    linarith [p.deltaPos]
  have startVote : voteTime p boundary ≤ proposalTime p (r + 1) := by
    have cast : (boundary : Time) ≤ r := by exact_mod_cast before
    change 4 * p.Δ * (boundary : Time) + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Time)
    push_cast; nlinarith [p.deltaPos]
  have service := recovery_proposal_service_quorum p E rho hΔ G hG h boundary sources r startVote
    syncVote horizon B proposal
  refine ⟨B, proposal, ?_, fun v hv => (service v hv).1⟩
  intro v hv
  obtain ⟨raw, c, selected, slot, target⟩ := service v hv
  have slotB := (honest_proposal_slot p E rho h.execution.toScheduleWellFormed
    (r + 1) B proposal).2.2
  have syncNext : E.t_GST ≤ voteTime p (r + 1) := by
    apply syncVote.trans
    change 4 * p.Δ * (r : Time) + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast; linarith [p.deltaPos]
  have startGate : voteTime p boundary ≤ gateTime p (r + 1) := by
    apply startVote.trans
    change 4 * p.Δ * ((r + 1 : Nat) : Time) ≤ 4 * p.Δ * ((r + 1 : Nat) : Time) + 6 * p.Δ
    linarith [p.deltaPos]
  refine ⟨recovery_gate_repairs_record_quorum p E rho hΔ G h boundary sources (r + 1) pos startGate
    syncNext horizon v hv B slotB raw c selected target, ?_⟩
  have retained := installedPC_retained_at_gate p E rho h.execution
    (capped_quorum_above_faults p rho (h.faultBound))
    (r + 1) v c selected slot
  simpa only [strong, retained, Option.map_some, Option.getD_some] using target

/-- The original Draft 4.3 interface is retained. -/
theorem recovery_proposal_after_sources {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (boundary : Slot) (positive : 0 < boundary) (sync : E.t_GST ≤ proposalTime p boundary)
    (sources : RecoverySourcesSupported p rho boundary)
    (s : Slot) (start : proposalTime p boundary < proposalTime p s)
    (proposer : HonestAwakeProposer E rho s) (horizon : gateTime p s ≤ rho.horizon) :
    ∃ B, HonestProposalAt E (sapcInterface p).toInterface rho s B ∧
      (∀ v ∈ rho.honest, stable (Run.readAt (sapc p) rho (gateTime p s) v) = B ∧
        strong (Run.readAt (sapc p) rho (gateTime p s) v) = B) ∧
      ∀ v ∈ rho.honest,
        SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s = some B :=
  recovery_proposal_after_sources_quorum p E rho hΔ G hG (recovery_to_quorum p G E rho hG h)
    boundary positive sync sources s start proposer horizon

/-- The requested recovery deadline includes a real fresh common repair
of S and strong, supplied by the unchanged opening recurrence. -/
theorem recovery_common_repair_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : QuorumRecoveryRegime p G E rho) :
    ∃ boundary s B, 0 < boundary ∧ E.t_GST < proposalTime p boundary ∧
      RecoverySourcesSupported p rho boundary ∧ boundary < s ∧
      gateTime p s ≤ E.t_GST + (sapcConstants p G).recoveryBound ∧
      HonestProposalAt E (sapcInterface p).toInterface rho s B ∧
      (∀ v ∈ rho.honest, stable (Run.readAt (sapc p) rho (gateTime p s) v) = B ∧
        strong (Run.readAt (sapc p) rho (gateTime p s) v) = B) ∧
      ∀ v ∈ rho.honest,
        SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s = some B := by
  obtain ⟨boundary, pos, sync, sources, bound⟩ := recovery_source_boundary_quorum p E rho hΔ G hG h
  have window : proposalTime p boundary + (sapcConstants p G).proposerGap ≤ rho.horizon := by
    have horizon := h.horizon
    change E.t_GST + (sapcConstants p G).recoveryBound ≤ rho.horizon at horizon
    change proposalTime p boundary + G ≤ rho.horizon
    linarith [p.deltaPos]
  obtain ⟨s, lo, hi, _, awake⟩ := h.recurrence (proposalTime p boundary) sync.le window
  change proposalTime p boundary < proposalTime p s at lo
  change proposalTime p s ≤ proposalTime p boundary + G at hi
  have repairTime : gateTime p s ≤ E.t_GST + (sapcConstants p G).recoveryBound := by
    change proposalTime p s + 6 * p.Δ ≤ _
    linarith
  obtain ⟨B, proposal, records, raw⟩ := recovery_proposal_after_sources_quorum p E rho hΔ G hG h
    boundary pos sync.le sources s lo awake (repairTime.trans h.horizon)
  have later : boundary < s := by
    by_contra hn
    exact (not_lt.mpr ((GridCO.proposalTime_le_iff p.engine s boundary).mpr
      (Nat.le_of_not_gt hn))) lo
  exact ⟨boundary, s, B, pos, sync, sources, later, repairTime, proposal, records, raw⟩

/-- The original Draft 4.3 interface is retained. -/
theorem recovery_common_repair {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho) :
    ∃ boundary s B, 0 < boundary ∧ E.t_GST < proposalTime p boundary ∧
      RecoverySourcesSupported p rho boundary ∧ boundary < s ∧
      gateTime p s ≤ E.t_GST + (sapcConstants p G).recoveryBound ∧
      HonestProposalAt E (sapcInterface p).toInterface rho s B ∧
      (∀ v ∈ rho.honest, stable (Run.readAt (sapc p) rho (gateTime p s) v) = B ∧
        strong (Run.readAt (sapc p) rho (gateTime p s) v) = B) ∧
      ∀ v ∈ rho.honest,
        SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s = some B :=
  recovery_common_repair_quorum p E rho hΔ G hG (recovery_to_quorum p G E rho hG h)

/-- Both base inclusion fields and the strong recovered inclusion field
hold after the declared deadline. Safety of arbitrary later reads is separate. -/
theorem recovery_included_from_engine_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : QuorumRecoveryRegime p G E rho) :
    IncludedFrom (sapc p) E (sapcInterface p).toInterface rho (sapcInterface p).stable
        (E.t_GST + (sapcConstants p G).recoveryBound) (sapcConstants p G).D_s ∧
      IncludedFrom (sapc p) E (sapcInterface p).toInterface rho (sapcInterface p).confirmed
        (E.t_GST + (sapcConstants p G).recoveryBound) (sapcConstants p G).D_c ∧
      IncludedFrom (sapc p) E (sapcInterface p).toInterface rho (sapcInterface p).strong
        (E.t_GST + (sapcConstants p G).recoveryBound) (sapcStrongConstants p).strongDelay := by
  obtain ⟨boundary, pos, sync, sources, bound⟩ := recovery_source_boundary_quorum p E rho hΔ G hG h
  have service (s : Slot)
      (after : E.t_GST + (sapcConstants p G).recoveryBound < proposalTime p s)
      (awake : HonestAwakeProposer E rho s) (horizon : gateTime p s ≤ rho.horizon) :
      ∃ B, HonestProposalAt E (sapcInterface p).toInterface rho s B ∧
        (∀ v ∈ rho.honest, stable (Run.readAt (sapc p) rho (gateTime p s) v) = B ∧
          strong (Run.readAt (sapc p) rho (gateTime p s) v) = B) := by
    have start : proposalTime p boundary < proposalTime p s := by
      linarith [p.deltaPos]
    obtain ⟨B, proposal, records, _⟩ := recovery_proposal_after_sources_quorum p E rho hΔ G hG h
      boundary pos sync.le sources s start awake horizon
    exact ⟨B, proposal, records⟩
  have base : IncludedFrom (sapc p) E (sapcInterface p).toInterface rho (sapcInterface p).stable
      (E.t_GST + (sapcConstants p G).recoveryBound) (6 * p.Δ) := by
    intro s after awake horizon
    obtain ⟨B, proposal, records⟩ := service s after awake horizon
    refine ⟨B, proposal, ?_⟩
    intro v hv
    change Block.Preceq B (stable (Run.readAt (sapc p) rho (gateTime p s) v))
    rw [(records v hv).1]
    exact GridCO.block_preceq_self _
  refine ⟨base, base, ?_⟩
  intro s after awake horizon
  obtain ⟨B, proposal, records⟩ := service s after awake horizon
  refine ⟨B, proposal, ?_⟩
  intro v hv
  change Block.Preceq B (strong (Run.readAt (sapc p) rho (gateTime p s) v))
  rw [(records v hv).2]
  exact GridCO.block_preceq_self _

/-- The original Draft 4.3 interface is retained. -/
theorem recovery_included_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho) :
    IncludedFrom (sapc p) E (sapcInterface p).toInterface rho (sapcInterface p).stable
        (E.t_GST + (sapcConstants p G).recoveryBound) (sapcConstants p G).D_s ∧
      IncludedFrom (sapc p) E (sapcInterface p).toInterface rho (sapcInterface p).confirmed
        (E.t_GST + (sapcConstants p G).recoveryBound) (sapcConstants p G).D_c ∧
      IncludedFrom (sapc p) E (sapcInterface p).toInterface rho (sapcInterface p).strong
        (E.t_GST + (sapcConstants p G).recoveryBound) (sapcStrongConstants p).strongDelay :=
  recovery_included_from_engine_quorum p E rho hΔ G hG (recovery_to_quorum p G E rho hG h)

end AvailableChain.SAPC
end
