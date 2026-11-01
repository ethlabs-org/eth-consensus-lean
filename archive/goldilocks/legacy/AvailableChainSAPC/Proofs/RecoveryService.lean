module
public import AvailableChainSAPC.Proofs.RecoveryProposal
public import AvailableChainSAPC.Proofs.StrongClean

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- Exact synchronous HEADs give the exact raw current-slot result.
This uses SA's slot-order bound, before either SA-PC gate guard. -/
theorem recovery_raw_result_eq_of_exact_heads_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ) (G : Time)
    (h : QuorumRecoveryRegime p G E rho)
    (s : Slot) (sync : E.t_GST ≤ voteTime p s) (horizon : earlyTime p s ≤ rho.horizon)
    (B : Block) (slot : B.slot = s)
    (heads : ∀ v ∈ rho.honest, (headData p rho s v).target = B)
    (v : V) (hv : v ∈ rho.honest) :
    SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s = some B := by
  have beforeEarly : voteTime p s ≤ earlyTime p s := by
    change 4 * p.Δ * (s : Time) + p.Δ ≤ 4 * p.Δ * (s : Time) + 2 * p.Δ
    linarith [p.deltaPos]
  obtain ⟨C, raw, below⟩ := preserve_from_heads p E rho h.execution hΔ h.partialSynchrony
    h.acceptedRelay s sync horizon (recovery_awake_majority_quorum p E rho G h _ sync
      (beforeEarly.trans horizon)) B
    (fun w hw => by rw [heads w hw]; exact GridCO.block_preceq_self _) v hv
  have ordered := (paths_at_fold p
    (rho.events.filter (fun e => decide (e.time < gateTime p s))) v).2.2
  have resultOrdered : GridCO.SlotOrdered C := by
    rcases @GridCO.confirmation_mem GridCO.slowLeasePolicy p.engine p.n _ s C raw with gen | stored
    · subst C; trivial
    · exact ordered C stored
  have bound := @GridCO.confirmation_slot_le GridCO.slowLeasePolicy p.engine p.n _ s C ordered raw
  have eq := GridCO.prefix_eq_of_slot_ge B C resultOrdered below (bound.trans_eq slot.symm)
  simpa only [eq] using raw

/-- The original Draft 4.3 interface is retained. -/
theorem recovery_raw_result_eq_of_exact_heads {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ) (G : Time)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (s : Slot) (sync : E.t_GST ≤ voteTime p s) (horizon : earlyTime p s ≤ rho.horizon)
    (B : Block) (slot : B.slot = s)
    (heads : ∀ v ∈ rho.honest, (headData p rho s v).target = B)
    (v : V) (hv : v ∈ rho.honest) :
    SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s = some B := by
  have beforeEarly : voteTime p s ≤ earlyTime p s := by
    change 4 * p.Δ * (s : Time) + p.Δ ≤ 4 * p.Δ * (s : Time) + 2 * p.Δ
    linarith [p.deltaPos]
  obtain ⟨C, raw, below⟩ := preserve_from_heads p E rho h.execution hΔ h.partialSynchrony
    h.acceptedRelay s sync horizon (recovery_awake_majority p E rho G h _ sync
      (beforeEarly.trans horizon)) B
    (fun w hw => by rw [heads w hw]; exact GridCO.block_preceq_self _) v hv
  have ordered := (paths_at_fold p
    (rho.events.filter (fun e => decide (e.time < gateTime p s))) v).2.2
  have resultOrdered : GridCO.SlotOrdered C := by
    rcases @GridCO.confirmation_mem GridCO.slowLeasePolicy p.engine p.n _ s C raw with gen | stored
    · subst C; trivial
    · exact ordered C stored
  have bound := @GridCO.confirmation_slot_le GridCO.slowLeasePolicy p.engine p.n _ s C ordered raw
  have eq := GridCO.prefix_eq_of_slot_ge B C resultOrdered below (bound.trans_eq slot.symm)
  simpa only [eq] using raw

/-- An exact fresh proposal after the source boundary gets a common PC
before its 6Δ gate. Its raw result also equals the proposal at every reader. -/
theorem recovery_proposal_service_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : QuorumRecoveryRegime p G E rho)
    (boundary : Slot) (sources : RecoverySourcesSupported p rho boundary)
    (r : Slot) (start : voteTime p boundary ≤ proposalTime p (r + 1))
    (sync : E.t_GST ≤ voteTime p r) (horizon : gateTime p (r + 1) ≤ rho.horizon)
    (B : Block) (proposal : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) B) :
    ∀ v ∈ rho.honest,
      SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p (r + 1)) v).base
        (r + 1) = some B ∧
      ∃ c, (Run.stateBeforeTime (sapc p) rho (gateTime p (r + 1)) v).bestPC = some c ∧
        c.slot = r + 1 ∧ c.target = B := by
  have times : voteTime p r ≤ proposalTime p (r + 1) ∧
      proposalTime p (r + 1) ≤ voteTime p (r + 1) ∧
      voteTime p (r + 1) ≤ earlyTime p (r + 1) ∧
      earlyTime p (r + 1) ≤ voteTime p (r + 1 + 1) ∧
      voteTime p (r + 1 + 1) ≤ gateTime p (r + 1) := by
    change 4 * p.Δ * (r : Time) + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Time) ∧
      4 * p.Δ * ((r + 1 : Nat) : Time) ≤ 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ ∧
      4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ ≤
        4 * p.Δ * ((r + 1 : Nat) : Time) + 2 * p.Δ ∧
      4 * p.Δ * ((r + 1 : Nat) : Time) + 2 * p.Δ ≤
        4 * p.Δ * ((r + 1 + 1 : Nat) : Time) + p.Δ ∧
      4 * p.Δ * ((r + 1 + 1 : Nat) : Time) + p.Δ ≤
        4 * p.Δ * ((r + 1 : Nat) : Time) + 6 * p.Δ
    push_cast
    constructor
    · linarith [p.deltaPos]
    constructor
    · linarith [p.deltaPos]
    constructor
    · linarith [p.deltaPos]
    constructor <;> linarith [p.deltaPos]
  have startSlot : boundary ≤ r + 1 := by
    have cast : (boundary : Time) ≤ (r + 1 : Nat) := by
      change 4 * p.Δ * (boundary : Time) + p.Δ ≤
        4 * p.Δ * ((r + 1 : Nat) : Time) at start
      nlinarith [p.deltaPos]
    exact_mod_cast cast
  have choices := recovery_honest_proposal_head_quorum p E rho hΔ G hG h boundary sources r start
    sync (((GridCO.gateTime_le_iff p.engine r (r + 1)).mpr (Nat.le_succ r)).trans horizon)
    B proposal
  have syncP := sync.trans times.1
  have syncHead := syncP.trans times.2.1
  have earlyBound := times.2.2.2.1.trans (times.2.2.2.2.trans horizon)
  have headBound := times.2.2.1.trans earlyBound
  have raw := recovery_raw_result_eq_of_exact_heads_quorum p E rho hΔ G h (r + 1) syncHead
    earlyBound
    B (honest_proposal_slot p E rho h.execution.toScheduleWellFormed (r + 1) B proposal).2.2 choices
  have ack := (recovery_boundary_genuine_supported_quorum p E rho hΔ G hG h boundary sources
    (r + 1) startSlot syncHead horizon (rho.proposerOf (r + 1)) proposal.1 B B
    (raw _ proposal.1) (GridCO.block_preceq_self _) (r + 1) (le_refl _) horizon).2.1
  have cap := h.faultBound
  intro v hv
  refine ⟨raw v hv, ?_⟩
  obtain ⟨⟨c, cs, cb, valid⟩, d, selected, rank⟩ := quorum_preparation_ack_service p E rho
    h.execution hΔ cap h.partialSynchrony h.acceptedRelay (r + 1) B proposal syncP horizon
    (h.quorumParticipation _ syncHead headBound)
    (h.quorumParticipation _
      (syncHead.trans (times.2.2.1.trans times.2.2.2.1)) (times.2.2.2.2.trans horizon))
    choices ack v hv
  have bound := installedPC_slot_le_at_gate p E rho h.execution
    (capped_quorum_above_faults p rho cap) v (r + 1) d selected
  have ds : d.slot = r + 1 := Nat.le_antisymm bound rank
  have target := pc_same_slot_unique p E rho h.execution.toScheduleWellFormed cap _ _
    (archive_authenticated_beforeTime p E rho h.execution.toUnforgeableSignatures _ v)
    (archive_authenticated_beforeTime p E rho h.execution.toUnforgeableSignatures _ v)
    c d valid (installedPC_valid_beforeTime p rho v _ d selected) (cs.trans ds.symm)
  exact ⟨d, selected, ds, target.symm.trans cb⟩

/-- The original Draft 4.3 interface is retained. -/
theorem recovery_proposal_service {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (boundary : Slot) (sources : RecoverySourcesSupported p rho boundary)
    (r : Slot) (start : voteTime p boundary ≤ proposalTime p (r + 1))
    (sync : E.t_GST ≤ voteTime p r) (horizon : gateTime p (r + 1) ≤ rho.horizon)
    (B : Block) (proposal : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) B) :
    ∀ v ∈ rho.honest,
      SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p (r + 1)) v).base
        (r + 1) = some B ∧
      ∃ c, (Run.stateBeforeTime (sapc p) rho (gateTime p (r + 1)) v).bestPC = some c ∧
        c.slot = r + 1 ∧ c.target = B :=
  recovery_proposal_service_quorum p E rho hΔ G hG (recovery_to_quorum p G E rho hG h) boundary
    sources r start sync horizon B proposal

end AvailableChain.SAPC
end
