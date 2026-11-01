module
public import AvailableChainSAPC.Proofs.RecoveryBoundary
public import AvailableChainSAPC.Proofs.ProposalRoots

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- A proposal clock cannot be a gate. -/
theorem proposalTime_ne_gateTime (p : Params) (r s : Slot) :
    proposalTime p r ≠ gateTime p s := by
  intro eq
  have scaled : (4 * (r : Time)) * p.Δ = (4 * (s : Time) + 6) * p.Δ := by
    change 4 * p.Δ * (r : Time) = 4 * p.Δ * (s : Time) + 6 * p.Δ at eq
    nlinarith
  have cancelled : 4 * (r : ℤ) = 4 * (s : ℤ) + 6 :=
    mul_right_cancel₀ (ne_of_gt p.deltaPos) scaled
  omega

/-- Each live row at a non-gate clock beyond the boundary has permanent
support from its actual source. Expiry uses the exact stored deadline. -/
theorem recovery_preGate_row_support {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (boundary : Slot) (sources : RecoverySourcesSupported p rho boundary)
    (cut : Time) (start : voteTime p boundary ≤ cut)
    (v : V) (hv : v ∈ rho.honest) (B : Block) (g : Nat) (d : Time)
    (row : (B, g, d) ∈
      (clockPreGate p (Run.stateBeforeTime (sapc p) rho cut v) cut).base.obligations) :
    ∃ s, gateTime p s < cut ∧
      ∀ t, s ≤ t → gateTime p t ≤ rho.horizon → RecoveryHeadCovers p rho t B := by
  set_option backward.isDefEq.respectTransparency false in
  rw [clockPreGate_base] at row
  have live := GridCO.clockPreGate_live_rows p.engine
    (Run.stateBeforeTime (sapc p) rho cut v).base cut (B, g, d) row
  have old := GridCO.clockPreGate_obligations_subset p.engine
    (Run.stateBeforeTime (sapc p) rho cut v).base cut _ row
  obtain ⟨s, C, time, raw, below, admission, deadline⟩ := time_input_row_admitted_source
    p E rho hx.toScheduleWellFormed cut v B g d old
  have deadlineBound : cut < d := by
    have now : (GridCO.clockPreGate p.engine
        (Run.stateBeforeTime (sapc p) rho cut v).base cut).now = cut := by
      unfold GridCO.clockPreGate
      dsimp only
      split_ifs <;> rfl
    simpa only [now] using live
  refine ⟨s, time, ?_⟩
  intro t le hh
  exact (sources s (((GridCO.gateTime_le_iff p.engine s t).mpr le).trans hh) v hv B C g
    (deadline ▸ start.trans_lt deadlineBound) raw below admission t le hh).2

/-- Each live row at a non-gate clock beyond the boundary has permanent
support from its actual source. Expiry uses the exact stored deadline. -/
theorem recovery_clock_row_support {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (boundary : Slot) (sources : RecoverySourcesSupported p rho boundary)
    (cut : Time) (start : voteTime p boundary ≤ cut) (noGate : ∀ r, cut ≠ gateTime p r)
    (v : V) (hv : v ∈ rho.honest) (B : Block) (g : Nat) (d : Time)
    (row : (B, g, d) ∈
      (clock p (Run.stateBeforeTime (sapc p) rho cut v) cut).base.obligations) :
    ∃ s, gateTime p s < cut ∧
      ∀ t, s ≤ t → gateTime p t ≤ rho.horizon → RecoveryHeadCovers p rho t B := by
  set_option backward.isDefEq.respectTransparency false in
  rw [clock_eq_preGate_of_no_gate p _ _ noGate] at row
  exact recovery_preGate_row_support p E rho hx boundary sources cut start v hv B g d row

/-- A genuine prefix with support above f is below the honest proposer's
F4 floor. This is independent of the proposer PC, including a conflicting PC. -/
theorem recovery_genuine_below_proposal_floor_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : QuorumRecoveryRegime p G E rho)
    (r : Slot) (sync : E.t_GST ≤ voteTime p r) (horizon : gateTime p r ≤ rho.horizon)
    (P : Block) (proposal : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) P)
    (v : V) (hv : v ∈ rho.honest) (B C : Block)
    (raw : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some C)
    (below : Block.Preceq B C) :
    let st := proposalState p rho (r + 1)
    Block.Preceq B (floor p st st.base.blocks (GridCO.proposerView st.base (r + 1))
      (GridCO.proposerSupportView st.base (r + 1)) (r + 1)) := by
  dsimp only
  by_cases genesis : B = .genesis
  · rw [genesis]; exact GridCO.genesis_prefix _
  have early : voteTime p r ≤ earlyTime p r ∧ earlyTime p r ≤ gateTime p r := by
    change 4 * p.Δ * (r : Time) + p.Δ ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ ∧
      4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
    constructor <;> linarith [p.deltaPos]
  have headBound : voteTime p (r + 1) ≤ rho.horizon := by
    apply le_trans _ horizon
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
    push_cast; linarith [p.deltaPos]
  have receipts := honest_proposal_transfer_receipts p E rho h.execution hΔ h.partialSynchrony
    h.acceptedRelay r (sync.trans early.1) headBound P proposal v hv B
  have high := recovery_genuine_support_above_floor_quorum p E rho hΔ G hG h r sync
    (early.2.trans horizon) v hv B C raw below
  have score : pcFaultCap p < GridCO.goldfishScore (proposalState p rho (r + 1)).base.blocks
      (GridCO.proposerView (proposalState p rho (r + 1)).base (r + 1))
      (GridCO.proposerSupportView (proposalState p rho (r + 1)).base (r + 1)) B := by
    apply high.trans_le
    rw [GridCO.prefixSupport_eq_card, GridCO.goldfishScore_eq_card]
    exact Finset.card_le_card receipts.supporters_subset
  have walk := genuine_prefix_at_ordinary_proposal p E rho h.execution hΔ h.partialSynchrony
    h.acceptedRelay r (sync.trans early.1) headBound P proposal v hv B C raw below
  have stored : B ∈ (proposalState p rho (r + 1)).base.blocks := by
    have pos : 0 < (GridCO.prefixSupportSeats p.engine
        (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r B).card := by
      rw [← GridCO.prefixSupport_eq_card]
      omega
    obtain ⟨i, member⟩ := Finset.card_pos.mp pos
    obtain ⟨o, clean, _, target, targetEq, belowTarget⟩ := GridCO.prefixSupportSeats_witness
      p.engine _ r B i member
    obtain ⟨_, target', eq, known⟩ := receipts.forward o clean ⟨target, targetEq, belowTarget⟩
    have targetSame : target' = target := Option.some.inj (eq.symm.trans targetEq)
    subst target'
    exact (proposalState_paths p rho (r + 1)).1 target known B genesis belowTarget
  exact floor_covers p _ _ _ _ (r + 1) B stored genesis walk score

/-- The original Draft 4.3 interface is retained. -/
theorem recovery_genuine_below_proposal_floor {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (r : Slot) (sync : E.t_GST ≤ voteTime p r) (horizon : gateTime p r ≤ rho.horizon)
    (P : Block) (proposal : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) P)
    (v : V) (hv : v ∈ rho.honest) (B C : Block)
    (raw : SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some C)
    (below : Block.Preceq B C) :
    let st := proposalState p rho (r + 1)
    Block.Preceq B (floor p st st.base.blocks (GridCO.proposerView st.base (r + 1))
      (GridCO.proposerSupportView st.base (r + 1)) (r + 1)) :=
  recovery_genuine_below_proposal_floor_quorum p E rho hΔ G hG (recovery_to_quorum p G E rho hG h)
    r sync horizon P proposal v hv B C raw below

/-- The proposer and all HEAD readers have finite roots below the same
proposal floor after the source boundary. No lease-to-S invariant is used. -/
theorem recovery_roots_below_proposal_floor_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : QuorumRecoveryRegime p G E rho)
    (boundary : Slot) (sources : RecoverySourcesSupported p rho boundary)
    (r : Slot) (start : voteTime p boundary ≤ proposalTime p (r + 1))
    (sync : E.t_GST ≤ voteTime p r) (horizon : gateTime p r ≤ rho.horizon)
    (P : Block) (proposal : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) P) :
    let st := proposalState p rho (r + 1)
    let F := floor p st st.base.blocks (GridCO.proposerView st.base (r + 1))
      (GridCO.proposerSupportView st.base (r + 1)) (r + 1)
    Block.Preceq (GridCO.liveRoot st.base) F ∧
      ∀ v ∈ rho.honest, Block.Preceq (GridCO.liveRoot (headState p rho (r + 1) v).base) F := by
  let st := proposalState p rho (r + 1)
  let F := floor p st st.base.blocks (GridCO.proposerView st.base (r + 1))
    (GridCO.proposerSupportView st.base (r + 1)) (r + 1)
  have root (cut : Time) (startCut : voteTime p boundary ≤ cut)
      (beforeGate : cut < gateTime p r) (noGate : ∀ s, cut ≠ gateTime p s)
      (v : V) (hv : v ∈ rho.honest) :
      Block.Preceq (GridCO.liveRoot
        (clock p (Run.stateBeforeTime (sapc p) rho cut v) cut).base) F := by
    apply GridCO.liveRoot_below_of_rows
    intro B g d row
    obtain ⟨s, time, support⟩ := recovery_clock_row_support p E rho h.execution
      boundary sources cut startCut noGate v hv B g d row
    have before : s < r := by
      by_contra hn
      have le := (GridCO.gateTime_le_iff p.engine r s).mpr (Nat.le_of_not_gt hn)
      exact (not_lt_of_ge le) (time.trans beforeGate)
    have eq : r - 1 + 1 = r := Nat.sub_add_cancel (Nat.zero_le s |>.trans_lt before)
    have cover := support (r - 1) (Nat.le_sub_one_of_lt before)
      (((GridCO.gateTime_le_iff p.engine (r - 1) r).mpr (Nat.sub_le r 1)).trans horizon)
    simp only [RecoveryHeadCovers, eq] at cover
    have early : voteTime p r ≤ earlyTime p r ∧ earlyTime p r ≤ gateTime p r := by
      change 4 * p.Δ * (r : Time) + p.Δ ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ ∧
        4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
      constructor <;> linarith [p.deltaPos]
    obtain ⟨C, raw, below⟩ := preserve_from_heads p E rho h.execution hΔ h.partialSynchrony
      h.acceptedRelay r sync (early.2.trans horizon)
      (recovery_awake_majority_quorum p E rho G h _ sync (early.1.trans (early.2.trans horizon)))
      B cover v hv
    exact recovery_genuine_below_proposal_floor_quorum p E rho hΔ G hG h r sync horizon
      P proposal v hv B C raw below
  have proposalBefore : proposalTime p (r + 1) < gateTime p r := by
    change 4 * p.Δ * ((r + 1 : Nat) : Time) < 4 * p.Δ * (r : Time) + 6 * p.Δ
    push_cast; linarith [p.deltaPos]
  have headBefore : voteTime p (r + 1) < gateTime p r := by
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ < 4 * p.Δ * (r : Time) + 6 * p.Δ
    push_cast; linarith [p.deltaPos]
  have proposalHead : proposalTime p (r + 1) ≤ voteTime p (r + 1) := by
    change 4 * p.Δ * ((r + 1 : Nat) : Time) ≤ 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    linarith [p.deltaPos]
  exact ⟨root _ start proposalBefore (proposalTime_ne_gateTime p (r + 1)) _ proposal.1,
    fun v hv => root _ (start.trans proposalHead) headBefore
      (voteTime_ne_gateTime p (r + 1)) v hv⟩

/-- The original Draft 4.3 interface is retained. -/
theorem recovery_roots_below_proposal_floor {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (boundary : Slot) (sources : RecoverySourcesSupported p rho boundary)
    (r : Slot) (start : voteTime p boundary ≤ proposalTime p (r + 1))
    (sync : E.t_GST ≤ voteTime p r) (horizon : gateTime p r ≤ rho.horizon)
    (P : Block) (proposal : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) P) :
    let st := proposalState p rho (r + 1)
    let F := floor p st st.base.blocks (GridCO.proposerView st.base (r + 1))
      (GridCO.proposerSupportView st.base (r + 1)) (r + 1)
    Block.Preceq (GridCO.liveRoot st.base) F ∧
      ∀ v ∈ rho.honest, Block.Preceq (GridCO.liveRoot (headState p rho (r + 1) v).base) F :=
  recovery_roots_below_proposal_floor_quorum p E rho hΔ G hG (recovery_to_quorum p G E rho hG h)
    boundary sources r start sync horizon P proposal

end AvailableChain.SAPC
end
