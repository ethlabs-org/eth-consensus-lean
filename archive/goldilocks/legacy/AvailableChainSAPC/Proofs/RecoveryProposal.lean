module
public import AvailableChainSAPC.Proofs.RecoveryRoots
public import AvailableChainSAPC.Proofs.ProposalEligibility

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- Under the cap, equal selected ranks give equal targets after an
arbitrary prefix. Clean history is not needed for this comparison. -/
theorem capped_honest_proposal_selectedPC_target {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (net : PartialSynchrony (sapc p) E rho) (relay : AcceptedObjectRelay (sapc p) E rho)
    (r : Slot) (sync : E.t_GST ≤ freezeTime p r) (horizon : voteTime p (r + 1) ≤ rho.horizon)
    (P : Block) (proposal : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) P)
    (v : V) (hv : v ∈ rho.honest) :
    (selectedPC p (headState p rho (r + 1) v) (r + 1)).map PC.target =
      (proposalState p rho (r + 1)).bestPC.map PC.target := by
  set_option backward.isDefEq.respectTransparency false in
  have ranks := honest_proposal_selectedPC_rank p E rho hx hΔ net relay
    r sync horizon P proposal v hv
  cases source : (proposalState p rho (r + 1)).bestPC with
  | none =>
    cases selected : selectedPC p (headState p rho (r + 1) v) (r + 1) with
    | none => rfl
    | some c => simp [source, selected] at ranks
  | some d =>
    cases selected : selectedPC p (headState p rho (r + 1) v) (r + 1) with
    | none => simp [source, selected] at ranks
    | some c =>
      have rank : c.slot = d.slot := by
        simpa only [source, selected, Option.map_some, Option.some.injEq] using ranks
      have certs := certificates_valid_at_fold p
        (rho.events.filter (fun e => decide (e.time < voteTime p (r + 1)))) v
      have validC := selectedPC_valid p _ (clock_frozenPC_valid p _ _ certs.2 certs.1)
        (r + 1) c selected
      have validD := clock_valid p _ _ (installedPC_valid_at_fold p _ _) d source
      have authC : ArchiveAuthenticated p E rho (headState p rho (r + 1) v) := by
        simpa only [ArchiveAuthenticated, headState, clock_archive] using!
          archive_authenticated_beforeTime p E rho hx.toUnforgeableSignatures
            (voteTime p (r + 1)) v
      have authD : ArchiveAuthenticated p E rho (proposalState p rho (r + 1)) := by
        simpa only [ArchiveAuthenticated, proposalState, clock_archive] using!
          archive_authenticated_beforeTime p E rho hx.toUnforgeableSignatures
            (proposalTime p (r + 1)) (rho.proposerOf (r + 1))
      have eq := pc_same_slot_unique p E rho hx.toScheduleWellFormed cap _ _ authC authD
        c d validC validD rank
      simp only [Option.map_some, eq]

/-- Common floors and equal-rank PC uniqueness give a common recovery
anchor. The anchor can be outside the ordinary genesis walk. -/
theorem recovery_proposal_anchor_eq_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (_hG : 0 < G)
    (h : QuorumRecoveryRegime p G E rho)
    (r : Slot) (sync : E.t_GST ≤ freezeTime p r) (horizon : voteTime p (r + 1) ≤ rho.horizon)
    (P : Block) (proposal : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) P)
    (v : V) (hv : v ∈ rho.honest) :
    let source := proposalState p rho (r + 1)
    let target := headState p rho (r + 1) v
    let cert := selectedPC p target (r + 1)
    preliminaryAnchor (floor p source source.base.blocks (GridCO.proposerView source.base (r + 1))
        (GridCO.proposerSupportView source.base (r + 1)) (r + 1)) source.bestPC =
      preliminaryAnchor (floor p target (activeVoterTree p target (r + 1) cert)
        (GridCO.voterView p.engine target.base (r + 1))
        (GridCO.voterSupportView p.engine target.base (r + 1)) (r + 1)) cert := by
  set_option backward.isDefEq.respectTransparency false in
  dsimp only
  have cap := h.faultBound
  have active : capBroken p (headState p rho (r + 1) v) = false := by
    rw [headState, capBroken_clock]
    exact capBroken_false_beforeTime p E rho h.execution cap v _
  rw [honest_proposal_floor_eq p E rho h.execution hΔ h.rootInjective h.partialSynchrony
    h.acceptedRelay r sync horizon P proposal v hv active
    (selectedPC p (headState p rho (r + 1) v) (r + 1))]
  have targets := capped_honest_proposal_selectedPC_target p E rho h.execution hΔ cap
    h.partialSynchrony h.acceptedRelay r sync horizon P proposal v hv
  cases source : (proposalState p rho (r + 1)).bestPC <;>
    cases selected : selectedPC p (headState p rho (r + 1) v) (r + 1) <;>
    simp only [source, selected, Option.map_some, Option.map_none, Option.some.injEq] at targets
  all_goals first | contradiction | rfl | simp only [preliminaryAnchor, targets]

/-- The original Draft 4.3 interface is retained. -/
theorem recovery_proposal_anchor_eq {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (r : Slot) (sync : E.t_GST ≤ freezeTime p r) (horizon : voteTime p (r + 1) ≤ rho.horizon)
    (P : Block) (proposal : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) P)
    (v : V) (hv : v ∈ rho.honest) :
    let source := proposalState p rho (r + 1)
    let target := headState p rho (r + 1) v
    let cert := selectedPC p target (r + 1)
    preliminaryAnchor (floor p source source.base.blocks (GridCO.proposerView source.base (r + 1))
        (GridCO.proposerSupportView source.base (r + 1)) (r + 1)) source.bestPC =
      preliminaryAnchor (floor p target (activeVoterTree p target (r + 1) cert)
        (GridCO.voterView p.engine target.base (r + 1))
        (GridCO.voterSupportView p.engine target.base (r + 1)) (r + 1)) cert :=
  recovery_proposal_anchor_eq_quorum p E rho hΔ G hG (recovery_to_quorum p G E rho hG h) r sync
    horizon P proposal v hv

/-- A full synchronous batch bounds detected equivocation in the proposal
view. This permits reuse of the clean eligible-path reflection theorem. -/
theorem recovery_proposal_detected_minority_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ) (G : Time)
    (h : QuorumRecoveryRegime p G E rho)
    (r : Slot) (sync : E.t_GST ≤ voteTime p r) (horizon : voteTime p (r + 1) ≤ rho.horizon)
    (P : Block) (proposal : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) P) :
    let raw := GridCO.proposerView (proposalState p rho (r + 1)).base (r + 1)
    2 * (detectedSeats raw).card < GridCO.voterCount raw := by
  have early : voteTime p r ≤ earlyTime p r ∧ earlyTime p r ≤ voteTime p (r + 1) := by
    change 4 * p.Δ * (r : Time) + p.Δ ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ ∧
      4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast
    constructor <;> linarith [p.deltaPos]
  obtain ⟨C, raw, _⟩ := preserve_from_heads p E rho h.execution hΔ h.partialSynchrony
    h.acceptedRelay r sync (early.2.trans horizon)
    (recovery_awake_majority_quorum p E rho G h _ sync (early.1.trans (early.2.trans horizon)))
    .genesis (fun _ _ => GridCO.genesis_prefix _) _ proposal.1
  exact transfer_detected_minority p _ r _ _ _ C
    (honest_proposal_transfer_receipts p E rho h.execution hΔ h.partialSynchrony
      h.acceptedRelay r (sync.trans early.1) horizon P proposal _ proposal.1 C)
    (@GridCO.confirmation_majority GridCO.slowLeasePolicy p.engine p.n _ r C raw)

/-- The original Draft 4.3 interface is retained. -/
theorem recovery_proposal_detected_minority {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ) (G : Time)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (r : Slot) (sync : E.t_GST ≤ voteTime p r) (horizon : voteTime p (r + 1) ≤ rho.horizon)
    (P : Block) (proposal : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) P) :
    let raw := GridCO.proposerView (proposalState p rho (r + 1)).base (r + 1)
    2 * (detectedSeats raw).card < GridCO.voterCount raw := by
  have early : voteTime p r ≤ earlyTime p r ∧ earlyTime p r ≤ voteTime p (r + 1) := by
    change 4 * p.Δ * (r : Time) + p.Δ ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ ∧
      4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast
    constructor <;> linarith [p.deltaPos]
  obtain ⟨C, raw, _⟩ := preserve_from_heads p E rho h.execution hΔ h.partialSynchrony
    h.acceptedRelay r sync (early.2.trans horizon)
    (recovery_awake_majority p E rho G h _ sync (early.1.trans (early.2.trans horizon)))
    .genesis (fun _ _ => GridCO.genesis_prefix _) _ proposal.1
  exact transfer_detected_minority p _ r _ _ _ C
    (honest_proposal_transfer_receipts p E rho h.execution hΔ h.partialSynchrony
      h.acceptedRelay r (sync.trans early.1) horizon P proposal _ proposal.1 C)
    (@GridCO.confirmation_majority GridCO.slowLeasePolicy p.engine p.n _ r C raw)

/-- A floor is always below the preliminary anchor, for any PC. -/
theorem floor_below_preliminaryAnchor {n : Nat} (F : Block) (cert : Option (PC n)) :
    Block.Preceq F (preliminaryAnchor F cert) := by
  cases cert with
  | none => exact GridCO.block_preceq_self _
  | some c =>
    simp only [preliminaryAnchor]
    split
    · rename_i test
      rcases Bool.or_eq_true_iff.mp test with genesis | below
      · have eq : F = .genesis := by simpa using genesis
        rw [eq]; exact GridCO.genesis_prefix _
      · exact below
    · exact GridCO.block_preceq_self _

/-- After unsupported sources expire, each honest HEAD names the exact
fresh honest proposal. The common anchor can come from an old PC. -/
theorem recovery_honest_proposal_head_quorum {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : QuorumRecoveryRegime p G E rho)
    (boundary : Slot) (sources : RecoverySourcesSupported p rho boundary)
    (r : Slot) (start : voteTime p boundary ≤ proposalTime p (r + 1))
    (syncVote : E.t_GST ≤ voteTime p r) (hh : gateTime p r ≤ rho.horizon)
    (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) b)
    (reader : V) (hr : reader ∈ rho.honest) :
    (headData p rho (r + 1) reader).target = b := by
  set_option backward.isDefEq.respectTransparency false in
  let source := proposalState p rho (r + 1)
  let target := headState p rho (r + 1) reader
  let cert := selectedPC p target (r + 1)
  let tree := activeVoterTree p target (r + 1) cert
  let F := floor p source source.base.blocks (GridCO.proposerView source.base (r + 1))
    (GridCO.proposerSupportView source.base (r + 1)) (r + 1)
  let A := preliminaryAnchor F source.bestPC
  have cap := h.faultBound
  have active : capBroken p target = false := by
    dsimp only [target]
    rw [headState, capBroken_clock]
    exact capBroken_false_beforeTime p E rho h.execution cap reader _
  have sourceActive : capBroken p source = false := by
    dsimp only [source]
    rw [proposalState, capBroken_clock]
    exact capBroken_false_beforeTime p E rho h.execution cap _ _
  have headBound : voteTime p (r + 1) ≤ rho.horizon := by
    apply le_trans _ hh
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
    push_cast; linarith [p.deltaPos]
  have sync : E.t_GST ≤ freezeTime p r := by
    apply syncVote.trans
    change 4 * p.Δ * (r : Time) + p.Δ ≤ 4 * p.Δ * (r : Time) + 3 * p.Δ
    linarith [p.deltaPos]
  have syncP : E.t_GST ≤ proposalTime p (r + 1) := by
    apply syncVote.trans
    change 4 * p.Δ * (r : Time) + p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Time)
    push_cast; linarith [p.deltaPos]
  have roots := recovery_roots_below_proposal_floor_quorum p E rho hΔ G hG h boundary sources
    r start syncVote hh b hb
  have sourceRootBelow : Block.Preceq (GridCO.liveRoot source.base) A :=
    GridCO.prefix_trans _ F A roots.1 (floor_below_preliminaryAnchor F source.bestPC)
  have targetRootBelow : Block.Preceq (GridCO.liveRoot target.base) A :=
    GridCO.prefix_trans _ F A (roots.2 reader hr) (floor_below_preliminaryAnchor F source.bestPC)
  have anchorEq : A = preliminaryAnchor
      (floor p target tree (GridCO.voterView p.engine target.base (r + 1))
        (GridCO.voterSupportView p.engine target.base (r + 1)) (r + 1)) cert :=
    recovery_proposal_anchor_eq_quorum p E rho hΔ G hG h r sync headBound b hb reader hr
  have parent : GridCO.ghost A source.base.blocks
      (GridCO.goldfishScore source.base.blocks (GridCO.proposerView source.base (r + 1))
        (GridCO.proposerSupportView source.base (r + 1)))
      (GridCO.goldfishEligible source.base.blocks (GridCO.proposerView source.base (r + 1))
        (GridCO.proposerSupportView source.base (r + 1)) (r + 1)) = b.parent := by
    obtain ⟨_, shape, _⟩ := honest_proposal_views p E rho h.execution.toScheduleWellFormed
      (r + 1) b hb
    conv_rhs => rw [shape]
    change _ = choice p source source.base.blocks _ _ (r + 1) source.bestPC
    simp only [choice, sourceActive, Bool.false_eq_true, ↓reduceIte]
    change _ = GridCO.ghost (mandatoryRoot (GridCO.liveRoot source.base) A) _ _ _
    rw [mandatoryRoot, ite_eq_left (show Block.preceq (GridCO.liveRoot source.base) A = true
      from sourceRootBelow)]
  have targetRootEq : mandatoryRoot (GridCO.liveRoot target.base)
      (preliminaryAnchor (floor p target tree (GridCO.voterView p.engine target.base (r + 1))
        (GridCO.voterSupportView p.engine target.base (r + 1)) (r + 1)) cert) = A := by
    rw [← anchorEq]
    exact ite_eq_left targetRootBelow
  have anchorParent : Block.Preceq A b.parent := by
    rw [← parent]
    exact GridCO.ghost_extends _ _ _ _
  have hslot := (honest_proposal_slot p E rho h.execution.toScheduleWellFormed
    (r + 1) b hb).2.2
  have sourceRoot : GridCO.RootInjectiveBelow source.base.blocks := by
    simpa only [source, proposalState, clock_blocks] using! time_input_rootInjectiveBelow p E rho
      h.execution.toScheduleWellFormed h.rootInjective (proposalTime p (r + 1)) _
  have targetRoot : GridCO.RootInjectiveBelow target.base.blocks := by
    simpa only [target, headState, clock_blocks] using! time_input_rootInjectiveBelow p E rho
      h.execution.toScheduleWellFormed h.rootInjective (voteTime p (r + 1)) reader
  have stored : b ∈ target.base.blocks := by
    have path := honest_proposal_path_before_head p E rho h.execution hΔ h.partialSynchrony
      (r + 1) b hb syncP headBound reader hr _ (le_refl _)
    simp only [target, headState, clock_blocks]
    cases b with
    | genesis => exact of_decide_eq_true (Bool.and_eq_true_iff.mp path).1
    | node parent slot r_slot root =>
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp path).1).1
  have targetClosed : GridCO.StoredPrefixClosed target.base := by
    simpa only [target, headState, GridCO.StoredPrefixClosed, clock_blocks] using!
      (paths_at_fold p
        (rho.events.filter (fun e => decide (e.time < voteTime p (r + 1)))) reader).1
  have parentEq : b.parent? = some b.parent := by
    obtain ⟨_, shape, _⟩ := honest_proposal_views p E rho h.execution.toScheduleWellFormed
      (r + 1) b hb
    rw [shape]
    rfl
  have counts := honest_proposal_counts p E rho h.execution hΔ h.partialSynchrony
    h.acceptedRelay r sync headBound b hb reader hr
  have covers := GridCO.ghost_adopts_of_rooted_proposal_transport p.engine source.base target.base
    (r + 1) b b.parent tree A A (activeVoterTree_subset p target (r + 1) cert)
    sourceRoot targetRoot (proposalState_paths p rho (r + 1)).1 parent
    ⟨GridCO.block_preceq_self _, anchorParent⟩
    parentEq hslot
    (fun c hn hp => activeVoterTree_contains_plain p target (r + 1) cert
      (GridCO.proposal_path_mem_voterTree p.engine target.base (r + 1) _ b c _ _
        (honest_proposal_base_stored_at_head p E rho h.execution hΔ h.partialSynchrony
          (r + 1) b hb syncP headBound reader hr) rfl hslot targetClosed stored hn hp))
    (fun c hc he => honest_proposal_eligible_reflects_of_minority p E rho hΔ h.execution
      h.partialSynchrony h.acceptedRelay r headBound sync
      (recovery_proposal_detected_minority_quorum p E rho hΔ G h r syncVote headBound b hb) b hb
      reader hr c (activeVoterTree_subset p target (r + 1) cert hc) he)
    counts.1.symm (fun c _ _ => (counts.2.2 c).symm)
  have cover : Block.Preceq b (headData p rho (r + 1) reader).target := by
    change Block.Preceq b (headTarget p target (r + 1))
    simp only [headTarget, Bool.false_eq_true, ↓reduceIte, active, choice]
    rw [targetRootEq]
    exact covers
  have ordered := (paths_at_fold p
    (rho.events.filter (fun e => decide (e.time < voteTime p (r + 1)))) reader).2.2
      _ (headData_target_stored p rho (r + 1) reader)
  exact (GridCO.prefix_eq_of_slot_ge _ _ ordered cover (by
    rw [hslot]
    exact headData_target_slot p E rho h.execution.toScheduleWellFormed (r + 1) reader)).symm

/-- The original Draft 4.3 interface is retained. -/
theorem recovery_honest_proposal_head {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G : Time) (hG : 0 < G)
    (h : RecoveryRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho)
    (boundary : Slot) (sources : RecoverySourcesSupported p rho boundary)
    (r : Slot) (start : voteTime p boundary ≤ proposalTime p (r + 1))
    (syncVote : E.t_GST ≤ voteTime p r) (hh : gateTime p r ≤ rho.horizon)
    (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) b)
    (reader : V) (hr : reader ∈ rho.honest) :
    (headData p rho (r + 1) reader).target = b :=
  recovery_honest_proposal_head_quorum p E rho hΔ G hG (recovery_to_quorum p G E rho hG h) boundary
    sources r start syncVote hh b hb reader hr

end AvailableChain.SAPC
end
