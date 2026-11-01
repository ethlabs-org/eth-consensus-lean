module
public import AvailableChainSAPC.Proofs.ProposalEligibility

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- A disabled HEAD chooses the exact honest proposal, even if its
proposer was still active. The ordinary parent and finite-root proof
allow direct use of the shared SA proposal-adoption theorem. -/
theorem clean_disabled_honest_proposal_head {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (r : Slot) (hh : gateTime p r ≤ rho.horizon)
    (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) b)
    (reader : V) (hr : reader ∈ rho.honest)
    (disabled : capBroken p (headState p rho (r + 1) reader) = true) :
    (headData p rho (r + 1) reader).target = b := by
  set_option backward.isDefEq.respectTransparency false in
  have headBound : voteTime p (r + 1) ≤ rho.horizon := by
    apply le_trans _ hh
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ ≤
      4 * p.Δ * (r : Time) + 6 * p.Δ
    push_cast
    linarith [p.deltaPos]
  have sync : E.t_GST ≤ freezeTime p r := by
    rw [hs.gst_zero]
    change 0 ≤ 4 * p.Δ * (r : Time) + 3 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have syncP : E.t_GST ≤ proposalTime p (r + 1) := by
    rw [hs.gst_zero]
    change 0 ≤ 4 * p.Δ * ((r + 1 : Nat) : Time)
    nlinarith [p.deltaPos, Int.natCast_nonneg (r + 1)]
  have parent := clean_proposal_parent_ordinary p E rho hΔ t₀ hs r hh b hb
  have roots := (clean_roots_at_ordinary_proposal p E rho hΔ t₀ hs r hh b hb).2 reader hr
  rw [← parent] at roots
  have hslot := (honest_proposal_slot p E rho hs.execution.toScheduleWellFormed
    (r + 1) b hb).2.2
  have sourceRoot : GridCO.RootInjectiveBelow (proposalState p rho (r + 1)).base.blocks := by
    simpa only [proposalState, clock_blocks] using! time_input_rootInjectiveBelow p E rho
      hs.execution.toScheduleWellFormed hs.rootInjective (proposalTime p (r + 1)) _
  have targetRoot : GridCO.RootInjectiveBelow (headState p rho (r + 1) reader).base.blocks := by
    simpa only [headState, clock_blocks] using! time_input_rootInjectiveBelow p E rho
      hs.execution.toScheduleWellFormed hs.rootInjective (voteTime p (r + 1)) reader
  have stored : b ∈ (headState p rho (r + 1) reader).base.blocks := by
    have path := honest_proposal_path_before_head p E rho hs.execution hΔ hs.partialSynchrony
      (r + 1) b hb syncP headBound reader hr _ (le_refl _)
    simp only [headState, clock_blocks]
    cases b with
    | genesis => exact of_decide_eq_true (Bool.and_eq_true_iff.mp path).1
    | node parent slot r_slot root =>
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp path).1).1
  have targetClosed : GridCO.StoredPrefixClosed (headState p rho (r + 1) reader).base := by
    simpa only [headState, GridCO.StoredPrefixClosed, clock_blocks] using!
      (paths_at_fold p
        (rho.events.filter (fun e => decide (e.time < voteTime p (r + 1)))) reader).1
  have parentEq : b.parent? = some b.parent := by
    obtain ⟨_, shape, _⟩ := honest_proposal_views p E rho hs.execution.toScheduleWellFormed
      (r + 1) b hb
    rw [shape]
    rfl
  have covers := GridCO.forkChoice_adopts_stored_proposal p.engine
    (proposalState p rho (r + 1)).base (headState p rho (r + 1) reader).base (r + 1) b b.parent
    _ _ _ (honest_proposal_base_stored_at_head p E rho hs.execution hΔ hs.partialSynchrony
      (r + 1) b hb syncP headBound reader hr) rfl stored hslot sourceRoot targetRoot
    (proposalState_paths p rho (r + 1)).1 targetClosed parent.symm roots parentEq
    (proposalViewTransport_from_engine p E rho hs.execution hΔ hs.partialSynchrony
      hs.acceptedRelay r sync headBound b hb reader hr)
  have cover : Block.Preceq b (headData p rho (r + 1) reader).target := by
    simpa only [headData, headTarget, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      decide_false, Bool.false_eq_true, ↓reduceIte, disabled, choice] using! covers
  have ordered := (paths_at_fold p
    (rho.events.filter (fun e => decide (e.time < voteTime p (r + 1)))) reader).2.2
      _ (headData_target_stored p rho (r + 1) reader)
  exact (GridCO.prefix_eq_of_slot_ge _ _ ordered cover (by
    rw [hslot]
    exact headData_target_slot p E rho hs.execution.toScheduleWellFormed (r + 1) reader)).symm

/-- The common preliminary anchor and the finite root are on the
ordinary proposal path. Eligible-path reflection then transports the
shared SA adoption proof through the enlarged active tree. -/
theorem clean_active_honest_proposal_head {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (r : Slot) (hh : gateTime p r ≤ rho.horizon)
    (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) b)
    (reader : V) (hr : reader ∈ rho.honest)
    (active : capBroken p (headState p rho (r + 1) reader) = false) :
    (headData p rho (r + 1) reader).target = b := by
  set_option backward.isDefEq.respectTransparency false in
  let source := proposalState p rho (r + 1)
  let target := headState p rho (r + 1) reader
  let cert := selectedPC p target (r + 1)
  let tree := activeVoterTree p target (r + 1) cert
  have headBound : voteTime p (r + 1) ≤ rho.horizon := by
    apply le_trans _ hh
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ ≤
      4 * p.Δ * (r : Time) + 6 * p.Δ
    push_cast
    linarith [p.deltaPos]
  have sync : E.t_GST ≤ freezeTime p r := by
    rw [hs.gst_zero]
    change 0 ≤ 4 * p.Δ * (r : Time) + 3 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have syncP : E.t_GST ≤ proposalTime p (r + 1) := by
    rw [hs.gst_zero]
    change 0 ≤ 4 * p.Δ * ((r + 1 : Nat) : Time)
    nlinarith [p.deltaPos, Int.natCast_nonneg (r + 1)]
  have parent := clean_proposal_parent_ordinary p E rho hΔ t₀ hs r hh b hb
  have roots := (clean_roots_at_ordinary_proposal p E rho hΔ t₀ hs r hh b hb).2 reader hr
  rw [← parent] at roots
  have sourceActive := honest_proposal_active_source p E rho hs.execution.toScheduleWellFormed
    hΔ hs.acceptedRelay (r + 1) syncP headBound hb.1 reader hr active
  have anchor : Block.Preceq
      (preliminaryAnchor (floor p target tree (GridCO.voterView p.engine target.base (r + 1))
        (GridCO.voterSupportView p.engine target.base (r + 1)) (r + 1)) cert) b.parent := by
    rw [← clean_honest_proposal_anchor_eq p E rho hΔ t₀ hs r headBound b hb reader hr active]
    have floorBelow : Block.Preceq
        (floor p source source.base.blocks (GridCO.proposerView source.base (r + 1))
          (GridCO.proposerSupportView source.base (r + 1)) (r + 1)) b.parent := by
      rw [parent]
      by_cases hg : floor p source source.base.blocks (GridCO.proposerView source.base (r + 1))
          (GridCO.proposerSupportView source.base (r + 1)) (r + 1) = .genesis
      · rw [hg]; exact GridCO.genesis_prefix _
      · exact (floor_properties p source _ _ _ (r + 1) hg).2.1
    cases selected : source.bestPC with
    | none => exact floorBelow
    | some c =>
      have pcBelow := clean_proposal_PC_at_ordinary_walk p E rho hΔ t₀ hs r headBound
        b hb sourceActive c selected
      rw [← parent] at pcBelow
      simp only [preliminaryAnchor]
      split <;> assumption
  have mandatory : Block.Preceq (mandatoryRoot (GridCO.liveRoot target.base)
      (preliminaryAnchor (floor p target tree (GridCO.voterView p.engine target.base (r + 1))
        (GridCO.voterSupportView p.engine target.base (r + 1)) (r + 1)) cert)) b.parent := by
    unfold mandatoryRoot
    split <;> assumption
  have hslot := (honest_proposal_slot p E rho hs.execution.toScheduleWellFormed
    (r + 1) b hb).2.2
  have sourceRoot : GridCO.RootInjectiveBelow source.base.blocks := by
    simpa only [source, proposalState, clock_blocks] using! time_input_rootInjectiveBelow p E rho
      hs.execution.toScheduleWellFormed hs.rootInjective (proposalTime p (r + 1)) _
  have targetRoot : GridCO.RootInjectiveBelow target.base.blocks := by
    simpa only [target, headState, clock_blocks] using! time_input_rootInjectiveBelow p E rho
      hs.execution.toScheduleWellFormed hs.rootInjective (voteTime p (r + 1)) reader
  have stored : b ∈ target.base.blocks := by
    have path := honest_proposal_path_before_head p E rho hs.execution hΔ hs.partialSynchrony
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
    obtain ⟨_, shape, _⟩ := honest_proposal_views p E rho hs.execution.toScheduleWellFormed
      (r + 1) b hb
    rw [shape]
    rfl
  have counts := honest_proposal_counts p E rho hs.execution hΔ hs.partialSynchrony
    hs.acceptedRelay r sync headBound b hb reader hr
  have covers := GridCO.ghost_adopts_of_eligible_proposal_transport p.engine source.base target.base
    (r + 1) b b.parent tree _ (activeVoterTree_subset p target (r + 1) cert)
    sourceRoot targetRoot (proposalState_paths p rho (r + 1)).1 parent.symm mandatory
    parentEq hslot
    (fun c hn hp => activeVoterTree_contains_plain p target (r + 1) cert
      (GridCO.proposal_path_mem_voterTree p.engine target.base (r + 1) _ b c _ _
        (honest_proposal_base_stored_at_head p E rho hs.execution hΔ hs.partialSynchrony
          (r + 1) b hb syncP headBound reader hr) rfl hslot targetClosed stored hn hp))
    (fun c hc he => clean_honest_proposal_eligible_reflects p E rho hΔ t₀ hs r headBound b hb
      reader hr c (activeVoterTree_subset p target (r + 1) cert hc) he)
    counts.1.symm (fun c _ _ => (counts.2.2 c).symm)
  have cover : Block.Preceq b (headData p rho (r + 1) reader).target := by
    simpa only [headData, headTarget, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
      decide_false, Bool.false_eq_true, ↓reduceIte, active, choice] using! covers
  have ordered := (paths_at_fold p
    (rho.events.filter (fun e => decide (e.time < voteTime p (r + 1)))) reader).2.2
      _ (headData_target_stored p rho (r + 1) reader)
  exact (GridCO.prefix_eq_of_slot_ge _ _ ordered cover (by
    rw [hslot]
    exact headData_target_slot p E rho hs.execution.toScheduleWellFormed (r + 1) reader)).symm

/-- Every honest HEAD chooses the exact honest proposal in either mode.
No fault cap or equality of raw key sets is required. -/
theorem clean_honest_proposal_head {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (r : Slot) (hh : gateTime p r ≤ rho.horizon)
    (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) b)
    (reader : V) (hr : reader ∈ rho.honest) :
    (headData p rho (r + 1) reader).target = b := by
  cases mode : capBroken p (headState p rho (r + 1) reader) with
  | false => exact clean_active_honest_proposal_head p E rho hΔ t₀ hs r hh b hb reader hr mode
  | true => exact clean_disabled_honest_proposal_head p E rho hΔ t₀ hs r hh b hb reader hr mode

end AvailableChain.SAPC
end
