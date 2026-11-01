module
public import AvailableChainSAPC.Proofs.ProposalDelivery
public import AvailableChainSAPC.Proofs.HeadEmission
public import AvailableChainGridCO.Proofs.Proposals

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

theorem clock_proposals (p : Params) {n : Nat} (st : State n) (t : Time) :
    (clock p st t).proposals = st.proposals := by
  unfold clock
  dsimp only
  split_ifs <;> simp only [gate, saveTimely]
  all_goals (try split_ifs) <;> rfl

/-- Both complete and projected proposal envelopes grow by append.
PC collection never rewrites their declared support metadata. -/
theorem process_proposals_prefix (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    st.proposals <+: (process p st o).proposals ∧
      st.base.proposals <+: (process p st o).base.proposals := by
  unfold process
  split
  · simp only [admitHead, collectPCs_proposals, receiveHead_proposals,
      collectPCs_base, receiveHead_base_proposals]
    exact ⟨List.prefix_rfl, List.prefix_rfl⟩
  · unfold admitProposal
    split
    · rename_i s b raw support c ha hp he
      simp only [collectPCs_proposals, receiveHeads_proposals, collectPCs_base,
        receiveHeads_base_proposals, (proposalEnters_data p st o b raw support he).1]
      exact ⟨List.prefix_append _ _, List.prefix_append _ _⟩
    · exact ⟨List.prefix_rfl, List.prefix_rfl⟩
  · split
    · simp only [collectPCs_proposals, collectPCs_base, installPC,
        receiveHeads_proposals, receiveHeads_base_proposals]
      exact ⟨List.prefix_rfl, List.prefix_rfl⟩
    · exact ⟨List.prefix_rfl, List.prefix_rfl⟩
  · exact ⟨List.prefix_rfl, List.prefix_rfl⟩

theorem stateBefore_proposals_prefix {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) {i j : Nat} (hij : i ≤ j) (v : V) :
    (Run.stateBefore (sapc p) rho i v).proposals <+:
        (Run.stateBefore (sapc p) rho j v).proposals ∧
      (Run.stateBefore (sapc p) rho i v).base.proposals <+:
        (Run.stateBefore (sapc p) rho j v).base.proposals := by
  set_option backward.isDefEq.respectTransparency false in
  constructor
  · exact stateBefore_field_prefix (P := sapc p) State.proposals
      (fun st t => by rw [show (sapc p).clock = clock p from rfl, clock_proposals])
      (fun st o => (process_proposals_prefix p st o).1) rho hij v
  · exact stateBefore_field_prefix (P := sapc p) (fun st => st.base.proposals)
      (fun st t => by
        change st.base.proposals <+: (clock p st t).base.proposals
        rw [clock_base_proposals])
      (fun st o => (process_proposals_prefix p st o).2) rho hij v

/-- The original signed proposal and its base projection are both
present at the actual HEAD choice, including for a sleeping reader. -/
theorem honest_proposal_stored_at_head {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (hnet : PartialSynchrony (sapc p) E rho) (s : Slot) (b : Block)
    (hb : HonestProposalAt E (sapcInterface p).toInterface rho s b)
    (hsync : E.t_GST ≤ proposalTime p s) (hh : voteTime p s ≤ rho.horizon)
    (reader : V) (hr : reader ∈ rho.honest) :
    let source := proposalState p rho s
    let raw := originalHeads source (GridCO.proposerView source.base s)
    let support := originalHeads source (GridCO.proposerSupportView source.base s)
    let o : Wire p.n := ⟨.proposer s, .proposal b raw support source.bestPC⟩
    o ∈ (headState p rho s reader).proposals ∧
      baseProposal o b raw support ∈ (headState p rho s reader).base.proposals := by
  set_option backward.isDefEq.respectTransparency false in
  dsimp only
  obtain ⟨_, _, hem⟩ := honest_proposal_views p E rho hx.toScheduleWellFormed s b hb
  obtain ⟨index, t, hlo, hhi, ha⟩ := synchronous_proposal_accepted p E rho hx hΔ hnet
    s hsync hh (rho.proposerOf s) reader hb.1 hr b _ _ _ hem
  obtain ⟨outer, hi, hhandles⟩ := ha.1
  have he := handles_proposal_direct p _ outer _ b _ _ _ rfl hhandles
  subst outer
  have hstored := (delivered_proposal_accepted p E rho hx hΔ index reader s b _ _ _
    t hlo hhi hi).2
  have hprefix := stateBefore_proposals_prefix p rho
    (Nat.succ_le_of_lt ((index_lt_read_length_iff hx.toScheduleWellFormed
      (voteTime p s - 1) hi).mpr (Int.le_sub_one_iff.mpr hhi))) reader
  simp only [headState, clock_proposals, clock_base_proposals,
    time_input_eq_event_prefix p E rho hx.toScheduleWellFormed]
  exact ⟨hprefix.1.subset hstored.2, hprefix.2.subset hstored.1⟩

theorem proposalState_baseArchived {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (s : Slot) : BaseArchived (proposalState p rho s) := by
  set_option backward.isDefEq.respectTransparency false in
  have h := baseArchived_at_fold p
    ((rho.events.filter (fun e => decide (e.time < proposalTime p s))) ++
      [.tick (rho.proposerOf s) (proposalTime p s)]) (rho.proposerOf s)
  simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil,
    World.step, Function.update_self] using! h

/-- The original-signature transport has exactly the ordinary projected
payload shape, so the existing SA proposal-merge proofs apply. -/
theorem originalHeads_base_heads {n : Nat} (st : State n) (h : BaseArchived st)
    (keys : List (GridCO.Wire n)) (hk : keys ⊆ st.base.votes) :
    (originalHeads st keys).map baseHead = keys.filterMap GridCO.toHead? := by
  have he := congrArg (List.filterMap GridCO.toHead?) (originalHeads_base_keys st h keys hk)
  simpa [List.filterMap_map, Function.comp_def, baseWire, GridCO.fromHead, GridCO.toHead?] using he

theorem honest_proposal_base_stored_at_head {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (hnet : PartialSynchrony (sapc p) E rho) (s : Slot) (b : Block)
    (hb : HonestProposalAt E (sapcInterface p).toInterface rho s b)
    (hsync : E.t_GST ≤ proposalTime p s) (hh : voteTime p s ≤ rho.horizon)
    (reader : V) (hr : reader ∈ rho.honest) :
    (⟨.proposer s, .proposal b
      ((GridCO.proposerView (proposalState p rho s).base s).filterMap GridCO.toHead?)
      ((GridCO.proposerSupportView (proposalState p rho s).base s).filterMap GridCO.toHead?)⟩ :
        GridCO.Wire p.n) ∈ (headState p rho s reader).base.proposals := by
  have h := (honest_proposal_stored_at_head p E rho hx hΔ hnet s b hb hsync hh reader hr).2
  dsimp only [baseProposal] at h
  rw [originalHeads_base_heads _ (proposalState_baseArchived p rho s)
      (GridCO.proposerView (proposalState p rho s).base s)
      (fun _ ho => (List.mem_filter.mp ho).1),
    originalHeads_base_heads _ (proposalState_baseArchived p rho s)
      (GridCO.proposerSupportView (proposalState p rho s).base s)
      (fun _ ho => (List.mem_filter.mp (List.mem_filter.mp ho).1).1)] at h
  exact h

/-- Every block already known to the proposer reaches the HEAD view.
The proof uses its accepted proposal source, including old dependencies. -/
theorem proposal_blocks_at_head {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hs : ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ)
    (hrelay : AcceptedObjectRelay (sapc p) E rho) (s : Slot)
    (hsync : E.t_GST ≤ proposalTime p s) (hh : voteTime p s ≤ rho.horizon)
    (hprop : rho.proposerOf s ∈ rho.honest) (reader : V) (hr : reader ∈ rho.honest)
    (b : Block) (hb : b ∈ (proposalState p rho s).base.blocks) :
    b ∈ (headState p rho s reader).base.blocks := by
  set_option backward.isDefEq.respectTransparency false in
  have he : max (proposalTime p s) E.t_GST + E.Δ = voteTime p s := by
    rw [max_eq_left hsync, hΔ]
    rfl
  simp only [proposalState, clock_blocks] at hb
  simp only [headState, clock_blocks]
  apply strict_block_relay p E rho hs (proposalTime p s) (voteTime p s)
    (by change 4 * p.Δ * (s : Time) ≤ 4 * p.Δ * (s : Time) + p.Δ
        linarith [p.deltaPos]) _ _ reader hprop hr b hb
  rw [← he]
  exact synchronous_relayBy p E rho (proposalTime p s) hrelay (by rwa [he])

/-- The shared SA merge proof includes every proposer raw key, with no
fault-cap premise and no synthetic outgoing signature. -/
theorem proposer_raw_subset_head_view {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (hnet : PartialSynchrony (sapc p) E rho) (s : Slot) (b : Block)
    (hb : HonestProposalAt E (sapcInterface p).toInterface rho s b)
    (hsync : E.t_GST ≤ proposalTime p s) (hh : voteTime p s ≤ rho.horizon)
    (reader : V) (hr : reader ∈ rho.honest) :
    GridCO.proposerView (proposalState p rho s).base s ⊆
      GridCO.voterView p.engine (headState p rho s reader).base s := by
  intro key hk
  exact GridCO.proposal_raw_mem_voterView p.engine _ _ s _ b _
    (honest_proposal_base_stored_at_head p E rho hx hΔ hnet s b hb hsync hh reader hr)
    rfl (honest_proposal_slot p E rho hx.toScheduleWellFormed s b hb).2.2 key hk

/-- The shared SA merge proof also includes every declared support key.
Its target path is relayed separately; no new support is declared. -/
theorem proposer_support_subset_head_view {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (hnet : PartialSynchrony (sapc p) E rho)
    (hrelay : AcceptedObjectRelay (sapc p) E rho) (s : Slot) (b : Block)
    (hb : HonestProposalAt E (sapcInterface p).toInterface rho s b)
    (hsync : E.t_GST ≤ proposalTime p s) (hh : voteTime p s ≤ rho.horizon)
    (reader : V) (hr : reader ∈ rho.honest) :
    GridCO.proposerSupportView (proposalState p rho s).base s ⊆
      GridCO.voterSupportView p.engine (headState p rho s reader).base s := by
  intro key hk
  have hres := (List.mem_filter.mp hk).2
  cases ht : GridCO.headTarget? key with
  | none => simp [GridCO.resolvedHead?, ht] at hres
  | some target =>
      have hknown : target ∈ (proposalState p rho s).base.blocks := by
        by_cases hm : target ∈ (proposalState p rho s).base.blocks
        · exact hm
        · simp [GridCO.resolvedHead?, ht, GridCO.resolveTarget, GridCO.resolutionTree,
            hm] at hres
      exact GridCO.proposal_support_mem_voterSupportView p.engine _ _ s _ b _
        (honest_proposal_base_stored_at_head p E rho hx hΔ hnet s b hb hsync hh reader hr)
        rfl (honest_proposal_slot p E rho hx.toScheduleWellFormed s b hb).2.2 key target hk ht
        (proposal_blocks_at_head p E rho hx.toScheduleWellFormed hΔ hrelay s hsync hh
          hb.1 reader hr target hknown)

end AvailableChain.SAPC
end
