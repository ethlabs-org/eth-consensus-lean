module
public import AvailableChainSAPC.Proofs.ProposalMerge
public import AvailableChainSAPC.Proofs.MergedReceipts

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

theorem proposalState_paths {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (s : Slot) :
    GridCO.StoredPrefixClosed (proposalState p rho s).base ∧
      Block.genesis ∈ (proposalState p rho s).base.blocks := by
  set_option backward.isDefEq.respectTransparency false in
  have h := paths_at_fold p (rho.events.filter (fun e => decide (e.time < proposalTime p s)))
    (rho.proposerOf s)
  simpa only [proposalState, GridCO.StoredPrefixClosed, clock_blocks] using! And.intro h.1 h.2.1

/-- The proposal parent is stored in both active and disabled mode. -/
theorem honest_proposal_parent_stored {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (s : Slot) (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho s b) :
    b.parent ∈ (proposalState p rho s).base.blocks := by
  obtain ⟨_, rfl, _⟩ := honest_proposal_views p E rho hs s b hb
  let events := rho.events.filter (fun e => decide (e.time < proposalTime p s)) ++
    [.tick (rho.proposerOf s) (proposalTime p s)]
  have he : (events.foldl World.step World.init) (rho.proposerOf s) =
      proposalState p rho s := by
    simp only [events, List.foldl_append, List.foldl_cons, List.foldl_nil,
      World.step, Function.update_self]
    rfl
  exact choice_mem_blocks p _ _ _ _ s _
    (he ▸ targetsStored_at_fold p events (rho.proposerOf s)) (proposalState_paths p rho s).2
    (List.Subset.refl _) (he ▸ installedPC_valid_at_fold p events (rho.proposerOf s))

/-- The ordinary merged tree contains only source blocks and the fresh
honest proposal. This uses actual receipt relay and complete paths. -/
theorem honest_proposal_tree_reflects {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hrelay : RelayBy p rho (freezeTime p r) (proposalTime p (r + 1)))
    (hh : freezeTime p r ≤ rho.horizon)
    (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) b)
    (reader : V) (hr : reader ∈ rho.honest) :
    ∀ c ∈ GridCO.voterTree p.engine (headState p rho (r + 1) reader).base (r + 1),
      c = b ∨ c ∈ (proposalState p rho (r + 1)).base.blocks := by
  have hs := hx.toScheduleWellFormed
  have hf := headState_base_frozenAt p E rho hs hΔ r reader hr hh
  intro c hc
  obtain ⟨_, hm⟩ := List.mem_filter.mp hc
  simp only [Nat.add_sub_cancel, hf] at hm
  rcases Bool.or_eq_true_iff.mp hm with frozen | proposal
  · apply Or.inr
    exact frozen_blocks_at_proposer p E rho hs r hrelay reader hr hb.1 c
      (List.mem_filter.mp (of_decide_eq_true frozen)).1
  · obtain ⟨target, ht, hct⟩ := List.any_eq_true.mp proposal
    obtain ⟨key, hk, hp⟩ := List.mem_filterMap.mp ht
    rw [headState_honest_base_proposal_unique p E rho hx (r + 1) b hb reader key hk] at hp
    have he : b = target := Option.some.inj hp
    subst target
    by_cases heq : c = b
    · exact Or.inl heq
    · apply Or.inr
      have hparent : Block.Preceq c b.parent := by
        cases b with
        | genesis => simp [Block.preceq] at hct; contradiction
        | node parent slot r_slot root =>
          simpa [Block.Preceq, Block.preceq, heq, Block.parent] using hct
      by_cases hg : c = .genesis
      · simpa only [hg] using (proposalState_paths p rho (r + 1)).2
      · exact (proposalState_paths p rho (r + 1)).1 b.parent
          (honest_proposal_parent_stored p E rho hs (r + 1) b hb) c hg hparent

/-- The shared SA proposal-walk interface holds for the ordinary part
of SA-PC's view. Raw list equality is not an input to this proof. -/
theorem proposalViewTransport_from_engine {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (hnet : PartialSynchrony (sapc p) E rho)
    (hrelay : AcceptedObjectRelay (sapc p) E rho) (r : Slot)
    (hsync : E.t_GST ≤ freezeTime p r) (hh : voteTime p (r + 1) ≤ rho.horizon)
    (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) b)
    (reader : V) (hr : reader ∈ rho.honest) :
    GridCO.ProposalViewTransport p.engine (proposalState p rho (r + 1)).base
      (headState p rho (r + 1) reader).base (r + 1) b := by
  have hfp : freezeTime p r < proposalTime p (r + 1) := by
    change 4 * p.Δ * (r : Time) + 3 * p.Δ < 4 * p.Δ * ((r + 1 : Nat) : Time)
    push_cast
    linarith [p.deltaPos]
  have hph : proposalTime p (r + 1) < voteTime p (r + 1) := by
    change 4 * p.Δ * ((r + 1 : Nat) : Time) <
      4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    linarith [p.deltaPos]
  have he : max (freezeTime p r) E.t_GST + E.Δ = proposalTime p (r + 1) := by
    rw [max_eq_left hsync, hΔ]
    change 4 * p.Δ * (r : Time) + 3 * p.Δ + p.Δ = 4 * p.Δ * ((r + 1 : Nat) : Time)
    push_cast
    ring
  have relay : RelayBy p rho (freezeTime p r) (proposalTime p (r + 1)) :=
    he ▸ synchronous_relayBy p E rho _ hrelay (he.symm ▸ hph.le.trans hh)
  have counts := honest_proposal_counts p E rho hx hΔ hnet hrelay r hsync hh b hb reader hr
  exact ⟨honest_proposal_tree_reflects p E rho hx hΔ r relay
    (hfp.le.trans (hph.le.trans hh)) b hb reader hr, counts.1.symm,
    fun c _ _ => (counts.2.2 c).symm⟩

/-- An active HEAD's score above f has a non-equivocating declared
source witness. Thus its path was already known to the proposer, even
above the fault cap. Private paths cannot add a new F4 candidate. -/
theorem honest_proposal_active_score_path {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (hnet : PartialSynchrony (sapc p) E rho)
    (hrelay : AcceptedObjectRelay (sapc p) E rho) (r : Slot)
    (hsync : E.t_GST ≤ freezeTime p r) (hh : voteTime p (r + 1) ≤ rho.horizon)
    (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) b)
    (reader : V) (hr : reader ∈ rho.honest)
    (hactive : capBroken p (headState p rho (r + 1) reader) = false) (c : Block)
    (hc : pcFaultCap p < GridCO.goldfishScore (headState p rho (r + 1) reader).base.blocks
      (GridCO.voterView p.engine (headState p rho (r + 1) reader).base (r + 1))
      (GridCO.voterSupportView p.engine (headState p rho (r + 1) reader).base (r + 1)) c) :
    c ∈ (proposalState p rho (r + 1)).base.blocks := by
  obtain ⟨i, o, target, ho, hi, he, ht, _, _, hct⟩ := active_score_witness p _ r _ _
    (headState_voterView_archived p rho (r + 1) reader)
    (by simpa using headState_voterView_label p rho (r + 1) reader) hactive c hc
  have hfp : freezeTime p r ≤ proposalTime p (r + 1) := by
    change 4 * p.Δ * (r : Time) + 3 * p.Δ ≤ 4 * p.Δ * ((r + 1 : Nat) : Time)
    push_cast
    linarith [p.deltaPos]
  have hsub := proposer_raw_subset_head_view p E rho hx hΔ hnet (r + 1) b hb
    (hsync.trans hfp) hh reader hr
  have hback := honest_proposal_support_back p E rho hx hΔ hrelay r hsync hh
    b hb reader hr o i hi ho
  have hs := hback.resolve_right (by
    intro h
    have := GridCO.equivocates_mono _ _ i hsub h
    simp [he] at this)
  have hresolved := (List.mem_filter.mp hs).2
  have hknown : target ∈ (proposalState p rho (r + 1)).base.blocks := by
    by_cases hm : target ∈ (proposalState p rho (r + 1)).base.blocks
    · exact hm
    · simp [GridCO.resolvedHead?, ht, GridCO.resolveTarget, GridCO.resolutionTree,
        hm] at hresolved
  by_cases hg : c = .genesis
  · simpa only [hg] using (proposalState_paths p rho (r + 1)).2
  · exact (proposalState_paths p rho (r + 1)).1 target hknown c hg hct

end AvailableChain.SAPC
end
