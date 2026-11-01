module
public import AvailableChainSAPC.Proofs.ProposalOrigins
public import AvailableChainSAPC.Proofs.ProposalCounts
public import AvailableChainSAPC.Proofs.TimelyTransfer

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

private theorem freeze_lt_proposal (p : Params) (r : Slot) :
    freezeTime p r < proposalTime p (r + 1) := by
  change 4 * p.Δ * (r : Time) + 3 * p.Δ < 4 * p.Δ * ((r + 1 : Nat) : Time)
  push_cast
  linarith [p.deltaPos]

private theorem proposal_lt_head (p : Params) (r : Slot) :
    proposalTime p r < voteTime p r := by
  change 4 * p.Δ * (r : Time) < 4 * p.Δ * (r : Time) + p.Δ
  linarith [p.deltaPos]

private theorem proposal_relay {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (hrelay : AcceptedObjectRelay (sapc p) E rho) (r : Slot)
    (hsync : E.t_GST ≤ freezeTime p r) (hh : voteTime p (r + 1) ≤ rho.horizon) :
    RelayBy p rho (freezeTime p r) (proposalTime p (r + 1)) := by
  have he : max (freezeTime p r) E.t_GST + E.Δ = proposalTime p (r + 1) := by
    rw [max_eq_left hsync, hΔ]
    change 4 * p.Δ * (r : Time) + 3 * p.Δ + p.Δ = 4 * p.Δ * ((r + 1 : Nat) : Time)
    push_cast
    ring
  exact he ▸ synchronous_relayBy p E rho _ hrelay
    (he.symm ▸ (proposal_lt_head p (r + 1)).le.trans hh)

/-- Frozen raw keys reach the proposer before its action, either as the
same key or as two-target evidence for the same seat. -/
theorem frozen_raw_at_proposer {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (hrelay : RelayBy p rho (freezeTime p r) (proposalTime p (r + 1)))
    (source : V) (hsource : source ∈ rho.honest)
    (hprop : rho.proposerOf (r + 1) ∈ rho.honest)
    (o : GridCO.Wire p.n) (i : Fin p.n) (hi : GridCO.headSeat? o = some i)
    (ho : o ∈ GridCO.votesAt (Run.stateBeforeTime (sapc p) rho (freezeTime p r) source).base r) :
    o ∈ GridCO.proposerView (proposalState p rho (r + 1)).base (r + 1) ∨
      GridCO.equivocates
        (GridCO.proposerView (proposalState p rho (r + 1)).base (r + 1)) i = true := by
  have hl : GridCO.headLabel? o = some r := by simpa using (List.mem_filter.mp ho).2
  obtain ⟨target, rfl⟩ := GridCO.head_wire_shape o r i hl hi
  obtain ⟨data, hm, ht⟩ := baseArchived_head _ (baseArchived_at_fold p _ source) r i target
    (List.mem_filter.mp ho).1
  have hread : Run.stateBeforeTime (sapc p) rho (freezeTime p r) =
      Run.readAt (sapc p) rho (freezeTime p r - 1) := by
    simp only [Run.stateBeforeTime, Run.readAt, ← Int.le_sub_one_iff]
  change (⟨.seat r i, data⟩ : HeadWire p.n) ∈
    (Run.stateBeforeTime (sapc p) rho (freezeTime p r) source).receivedHeads at hm
  rw [hread] at hm
  have hz : 0 < proposalTime p (r + 1) := by
    change 0 < 4 * p.Δ * ((r + 1 : Nat) : Time)
    have := p.deltaPos
    positivity
  have hd : proposalTime p (r + 1) ≤ proposalTime p (r + 2) := by
    change 4 * p.Δ * ((r + 1 : Nat) : Time) ≤ 4 * p.Δ * ((r + 2 : Nat) : Time)
    push_cast
    linarith [p.deltaPos]
  have h := read_head_base_relay p E rho hs (freezeTime p r - 1) (proposalTime p (r + 1))
    ((sub_le_self _ (by norm_num)).trans_lt (freeze_lt_proposal p r)) hz r hd
    (fun v hv j obj t ht ha w hw hn =>
      hrelay v hv j obj t (ht.trans (sub_le_self _ (by norm_num))) ha w hw hn)
    source (rho.proposerOf (r + 1)) hsource hprop i data hm
  have hvotes := congrArg (fun d => d.2.2.1)
    (clock_receiptData p (Run.stateBeforeTime (sapc p) rho (proposalTime p (r + 1))
      (rho.proposerOf (r + 1))) (proposalTime p (r + 1)))
  change (clock p (Run.stateBeforeTime (sapc p) rho (proposalTime p (r + 1))
    (rho.proposerOf (r + 1))) (proposalTime p (r + 1))).base.votes = _ at hvotes
  simpa only [proposalState, GridCO.proposerView, Nat.add_sub_cancel, GridCO.votesAt,
    hvotes, baseWire, baseHead, GridCO.fromHead, ht] using! h

theorem frozen_blocks_at_proposer {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (hrelay : RelayBy p rho (freezeTime p r) (proposalTime p (r + 1)))
    (source : V) (hsource : source ∈ rho.honest)
    (hprop : rho.proposerOf (r + 1) ∈ rho.honest) (b : Block)
    (hb : b ∈ (Run.stateBeforeTime (sapc p) rho (freezeTime p r) source).base.blocks) :
    b ∈ (proposalState p rho (r + 1)).base.blocks := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [proposalState, clock_blocks]
  exact strict_block_relay p E rho hs _ _ (freeze_lt_proposal p r).le
    hrelay source (rho.proposerOf (r + 1)) hsource hprop b hb

/-- Frozen declared support also reaches the proposer. A raw key is
never promoted to support merely because the voter resolves it later. -/
theorem frozen_support_at_proposer {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (hrelay : RelayBy p rho (freezeTime p r) (proposalTime p (r + 1)))
    (source : V) (hsource : source ∈ rho.honest)
    (hprop : rho.proposerOf (r + 1) ∈ rho.honest)
    (o : GridCO.Wire p.n) (i : Fin p.n) (hi : GridCO.headSeat? o = some i)
    (ho : o ∈ (GridCO.freezeView p.engine
      (Run.stateBeforeTime (sapc p) rho (freezeTime p r) source).base r).2.1) :
    o ∈ GridCO.proposerSupportView (proposalState p rho (r + 1)).base (r + 1) ∨
      GridCO.equivocates
        (GridCO.proposerView (proposalState p rho (r + 1)).base (r + 1)) i = true := by
  obtain ⟨hraw, hresolved⟩ := List.mem_filter.mp ho
  rcases frozen_raw_at_proposer p E rho hs r hrelay source hsource hprop o i hi hraw with hk | he
  · apply Or.inl
    apply List.mem_filter.mpr
    refine ⟨hk, ?_⟩
    cases ht : GridCO.headTarget? o with
    | none => simp [GridCO.resolvedBefore_block, ht] at hresolved
    | some target =>
      have hl : GridCO.headLabel? o = some r := by simpa using (List.mem_filter.mp hraw).2
      simp only [GridCO.resolvedBefore_block, ht, hl, Option.getD_some, Bool.and_eq_true,
        decide_eq_true_eq, GridCO.blockKnown] at hresolved
      have hb := frozen_blocks_at_proposer p E rho hs r hrelay source hsource hprop
        target hresolved.1.1.1
      simp [GridCO.resolvedHead?, ht, GridCO.resolveTarget, GridCO.resolutionTree,
        hb, hresolved.1.1.2]
  · exact Or.inr he

private theorem head_roundtrip_mem {n : Nat} (xs : List (GridCO.Wire n)) (o : GridCO.Wire n)
    (h : o ∈ (xs.filterMap GridCO.toHead?).map GridCO.fromHead) : o ∈ xs := by
  obtain ⟨head, hm, he⟩ := List.mem_map.mp h
  obtain ⟨key, hk, ht⟩ := List.mem_filterMap.mp hm
  have hr : GridCO.fromHead head = key := by
    cases key with
    | mk auth payload =>
      cases payload with
      | head b => simp only [GridCO.toHead?, Option.some.injEq] at ht; rw [← ht]; rfl
      | proposal b raw support => simp [GridCO.toHead?] at ht
  exact (hr.symm.trans he) ▸ hk

/-- The merged raw view has no new non-equivocating key. Each carried
key is from the unique honest proposal; each frozen key has relayed. -/
theorem honest_proposal_raw_back {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (hrelay : AcceptedObjectRelay (sapc p) E rho) (r : Slot)
    (hsync : E.t_GST ≤ freezeTime p r) (hh : voteTime p (r + 1) ≤ rho.horizon)
    (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) b)
    (reader : V) (hr : reader ∈ rho.honest) (o : GridCO.Wire p.n) (i : Fin p.n)
    (hi : GridCO.headSeat? o = some i)
    (ho : o ∈ GridCO.voterView p.engine (headState p rho (r + 1) reader).base (r + 1)) :
    o ∈ GridCO.proposerView (proposalState p rho (r + 1)).base (r + 1) ∨
      GridCO.equivocates
        (GridCO.proposerView (proposalState p rho (r + 1)).base (r + 1)) i = true := by
  have hs := hx.toScheduleWellFormed
  have hf := headState_base_frozenAt p E rho hs hΔ r reader hr
    ((freeze_lt_proposal p r).le.trans ((proposal_lt_head p (r + 1)).le.trans hh))
  simp only [GridCO.voterView, Nat.add_sub_cancel, hf] at ho
  rcases List.mem_append.mp (List.mem_eraseDups.mp ho) with frozen | carried
  · rw [(base_freezeView_at_input p E rho hs r reader).1] at frozen
    exact frozen_raw_at_proposer p E rho hs r (proposal_relay p E rho hΔ hrelay r hsync hh)
      reader hr hb.1 o i hi frozen
  · obtain ⟨hm, _⟩ := List.mem_filter.mp carried
    obtain ⟨key, hk, hkey⟩ := List.mem_flatMap.mp hm
    rw [headState_honest_base_proposal_unique p E rho hx (r + 1) b hb reader key hk] at hkey
    exact Or.inl (head_roundtrip_mem _ o hkey)

theorem honest_proposal_support_back {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (hrelay : AcceptedObjectRelay (sapc p) E rho) (r : Slot)
    (hsync : E.t_GST ≤ freezeTime p r) (hh : voteTime p (r + 1) ≤ rho.horizon)
    (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) b)
    (reader : V) (hr : reader ∈ rho.honest) (o : GridCO.Wire p.n) (i : Fin p.n)
    (hi : GridCO.headSeat? o = some i)
    (ho : o ∈ GridCO.voterSupportView p.engine (headState p rho (r + 1) reader).base (r + 1)) :
    o ∈ GridCO.proposerSupportView (proposalState p rho (r + 1)).base (r + 1) ∨
      GridCO.equivocates
        (GridCO.proposerView (proposalState p rho (r + 1)).base (r + 1)) i = true := by
  have hs := hx.toScheduleWellFormed
  have hf := headState_base_frozenAt p E rho hs hΔ r reader hr
    ((freeze_lt_proposal p r).le.trans ((proposal_lt_head p (r + 1)).le.trans hh))
  simp only [GridCO.voterSupportView, Nat.add_sub_cancel, hf] at ho
  rcases List.mem_append.mp (List.mem_eraseDups.mp ho) with frozen | carried
  · exact frozen_support_at_proposer p E rho hs r (proposal_relay p E rho hΔ hrelay r hsync hh)
      reader hr hb.1 o i hi frozen
  · obtain ⟨hm, _⟩ := List.mem_filter.mp carried
    obtain ⟨key, hk, hkey⟩ := List.mem_flatMap.mp hm
    rw [headState_honest_base_proposal_unique p E rho hx (r + 1) b hb reader key hk] at hkey
    exact Or.inl (head_roundtrip_mem _ o hkey)

/-- The actual proposer and HEAD views have common participant counts,
equivocation tests, and scores on every block, in either mode. -/
theorem honest_proposal_counts {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hΔ : E.Δ = p.Δ)
    (hnet : PartialSynchrony (sapc p) E rho)
    (hrelay : AcceptedObjectRelay (sapc p) E rho) (r : Slot)
    (hsync : E.t_GST ≤ freezeTime p r) (hh : voteTime p (r + 1) ≤ rho.horizon)
    (b : Block) (hb : HonestProposalAt E (sapcInterface p).toInterface rho (r + 1) b)
    (reader : V) (hr : reader ∈ rho.honest) :
    let source := (proposalState p rho (r + 1)).base
    let target := (headState p rho (r + 1) reader).base
    GridCO.voterCount (GridCO.proposerView source (r + 1)) =
        GridCO.voterCount (GridCO.voterView p.engine target (r + 1)) ∧
      (∀ i, GridCO.equivocates (GridCO.proposerView source (r + 1)) i =
        GridCO.equivocates (GridCO.voterView p.engine target (r + 1)) i) ∧
      ∀ c, GridCO.goldfishScore source.blocks (GridCO.proposerView source (r + 1))
          (GridCO.proposerSupportView source (r + 1)) c =
        GridCO.goldfishScore target.blocks (GridCO.voterView p.engine target (r + 1))
          (GridCO.voterSupportView p.engine target (r + 1)) c := by
  dsimp only
  have ht := hsync.trans (freeze_lt_proposal p r).le
  have hraw := proposer_raw_subset_head_view p E rho hx hΔ hnet (r + 1) b hb ht hh reader hr
  have hback := fun o ho i hi =>
    honest_proposal_raw_back p E rho hx hΔ hrelay r hsync hh b hb reader hr o i hi ho
  refine ⟨voterCount_eq_of_mem_or_equivocates _ _ hraw hback,
    equivocates_eq_of_mem_or_equivocates _ _ hraw hback, ?_⟩
  intro c
  apply goldfishScore_eq_of_mem_or_equivocates _ _ _ _ _ _ hraw hback
    (proposer_support_subset_head_view p E rho hx hΔ hnet hrelay (r + 1) b hb ht hh reader hr)
    (fun o ho i hi =>
      honest_proposal_support_back p E rho hx hΔ hrelay r hsync hh b hb reader hr o i hi ho)
  intro o ho target htgt
  have hres := (List.mem_filter.mp ho).2
  have hknown : target ∈ (proposalState p rho (r + 1)).base.blocks := by
    by_cases hm : target ∈ (proposalState p rho (r + 1)).base.blocks
    · exact hm
    · simp [GridCO.resolvedHead?, htgt, GridCO.resolveTarget, GridCO.resolutionTree,
        hm] at hres
  exact iff_of_true hknown (proposal_blocks_at_head p E rho hx.toScheduleWellFormed hΔ hrelay
    (r + 1) ht hh hb.1 reader hr target hknown)

end AvailableChain.SAPC
end
