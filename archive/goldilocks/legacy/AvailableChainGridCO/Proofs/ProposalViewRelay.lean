module
public import AvailableChainGridCO.Proofs.ProposalViews

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Ready receipt relay stores a checked block before the proposal. -/
theorem accepted_block_before_ready_proposal {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hx : ExecutionValid (gridCO p) E rho) (hΔ : E.Δ = p.Δ) (s : Slot)
    (hready : ProposalRelayReady p E rho s) (hh : proposalTime p s ≤ rho.horizon)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (index : Nat) (o : Wire p.n) (t : Time)
    {B : Block} {raw support : List (HeadWire p.n)} (hp : o.payload = .proposal B raw support)
    (ha : Run.acceptsAt (gridCO p) rho index source o t)
    (hd : t + E.Δ ≤ proposalTime p s) :
    ∃ j e, rho.events[j]? = some e ∧ e.time < proposalTime p s ∧
      processed (Run.stateBefore (gridCO p) rho (j + 1) reader) o = true := by
  obtain ⟨parent, hi, _⟩ := ha.1
  by_cases hk : processed (Run.stateBefore (gridCO p) rho (index + 1) reader) o = true
  · exact ⟨index, .deliver source parent t, hi,
      by change t < proposalTime p s; linarith [E.Δ_pos], hk⟩
  obtain ⟨j, t', hj, htt, ht⟩ := handled_before_proposal_of_ready p E rho s hready hh
    source reader hs hr index o t ha (Bool.eq_false_iff.mpr hk) hd
    (fun u _ => proposal_not_excluded p rho reader o B raw support hp u)
  have hm := accepted_proposal_handled_stored p E rho hx hΔ index j source reader
    o B raw support t t' hp ha hj htt
  obtain ⟨parent', he, _⟩ := hj
  exact ⟨j, .deliver reader parent' t', he, ht,
    by simpa [processed, hp, blockKnown] using hm⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A block stored at least Δ before the proposal reaches the proposer
before it acts. This includes old blocks from an arbitrary prefix. -/
theorem stored_block_before_ready_proposal {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hx : ExecutionValid (gridCO p) E rho) (hΔ : E.Δ = p.Δ)
    (s : Slot) (hready : ProposalRelayReady p E rho s)
    (hh : proposalTime p s ≤ rho.horizon)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (cut : Time) (hd : cut + E.Δ ≤ proposalTime p s) (B : Block)
    (hm : B ∈ (Run.stateBeforeTime (gridCO p) rho cut source).blocks) :
    B ∈ (Run.stateBeforeTime (gridCO p) rho (proposalTime p s) reader).blocks := by
  have hsched := hx.toScheduleWellFormed
  by_cases hn : B = .genesis
  · subst B; exact (genesis_stored_at_time p E rho hsched _ reader).1
  rw [time_input_eq_event_prefix p E rho hsched] at hm
  obtain ⟨index, hil, t, o, raw, support, hi, hp, ha⟩ :=
    stored_block_accepted p rho _ source B hn hm
  have ht : t < cut := Int.le_sub_one_iff.mp ((index_lt_read_length_iff hsched (cut - 1) hi).mp hil)
  obtain ⟨j, e, hj, he, hk⟩ := accepted_block_before_ready_proposal p E rho hx hΔ s hready hh
    source reader hs hr index o t hp ha (by linarith)
  exact (stored_block_stamp_before_cut p E rho hsched hj
    (by simpa [processed, hp, blockKnown] using hk) he (le_refl _)).1

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A frozen raw HEAD reaches the proposer or exposes its seat as an
equivocator. No honesty premise is imposed on that seat. -/
theorem stored_head_before_ready_proposal {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hsched : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (hready : ProposalRelayReady p E rho (r + 1))
    (hh : proposalTime p (r + 1) ≤ rho.horizon)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (cut : Time) (hd : cut + E.Δ ≤ proposalTime p (r + 1)) (o : Wire p.n)
    (target : Block) (hp : o.payload = .head target) (hl : headLabel? o = some r)
    (hm : o ∈ (Run.stateBeforeTime (gridCO p) rho cut source).votes) :
    ∀ i, headSeat? o = some i →
      o ∈ votesAt (Run.stateBeforeTime (gridCO p) rho (proposalTime p (r + 1)) reader) r ∨
      equivocates (votesAt (Run.stateBeforeTime (gridCO p) rho
        (proposalTime p (r + 1)) reader) r) i = true := by
  rw [time_input_eq_event_prefix p E rho hsched] at hm
  obtain ⟨index, hil, t, ha, _⟩ := stored_head_stamp_source p rho _ source o _
    (stampVote_mem_of_stored _ (run_receiptStamped p rho _ source) o hm)
  obtain ⟨parent, hi, _⟩ := ha.1
  have ht : t < cut := Int.le_sub_one_iff.mp
    ((index_lt_read_length_iff hsched (cut - 1) hi).mp hil)
  intro i hseat
  have he : o = ⟨.seat r i, .head target⟩ := by
    cases o with
    | mk auth payload => cases auth <;> cases payload <;> simp_all [headLabel?, headSeat?]
  subst o
  have hwin : proposalTime p (r + 1) ≤ proposalTime p (r + 2) := by
    dsimp [proposalTime]; nlinarith [p.deltaPos]
  rcases head_not_excluded_or_equivocates p E rho hsched reader r i target _ hwin with
    hx | ⟨u, hu, heq⟩
  swap
  · -- The reader's votes only grow up to the proposal read.
    have hsub : votesAt (Run.stateBeforeTime (gridCO p) rho u reader) r ⊆
        votesAt (Run.stateBeforeTime (gridCO p) rho (proposalTime p (r + 1)) reader) r := by
      rw [time_input_eq_event_prefix p E rho hsched, time_input_eq_event_prefix p E rho hsched]
      intro q hq
      obtain ⟨hm, hl⟩ := List.mem_filter.mp hq
      exact List.mem_filter.mpr ⟨(stateBefore_receiptPrefix p rho
        (read_length_mono _ _ (by linarith)) reader).votes.subset hm, hl⟩
    exact Or.inr (equivocates_mono _ _ i hsub heq)
  have hrec := accepted_head_receipt_before p E rho hsched hΔ index source reader r i target
    t (proposalTime p (r + 1)) (proposalTime p (r + 1)) ha
    (by linarith [E.Δ_pos]) (le_refl _) hwin (fun hm => by
      obtain ⟨j, t', hj, htt, ht'⟩ := handled_before_proposal_of_ready p E rho (r + 1)
        hready hh source reader hs hr index _ t ha hm (by linarith) hx
      exact ⟨t', htt, ht', j, hj⟩)
  rcases hrec with hm | he
  · exact Or.inl (List.mem_filter.mp hm).1
  · exact Or.inr (equivocates_mono _ _ i (fun q hq => (List.mem_filter.mp hq).1) he)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The proposer clock preserves all block and vote receipts. -/
theorem proposalState_receiptData {V : Type} [DecidableEq V]
    (p : Params) (rho : Run V (gridCO p)) (s : Slot) :
    receiptData (proposalState p rho s) = receiptData
      (Run.stateBeforeTime (gridCO p) rho (proposalTime p s) (rho.proposerOf s)) :=
  clock_receiptData p _ _

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The actual saved freeze needs only the schedule and a finite horizon.
It does not require the preceding label to start after GST. -/
theorem nextHeadState_frozenAt_of_schedule {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (reader : V) (hr : reader ∈ rho.honest)
    (hh : freezeTime p r ≤ rho.horizon) :
    frozenAt (nextHeadState p rho r reader) r =
      some (freezeView p (Run.stateBeforeTime (gridCO p) rho (freezeTime p r) reader) r) := by
  apply clock_frozenAt_of_some p _ (run_time_receiptStamped p rho _ reader)
  exact frozenAt_after_freeze p E rho hs hΔ r reader hr (releaseTime p r)
    (by dsimp [freezeTime, releaseTime]; linarith [p.deltaPos]) hh

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Every block in the previous frozen domain is in the honest proposer's
store. This uses the full relay interval before the proposal. -/
theorem frozen_blocks_at_proposer {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hx : ExecutionValid (gridCO p) E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (hready : ProposalRelayReady p E rho (r + 1))
    (hh : proposalTime p (r + 1) ≤ rho.horizon)
    (hprop : rho.proposerOf (r + 1) ∈ rho.honest)
    (reader : V) (hr : reader ∈ rho.honest) (B : Block)
    (hm : B ∈ (Run.stateBeforeTime (gridCO p) rho (freezeTime p r) reader).blocks) :
    B ∈ (proposalState p rho (r + 1)).blocks := by
  have hb := congrArg Prod.fst (proposalState_receiptData p rho (r + 1))
  change (proposalState p rho (r + 1)).blocks = _ at hb
  rw [hb]
  exact stored_block_before_ready_proposal p E rho hx hΔ (r + 1) hready hh reader
    (rho.proposerOf (r + 1)) hr hprop (freezeTime p r)
    (by apply le_of_eq
        simp only [hΔ, freezeTime, proposalTime, Nat.cast_add, Nat.cast_one]
        ring) B hm

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Every frozen raw HEAD is in the proposer pool or its seat equivocates. -/
theorem frozen_raw_at_proposer {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hsched : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (hready : ProposalRelayReady p E rho (r + 1))
    (hh : proposalTime p (r + 1) ≤ rho.horizon)
    (hprop : rho.proposerOf (r + 1) ∈ rho.honest)
    (reader : V) (hr : reader ∈ rho.honest) (o : Wire p.n)
    (hm : o ∈ votesAt (Run.stateBeforeTime (gridCO p) rho (freezeTime p r) reader) r) :
    ∀ i, headSeat? o = some i →
      o ∈ proposerView (proposalState p rho (r + 1)) (r + 1) ∨
      equivocates (proposerView (proposalState p rho (r + 1)) (r + 1)) i = true := by
  obtain ⟨ho, hl⟩ := List.mem_filter.mp hm
  have hp : ∃ target, o.payload = .head target := by
    cases ha : o.auth <;> cases hb : o.payload <;> simp_all [headLabel?]
  obtain ⟨target, hp⟩ := hp
  have hv := congrArg (fun x => x.2.2.1) (proposalState_receiptData p rho (r + 1))
  change (proposalState p rho (r + 1)).votes = _ at hv
  simp only [proposerView, Nat.add_sub_cancel, votesAt, hv]
  exact stored_head_before_ready_proposal p E rho hsched hΔ r hready hh reader
    (rho.proposerOf (r + 1)) hr hprop (freezeTime p r)
    (by apply le_of_eq
        simp only [hΔ, freezeTime, proposalTime, Nat.cast_add, Nat.cast_one]
        ring) o target hp (by simpa using hl) ho

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Frozen resolved support is also resolved at the proposer. Relay of
its target block is distinct from relay of the HEAD object. -/
theorem frozen_support_at_proposer {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hx : ExecutionValid (gridCO p) E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (hready : ProposalRelayReady p E rho (r + 1))
    (hh : proposalTime p (r + 1) ≤ rho.horizon)
    (hprop : rho.proposerOf (r + 1) ∈ rho.honest)
    (reader : V) (hr : reader ∈ rho.honest) (o : Wire p.n)
    (hm : o ∈ (freezeView p (Run.stateBeforeTime (gridCO p) rho (freezeTime p r) reader) r).2.1) :
    ∀ i, headSeat? o = some i →
      o ∈ proposerSupportView (proposalState p rho (r + 1)) (r + 1) ∨
      equivocates (proposerView (proposalState p rho (r + 1)) (r + 1)) i = true := by
  obtain ⟨ho, hres⟩ := List.mem_filter.mp hm
  have hl : headLabel? o = some r := by simpa using (List.mem_filter.mp ho).2
  intro i hi
  rcases frozen_raw_at_proposer p E rho hx.toScheduleWellFormed hΔ r hready hh
      hprop reader hr o ho i hi with hraw | he
  · left
    apply List.mem_filter.mpr
    refine ⟨hraw, ?_⟩
    have hres := (resolvedBefore_block _ o _).symm.trans hres
    cases ht : headTarget? o with
    | none => simp [ht] at hres
    | some target =>
        simp only [ht, hl, Option.getD_some, Bool.and_eq_true,
          decide_eq_true_eq, blockKnown] at hres
        have hb := frozen_blocks_at_proposer p E rho hx hΔ r hready hh hprop reader hr
          target hres.1.1.1
        simpa [resolvedHead?, ht, resolveTarget, resolutionTree, hb] using hres.1.1.2
  · exact Or.inr he

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The actual proposal parent is already stored at the source, including
when the constrained walk stays at its live root. -/
theorem honest_proposal_parent_stored {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (s : Slot) (B : Block) (hB : HonestProposalAt E (gridInterface p) rho s B) :
    B.parent ∈ (proposalState p rho s).blocks := by
  have ht : TargetsStored (proposalState p rho s) := by
    apply clock_targetsStored
    rw [time_input_eq_event_prefix p E rho hs]
    exact run_targetsStored p rho _ _
  have hg : Block.genesis ∈ (proposalState p rho s).blocks := by
    have he := congrArg Prod.fst (proposalState_receiptData p rho s)
    change (proposalState p rho s).blocks = _ at he
    rw [he]
    exact (genesis_stored_at_time p E rho hs _ _).1
  obtain ⟨_, hnode, _⟩ := honest_proposal_views p E rho hs s B hB
  rw [hnode]
  change ghost _ _ _ _ ∈ _
  unfold ghost
  rcases ghostWalk_mem (proposalState p rho s).blocks.eraseDups _ _
      (proposalState p rho s).blocks.eraseDups.length
      (liveRoot (proposalState p rho s)) with he | hm
  · rw [he]
    exact liveRoot_mem_blocks _ ht hg
  · exact List.mem_eraseDups.mp hm

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Every source block reaches every reader before the proposal's HEAD.
In particular, each declared support target is resolved in the merged view. -/
theorem proposal_blocks_at_head {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho (r + 1))
    (hprop : rho.proposerOf (r + 1) ∈ rho.honest)
    (reader : V) (hr : reader ∈ rho.honest) (B : Block)
    (hm : B ∈ (proposalState p rho (r + 1)).blocks) :
    B ∈ (nextHeadState p rho r reader).blocks := by
  have hs := hsync.1.toScheduleWellFormed
  have hdst := congrArg Prod.fst
    (clock_receiptData p (releaseInput p rho r reader) (releaseTime p r))
  change (nextHeadState p rho r reader).blocks = (releaseInput p rho r reader).blocks at hdst
  rw [hdst]
  change B ∈ (Run.stateBeforeTime (gridCO p) rho (releaseTime p r) reader).blocks
  rw [release_eq_next_vote]
  by_cases hn : B = .genesis
  · subst B; exact (genesis_stored_at_time p E rho hs _ reader).1
  have hsrc := congrArg Prod.fst (proposalState_receiptData p rho (r + 1))
  change (proposalState p rho (r + 1)).blocks = _ at hsrc
  rw [hsrc, time_input_eq_event_prefix p E rho hs] at hm
  obtain ⟨index, hil, t, o, raw, support, hi, hp, ha⟩ :=
    stored_block_accepted p rho _ (rho.proposerOf (r + 1)) B hn hm
  have ht : t < proposalTime p (r + 1) := Int.le_sub_one_iff.mp
    ((index_lt_read_length_iff hs (proposalTime p (r + 1) - 1) hi).mp hil)
  obtain ⟨j, e, hj, he, hk⟩ := synchronous_accepted_block_before p E rho hΔ (r + 1) hsync
    (rho.proposerOf (r + 1)) reader hprop hr index o t (voteTime p (r + 1)) hp ha
    (by rw [hΔ]; dsimp [voteTime]; linarith)
    (by rw [hΔ]; exact le_refl _)
    (by dsimp [voteTime, gateTime]; linarith [p.deltaPos])
  exact (stored_block_stamp_before_cut p E rho hs hj
    (by simpa [processed, hp, blockKnown] using hk) he (le_refl _)).1

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The merged voter tree adds only the honest fresh proposal to the
proposer's domain. Every frozen block relays before proposal time, and
all other proposal ancestors were already stored at the source. -/
theorem honest_proposal_tree_reflects {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho (r + 1))
    (hready : ProposalRelayReady p E rho (r + 1)) (B : Block)
    (hB : HonestProposalAt E (gridInterface p) rho (r + 1) B)
    (reader : V) (hr : reader ∈ rho.honest) :
    ∀ C ∈ voterTree p (nextHeadState p rho r reader) (r + 1),
      C = B ∨ C ∈ (proposalState p rho (r + 1)).blocks := by
  have hs := hsync.1.toScheduleWellFormed
  have hpropTime : proposalTime p (r + 1) ≤ rho.horizon := by
    have hh := hsync.2.2.1
    dsimp [gateTime] at hh
    linarith [p.deltaPos]
  have hf := nextHeadState_frozenAt_of_schedule p E rho hs hΔ r reader hr (by
    apply le_trans _ hpropTime
    dsimp [freezeTime, proposalTime]; nlinarith [p.deltaPos])
  intro C hC
  obtain ⟨_, hm⟩ := List.mem_filter.mp hC
  simp only [Nat.add_sub_cancel, hf] at hm
  rcases Bool.or_eq_true_iff.mp hm with hfrozen | hproposal
  · right
    have hm' : C ∈ (Run.stateBeforeTime (gridCO p) rho (freezeTime p r) reader).blocks :=
      (List.mem_filter.mp (of_decide_eq_true hfrozen)).1
    exact frozen_blocks_at_proposer p E rho hsync.1 hΔ r hready hpropTime hB.1 reader hr C hm'
  · obtain ⟨D, hD, hCD⟩ := List.any_eq_true.mp hproposal
    obtain ⟨o, ho, hp⟩ := List.mem_filterMap.mp hD
    have he := nextHeadState_honest_proposal_unique p E rho hsync.1 r B hB reader o ho
    rw [he] at hp
    have hDB : B = D := Option.some.inj hp
    subst D
    by_cases heq : C = B
    · exact Or.inl heq
    · right
      have hp : Block.Preceq C B.parent := by
        cases B with
        | genesis => simp [Block.preceq] at hCD; contradiction
        | node parent slot r_slot root => simpa [Block.Preceq, Block.preceq, heq, Block.parent]
          using hCD
      by_cases hg : C = .genesis
      · subst C
        have he := congrArg Prod.fst (proposalState_receiptData p rho (r + 1))
        change (proposalState p rho (r + 1)).blocks = _ at he
        rw [he]
        exact (genesis_stored_at_time p E rho hs _ _).1
      · have hclosed := clock_stored_prefix_closed p
          (Run.stateBeforeTime (gridCO p) rho (proposalTime p (r + 1)) (rho.proposerOf (r + 1)))
          (proposalTime p (r + 1)) (run_time_stored_prefix_closed p rho _ _)
        exact hclosed B.parent (honest_proposal_parent_stored p E rho hs (r + 1) B hB) C hg hp

end AvailableChain.GridCO
end
