module
public import AvailableChainSAPC.Proofs.Floor
public import AvailableChainSAPC.Proofs.FrozenCertificates
public import AvailableChainSAPC.Proofs.CertificateRelay
public import AvailableChainSAPC.Proofs.GateSources

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- Lease sources, rather than the public S record, supply stored targets. -/
theorem gateWithPC_targetsStored (p : Params) {n : Nat} (st : GridCO.State n)
    (r : Slot) (c : Option (PC n)) (ht : GridCO.TargetsStored st)
    (hp : GridCO.StoredPrefixClosed st) (hg : Block.genesis ∈ st.blocks) :
    GridCO.TargetsStored (gateWithPC p st r c) := by
  intro ⟨b, g, d⟩ hm
  have hblocks := congrArg Prod.fst (gateWithPC_receiptData p st r c)
  change (gateWithPC p st r c).blocks = st.blocks at hblocks
  rw [hblocks]
  rcases gateWithPC_row_origin p st r c b g d hm with hold | ⟨x, hx, hb, _⟩
  · exact ht _ hold
  · by_cases he : b = .genesis
    · simpa [he] using hg
    · have hxmem : x ∈ st.blocks := by
        rcases GridCO.confirmation_mem p.engine st r x hx with rfl | hmem
        · exact hg
        · exact hmem
      exact hp x hxmem b he hb

theorem clock_targetsStored (p : Params) {n : Nat} (st : State n) (t : Time)
    (ht : GridCO.TargetsStored st.base) (hp : GridCO.StoredPrefixClosed st.base)
    (hg : Block.genesis ∈ st.base.blocks) : GridCO.TargetsStored (clock p st t).base := by
  have hexp : GridCO.TargetsStored (GridCO.expire { st.base with now := t } t) := by
    intro row hr
    exact ht row (List.mem_filter.mp hr).1
  have hrel (acc : GridCO.State n) r (h : GridCO.TargetsStored acc) :
      GridCO.TargetsStored (GridCO.release p.engine acc r) := by
    intro row hr
    exact h row (List.mem_filter.mp hr).1
  unfold clock
  dsimp only
  split_ifs
  all_goals try apply gateWithPC_targetsStored
  all_goals simp only [saveTimely]
  all_goals (try split_ifs)
  all_goals first
    | exact hp
    | exact hg
    | exact hrel _ _ hexp
    | exact hexp

/-- All finite targets remain in the archive's admitted block store.
No assertion that they are below S is used. -/
theorem targetsStored_at_fold {V : Type} [DecidableEq V] (p : Params)
    (events : List (Event V (sapc p).Object)) (v : V) :
    GridCO.TargetsStored ((events.foldl World.step World.init) v).base := by
  have h : ∀ v, GridCO.TargetsStored ((events.foldl World.step World.init) v).base ∧
      GridCO.StoredPrefixClosed ((events.foldl World.step World.init) v).base ∧
      Block.genesis ∈ ((events.foldl World.step World.init) v).base.blocks := by
    intro reader
    apply fold_invariant p (fun st => GridCO.TargetsStored st.base ∧
      GridCO.StoredPrefixClosed st.base ∧ Block.genesis ∈ st.base.blocks)
    · exact ⟨by simp [GridCO.TargetsStored, initial, GridCO.initial],
        GridCO.initial_stored_prefix_closed p.n, by simp [initial, GridCO.initial]⟩
    · intro st t h
      exact ⟨clock_targetsStored p st t h.1 h.2.1 h.2.2,
        by simpa only [GridCO.StoredPrefixClosed, clock_blocks] using h.2.1,
        by simpa only [clock_blocks] using h.2.2⟩
    · intro st o h
      apply process_base_invariant p (fun acc => GridCO.TargetsStored acc ∧
        GridCO.StoredPrefixClosed acc ∧ Block.genesis ∈ acc.blocks) _ _ st o h
      · intro acc head h
        exact ⟨by simpa only [GridCO.TargetsStored, GridCO.admitVote_blocks,
            GridCO.admitVote_obligations] using h.1,
          GridCO.admitVote_stored_prefix_closed p.engine acc head h.2.1,
          by simpa only [GridCO.admitVote_blocks] using h.2.2⟩
      · intro acc proposal b h
        refine ⟨?_, GridCO.admitProposal_stored_prefix_closed p.engine acc proposal b [] h.2.1,
          (GridCO.admitProposal_receiptPrefix p.engine acc proposal b []).blocks.subset h.2.2⟩
        intro row hr
        have hm : row ∈ acc.obligations := by
          simpa only [GridCO.admitProposal_obligations] using hr
        exact (GridCO.admitProposal_receiptPrefix p.engine acc proposal b []).blocks.subset
          (h.1 row hm)
  exact (h v).1

theorem choice_mem_blocks (p : Params) {n : Nat} (st : State n) (tree : List Block)
    (raw support : List (GridCO.Wire n)) (r : Slot) (c : Option (PC n))
    (ht : GridCO.TargetsStored st.base) (hg : Block.genesis ∈ st.base.blocks)
    (htree : tree ⊆ st.base.blocks)
    (hc : ∀ cert, c = some cert → pcValid p st cert = true) :
    choice p st tree raw support r c ∈ st.base.blocks := by
  have hr := GridCO.liveRoot_mem_blocks st.base ht hg
  have hf : floor p st tree raw support r ∈ st.base.blocks := by
    by_cases he : floor p st tree raw support r = .genesis
    · simpa [he] using hg
    · exact (floor_properties p st tree raw support r he).1
  have ha : preliminaryAnchor (floor p st tree raw support r) c ∈ st.base.blocks := by
    cases c with
    | none => exact hf
    | some cert =>
        have hm := pathKnown_mem st cert.target
          (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
            (Bool.and_eq_true_iff.mp (hc cert rfl)).1).2).1
        simp only [preliminaryAnchor]
        split <;> assumption
  have hroot : mandatoryRoot (GridCO.liveRoot st.base)
      (preliminaryAnchor (floor p st tree raw support r) c) ∈ st.base.blocks := by
    unfold mandatoryRoot
    split <;> assumption
  have hwalk (root : Block) (hroot : root ∈ st.base.blocks) :
      GridCO.ghost root tree (GridCO.goldfishScore st.base.blocks raw support)
        (GridCO.goldfishEligible st.base.blocks raw support r) ∈ st.base.blocks := by
    unfold GridCO.ghost
    rcases GridCO.ghostWalk_mem tree.eraseDups _ _ tree.eraseDups.length root with he | hm
    · rw [he]; exact hroot
    · exact htree (List.mem_eraseDups.mp hm)
  unfold choice
  split
  · exact hwalk _ hr
  · exact hwalk _ hroot

/-- Both modes emit only admitted targets. The active case uses the
valid frozen/carried PC, not the later live PC. -/
theorem headTarget_mem_at_fold {V : Type} [DecidableEq V] (p : Params)
    (events : List (Event V (sapc p).Object)) (v : V) (r : Slot) :
    let st := (events.foldl World.step World.init) v
    headTarget p st r ∈ st.base.blocks := by
  dsimp only
  unfold headTarget
  split
  · exact (paths_at_fold p events v).2.1
  · apply choice_mem_blocks p _ _ _ _ r _ (targetsStored_at_fold p events v)
      (paths_at_fold p events v).2.1
    · split
      · exact fun _ hb => (List.mem_filter.mp hb).1
      · exact activeVoterTree_subset p _ r _
    · exact selectedPC_valid p _ (certificates_valid_at_fold p events v).2 r

/-- Admission bounds a new block's slot even during an arbitrary prefix. -/
theorem process_new_block_slot (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (b : Block) (hn : b ∉ st.base.blocks) (hm : b ∈ (process p st o).base.blocks) :
    b.slot ≤ (st.base.now / (4 * p.Δ)).toNat := by
  unfold process at hm
  split at hm
  · exact (hn (by simpa [admitHead, collectPCs_base, receiveHead_blocks] using hm)).elim
  · unfold admitProposal at hm
    split at hm
    · rename_i s target raw support c ha hp he
      have hdata := proposalEnters_data p st o target raw support he
      simp only [collectPCs_base, receiveHeads_blocks] at hm
      unfold proposalBase GridCO.admitProposal at hm
      dsimp only at hm
      split_ifs at hm
      · exact (hn hm).elim
      · have heq : b = target := by simpa [hn] using hm
        simpa only [heq] using hdata.2
    · exact (hn hm).elim
  · split at hm
    · exact (hn (by simpa [collectPCs_base, installPC, receiveHeads_blocks] using hm)).elim
    · exact (hn hm).elim
  · exact (hn hm).elim

theorem stored_before_head_slot_le {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (v : V) (b : Block)
    (hm : b ∈ (Run.stateBeforeTime (sapc p) rho (voteTime p r) v).base.blocks) :
    b.slot ≤ r := by
  by_cases hg : b = .genesis
  · simp [hg, Block.slot]
  rw [time_input_eq_event_prefix p E rho hs] at hm
  obtain ⟨i, hil, t, o, raw, support, c, hi, hp, ha⟩ := stored_block_accepted p rho _ v b hg hm
  have ht : t < voteTime p r :=
    Int.le_sub_one_iff.mp ((index_lt_read_length_iff hs (voteTime p r - 1) hi).mp hil)
  have hn : b ∉ (Run.stateBefore (sapc p) rho i v).base.blocks := by
    simpa [sapc, processed, hp, GridCO.blockKnown] using ha.2.1
  have hb : b ∈ (process p (Run.stateBefore (sapc p) rho i v) o).base.blocks := by
    have h := ha.2.2
    rw [stateBefore_succ_event hi] at h
    simpa [World.step, sapc, processed, hp, GridCO.blockKnown] using h
  apply (process_new_block_slot p _ o b hn hb).trans
  apply Int.toNat_le.mpr
  apply (Int.ediv_le_iff_le_mul (by linarith [p.deltaPos])).mpr
  have hnow := (stateBefore_now_le_event p E rho hs hi v).trans_lt ht
  change _ < 4 * p.Δ * (r : Time) + p.Δ at hnow
  nlinarith [p.deltaPos]

end AvailableChain.SAPC
end
