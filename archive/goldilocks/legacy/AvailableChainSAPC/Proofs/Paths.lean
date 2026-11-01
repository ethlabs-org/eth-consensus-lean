module
public import AvailableChainSAPC.Proofs.Acceptance
public import AvailableChainGridCO.Proofs.Roots -- shake: keep (re-export)
public import AvailableChainGridCO.Proofs.RecordSlots

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- The shared admission rules supply complete paths with increasing
parent slots. The PC gate does not change the block store. -/
theorem paths_at_fold {V : Type} [DecidableEq V] (p : Params)
    (events : List (Event V (sapc p).Object)) (v : V) :
    let st := (events.foldl World.step World.init) v
    GridCO.StoredPrefixClosed st.base ∧ Block.genesis ∈ st.base.blocks ∧
      ∀ b ∈ st.base.blocks, GridCO.SlotOrdered b := by
  apply fold_invariant p (fun st => GridCO.StoredPrefixClosed st.base ∧
    Block.genesis ∈ st.base.blocks ∧ ∀ b ∈ st.base.blocks, GridCO.SlotOrdered b)
  · exact ⟨GridCO.initial_stored_prefix_closed p.n, by simp [initial, GridCO.initial],
      by simp [initial, GridCO.initial, GridCO.SlotOrdered]⟩
  · intro st t h
    simpa only [GridCO.StoredPrefixClosed, clock_blocks] using h
  · intro st o h
    refine ⟨?_, process_blocks_mono p st o h.2.1, ?_⟩
    · exact process_base_invariant p GridCO.StoredPrefixClosed
        (GridCO.admitVote_stored_prefix_closed p.engine)
        (fun st o b h => GridCO.admitProposal_stored_prefix_closed p.engine st o b [] h)
        st o h.1
    · exact process_base_invariant p (fun st => ∀ b ∈ st.blocks, GridCO.SlotOrdered b)
        (fun st o h => by simpa only [GridCO.admitVote_blocks] using h)
        (fun st o b h => GridCO.admitProposal_blocks_ordered p.engine st o b [] h)
        st o h.2.2

theorem pathKnown_of_mem {n : Nat} (st : State n)
    (hclosed : GridCO.StoredPrefixClosed st.base) (hg : Block.genesis ∈ st.base.blocks)
    (b : Block) (hb : b ∈ st.base.blocks) : pathKnown st b = true := by
  induction b with
  | genesis => simpa [pathKnown, GridCO.blockKnown] using hg
  | node parent s r_s root ih =>
      have hp : parent ∈ st.base.blocks := by
        by_cases he : parent = .genesis
        · simpa [he] using hg
        · exact hclosed _ hb parent he
            (by simp only [Block.preceq, Bool.or_eq_true]
                exact Or.inr (GridCO.block_preceq_self parent))
      simp only [pathKnown, Bool.and_eq_true_iff]
      exact ⟨by simpa [GridCO.blockKnown] using hb, ih hp⟩

theorem stored_pathKnown_at_fold {V : Type} [DecidableEq V] (p : Params)
    (events : List (Event V (sapc p).Object)) (v : V) (b : Block)
    (hb : b ∈ ((events.foldl World.step World.init) v).base.blocks) :
    pathKnown ((events.foldl World.step World.init) v) b = true :=
  pathKnown_of_mem _ (paths_at_fold p events v).1 (paths_at_fold p events v).2.1 b hb

/-- A new path block comes only from the directly delivered proposal.
An unsigned envelope or a HEAD cannot introduce a block. -/
theorem process_new_block (p : Params) {n : Nat} (st : State n) (o : Wire n) (b : Block)
    (hnew : b ∉ st.base.blocks) (hm : b ∈ (process p st o).base.blocks) :
    ∃ raw support c, o.payload = .proposal b raw support c := by
  unfold process at hm
  split at hm
  · simp only [admitHead, collectPCs_base, receiveHead_blocks] at hm
    exact (hnew hm).elim
  · rename_i s target raw support c ha hp
    unfold admitProposal at hm
    split at hm
    · simp only [collectPCs_base, receiveHeads_blocks] at hm
      unfold proposalBase GridCO.admitProposal at hm
      dsimp only at hm
      split_ifs at hm
      · exact (hnew hm).elim
      · have he : b = target := by simpa [hnew] using hm
        exact ⟨raw, support, c, by simpa [he] using hp⟩
    · exact (hnew hm).elim
  · split at hm
    · simp only [collectPCs_base, installPC, receiveHeads_blocks] at hm
      exact (hnew hm).elim
    · exact (hnew hm).elim
  · exact (hnew hm).elim

/-- Path provenance includes the actual acceptance event, so the common
accepted-object relay premise applies to these dependencies. -/
theorem stored_block_accepted {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (index : Nat) (v : V) (b : Block) (hne : b ≠ .genesis)
    (hm : b ∈ (Run.stateBefore (sapc p) rho index v).base.blocks) :
    ∃ j < index, ∃ t o raw support c,
      rho.events[j]? = some (.deliver v o t) ∧ o.payload = .proposal b raw support c ∧
        Run.acceptsAt (sapc p) rho j v o t := by
  induction index with
  | zero => simp [Run.stateBefore, World.init, sapc, initial, GridCO.initial, hne] at hm
  | succ index ih =>
      by_cases hold : b ∈ (Run.stateBefore (sapc p) rho index v).base.blocks
      · obtain ⟨j, hj, rest⟩ := ih hold
        exact ⟨j, by omega, rest⟩
      · cases hi : rho.events[index]? with
        | none => simp [Run.stateBefore, List.take_add_one, hi] at hm; exact (hold hm).elim
        | some e =>
            rw [stateBefore_succ_event hi] at hm
            cases e with
            | tick u t =>
                by_cases hv : v = u
                · subst u
                  exact (hold (by simpa [World.step, sapc, clock_blocks] using hm)).elim
                · exact (hold (by simpa [World.step, hv] using hm)).elim
            | deliver u o t =>
                by_cases hv : v = u
                · subst u
                  have hnew : b ∈
                      (process p (Run.stateBefore (sapc p) rho index v) o).base.blocks := by
                    simpa [World.step, sapc] using hm
                  obtain ⟨raw, support, c, hp⟩ := process_new_block p _ o b hold hnew
                  refine ⟨index, by omega, t, o, raw, support, c, hi, hp,
                    ⟨o, hi, Or.inl rfl⟩, ?_, ?_⟩
                  · simpa [sapc, processed, hp, GridCO.blockKnown] using hold
                  · rw [stateBefore_succ_event hi]
                    simpa [World.step, sapc, processed, hp, GridCO.blockKnown] using hnew
                · exact (hold (by simpa [World.step, hv] using hm)).elim

theorem stateBefore_blocks_mono {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) {i j : Nat} (hij : i ≤ j) (v : V) :
    (Run.stateBefore (sapc p) rho i v).base.blocks ⊆
      (Run.stateBefore (sapc p) rho j v).base.blocks := by
  induction j with
  | zero => rw [Nat.le_zero.mp hij]
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hlt
      · exact List.Subset.refl _
      · apply List.Subset.trans (ih (by omega))
        cases hj : rho.events[j]? with
        | none => simp [Run.stateBefore, List.take_add_one, hj]
        | some e =>
            rw [stateBefore_succ_event hj]
            cases e with
            | tick u t =>
                by_cases hv : v = u
                · subst u; simp [World.step, sapc, clock_blocks]
                · simp [World.step, hv]
            | deliver u o t =>
                by_cases hv : v = u
                · subst u
                  simpa [World.step, sapc] using process_blocks_mono p
                    (Run.stateBefore (sapc p) rho j v) o
                · simp [World.step, hv]

theorem accepted_block_before_cut {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (index : Nat) (v : V) (o : Wire p.n) (b : Block) (raw support : List (HeadWire p.n))
    (c : Option (PC p.n)) (hp : o.payload = .proposal b raw support c) (t cut : Time)
    (ha : Run.acceptsAt (sapc p) rho index v o t) (ht : t < cut) :
    b ∈ (Run.stateBeforeTime (sapc p) rho cut v).base.blocks := by
  obtain ⟨parent, hi, _⟩ := ha.1
  have hm : b ∈ (Run.stateBefore (sapc p) rho (index + 1) v).base.blocks := by
    simpa [sapc, processed, hp, GridCO.blockKnown] using ha.2.2
  rw [time_input_eq_event_prefix p E rho hs]
  apply stateBefore_blocks_mono p rho (v := v) _ hm
  exact Nat.succ_le_of_lt ((index_lt_read_length_iff hs (cut - 1) hi).mpr
    (Int.le_sub_one_iff.mpr ht))

/-- Every stored block lies in the unchanged Draft 4.2 root scope. -/
theorem stored_block_in_run {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (sapc p)) (index : Nat) (v : V) (b : Block)
    (hm : b ∈ (Run.stateBefore (sapc p) rho index v).base.blocks) :
    BlockInRun E (sapcInterface p).toInterface rho b := by
  by_cases he : b = .genesis
  · exact Or.inl he
  · obtain ⟨j, _, t, o, raw, support, c, hi, hp, _⟩ :=
      stored_block_accepted p rho index v b he hm
    exact Or.inr ⟨v, o, t, b, Or.inl ⟨j, hi⟩,
      by simp [sapcInterface, block, hp], GridCO.block_preceq_self b⟩

theorem blockInRun_of_prefix {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (sapc p)) (a b : Block)
    (hb : BlockInRun E (sapcInterface p).toInterface rho b) (hab : Block.Preceq a b) :
    BlockInRun E (sapcInterface p).toInterface rho a := by
  rcases hb with rfl | ⟨v, o, t, tip, hs, hp, htip⟩
  · exact Or.inl (by simpa [Block.Preceq, Block.preceq] using hab)
  · exact Or.inr ⟨v, o, t, tip, hs, hp, GridCO.prefix_trans a b tip hab htip⟩

theorem stateBefore_rootInjectiveBelow {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p))
    (hroot : RootInjective E (sapcInterface p).toInterface rho) (index : Nat) (v : V) :
    GridCO.RootInjectiveBelow (Run.stateBefore (sapc p) rho index v).base.blocks := by
  intro a c ha hc he
  obtain ⟨b, hb, hab⟩ := ha
  obtain ⟨d, hd, hcd⟩ := hc
  exact hroot a c
    (blockInRun_of_prefix p E rho a b (stored_block_in_run p E rho index v b hb) hab)
    (blockInRun_of_prefix p E rho c d (stored_block_in_run p E rho index v d hd) hcd) he

theorem time_input_rootInjectiveBelow {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hroot : RootInjective E (sapcInterface p).toInterface rho) (t : Time) (v : V) :
    GridCO.RootInjectiveBelow (Run.stateBeforeTime (sapc p) rho t v).base.blocks := by
  rw [time_input_eq_event_prefix p E rho hs]
  exact stateBefore_rootInjectiveBelow p E rho hroot _ v

end AvailableChain.SAPC
end
