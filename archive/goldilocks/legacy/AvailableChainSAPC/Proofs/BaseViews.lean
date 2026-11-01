module
public import AvailableChainSAPC.Proofs.BaseArchive
public import AvailableChainGridCO.Proofs.Frozen

-- ROOT-DIGEST-2: a private unfolding fact avoids a public equation export (BUILD B3).
namespace AvailableChain.SAPC
private theorem hygiene_resolvedBefore_eq {n : Nat} {mode : GridCO.HeadMode}
    (st : GridCO.State n mode) (o : GridCO.Wire n mode) (cutoff : Time) :
    GridCO.resolvedBefore st o cutoff = (match GridCO.resolvedHead? st o with
      | none => false
      | some B => decide (B.slot ≤ (GridCO.headLabel? o).getD 0) &&
          decide (GridCO.stampVote st o < cutoff) &&
          decide (GridCO.stampBlock st B < cutoff)) := rfl
end AvailableChain.SAPC

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- Ordinary saved views retain their original base keys and declared
support. This invariant does not identify them with the live view. -/
def FrozenViewsStored {n : Nat} (st : GridCO.State n .block) : Prop :=
  ∀ r raw support tree, (r, raw, support, tree) ∈ st.frozen →
    raw ⊆ st.votes ∧ support ⊆ raw ∧
      ∀ o ∈ raw, GridCO.headLabel? o = some r

private theorem freeze_stored (p : Params) {n : Nat} (st : GridCO.State n .block)
    (r : Slot) (h : FrozenViewsStored st) : FrozenViewsStored (GridCO.freeze p.engine st r) := by
  intro label raw support tree hm
  rcases List.mem_append.mp hm with hold | hnew
  · exact h label raw support tree hold
  · cases List.mem_singleton.mp hnew
    refine ⟨fun _ ho => (List.mem_filter.mp (List.mem_filter.mp ho).1).1, ?_, ?_⟩
    · intro o ho
      obtain ⟨hm, ht⟩ := List.mem_filter.mp ho
      apply List.mem_filter.mpr
      refine ⟨hm, ?_⟩
      cases he : GridCO.resolvedHead? st o with
      | none => simp [hygiene_resolvedBefore_eq, he] at ht
      | some b =>
          simp only [hygiene_resolvedBefore_eq, he, Bool.and_eq_true, decide_eq_true_eq] at ht
          exact decide_eq_true ht.1.2
    · intro o ho
      simpa using (List.mem_filter.mp (List.mem_filter.mp ho).1).2

private theorem stored_mono {n : Nat} (a b : GridCO.State n .block)
    (hf : b.frozen = a.frozen) (hv : a.votes ⊆ b.votes)
    (h : FrozenViewsStored a) : FrozenViewsStored b := by
  intro r raw support tree hm
  obtain ⟨hr, hs, hl⟩ := h r raw support tree (hf ▸ hm)
  exact ⟨List.Subset.trans hr hv, hs, hl⟩

theorem gateWithPC_frozen (p : Params) {n : Nat} (st : GridCO.State n .block)
    (r : Slot) (c : Option (PC n)) : (gateWithPC p st r c).frozen = st.frozen := by
  cases c with
  | none => exact @GridCO.gate_frozen GridCO.slowLeasePolicy p.engine n st r
  | some c =>
      simp only [gateWithPC]
      split
      · rfl
      · try dsimp only
        split
        · rfl
        · rw [fold_field GridCO.State.frozen _ (by
            intro acc b
            exact fold_field GridCO.State.frozen _ (by intros; rfl) _ _)]
          split <;> rfl

private theorem admitVote_frozen (p : Params) {n : Nat} (st : GridCO.State n .block)
    (o : GridCO.Wire n) : (GridCO.admitVote p.engine st o).frozen = st.frozen := by
  unfold GridCO.admitVote
  split
  · dsimp only; split <;> rfl
  · rfl

theorem process_base_frozen (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    (process p st o).base.frozen = st.base.frozen := by
  apply process_base_invariant p (fun acc => acc.frozen = st.base.frozen)
  · intro acc head h
    exact (admitVote_frozen p acc head).trans h
  · intro acc proposal b h
    unfold GridCO.admitProposal
    dsimp only
    split_ifs <;> exact h
  · rfl

theorem process_frozenViewsStored (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (h : FrozenViewsStored st.base) : FrozenViewsStored (process p st o).base :=
  stored_mono _ _ (process_base_frozen p st o)
    (process_base_receiptPrefix p st o).votes.subset h

theorem clock_frozenViewsStored (p : Params) {n : Nat} (st : State n) (t : Time)
    (h : FrozenViewsStored st.base) : FrozenViewsStored (clock p st t).base := by
  have hg (st : State n) r (h : FrozenViewsStored st.base) :
      FrozenViewsStored (gate p st r).base := by
    apply stored_mono st.base _ (gateWithPC_frozen p _ _ _)
    · have hv := congrArg (fun d => d.2.2.1)
        (gateWithPC_receiptData p st.base r (if capBroken p st then none else st.bestPC))
      change (gateWithPC p st.base r _).votes = st.base.votes at hv
      rw [hv]
    · exact h
  unfold clock
  dsimp only
  split_ifs
  all_goals try apply hg
  all_goals simp only [saveTimely]
  all_goals (try split_ifs)
  all_goals first | exact freeze_stored p _ _ h | exact h

/-- The invariant holds at any engine fold, including sleeping readers. -/
theorem frozenViewsStored_at_fold {V : Type} [DecidableEq V] (p : Params)
    (events : List (Event V (sapc p).Object)) (v : V) :
    FrozenViewsStored ((events.foldl World.step World.init) v).base := by
  apply fold_invariant p (fun st => FrozenViewsStored st.base)
  · simp [FrozenViewsStored, initial, GridCO.initial]
  · exact clock_frozenViewsStored p
  · exact process_frozenViewsStored p

theorem frozenAt_stored {n : Nat} (st : GridCO.State n .block) (h : FrozenViewsStored st)
    (r : Slot) (raw support : List (GridCO.Wire n)) (tree : List Block)
    (hf : GridCO.frozenAt st r = some (raw, support, tree)) :
    raw ⊆ st.votes ∧ support ⊆ raw ∧ ∀ o ∈ raw, GridCO.headLabel? o = some r := by
  unfold GridCO.frozenAt at hf
  obtain ⟨row, hr, he⟩ := Option.map_eq_some_iff.mp hf
  have hl : row.1 = r := by simpa using List.find?_some hr
  have hm := List.mem_of_find?_eq_some hr
  have heq : row = (r, raw, support, tree) := Prod.ext hl he
  exact h r raw support tree (heq ▸ hm)


/-- Each stored base proposal retains the original signed raw view.
Only the preceding-label members are used by the effective view. -/
def ProposalViewsArchived {n : Nat} (st : State n) : Prop :=
  ∀ o ∈ st.base.proposals, ∃ parent b raw support,
    o = baseProposal parent b raw support ∧
    ∀ h ∈ raw, headLabel? h = some (b.slot - 1) → h ∈ st.receivedHeads

private theorem proposalViews_mono {n : Nat} (a b : State n)
    (hp : b.base.proposals = a.base.proposals) (ha : a.receivedHeads ⊆ b.receivedHeads)
    (h : ProposalViewsArchived a) : ProposalViewsArchived b := by
  intro o ho
  obtain ⟨parent, block, raw, support, he, hh⟩ := h o (hp ▸ ho)
  exact ⟨parent, block, raw, support, he, fun head hm hl => ha (hh head hm hl)⟩

theorem receiveHead_base_proposals (p : Params) {n : Nat} (st : State n) (h : HeadWire n) :
    (receiveHead p st h).base.proposals = st.base.proposals := by
  rw [receiveHead_base]
  unfold GridCO.admitVote
  split
  · dsimp only; split <;> rfl
  · rfl

theorem receiveHeads_base_proposals (p : Params) {n : Nat} (st : State n)
    (xs : List (HeadWire n)) :
    (xs.foldl (receiveHead p) st).base.proposals = st.base.proposals :=
  fold_field (fun st => st.base.proposals) _ (receiveHead_base_proposals p) xs st

theorem gateWithPC_proposals (p : Params) {n : Nat} (st : GridCO.State n .block)
    (r : Slot) (c : Option (PC n)) : (gateWithPC p st r c).proposals = st.proposals := by
  cases c with
  | none =>
      simp only [gateWithPC, SA.gate]
      unfold GridCO.gate
      split
      · rfl
      · try dsimp only
        split
        · rfl
        · exact fold_field GridCO.State.proposals _ (by
            intro acc b
            exact fold_field GridCO.State.proposals _ (by intros; rfl) _ _) _ _
  | some c =>
      simp only [gateWithPC]
      split
      · rfl
      · try dsimp only
        split
        · rfl
        · rw [fold_field GridCO.State.proposals _ (by
            intro acc b
            exact fold_field GridCO.State.proposals _ (by intros; rfl) _ _)]
          split <;> rfl

theorem clock_base_proposals (p : Params) {n : Nat} (st : State n) (t : Time) :
    (clock p st t).base.proposals = st.base.proposals := by
  unfold clock
  dsimp only
  split_ifs <;> simp only [gate, gateWithPC_proposals, saveTimely]
  all_goals (try split_ifs) <;> rfl

/-- Block admission supplies the non-future guard for all preceding-label
carried signatures, even when the ordinary two-target cache is full. -/
theorem proposalEnters_data (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (b : Block) (raw support : List (HeadWire n))
    (he : proposalEnters p st o b raw support = true) :
    (proposalBase p st o b raw support).proposals =
      st.base.proposals ++ [baseProposal o b raw support] ∧
    b.slot ≤ (st.base.now / (4 * p.Δ)).toNat := by
  unfold proposalEnters at he
  unfold proposalBase GridCO.admitProposal at he ⊢
  dsimp only at he ⊢
  split_ifs with hg
  · simp only [hg, ↓reduceIte] at he
    simp at he
  · constructor
    · rfl
    · by_contra hn
      have hgt := Nat.lt_of_not_ge hn
      simp [SA.Params.engine, hgt] at hg

/-- The store dependency lookup with the `wellFormed` parent-slot test: the
parent is in the base store with a slot below `s` iff a stored block has the
parent's root and a slot below `s`. `wellFormed` itself reads no store. -/
theorem blockKnown_parent_slot_iff_root {n : Nat} (st : State n) (b : Block) (s : Slot)
    (hr : ∀ q ∈ st.base.blocks, q.root = b.parent.root → q = b.parent) :
    (GridCO.blockKnown st.base b.parent = true ∧ b.parent.slot < s) ↔
      ∃ q ∈ st.base.blocks, q.root = b.parent.root ∧ q.slot < s := by
  simpa [GridCO.blockKnown] using
    parent_mem_and_iff_root b st.base.blocks (fun q => q.slot < s) hr

/-- A proposal with an unknown parent is a missing dependency: its block does
not enter the base store. -/
theorem proposalEnters_missingParent (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (b : Block) (raw support : List (HeadWire n))
    (h : ¬ GridCO.blockKnown st.base b.parent) :
    proposalEnters p st o b raw support = false := by
  simp [proposalEnters, proposalBase, GridCO.admitProposal, h]

/-- The proposal handler returns the state unchanged for an unknown parent. -/
theorem admitProposal_missingParent (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (b : Block) (raw support : List (HeadWire n)) (c : Option (PC n))
    (h : ¬ GridCO.blockKnown st.base b.parent) :
    admitProposal p st o b raw support c = st := by
  simp [admitProposal, proposalEnters_missingParent p st o b raw support h]

theorem process_proposalViewsArchived (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (h : ProposalViewsArchived st) : ProposalViewsArchived (process p st o) := by
  have hcollect (st : State n) (h : ProposalViewsArchived st) :
      ProposalViewsArchived (collectPCs p st) :=
    proposalViews_mono st _ (congrArg GridCO.State.proposals (collectPCs_base p st))
      (by rw [collectPCs_archive]) h
  have hfold (st : State n) (xs : List (HeadWire n)) (h : ProposalViewsArchived st) :
      ProposalViewsArchived (xs.foldl (receiveHead p) st) :=
    proposalViews_mono st _ (receiveHeads_base_proposals p st xs)
      (receiveHeads_archive_mono p st xs) h
  unfold process
  split
  · apply hcollect
    exact proposalViews_mono st _ (receiveHead_base_proposals p st _)
      (receiveHead_archive_mono p st _) h
  · rename_i slot b raw support c ha hp
    unfold admitProposal
    split
    · rename_i he
      apply hcollect
      intro key hk
      rw [receiveHeads_base_proposals, (proposalEnters_data p st o b raw support he).1] at hk
      rcases List.mem_append.mp hk with hold | hnew
      · obtain ⟨parent, b, raw, support, he, hh⟩ := h key hold
        exact ⟨parent, b, raw, support, he, fun head hm hl =>
          receiveHeads_archive_mono p _ _ (hh head hm hl)⟩
      · have heq := List.mem_singleton.mp hnew
        refine ⟨o, b, raw, support, heq, ?_⟩
        intro head hm hl
        apply receiveHeads_mem p _ _ head (List.mem_append_left _ hm) (b.slot - 1) hl
        rw [proposalBase_now]
        exact (Nat.sub_le _ _).trans (proposalEnters_data p st o b raw support he).2
    · exact h
  · split
    · apply hcollect
      exact hfold st _ h
    · exact h
  · exact h

theorem proposalViewsArchived_at_fold {V : Type} [DecidableEq V] (p : Params)
    (events : List (Event V (sapc p).Object)) (v : V) :
    ProposalViewsArchived ((events.foldl World.step World.init) v) := by
  apply fold_invariant p ProposalViewsArchived
  · simp [ProposalViewsArchived, initial, GridCO.initial]
  · intro st t h
    exact proposalViews_mono st _ (clock_base_proposals p st t)
      (by rw [clock_archive]) h
  · exact process_proposalViewsArchived p

theorem baseWire_label {n : Nat} (o : HeadWire n) :
    GridCO.headLabel? (baseWire o) = headLabel? o := by
  cases o with | mk auth data => cases auth <;> rfl

/-- Each merged carried key has its complete original signature in the
archive. No inclusion in the capped ordinary cache is asserted. -/
theorem carriedRaw_archived {n : Nat} (st : State n) (h : ProposalViewsArchived st)
    (s : Slot) (o : GridCO.Wire n) (ho : o ∈ GridCO.carriedRaw st.base s) :
    ∃ head ∈ st.receivedHeads, baseWire head = o := by
  obtain ⟨hm, hl⟩ := List.mem_filter.mp ho
  obtain ⟨parent, hp, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨hp, hs⟩ := List.mem_filter.mp hp
  obtain ⟨original, b, raw, support, rfl, hh⟩ := h parent hp
  have hb : b.slot = s := by simpa [baseProposal] using hs
  simp only [baseProposal, List.map_map] at hm
  obtain ⟨head, hmem, heq⟩ := List.mem_map.mp hm
  change baseWire head = o at heq
  have hlabel : headLabel? head = some (b.slot - 1) := by
    rw [← baseWire_label, heq, hb]
    simpa using hl
  exact ⟨head, hh head hmem hlabel, heq⟩

theorem voterView_archived (p : Params) {n : Nat} (st : State n)
    (hb : BaseArchived st) (hf : FrozenViewsStored st.base) (hp : ProposalViewsArchived st)
    (s : Slot) (o : GridCO.Wire n) (ho : o ∈ GridCO.voterView p.engine st.base s) :
    ∃ head ∈ st.receivedHeads, baseWire head = o := by
  unfold GridCO.voterView at ho
  rcases List.mem_append.mp (List.mem_eraseDups.mp ho) with hfr | hc
  · cases he : GridCO.frozenAt st.base (s - 1) with
    | none => simp [he] at hfr
    | some view =>
        exact hb o ((frozenAt_stored st.base hf _ view.1 view.2.1 view.2.2 he).1
          (by simpa [he] using hfr))
  · exact carriedRaw_archived st hp s o hc

theorem voterView_label (p : Params) {n : Nat} (st : State n)
    (hf : FrozenViewsStored st.base) (s : Slot) (o : GridCO.Wire n)
    (ho : o ∈ GridCO.voterView p.engine st.base s) : GridCO.headLabel? o = some (s - 1) := by
  unfold GridCO.voterView at ho
  rcases List.mem_append.mp (List.mem_eraseDups.mp ho) with hfr | hc
  · cases he : GridCO.frozenAt st.base (s - 1) with
    | none => simp [he] at hfr
    | some view =>
        exact (frozenAt_stored st.base hf _ view.1 view.2.1 view.2.2 he).2.2 o
          (by simpa [he] using hfr)
  · simpa using (List.mem_filter.mp hc).2

end AvailableChain.SAPC
end
