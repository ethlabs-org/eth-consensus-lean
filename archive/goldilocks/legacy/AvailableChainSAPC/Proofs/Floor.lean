module
public import AvailableChainSAPC.Proofs.ActiveCounts
public import AvailableChainSAPC.Proofs.DeclaredSupport
public import AvailableChainGridCO.Proofs.Transfer

@[expose] public section
namespace AvailableChain.SAPC

/-- A score above the detected-equivocator count needs a resolved,
non-equivocating declared supporter. It need not be an honest seat. -/
theorem score_above_detected_witness {n : Nat} (tree : List Block)
    (raw support : List (GridCO.Wire n)) (b : Block)
    (hscore : (detectedSeats raw).card < GridCO.goldfishScore tree raw support b) :
    ∃ i o target, o ∈ support ∧ GridCO.headSeat? o = some i ∧
      GridCO.equivocates raw i = false ∧ GridCO.headTarget? o = some target ∧
      target ∈ tree ∧ target.slot ≤ (GridCO.headLabel? o).getD 0 ∧ Block.Preceq b target := by
  rw [GridCO.goldfishScore_eq_card] at hscore
  have hn : ¬ GridCO.scoreSeats tree raw support b ⊆ detectedSeats raw := by
    intro hs
    exact Nat.not_lt_of_ge (Finset.card_le_card hs) hscore
  obtain ⟨i, hi, hni⟩ := Finset.not_subset.mp hn
  obtain ⟨hr, hs⟩ := Finset.mem_filter.mp hi
  have he : GridCO.equivocates raw i = false := by
    by_contra hn
    have ht : GridCO.equivocates raw i = true := Bool.eq_true_of_not_eq_false hn
    exact hni (Finset.mem_filter.mpr ⟨by
      simpa only [GridCO.seats, List.mem_toFinset, List.mem_dedup] using hr, ht⟩)
  simp only [he, Bool.false_or] at hs
  obtain ⟨o, ho, ht⟩ := List.any_eq_true.mp hs
  obtain ⟨ho, hi⟩ := List.mem_filter.mp ho
  cases hh : GridCO.headTarget? o with
  | none => simp [hh] at ht
  | some target =>
      simp only [hh, Bool.and_eq_true, decide_eq_true_eq] at ht
      exact ⟨i, o, target, ho, by simpa using hi, he, hh, ht.1.1, ht.1.2, ht.2⟩

/-- The F4 test has a declared witness in an active view, including
above-cap executions. The hypothesis bounds detected evidence only. -/
theorem active_score_witness (p : Params) {n : Nat} (st : State n)
    (r : Slot) (raw support : List (GridCO.Wire n))
    (ha : ∀ o ∈ raw, ∃ h ∈ st.receivedHeads, baseWire h = o)
    (hl : ∀ o ∈ raw, GridCO.headLabel? o = some r)
    (hactive : capBroken p st = false) (b : Block)
    (hscore : pcFaultCap p < GridCO.goldfishScore st.base.blocks raw support b) :
    ∃ i o target, o ∈ support ∧ GridCO.headSeat? o = some i ∧
      GridCO.equivocates raw i = false ∧ GridCO.headTarget? o = some target ∧
      target ∈ st.base.blocks ∧ target.slot ≤ (GridCO.headLabel? o).getD 0 ∧
      Block.Preceq b target :=
  score_above_detected_witness _ _ _ b
    ((active_view_count_le p st r raw ha hl hactive).trans_lt hscore)

theorem deepest_origin (xs : List Block) : deepest xs = .genesis ∨ deepest xs ∈ xs :=
  GridCO.fold_deeper_origin xs .genesis

theorem deepest_depth (xs : List Block) (b : Block) (hb : b ∈ xs) :
    b.depth ≤ (deepest xs).depth := (GridCO.fold_deeper_depth xs .genesis).2 b hb

/-- A nonempty floor is an admitted prefix of the ordinary genesis walk
and has score strictly above f. -/
theorem floor_properties (p : Params) {n : Nat} (st : State n) (tree : List Block)
    (raw support : List (GridCO.Wire n)) (r : Slot)
    (hn : floor p st tree raw support r ≠ .genesis) :
    floor p st tree raw support r ∈ st.base.blocks ∧
      Block.Preceq (floor p st tree raw support r)
        (GridCO.ghost .genesis tree (GridCO.goldfishScore st.base.blocks raw support)
          (GridCO.goldfishEligible st.base.blocks raw support r)) ∧
      pcFaultCap p < GridCO.goldfishScore st.base.blocks raw support
        (floor p st tree raw support r) := by
  have hm := (deepest_origin (st.base.blocks.filter (fun b =>
    b != .genesis && Block.preceq b
      (GridCO.ghost .genesis tree (GridCO.goldfishScore st.base.blocks raw support)
        (GridCO.goldfishEligible st.base.blocks raw support r)) &&
      pcFaultCap p < GridCO.goldfishScore st.base.blocks raw support b))).resolve_left hn
  obtain ⟨hb, ht⟩ := List.mem_filter.mp hm
  simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at ht
  exact ⟨hb, ht.1.2, ht.2⟩

/-- The deepest floor covers every qualifying prefix of the same walk. -/
theorem floor_covers (p : Params) {n : Nat} (st : State n) (tree : List Block)
    (raw support : List (GridCO.Wire n)) (r : Slot) (b : Block)
    (hb : b ∈ st.base.blocks) (hn : b ≠ .genesis)
    (hw : Block.Preceq b
      (GridCO.ghost .genesis tree (GridCO.goldfishScore st.base.blocks raw support)
        (GridCO.goldfishEligible st.base.blocks raw support r)))
    (hs : pcFaultCap p < GridCO.goldfishScore st.base.blocks raw support b) :
    Block.Preceq b (floor p st tree raw support r) := by
  have hm : b ∈ st.base.blocks.filter (fun b => b != .genesis && Block.preceq b
      (GridCO.ghost .genesis tree (GridCO.goldfishScore st.base.blocks raw support)
        (GridCO.goldfishEligible st.base.blocks raw support r)) &&
      pcFaultCap p < GridCO.goldfishScore st.base.blocks raw support b) := by
    refine List.mem_filter.mpr ⟨hb, ?_⟩
    simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq]
    exact ⟨⟨hn, hw⟩, hs⟩
  have hd := deepest_depth _ b hm
  change b.depth ≤ (floor p st tree raw support r).depth at hd
  have hf : floor p st tree raw support r ≠ .genesis := by
    intro he
    rw [he] at hd
    cases b <;> simp_all [Block.depth]
  have hp := (floor_properties p st tree raw support r hf).2.1
  exact GridCO.preceq_of_compatible_depth_le _ _
    (GridCO.ancestors_compatible _ _ _ hw hp) hd

theorem activeVoterTree_subset (p : Params) {n : Nat} (st : State n) (r : Slot)
    (c : Option (PC n)) : activeVoterTree p st r c ⊆ st.base.blocks :=
  fun _ hb => (List.mem_filter.mp hb).1

theorem activeVoterTree_contains_plain (p : Params) {n : Nat} (st : State n) (r : Slot)
    (c : Option (PC n)) : GridCO.voterTree p.engine st.base r ⊆ activeVoterTree p st r c := by
  intro b hb
  exact List.mem_filter.mpr ⟨(List.mem_filter.mp hb).1, by simp [hb]⟩

/-- Declared support supplies an admitted path in the active duty tree. -/
theorem activeVoterTree_support_path (p : Params) {n : Nat} (st : State n)
    (hclosed : GridCO.StoredPrefixClosed st.base) (r : Slot) (c : Option (PC n))
    (o : GridCO.Wire n) (ho : o ∈ GridCO.voterSupportView p.engine st.base r)
    (target b : Block) (ht : GridCO.headTarget? o = some target)
    (hm : target ∈ st.base.blocks) (hn : b ≠ .genesis) (hb : Block.Preceq b target) :
    b ∈ activeVoterTree p st r c := by
  apply List.mem_filter.mpr
  refine ⟨hclosed target hm b hn hb, ?_⟩
  have ha : (GridCO.voterSupportView p.engine st.base r).any (fun o =>
      match GridCO.headTarget? o with
      | some h => Block.preceq b h
      | none => false) = true :=
    List.any_eq_true.mpr ⟨o, ho, by simpa only [ht] using! hb⟩
  exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr
    (Or.inl (Bool.or_eq_true_iff.mpr (Or.inr ha)))))


/-- A floor overrides any conflicting PC but keeps all mandatory finite
roots. Compatible finite roots suffice for coverage of its prefix. -/
theorem choice_covers_of_floor (p : Params) {n : Nat} (st : State n) (tree : List Block)
    (raw support : List (GridCO.Wire n)) (r : Slot) (c : Option (PC n)) (b : Block)
    (ha : capBroken p st = false)
    (hf : Block.Preceq b (floor p st tree raw support r))
    (hr : Block.Compatible (GridCO.liveRoot st.base) b) :
    Block.Preceq b (choice p st tree raw support r c) := by
  have hanchor : Block.Preceq b (preliminaryAnchor (floor p st tree raw support r) c) := by
    cases c with
    | none => exact hf
    | some cert =>
        simp only [preliminaryAnchor]
        split
        · rename_i ht
          rcases Bool.or_eq_true_iff.mp ht with hz | hp
          · have hz : floor p st tree raw support r = .genesis := by simpa using hz
            rw [hz] at hf
            have hb : b = .genesis := by simpa [Block.Preceq, Block.preceq] using hf
            rw [hb]
            exact GridCO.genesis_prefix _
          · exact GridCO.prefix_trans _ _ _ hf hp
        · exact hf
  have hroot : Block.Preceq b
      (mandatoryRoot (GridCO.liveRoot st.base)
        (preliminaryAnchor (floor p st tree raw support r) c)) := by
    unfold mandatoryRoot
    split
    · exact hanchor
    · rename_i hn
      rcases Bool.or_eq_true_iff.mp hr with hp | hp
      · exact (hn (GridCO.prefix_trans _ _ _ hp hanchor)).elim
      · exact hp
  exact GridCO.prefix_trans _ _ _ hroot (by
    simpa only [choice, ha, Bool.false_eq_true, ↓reduceIte] using!
      GridCO.ghost_extends
        (mandatoryRoot (GridCO.liveRoot st.base)
          (preliminaryAnchor (floor p st tree raw support r) c)) tree
        (GridCO.goldfishScore st.base.blocks raw support)
        (GridCO.goldfishEligible st.base.blocks raw support r))

/-- Source-transfer interface for F4. An ordinary walk covering a
prefix with score above f still covers it after arbitrary PC selection,
provided the remaining finite root is compatible with that prefix. -/
theorem choice_covers_of_ordinary_floor (p : Params) {n : Nat} (st : State n)
    (tree : List Block) (raw support : List (GridCO.Wire n)) (r : Slot)
    (c : Option (PC n)) (b : Block) (ha : capBroken p st = false)
    (hb : b ∈ st.base.blocks) (hn : b ≠ .genesis)
    (hw : Block.Preceq b
      (GridCO.ghost .genesis tree (GridCO.goldfishScore st.base.blocks raw support)
        (GridCO.goldfishEligible st.base.blocks raw support r)))
    (hs : pcFaultCap p < GridCO.goldfishScore st.base.blocks raw support b)
    (hr : Block.Compatible (GridCO.liveRoot st.base) b) :
    Block.Preceq b (choice p st tree raw support r c) :=
  choice_covers_of_floor p st tree raw support r c b ha
    (floor_covers p st tree raw support r b hb hn hw hs) hr


/-- Every above-f prefix in an active merged view is on a declared
support path in the active domain. This statement uses no fault cap. -/
theorem active_voter_score_path {V : Type} [DecidableEq V] (p : Params)
    (events : List (AvailableChain.Generic.Event V (sapc p).Object)) (v : V)
    (r : Slot) (c : Option (PC p.n)) (b : Block) (hn : b ≠ .genesis)
    (ha : capBroken p ((events.foldl AvailableChain.Generic.World.step
      AvailableChain.Generic.World.init) v) = false)
    (hs : let st := (events.foldl AvailableChain.Generic.World.step
        AvailableChain.Generic.World.init) v
      pcFaultCap p < GridCO.goldfishScore st.base.blocks
        (GridCO.voterView p.engine st.base r) (GridCO.voterSupportView p.engine st.base r) b) :
    b ∈ activeVoterTree p ((events.foldl AvailableChain.Generic.World.step
      AvailableChain.Generic.World.init) v) r c := by
  obtain ⟨_, o, target, ho, _, _, ht, hm, _, hb⟩ := active_score_witness p _ (r - 1) _ _
    (voterView_archived p _ (baseArchived_at_fold p events v)
      (frozenViewsStored_at_fold p events v) (proposalViewsArchived_at_fold p events v) r)
    (voterView_label p _ (frozenViewsStored_at_fold p events v) r) ha b hs
  exact activeVoterTree_support_path p _ (paths_at_fold p events v).1 r c o ho target b
    ht hm hn hb

end AvailableChain.SAPC
end
