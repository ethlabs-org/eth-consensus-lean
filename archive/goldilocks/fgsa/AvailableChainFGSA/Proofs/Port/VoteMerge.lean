module
public import AvailableChainFGSA.Model.FrameNext -- shake: keep (re-export)
public import AvailableChainFGSA.Model.Legacy.Frame -- shake: keep (re-export)
public import AvailableChainFGSA.Proofs.Port.ContestFrame -- shake: keep (re-export)
public import AvailableChainFGSA.Proofs.Port.Tree

public section

namespace AvailableChain.FGSA.Legacy

/-! The Legacy chain has the pre-SWITCH canonical bodies. For switched readers,
state that old body explicitly; unchanged readers still equal the canonical reader.
The comparisons below relate the old reads to the current canonical reads. -/

open AvailableChain.SimplexFG

theorem controls_eq (p : Params) (st : State p.n) :
    controls p st =
      KitFG.storeControlsView (heightView p) st.fg := rfl

theorem fullTree_eq (p : Params) (st : State p.n) :
    fullTree p st =
      KitFG.storeFrameView (heightView p) st.fg st.fg.TF := rfl

theorem erasedList_eq : @erasedList = @FGSA.erasedList := rfl

theorem liveRoot_eq (p : Params) (st : State p.n) :
    liveRoot p st =
      let tree := fullTree p st
      let targets := st.base.obligations.filterMap (fun row =>
        if st.base.now < row.2.2 && decide (∃ B ∈ tree, eraseFG B = row.1)
          then some row.1 else none)
      targets.foldl (fun best b =>
        if best.depth < b.depth || (best.depth == b.depth && best.root < b.root) then b else best)
        (eraseFG (controls p st).Z) := rfl

theorem legacy_eligible_eq (p : Params) (st : State p.n)
    (raw support : List (GridCO.Wire p.n .root))
    (b : Block) :
    eligible p st raw support b =
      (decide (∃ P ∈ st.fg.TF, eraseFG P = b.parent ∧ (heightView p P).h < (controls p st).lo) ||
        decide (GridCO.voterCount raw < 2 * GridCO.goldfishScore st.base.blocks raw support b) ||
        b.slot == st.slot p) := rfl

theorem headInTree_eq (p : Params) (st : State p.n) (tree : List Block)
    (raw support : List (GridCO.Wire p.n .root)) :
    headInTree p st tree raw support =
      GridCO.ghost (liveRoot p st) tree (GridCO.goldfishScore st.base.blocks raw support)
        (eligible p st raw support) := rfl

theorem getHead_eq (p : Params) (st : State p.n) (raw support : List (GridCO.Wire p.n .root)) :
    getHead p st raw support =
      headInTree p st (erasedList st (fullTree p st)) raw support := rfl

theorem proposalsAt_eq {n : Nat} (st : State n) (s : Slot) :
    proposalsAt st s =
      st.proposals.filterMap (fun o => match o.decode with
        | some (.block _ N) => if N.slot = s then some (N.raw, N.support) else none
        | _ => none) := rfl

theorem voterBlocks_eq (p : Params) (st : State p.n) (s : Slot) :
    voterBlocks p st s =
      st.fg.TF.filter (fun B =>
        decide (GridCO.stampBlock st.base (eraseFG B) < SA.freezeTime p.toParams (s - 1)) ||
        decide (∃ P ∈ st.fg.TF, P.slot = s ∧ FGBlock.Preceq B P)) := rfl

theorem headVotes_eq (p : Params) (st : State p.n) (s : Slot) :
    headVotes p st s =
      let frozenArm := (GridCO.votesAt st.base (s - 1)).filter (fun o =>
        decide (GridCO.stampVote st.base o < SA.freezeTime p.toParams (s - 1)))
      let carried := ((proposalsAt st s).flatMap (fun row => row.1.map baseVote)).filter
        (fun o => GridCO.headLabel? o == some (s - 1))
      (frozenArm ++ carried).eraseDups := rfl

theorem headSupport_eq (p : Params) (st : State p.n) (s : Slot) :
    headSupport p st s =
      let frozenArm := (GridCO.votesAt st.base (s - 1)).filter (fun o =>
        GridCO.resolvedBefore (actView st) o (SA.freezeTime p.toParams (s - 1)))
      let carried := ((proposalsAt st s).flatMap (fun row => row.2.map baseVote)).filter (fun o =>
        GridCO.headLabel? o == some (s - 1) &&
          match GridCO.resolvedHead? st.base o with
          | some h => decide (h.slot ≤ s - 1)
          | none => false)
      (frozenArm ++ carried).eraseDups := rfl

theorem headVote_eq (p : Params) (st : State p.n) (s : Slot) :
    headVote p st s =
      if s = 0 then .genesis else
        headInTree p st
          (erasedList st (KitFG.storeFrameView (heightView p) st.fg (voterBlocks p st s)))
          (headVotes p st s) (headSupport p st s) := rfl

theorem proposerVotes_eq : @proposerVotes = @FGSA.proposerVotes := rfl

theorem proposerSupport_eq {n : Nat} (st : State n) (s : Slot) :
    proposerSupport st s =
      (proposerVotes st s).filter (fun o => match GridCO.resolvedHead? (actView st) o with
        | some h => decide (h.slot ≤ s - 1)
        | none => false) := rfl

theorem chainWireRows_eq : @chainWireRows = @FGSA.chainWireRows := rfl

theorem blockWireRows_eq : @blockWireRows = @FGSA.blockWireRows := rfl

theorem proposalRows_eq : @proposalRows = @FGSA.proposalRows := rfl

theorem propose_eq (p : Params) (st : State p.n) (s : Slot) :
    propose p st s =
      if s = 0 then none else
        let raw := proposerVotes st s
        let sup := proposerSupport st s
        let H := getHead p st raw sup
        let rows := proposalRows p st H
        let rawWire := raw.filterMap liftHead?
        let supportWire := sup.filterMap liftHead?
        (namedByErase? st H).map (fun P =>
          .proposal (namedProposal p P s 0 rawWire supportWire rows)) := rfl

theorem fgHead_eq (p : Params) (st : State p.n) :
    fgHead p st =
      let s := st.slot p
      let raw := GridCO.votesAt st.base s
      let sup := raw.filter (fun o => match GridCO.resolvedHead? (actView st) o with
        | some h => decide (h.slot ≤ s)
        | none => false)
      getHead p st raw sup := rfl

theorem fgBlockOf_eq : @fgBlockOf = @FGSA.fgBlockOf := rfl

theorem deepest_eq : @deepest = @FGSA.deepest := rfl

theorem fgSource_eq (p : Params) (st : State p.n) :
    fgSource p st =
      let r := p.round (st.slot p)
      let fw := (fastWriteAt st (r * p.R)).getD []
      deepest ((fullTree p st).filter (fun B => decide (eraseFG B ∈ fw) &&
        match leaseOf st (eraseFG B) with
        | some d => decide (st.base.now < d)
        | none => false)) := rfl

theorem fgInputs_eq (p : Params) (st : State p.n) :
    fgInputs p st =
      (fgSource p st, match fgBlockOf st (fgHead p st) with
        | some Hd => Window.headFields p p.K_W Hd
        | none => ⟨0, genesisRoot, 0⟩) := rfl

theorem attest_eq (p : Params) (st : State p.n) (Λ : RecordOnce) (i : Fin p.n) :
    attest p st Λ i =
      let x := fgInputs p st
      let y := createRowOnce p.E p.cfg Λ i x.1 x.2
      (y.1.map (fun a => .vote (RowBody.ofRow a)), y.2) := rfl

end AvailableChain.FGSA.Legacy

namespace AvailableChain.FGSA.Next

open AvailableChain.SimplexFG

/-- Pure comparison: every selected proposal is still held above F. -/
theorem proposalsAtNext_eq_of_retained (p : Params) (st : State p.n) (s : Slot)
    (hP : ∀ o ∈ st.proposals, ∀ r N, o.decode = some (.block r N) → N.slot = s →
      ∃ B ∈ tree p st, eraseFG B = N.erase) :
    proposalsAtNext p st s = proposalsAt st s := by
  unfold proposalsAtNext proposalsAt
  apply List.filterMap_congr
  intro o ho
  cases hd : o.decode with
  | none => rfl
  | some d =>
      cases d with
      | block r N =>
          dsimp only
          by_cases hs : N.slot = s
          · simp [hs, hP o ho r N hd hs]
            simpa only [tree, Finset.mem_filter, and_assoc] using hP o ho r N hd hs
          · simp [hs]
      | vote r i h => rfl
      | row i r => rfl

/-- Raw merge equality only needs equality of the retained proposal lists. -/
theorem headVotesNext_eq_of_proposals (p : Params) (st : State p.n) (s : Slot)
    (hP : proposalsAtNext p st s = proposalsAt st s) :
    headVotesNext p st s = headVotes p st s := by
  delta headVotesNext headVotes
  rw [hP]

/-- The new voter view agrees when every held block extends F. -/
theorem voterBlocksNext_eq_of_tree (p : Params) (st : State p.n) (s : Slot)
    (hT : tree p st = st.fg.TF) : voterBlocksNext p st s = voterBlocks p st s := by
  have _ := hT
  rfl

/-- Pure support comparison. Only carried heads with the correct label and
slot need retention. There is no new condition on the frozen arm. -/
theorem headSupportNext_eq_of_retained (p : Params) (st : State p.n) (s : Slot)
    (hP : proposalsAtNext p st s = proposalsAt st s)
    (hH : ∀ o ∈ (proposalsAt st s).flatMap (fun row => row.2.map baseVote),
      GridCO.headLabel? o = some (s - 1) → ∀ h,
      GridCO.resolvedHead? st.base o = some h → h.slot ≤ s - 1 →
      ∃ B ∈ tree p st, eraseFG B = h) :
    headSupportNext p st s = headSupport p st s := by
  have _ := hH
  delta headSupportNext headSupport
  rw [hP]
  rfl

/-- The tree condition can be supplied by a pure prefix fact on held blocks. -/
theorem tree_eq_of_all_extends (p : Params) (st : State p.n)
    (hF : ∀ B ∈ st.fg.TF, FGBlock.Preceq st.fg.F B) : tree p st = st.fg.TF := by
  apply Finset.filter_eq_self.mpr
  exact hF

/-- Once the live controls agree, the full viable trees agree as well. -/
theorem fullTree_eq_of_controls (p : Params) (st : State p.n)
    (hc : controls p st = FGSA.controls p st) : fullTree p st = FGSA.fullTree p st := by
  have _ := hc
  rfl

/-- Live leases are selected by the copied fold over the guarded full tree. -/
theorem liveRootNext_eq_of_controls (p : Params) (st : State p.n)
    (hc : controls p st = FGSA.controls p st) : liveRootNext p st = liveRoot p st := by
  have _ := hc
  rfl

/-- Eligibility keeps the cumulative parent heights and uses the new floor. -/
theorem eligibleNext_eq_of_controls (p : Params) (st : State p.n)
    (hc : controls p st = FGSA.controls p st) : eligibleNext p st = eligible p st := by
  have _ := hc
  rfl

theorem headInTreeNext_eq_of_controls (p : Params) (st : State p.n)
    (hc : controls p st = FGSA.controls p st) : headInTreeNext p st = headInTree p st := by
  have _ := hc
  rfl

theorem getHeadNext_eq_of_controls (p : Params) (st : State p.n)
    (hc : controls p st = FGSA.controls p st) : getHeadNext p st = getHead p st := by
  have _ := hc
  rfl

/-- The guarded voter walk agrees when controls, the voter tree, and both
merges agree. The preceding lemmas give pure retention conditions for them. -/
theorem headVoteNext_eq_of_reads (p : Params) (st : State p.n) (s : Slot)
    (hc : controls p st = FGSA.controls p st)
    (hT : voterBlocksNext p st s = voterBlocks p st s)
    (hV : headVotesNext p st s = headVotes p st s)
    (hS : headSupportNext p st s = headSupport p st s) :
    headVoteNext p st s = headVote p st s := by
  delta headVoteNext headVote
  rw [hT, hV, hS, headInTreeNext_eq_of_controls p st hc]
  rfl

/-- Compare retained proposal reads with the pre-SWITCH canonical chain. -/
theorem port_proposalsAt_eq_legacy_of_retained (p : Params) (st : State p.n) (s : Slot)
    (hP : ∀ o ∈ st.proposals, ∀ r N, o.decode = some (.block r N) → N.slot = s →
      ∃ B ∈ tree p st, eraseFG B = N.erase) :
    proposalsAtNext p st s = Legacy.proposalsAt st s := by
  unfold proposalsAtNext Legacy.proposalsAt
  apply List.filterMap_congr
  intro o ho
  cases hd : o.decode with
  | none => rfl
  | some d =>
      cases d with
      | block r N =>
          by_cases hs : N.slot = s
          · simp [hs, hP o ho r N hd hs]
          · simp [hs]
      | vote r i h => rfl
      | row i r => rfl

theorem port_headVotes_eq_legacy_of_proposals (p : Params) (st : State p.n) (s : Slot)
    (hP : proposalsAtNext p st s = Legacy.proposalsAt st s) :
    headVotesNext p st s = Legacy.headVotes p st s := by
  delta headVotesNext Legacy.headVotes
  rw [hP]

theorem port_voterBlocks_eq_legacy_of_tree (p : Params) (st : State p.n) (s : Slot)
    (hT : tree p st = st.fg.TF) : voterBlocksNext p st s = Legacy.voterBlocks p st s := by
  delta voterBlocksNext Legacy.voterBlocks
  rw [hT]

theorem port_headSupport_eq_legacy_of_retained (p : Params) (st : State p.n) (s : Slot)
    (hP : proposalsAtNext p st s = Legacy.proposalsAt st s)
    (hH : ∀ o ∈ (Legacy.proposalsAt st s).flatMap (fun row => row.2.map baseVote),
      GridCO.headLabel? o = some (s - 1) → ∀ h,
      GridCO.resolvedHead? st.base o = some h → h.slot ≤ s - 1 →
      ∃ B ∈ tree p st, eraseFG B = h) :
    headSupportNext p st s = Legacy.headSupport p st s := by
  delta headSupportNext Legacy.headSupport
  rw [hP]
  dsimp only
  apply congrArg List.eraseDups
  apply congrArg (List.append _)
  apply List.filter_congr
  intro o ho
  by_cases hl : GridCO.headLabel? o = some (s - 1)
  · cases hr : GridCO.resolvedHead? st.base o with
    | none => rfl
    | some h =>
        change (GridCO.headLabel? o == some (s - 1) &&
            (decide (∃ B ∈ tree p st, eraseFG B = h) && decide (h.slot ≤ s - 1))) =
          (GridCO.headLabel? o == some (s - 1) && decide (h.slot ≤ s - 1))
        by_cases hs : h.slot ≤ s - 1
        · simp [hl, hs, hH o ho hl h hr hs]
        · simp [hs]
  · have hb : (GridCO.headLabel? o == some (s - 1)) = false := by
      exact beq_eq_false_iff_ne.mpr hl
    rw [hb, Bool.false_and, Bool.false_and]

theorem port_fullTree_eq_legacy_of_controls (p : Params) (st : State p.n)
    (hc : controls p st = Legacy.controls p st) : fullTree p st = Legacy.fullTree p st := by
  unfold fullTree Legacy.fullTree KitFG.treeStoreFrameView KitFG.storeFrameView
  change KitFG.filteredFromView (heightView p) (controls p st) st.fg.TF = _
  rw [hc]
  rfl

theorem port_liveRoot_eq_legacy_of_controls (p : Params) (st : State p.n)
    (hc : controls p st = Legacy.controls p st) : liveRootNext p st = Legacy.liveRoot p st := by
  delta liveRootNext Legacy.liveRoot
  rw [port_fullTree_eq_legacy_of_controls p st hc, hc]

theorem port_eligible_eq_legacy_of_controls (p : Params) (st : State p.n)
    (hc : controls p st = Legacy.controls p st) : eligibleNext p st = Legacy.eligible p st := by
  funext raw support b
  delta eligibleNext Legacy.eligible
  rw [hc]

theorem port_headInTree_eq_legacy_of_controls (p : Params) (st : State p.n)
    (hc : controls p st = Legacy.controls p st) : headInTreeNext p st = Legacy.headInTree p st := by
  funext T raw support
  delta headInTreeNext Legacy.headInTree
  rw [port_liveRoot_eq_legacy_of_controls p st hc,
    port_eligible_eq_legacy_of_controls p st hc]

theorem port_getHead_eq_legacy_of_controls (p : Params) (st : State p.n)
    (hc : controls p st = Legacy.controls p st) : getHeadNext p st = Legacy.getHead p st := by
  funext raw support
  delta getHeadNext Legacy.getHead
  rw [port_fullTree_eq_legacy_of_controls p st hc, erasedList_eq,
    port_headInTree_eq_legacy_of_controls p st hc]
  rfl

theorem port_headVote_eq_legacy_of_reads (p : Params) (st : State p.n) (s : Slot)
    (hc : controls p st = Legacy.controls p st)
    (hT : voterBlocksNext p st s = Legacy.voterBlocks p st s)
    (hV : headVotesNext p st s = Legacy.headVotes p st s)
    (hS : headSupportNext p st s = Legacy.headSupport p st s) :
    headVoteNext p st s = Legacy.headVote p st s := by
  have hf : KitFG.treeStoreFrameView (heightView p) st.fg (Legacy.voterBlocks p st s) =
      KitFG.storeFrameView (heightView p) st.fg (Legacy.voterBlocks p st s) := by
    unfold KitFG.treeStoreFrameView KitFG.storeFrameView
    change KitFG.filteredFromView (heightView p) (controls p st) _ = _
    rw [hc]
    rfl
  delta headVoteNext Legacy.headVote
  rw [hT, hV, hS, hf, erasedList_eq,
    port_headInTree_eq_legacy_of_controls p st hc]
  rfl

end AvailableChain.FGSA.Next
end
