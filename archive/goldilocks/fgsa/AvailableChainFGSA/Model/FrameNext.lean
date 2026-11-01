module
public import AvailableChainFGSA.Model.Handlers -- shake: keep (re-export)
public import AvailableChainFGSA.Model.Clock -- shake: keep (re-export)
public import AvailableChainFGSA.Model.RowCore -- shake: keep (re-export)
public import AvailableChainFGSA.Model.WindowViews -- shake: keep (re-export)
public import AvailableChainKitFG.ClientOnce

public import AvailableChainFGSA.Model.VoteMerge
public import AvailableChainFGSA.Model.Resolution

@[expose] public section

namespace AvailableChain.FGSA.Next

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 648–655, 1086–1098] `live_root`: the deepest live lease target in the
full filtered tree (ties: the greater root), else the FG root Z. -/
def liveRootNext (p : Params) (st : State p.n) : Block :=
  let tree := fullTree p st
  let targets := st.base.obligations.filterMap (fun row =>
    if st.base.now < row.2.2 && decide (∃ B ∈ tree, eraseFG B = row.1) then some row.1 else none)
  targets.foldl (fun best b =>
    if best.depth < b.depth || (best.depth == b.depth && best.root < b.root) then b else best)
    (eraseFG (controls p st).Z)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 1063–1072] `goldfish_eligible` with the band floor: the parent's state
height is below `lo`, or a strict majority, or the store's current slot. -/
def eligibleNext (p : Params) (st : State p.n) (raw support : List (GridCO.Wire p.n .root))
    (b : Block) :
    Bool :=
  decide (∃ P ∈ st.fg.TF, eraseFG P = b.parent ∧ (heightView p P).h < (controls p st).lo) ||
    decide (GridCO.voterCount raw < 2 * GridCO.goldfishScore st.base.blocks raw support b) ||
    b.slot == st.slot p

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 1074–1107] `get_head_in_tree`: GHOST from the live root over `tree`. -/
def headInTreeNext (p : Params) (st : State p.n) (tree : List Block)
    (raw support : List (GridCO.Wire p.n .root)) : Block :=
  GridCO.ghost (liveRootNext p st) tree (GridCO.goldfishScore st.base.blocks raw support)
    (eligibleNext p st raw support)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 1109–1114] `get_head`: the full filtered tree. -/
def getHeadNext (p : Params) (st : State p.n)
    (raw support : List (GridCO.Wire p.n .root)) : Block :=
  headInTreeNext p st (erasedList st (fullTree p st)) raw support

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 1276–1302] `goldfish_vote` at `v_s`: genesis at slot 0; else the head
of the filtered voter view (live controls, M9) from the live root. Condition
(G6 O-m3): the spec sets `s ← Σ.s` (spec 1278), and `eligibleNext` reads `Σ.s`, so
this agrees with the spec only when `s = st.slot p`; the caller (T7) must
guarantee it. -/
def headVoteNext (p : Params) (st : State p.n) (s : Slot) : Block :=
  if s = 0 then .genesis else
    headInTreeNext p st
      (erasedList st (KitFG.treeStoreFrameView (heightView p) st.fg (voterBlocksNext p st s)))
      (headVotesNext p st s) (headSupportNext p st s)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 1240–1243] The proposer's votes: every slot-`(s−1)` pool vote; the
support: those that resolve now (active head, valid slot). -/
def proposerVotesNext {n : Nat} (st : State n) (s : Slot) : List (GridCO.Wire n .root) :=
  GridCO.votesAt st.base (s - 1)
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 552–553, 1264–1265; helper] The signed rows of the stored blocks on the chain
of `H`. -/
def chainWireRowsNext {n : Nat} (st : State n) (H : Block) : List (RowWire n) :=
  (st.proposals.filterMap (fun o => match o.decode with
    | some (.block _ N) => if Block.preceq N.erase H then some N.rows else none
    | _ => none)).flatten
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[R7] All rows carried in admitted blocks. -/
def blockWireRowsNext {n : Nat} (st : State n) : List (RowWire n) := allBlockRows st

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[R7] Select held, parent-valid rows absent from the parent chain at the
current slot. `proposalRowsFor` exposes this same selector above Frame. -/
def proposalRowsNext (p : Params) (st : State p.n) (H : Block) : List (RowWire p.n) :=
  proposalRowsCore p chainWireRowsNext
    (fun st b => pickPair st.fg.TF (fun B => decide (eraseFG B = b)))
    allBlockRows st (st.slot p) H

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 1236–1253; D5, D9] `propose_block` at `t_s`, `s > 0`. It selects the
geometric head and the signed rows first. It resolves the head to one distinct stored named
parent and constructs the full proposal. A missing or ambiguous named parent gives `none`.
The body packs application value `0` and the signed rows. Condition (G6 O-m3): the spec sets `s
    ← Σ.s` (spec 1238), and
`eligibleNext` and `proposalRowsNext` read `Σ.s`, so this agrees with the spec only
when `s = st.slot p`; the caller (T7) must guarantee it. -/
def proposeNext (p : Params) (st : State p.n) (s : Slot) : Option (Msg p.n) :=
  if s = 0 then none else
    let raw := proposerVotesNext st s
    let sup := proposerSupportNext st s
    let H := getHeadNext p st raw sup
    let rows := proposalRowsNext p st H
    let rawWire := raw.filterMap liftHead?
    let supportWire := sup.filterMap liftHead?
    (namedByErase? st H).map (fun P =>
      .proposal (namedProposal p P s 0 rawWire supportWire rows))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 1318–1323] The finality head: `get_head` with the current-slot votes
and their active resolved subset. -/
def fgHeadNext (p : Params) (st : State p.n) : Block :=
  let s := st.slot p
  let raw := GridCO.votesAt st.base s
  let sup := raw.filter (fun o => match GridCO.resolvedHead? (actView st) o with
    | some h => decide (h.slot ≤ s)
    | none => false)
  getHeadNext p st raw sup

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 1324–1326; helper] The stored FG block of an erased block (exact under CStoreInv:
Task 11, `fgBlockOf_spec`). -/
def fgBlockOfNext {n : Nat} (st : State n) (b : Block) : Option (FGBlock (Fin n)) :=
  pickPair st.fg.TF (fun B => decide (eraseFG B = b))
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
[spec 260–262, 1327–1335; DQ13] The deepest member (depth of the erasure);
ties: the greater root. `deepestNext ∅ = none`. For a nonempty set, `none` only if
two distinct maximal candidates share both depth and root (which
local store root uniqueness excludes); a tie between
members that are not maximal does not cause `none`. For a nonempty subset of
Σ.T, the result is `some` (Task 11, `deepest_spec`). -/
def deepestNext {n : Nat} (X : Finset (FGBlock (Fin n))) : Option (FGBlock (Fin n)) :=
  pickPair X (fun B => decide (∀ C ∈ X, (eraseFG C).depth < (eraseFG B).depth ∨
    ((eraseFG C).depth = (eraseFG B).depth ∧ C.root.value ≤ B.root.value)))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 666–677, 1327–1335] `C_fg`: the deepest block of the full filtered
tree that is in `fastWrite[rR]` and has a lease deadline after now. The set is
the one of the scheduled gate `d_{rR}`; there is no older set and no fallback. -/
def fgSourceNext (p : Params) (st : State p.n) : Option (FGBlock (Fin p.n)) :=
  let r := p.round (st.slot p)
  let fw := (fastWriteAt st (r * p.R)).getD []
  deepestNext ((fullTree p st).filter (fun B => decide (eraseFG B ∈ fw) &&
    match leaseOf st (eraseFG B) with
    | some d => decide (st.base.now < d)
    | none => false))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 1315–1338] `get_fg_vote`: the source and the head fields of the
finality head. The fallback fields are unreachable under CStoreInv (Task 11,
`fgHead_stored`, `fgBlockOf_spec`). -/
def fgInputsNext (p : Params) (st : State p.n) : Option (FGBlock (Fin p.n)) × HeadFields :=
  (fgSourceNext p st, match fgBlockOfNext st (fgHeadNext p st) with
    | some Hd => Window.headFields p p.K_W Hd
    | none => ⟨0, genesisRoot, 0⟩)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[R2/R3/R4] The send-once client action. A suppressed row keeps the
complete durable record. The caller supplies the signing identity. -/
def attestNext (p : Params) (st : State p.n) (Λ : RecordOnce) (i : Fin p.n) :
    Option RowPayload × RecordOnce :=
  let x := fgInputsNext p st
  let y := createRowOnce p.E p.cfg Λ i x.1 x.2
  (y.1.map (fun a => .vote (RowBody.ofRow a)), y.2)

private theorem liveRootNext_eq_1_export :
    type_of% (@liveRootNext.eq_1) := @liveRootNext.eq_1
private theorem eligibleNext_eq_1_export :
    type_of% (@eligibleNext.eq_1) := @eligibleNext.eq_1
private theorem headInTreeNext_eq_1_export :
    type_of% (@headInTreeNext.eq_1) := @headInTreeNext.eq_1
private theorem getHeadNext_eq_1_export :
    type_of% (@getHeadNext.eq_1) := @getHeadNext.eq_1
private theorem headVoteNext_eq_1_export :
    type_of% (@headVoteNext.eq_1) := @headVoteNext.eq_1
private theorem proposerVotesNext_eq_1_export :
    type_of% (@proposerVotesNext.eq_1) := @proposerVotesNext.eq_1
private theorem chainWireRowsNext_eq_1_export :
    type_of% (@chainWireRowsNext.eq_1) := @chainWireRowsNext.eq_1
private theorem blockWireRowsNext_eq_1_export :
    type_of% (@blockWireRowsNext.eq_1) := @blockWireRowsNext.eq_1
private theorem proposalRowsNext_eq_1_export :
    type_of% (@proposalRowsNext.eq_1) := @proposalRowsNext.eq_1
private theorem proposeNext_eq_1_export :
    type_of% (@proposeNext.eq_1) := @proposeNext.eq_1
private theorem fgHeadNext_eq_1_export :
    type_of% (@fgHeadNext.eq_1) := @fgHeadNext.eq_1
private theorem fgBlockOfNext_eq_1_export :
    type_of% (@fgBlockOfNext.eq_1) := @fgBlockOfNext.eq_1
private theorem deepestNext_eq_1_export :
    type_of% (@deepestNext.eq_1) := @deepestNext.eq_1
private theorem fgSourceNext_eq_1_export :
    type_of% (@fgSourceNext.eq_1) := @fgSourceNext.eq_1
private theorem fgInputsNext_eq_1_export :
    type_of% (@fgInputsNext.eq_1) := @fgInputsNext.eq_1
private theorem attestNext_eq_1_export :
    type_of% (@attestNext.eq_1) := @attestNext.eq_1

end AvailableChain.FGSA.Next
end
