module
public import AvailableChainFGSA.Model.Handlers
public import AvailableChainFGSA.Model.Clock
public import AvailableChainFGSA.Model.RowCore -- shake: keep (re-export)
public import AvailableChainFGSA.Model.WindowViews -- shake: keep (re-export)
public import AvailableChainKitFG.ClientOnce -- shake: keep (re-export)
public import AvailableChainFGSA.Model.FrameNext -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 616–633] The live frame: the FG module's store controls. -/
def controls (p : Params) (st : State p.n) : Controls (Fin p.n) :=
  KitFG.treeStoreControlsView (heightView p) st.fg
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 1033–1037] `get_filtered_block_tree(Σ)`. -/
def fullTree (p : Params) (st : State p.n) : Finset (FGBlock (Fin p.n)) :=
  KitFG.treeStoreFrameView (heightView p) st.fg st.fg.TF
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 1025–1037; model representation of a block set as the erased base list]
The erasure of an FG block set, in the order of the base list. -/
def erasedList {n : Nat} (st : State n) (X : Finset (FGBlock (Fin n))) : List Block :=
  st.base.blocks.filter (fun b => decide (∃ B ∈ X, eraseFG B = b))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 648–655, 1086–1098] `live_root`: the deepest live lease target in the
full filtered tree (ties: the greater root), else the FG root Z. -/
def liveRoot (p : Params) (st : State p.n) : Block :=
  let tree := fullTree p st
  let targets := st.base.obligations.filterMap (fun row =>
    if st.base.now < row.2.2 && decide (∃ B ∈ tree, eraseFG B = row.1) then some row.1 else none)
  targets.foldl (fun best b =>
    if best.depth < b.depth || (best.depth == b.depth && best.root < b.root) then b else best)
    (eraseFG (controls p st).Z)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 1063–1072] `goldfish_eligible` with the band floor: the parent's state
height is below `lo`, or a strict majority, or the store's current slot. -/
def eligible (p : Params) (st : State p.n) (raw support : List (GridCO.Wire p.n .root))
    (b : Block) :
    Bool :=
  decide (∃ P ∈ st.fg.TF, eraseFG P = b.parent ∧ (heightView p P).h < (controls p st).lo) ||
    decide (GridCO.voterCount raw < 2 * GridCO.goldfishScore st.base.blocks raw support b) ||
    b.slot == st.slot p

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 1074–1107] `get_head_in_tree`: GHOST from the live root over `tree`. -/
def headInTree (p : Params) (st : State p.n) (tree : List Block)
    (raw support : List (GridCO.Wire p.n .root)) : Block :=
  GridCO.ghost (liveRoot p st) tree (GridCO.goldfishScore st.base.blocks raw support)
    (eligible p st raw support)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 1109–1114] `get_head`: the full filtered tree. -/
def getHead (p : Params) (st : State p.n) (raw support : List (GridCO.Wire p.n .root)) : Block :=
  headInTree p st (erasedList st (fullTree p st)) raw support

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 190–193, 1288–1293; helper] The admitted slot-`s` proposals, with their
vote lists. Only proposals retained above F supply lists (port r2, change j). -/
def proposalsAt {n : Nat} (st : State n) (s : Slot) :
    List (List (HeadWire n) × List (HeadWire n)) :=
  let tree := st.fg.TF.filter (fun B => FGBlock.preceq st.fg.F B)
  st.proposals.filterMap (fun o => match o.decode with
    | some (.block _ N) =>
        if N.slot = s ∧ ∃ B ∈ tree, eraseFG B = N.erase then
          some (N.raw, N.support) else none
    | _ => none)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 598–606, 1219–1226] `voter_processed_block_tree(Σ, s)`: blocks of Σ.T
received before `z_{s−1}`, and every ancestor of an admitted slot-`s` proposal. -/
def voterBlocks (p : Params) (st : State p.n) (s : Slot) : Finset (FGBlock (Fin p.n)) :=
  (Next.tree p st).filter (fun B =>
    decide (GridCO.stampBlock st.base (eraseFG B) < SA.freezeTime p.toParams (s - 1)) ||
    decide (∃ P ∈ Next.tree p st, P.slot = s ∧ FGBlock.Preceq B P))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 606–612, 1283–1294] The HEAD raw merge: pool votes of slot `s − 1`
received before `z_{s−1}`, and the slot-`(s−1)` votes of every admitted slot-`s`
proposal. -/
def headVotes (p : Params) (st : State p.n) (s : Slot) : List (GridCO.Wire p.n .root) :=
  let frozenArm := (GridCO.votesAt st.base (s - 1)).filter (fun o =>
    decide (GridCO.stampVote st.base o < SA.freezeTime p.toParams (s - 1)))
  let carried := ((proposalsAt st s).flatMap (fun row => row.1.map baseVote)).filter
    (fun o => GridCO.headLabel? o == some (s - 1))
  (frozenArm ++ carried).eraseDups

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 423–430, 1286–1293] The HEAD support merge: pool votes resolved
before `z_{s−1}` against the CURRENT `act(Σ)`; the declared support of every
admitted slot-`s` proposal whose head is in Σ.T with a valid slot. -/
def headSupport (p : Params) (st : State p.n) (s : Slot) : List (GridCO.Wire p.n .root) :=
  let frozenArm := (GridCO.votesAt st.base (s - 1)).filter (fun o =>
    GridCO.resolvedBefore (actView st) o (SA.freezeTime p.toParams (s - 1)))
  let carried := ((proposalsAt st s).flatMap (fun row => row.2.map baseVote)).filter (fun o =>
    GridCO.headLabel? o == some (s - 1) &&
      match GridCO.resolvedHead? st.base o with
      | some h => decide (∃ B ∈ Next.tree p st, eraseFG B = h) && decide (h.slot ≤ s - 1)
      | none => false)
  (frozenArm ++ carried).eraseDups

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 1276–1302] `goldfish_vote` at `v_s`: genesis at slot 0; else the head
of the filtered voter view (live controls, M9) from the live root. Condition
(G6 O-m3): the spec sets `s ← Σ.s` (spec 1278), and `eligible` reads `Σ.s`, so
this agrees with the spec only when `s = st.slot p`; the caller (T7) must
guarantee it. -/
def headVote (p : Params) (st : State p.n) (s : Slot) : Block :=
  if s = 0 then .genesis else
    headInTree p st
      (erasedList st (KitFG.treeStoreFrameView (heightView p) st.fg (voterBlocks p st s)))
      (headVotes p st s) (headSupport p st s)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 1240–1243] The proposer's votes: every slot-`(s−1)` pool vote; the
support: those that resolve now (active head, valid slot). -/
def proposerVotes {n : Nat} (st : State n) (s : Slot) : List (GridCO.Wire n .root) :=
  GridCO.votesAt st.base (s - 1)
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 1240–1243] The proposer's support: the pool votes that resolve now
(head in `act(Σ)`, above F, valid slot; port r2, change h). -/
def proposerSupport {n : Nat} (st : State n) (s : Slot) : List (GridCO.Wire n .root) :=
  (proposerVotes st s).filter (fun o => match GridCO.resolvedHead? (actView st) o with
    | some h => Block.preceq (eraseFG st.fg.F) h && decide (h.slot ≤ s - 1)
    | none => false)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 552–553, 1264–1265; helper] The signed rows of the stored blocks on the chain
of `H`. -/
def chainWireRows {n : Nat} (st : State n) (H : Block) : List (RowWire n) :=
  (st.proposals.filterMap (fun o => match o.decode with
    | some (.block _ N) => if Block.preceq N.erase H then some N.rows else none
    | _ => none)).flatten
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[R7] All rows carried in admitted blocks. -/
def blockWireRows {n : Nat} (st : State n) : List (RowWire n) := allBlockRows st

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[R7] Select held, parent-valid rows absent from the parent chain at the
current slot. `proposalRowsFor` exposes this same selector above Frame. -/
def proposalRows (p : Params) (st : State p.n) (H : Block) : List (RowWire p.n) :=
  proposalRowsCore p chainWireRows
    (fun st b => pickPair st.fg.TF (fun B => decide (eraseFG B = b)))
    allBlockRows st (st.slot p) H

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 1236–1253; D5, D9] `propose_block` at `t_s`, `s > 0`. It selects the
geometric head and the signed rows first. It resolves the head to one distinct stored named
parent and constructs the full proposal. A missing or ambiguous named parent gives `none`.
The body packs application value `0` and the signed rows. Condition (G6 O-m3): the spec sets `s
    ← Σ.s` (spec 1238), and
`eligible` and `proposalRows` read `Σ.s`, so this agrees with the spec only
when `s = st.slot p`; the caller (T7) must guarantee it. -/
def propose (p : Params) (st : State p.n) (s : Slot) : Option (Msg p.n) :=
  if s = 0 then none else
    let raw := proposerVotes st s
    let sup := proposerSupport st s
    let H := getHead p st raw sup
    let rows := proposalRows p st H
    let rawWire := raw.filterMap liftHead?
    let supportWire := sup.filterMap liftHead?
    (namedByErase? st H).map (fun P =>
      .proposal (namedProposal p P s 0 rawWire supportWire rows))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 1318–1323] The finality head: `get_head` with the current-slot votes
and their active resolved subset. -/
def fgHead (p : Params) (st : State p.n) : Block :=
  let s := st.slot p
  let raw := GridCO.votesAt st.base s
  let sup := raw.filter (fun o => match GridCO.resolvedHead? (actView st) o with
    | some h => decide (h.slot ≤ s)
    | none => false)
  getHead p st raw sup

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 1324–1326; helper] The stored FG block of an erased block (exact under CStoreInv:
Task 11, `fgBlockOf_spec`). -/
def fgBlockOf {n : Nat} (st : State n) (b : Block) : Option (FGBlock (Fin n)) :=
  pickPair st.fg.TF (fun B => decide (eraseFG B = b))
/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[ROOT-DIGEST W1; DC NamedBlocks and RootInjectiveOnAncestors]
[spec 260–262, 1327–1335; DQ13] The deepest member (depth of the erasure);
ties: the greater root. `deepest ∅ = none`. For a nonempty set, `none` only if
two distinct maximal candidates share both depth and root (which
local store root uniqueness excludes); a tie between
members that are not maximal does not cause `none`. For a nonempty subset of
Σ.T, the result is `some` (Task 11, `deepest_spec`). -/
def deepest {n : Nat} (X : Finset (FGBlock (Fin n))) : Option (FGBlock (Fin n)) :=
  pickPair X (fun B => decide (∀ C ∈ X, (eraseFG C).depth < (eraseFG B).depth ∨
    ((eraseFG C).depth = (eraseFG B).depth ∧ C.root.value ≤ B.root.value)))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 666–677, 1327–1335] `C_fg`: the deepest block of the full filtered
tree that is in `fastWrite[rR]` and has a lease deadline after now. The set is
the one of the scheduled gate `d_{rR}`; there is no older set and no fallback. -/
def fgSource (p : Params) (st : State p.n) : Option (FGBlock (Fin p.n)) :=
  let r := p.round (st.slot p)
  let fw := (fastWriteAt st (r * p.R)).getD []
  deepest ((fullTree p st).filter (fun B => decide (eraseFG B ∈ fw) &&
    match leaseOf st (eraseFG B) with
    | some d => decide (st.base.now < d)
    | none => false))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[spec 1315–1338] `get_fg_vote`: the source and the head fields of the
finality head. The fallback fields are unreachable under CStoreInv (Task 11,
`fgHead_stored`, `fgBlockOf_spec`). -/
def fgInputs (p : Params) (st : State p.n) : Option (FGBlock (Fin p.n)) × HeadFields :=
  (fgSource p st, match fgBlockOf st (fgHead p st) with
    | some Hd => Window.headFields p p.K_W Hd
    | none => ⟨0, genesisRoot, 0⟩)

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[R2/R3/R4] The send-once client action. A suppressed row keeps the
complete durable record. The caller supplies the signing identity. -/
def attest (p : Params) (st : State p.n) (Λ : RecordOnce) (i : Fin p.n) :
    Option RowPayload × RecordOnce :=
  let x := fgInputs p st
  let y := createRowOnce p.E p.cfg Λ i x.1 x.2
  (y.1.map (fun a => .vote (RowBody.ofRow a)), y.2)

-- ROOT-DIGEST-2 option 3: generate equations in their home module (BUILD B3a).
private theorem propose_eq_1_export :
    type_of% (@propose.eq_1) := @propose.eq_1

end AvailableChain.FGSA
end
