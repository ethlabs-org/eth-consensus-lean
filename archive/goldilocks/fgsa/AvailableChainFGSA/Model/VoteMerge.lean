module
public import AvailableChainFGSA.Model.ContestFrame -- shake: keep (re-export)
public import AvailableChainFGSA.Model.Clock -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.FGSA.Next

open AvailableChain.SimplexFG

/-- [pinned spec 1382–1388] Read the lists of slot-s proposals retained in Φ.tree.
The proposal store remains cumulative. Erased membership uses the held FG blocks. -/
def proposalsAtNext (p : Params) (st : State p.n) (s : Slot) :
    List (List (HeadWire p.n) × List (HeadWire p.n)) :=
  st.proposals.filterMap (fun o => match o.decode with
    | some (.block _ N) =>
        if N.slot = s ∧ ∃ B ∈ tree p st, eraseFG B = N.erase then
          some (N.raw, N.support) else none
    | _ => none)

/-- [pinned spec 1365–1371] Retained blocks received before the freeze, or
ancestors of retained slot-s proposals. This is the accepted, not the viable, tree. -/
def voterBlocksNext (p : Params) (st : State p.n) (s : Slot) :
    Finset (FGBlock (Fin p.n)) :=
  (tree p st).filter (fun B =>
    decide (GridCO.stampBlock st.base (eraseFG B) < SA.freezeTime p.toParams (s - 1)) ||
    decide (∃ P ∈ tree p st, P.slot = s ∧ FGBlock.Preceq B P))

/-- [pinned spec 1377–1384] Raw votes from retained proposals enter in full,
subject to the previous-slot label test. First-occurrence order is kept. -/
def headVotesNext (p : Params) (st : State p.n) (s : Slot) : List (GridCO.Wire p.n .root) :=
  let frozenArm := (GridCO.votesAt st.base (s - 1)).filter (fun o =>
    decide (GridCO.stampVote st.base o < SA.freezeTime p.toParams (s - 1)))
  let carried := ((proposalsAtNext p st s).flatMap (fun row => row.1.map baseVote)).filter
    (fun o => GridCO.headLabel? o == some (s - 1))
  (frozenArm ++ carried).eraseDups

/-- [pinned spec 1380–1388; minimal derisk (j)] Keep the frozen arm unchanged.
Resolve carried heads in the cumulative domain, then require membership in
Φ.tree and the existing slot bound. Ambiguous roots remain unresolved. -/
def headSupportNext (p : Params) (st : State p.n) (s : Slot) : List (GridCO.Wire p.n .root) :=
  let frozenArm := (GridCO.votesAt st.base (s - 1)).filter (fun o =>
    GridCO.resolvedBefore (actView st) o (SA.freezeTime p.toParams (s - 1)))
  let carried := ((proposalsAtNext p st s).flatMap (fun row => row.2.map baseVote)).filter
    (fun o => GridCO.headLabel? o == some (s - 1) &&
      match GridCO.resolvedHead? st.base o with
      | some h => decide (∃ B ∈ tree p st, eraseFG B = h) && decide (h.slot ≤ s - 1)
      | none => false)
  (frozenArm ++ carried).eraseDups

private theorem proposalsAtNext_eq_1_export :
    type_of% (@proposalsAtNext.eq_1) := @proposalsAtNext.eq_1
private theorem voterBlocksNext_eq_1_export :
    type_of% (@voterBlocksNext.eq_1) := @voterBlocksNext.eq_1
private theorem headVotesNext_eq_1_export :
    type_of% (@headVotesNext.eq_1) := @headVotesNext.eq_1
private theorem headSupportNext_eq_1_export :
    type_of% (@headSupportNext.eq_1) := @headSupportNext.eq_1

end AvailableChain.FGSA.Next
end
