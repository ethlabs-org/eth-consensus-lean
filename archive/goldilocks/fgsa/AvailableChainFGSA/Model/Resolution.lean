module
public import AvailableChainFGSA.Model.Store

@[expose] public section

namespace AvailableChain.FGSA.Next

/-- [pinned spec 975–1015, 1120–1150; old spec tags 1240–1243]
The proposal support subset: resolve each previous-slot pool vote in the
cumulative domain pinned by `actView`, then require a head above F and a valid
slot. The prefix test cannot resolve an ambiguous root. Vote order is kept.
This proposal-time reader has no receipt cutoff. -/
def proposerSupportNext {n : Nat} (st : State n) (s : Slot) :
    List (GridCO.Wire n .root) :=
  (GridCO.votesAt st.base (s - 1)).filter (fun o =>
    match GridCO.resolvedHead? (actView st) o with
    | some h => Block.preceq (eraseFG st.fg.F) h && decide (h.slot ≤ s - 1)
    | none => false)

-- Generate the equation in its model module (BUILD B3a).
private theorem proposerSupportNext_eq_1_export :
    type_of% (@proposerSupportNext.eq_1) := @proposerSupportNext.eq_1

end AvailableChain.FGSA.Next
end
