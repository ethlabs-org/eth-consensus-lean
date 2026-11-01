module
public import AvailableChainFGSA.Model.Store

@[expose] public section

namespace AvailableChain.FGSA.Next

open AvailableChain.SimplexFG

/-- [spec 274–275, 305–326, 339–353, 527–540] `Φ.tree`: the accepted blocks above F.
`st.fg.TF` holds the cumulative accepted FG blocks, including their rows;
`admitBlock` inserts into this set through `Window.on_block`. The erased base
list is its SA representation. This reader filters TF without changing the
store or the cumulative resolution domain. It does not apply the viable
frame filter and does not include strict ancestors of F. -/
def tree (p : Params) (st : State p.n) : Finset (FGBlock (Fin p.n)) :=
  st.fg.TF.filter (fun B => FGBlock.preceq st.fg.F B)

/-- [spec 305–326, 975–1015; model representation of a block set as an erased list]
Erase an FG block set in the order of the cumulative base list. A resolution
reader can use `erasedList st (tree p st)` for membership after it resolves a
root in the cumulative domain. This helper does not resolve roots. -/
def erasedList {n : Nat} (st : State n) (X : Finset (FGBlock (Fin n))) : List Block :=
  st.base.blocks.filter (fun b => decide (∃ B ∈ X, eraseFG B = b))

-- Generate equations in their model module (BUILD B3a).
private theorem tree_eq_1_export :
    type_of% (@tree.eq_1) := @tree.eq_1
private theorem erasedList_eq_1_export :
    type_of% (@erasedList.eq_1) := @erasedList.eq_1

end AvailableChain.FGSA.Next
end
