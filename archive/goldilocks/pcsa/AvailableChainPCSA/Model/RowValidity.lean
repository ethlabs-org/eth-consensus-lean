module
public import AvailableChainPCSA.Model.RowStore
public import AvailableChainPCSA.Model.RowCore

@[expose] public section

namespace AvailableChain.PCSA

open AvailableChain.SimplexFG

/-- [PC-SA M1] [R6] A separate store obligation for activation. StoreBundle is unchanged. -/
def RowsValidStored (p : Params) (st : State p.n) : Prop :=
  ∀ o ∈ st.proposals, ∀ s N,
    o.decode = some (.block s N) →
    ∃ P, fgBlockOf st N.parent.erase = some P ∧ rowsValidForParent p P N.slot N.rows = true

end AvailableChain.PCSA
end
