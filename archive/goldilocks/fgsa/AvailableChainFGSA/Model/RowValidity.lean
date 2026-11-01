module
public import AvailableChainFGSA.Model.RowStore -- shake: keep (re-export)
public import AvailableChainFGSA.Model.RowCore -- shake: keep (re-export)

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[R6] A separate store obligation for activation. StoreBundle is unchanged. -/
def RowsValidStored (p : Params) (st : State p.n) : Prop :=
  ∀ o ∈ st.proposals, ∀ s N,
    o.decode = some (.block s N) →
    ∃ P, fgBlockOf st N.parent.erase = some P ∧ rowsValidForParent p P N.slot N.rows = true

end AvailableChain.FGSA
end
