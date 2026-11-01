module
public import AvailableChainPCSA.Model.RowStore
public import AvailableChainPCSA.Model.RowValidity

@[expose] public section

namespace AvailableChain.PCSA

/-- [PC-SA M1] [R7] Keep the first copy of each held row, then apply R6 and exact chain
exclusion. The pool precedes the admitted-block rows. There is no row limit. -/
def proposalRowsFor (p : Params) (st : State p.n) (s : Slot) (H : Block) :
    List (RowWire p.n) :=
  proposalRowsCore p chainWireRows fgBlockOf allBlockRows st s H

end AvailableChain.PCSA
end
