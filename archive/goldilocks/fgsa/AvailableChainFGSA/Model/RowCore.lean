module
public import AvailableChainFGSA.Model.Store
public import AvailableChainFGSA.Model.WindowViews

@[expose] public section

namespace AvailableChain.FGSA

open AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[R7] All signed rows of admitted proposals, in stored order. -/
def allBlockRows {n : Nat} (st : State n) : List (RowWire n) :=
  (st.proposals.filterMap (fun o => match o.decode with
    | some (.block _ N) => some N.rows
    | _ => none)).flatten

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[R6W] The window parent post-state with the child slot, before the row fold. -/
def parentFoldState (p : Params) (s : Slot) (P : FGBlock (Fin p.n)) :
    Window.State (Fin p.n) :=
  Window.parentState p p.K_W P s

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[R6] Check every row against the same state before any row is folded. -/
def rowsValidForParent (p : Params) (P : FGBlock (Fin p.n)) (s : Slot)
    (rows : List (RowWire p.n)) : Bool :=
  rows.all (Window.rowValidW (parentFoldState p s P))

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
[R7] Select held rows with the supplied chain and parent lookup functions.
This core does not depend on Frame. -/
def proposalRowsCore (p : Params)
    (chainRows : State p.n → Block → List (RowWire p.n))
    (blockOf : State p.n → Block → Option (FGBlock (Fin p.n)))
    (blockRows : State p.n → List (RowWire p.n))
    (st : State p.n) (s : Slot) (H : Block) : List (RowWire p.n) :=
  match blockOf st H with
  | none => []
  | some P =>
      (st.rowPool ++ blockRows st).eraseDups.filter (fun a =>
        Window.rowValidW (parentFoldState p s P) a && !decide (a ∈ chainRows st H))

end AvailableChain.FGSA
end
