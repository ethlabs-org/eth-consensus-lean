module
public import AvailableChainPCSA.Model.Store
public import AvailableChainFGSA.Model.WindowViews
public import AvailableChainKitFG.ClientOnce

@[expose] public section

namespace AvailableChain.PCSA

open AvailableChain.Generic AvailableChain.SimplexFG

/-- [PC-SA M1; pcsa34-r4.3 §3.7 (i)] Read the live FG frame controls. -/
def controls (p : Params) (st : State p.n) : Controls (Fin p.n) :=
  KitFG.storeControlsView (FGSA.heightView p) st.fg

theorem controls_def (p : Params) (st : State p.n) :
    controls p st = KitFG.storeControlsView (FGSA.heightView p) st.fg := rfl

/-- [PC-SA M1; pcsa34-r4.3 §3.7 (i)] Read the full filtered FG tree. -/
def fullTree (p : Params) (st : State p.n) : Finset (FGBlock (Fin p.n)) :=
  KitFG.storeFrameView (FGSA.heightView p) st.fg st.fg.TF

theorem fullTree_def (p : Params) (st : State p.n) :
    fullTree p st = KitFG.storeFrameView (FGSA.heightView p) st.fg st.fg.TF := rfl

/-- [PC-SA M1; pcsa34-r4.3 §3.7] Erase an FG block set. Keep the
order of the base block list. -/
def erasedList {n : Nat} (st : State n) (X : Finset (FGBlock (Fin n))) : List Block :=
  st.base.blocks.filter (fun b => decide (∃ B ∈ X, eraseFG B = b))

theorem erasedList_def {n : Nat} (st : State n) (X : Finset (FGBlock (Fin n))) :
    erasedList st X = st.base.blocks.filter (fun b => decide (∃ B ∈ X, eraseFG B = b)) := rfl

/-- [PC-SA M1; pcsa34-r4.3 §3.7 (i), 3.3 frame_active] A PC is active
when its target is in the full filtered tree at the time of the read. -/
def frameActive (p : Params) (st : State p.n) (c : PC p.n) : Bool :=
  decide (∃ B ∈ fullTree p st, eraseFG B = c.target)

theorem frameActive_def (p : Params) (st : State p.n) (c : PC p.n) :
    frameActive p st c = decide (∃ B ∈ fullTree p st, eraseFG B = c.target) := rfl

/-- [PC-SA M1; pcsa34-r4.3 §3.7 (i)] Read `ρ_s` at the gate. Select
frame-active held PCs with a first acceptance time strictly before `e_s`.
The empty set gives the empty rank. -/
def gateRank (p : Params) (st : State p.n) (s : Slot) : Option PCRank :=
  (bestPC (st.pcs.filter (fun c => frameActive p st c &&
    (pcStamp? st c).any (fun t => t < SA.earlyTime p.toParams s)))).map PC.rank

theorem gateRank_def (p : Params) (st : State p.n) (s : Slot) :
    gateRank p st s = (bestPC (st.pcs.filter (fun c => frameActive p st c &&
      (pcStamp? st c).any (fun t => t < SA.earlyTime p.toParams s)))).map PC.rank := rfl

end AvailableChain.PCSA
end
