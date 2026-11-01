module
public import AvailableChainFGSARun.Model.Families
public import AvailableChainEngineV2.Laws.Duty.Outputs

@[expose] public section

/-! The FG-SA output interface and its store factors (plan T7.3). -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Gossiped row objects, including rows with malformed authentication.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
def isRowObject {p : Params} (o : Obj p) : Prop :=
  match o.payload with
  | .row _ => True
  | _ => False

theorem isRowObject_def {p : Params} (o : Obj p) :
    isRowObject o = (match o.payload with | .row _ => True | _ => False) := by
  -- Generate the equation in its home module (BUILD B3a).
  have _h := @isRowObject.eq_1
  rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Per-object delivery bound for FG-SA.
DC b241081: INTENTIONAL: FG-SA rows have their own delivery bound (user 2026-10-01);
non-row traffic keeps Δ. -/
def fgsaDelay {p : Params} (Δ ΔF : Time) (o : Obj p) : Time :=
  match o.payload with
  | .row _ => ΔF
  | _ => Δ

theorem fgsaDelay_def {p : Params} (Δ ΔF : Time) (o : Obj p) :
    fgsaDelay Δ ΔF o = (match o.payload with | .row _ => ΔF | _ => Δ) := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Both outputs read the stable record. All slots open, as in SA. -/
def fgsaInterface (p : Params) {In : Type} (c : AppCodec In) :
    V2.D.Interface (fgsa p c) where
  confirmed nd := nd.st.base.stableRecord
  stable nd := nd.st.base.stableRecord
  block m := match m with
    | .proposal N => some N.erase
    | _ => none
  opening _ := True
  propLabel s := .prop s
  propDuty s := .propAction s
  propDuty_label _ := rfl
  propLabel_single _ := rfl
  propLabel_injective := fun _ _ h => RunLabel.prop.inj h

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
Both output getters factor through the store. -/
def fgsaOutputs (p : Params) {In : Type} (c : AppCodec In) :
    V2.D.OutputsFactor (fgsaInterface p c) (fgsaIso p c) where
  confirmedB st := st.base.stableRecord
  confirmed_base _ := rfl
  stableB st := st.base.stableRecord
  stable_base _ := rfl

/-- [ROOT-DIGEST-2 W1; DC named and HEAD interfaces]
The finalized output is the erasure of the stored FG block. -/
def finalizedOut {p : Params} (nd : Node p) : Block := eraseFG nd.st.fg.F

end AvailableChain.FGSA.Run

end
