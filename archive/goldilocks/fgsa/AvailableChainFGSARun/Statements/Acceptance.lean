module
public import AvailableChainFGSARun.Model.Protocol
public import AvailableChainFGSA.Statements.Invariants
public import AvailableChainGeneric.Statements.V2.Duty.Receipt

@[expose] public section

namespace AvailableChain.FGSA.Run

/-- The admission threshold, rather than the duty time. -/
def fgsaAdmissionTime (p : Params) (o : Obj p) : Time :=
  match o.auth with
  | .seat (.base (.head s)) _ => 4 * p.Δ * s
  | .seat (.base .fg) _ => 0
  | .seat (.prop s) _ => 4 * p.Δ * s
  | .none => 0

/-- The pre-state clock has reached the handler's threshold. -/
def fgsaTimely (p : Params) (nd : Node p) (o : Obj p) : Prop :=
  fgsaAdmissionTime p o ≤ nd.st.base.now

/-- The store invariant used by the acceptance law. -/
def fgsaAcceptanceInv (p : Params) (nd : Node p) : Prop := CStoreInv p nd.st

/-- An honest emission or acceptance in an FG-SA run. -/
def fgsaTrigger (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (o : Obj p) (t : Time) : Prop :=
  Gen.V2.Duty.Trigger E rho o t

end AvailableChain.FGSA.Run
end
