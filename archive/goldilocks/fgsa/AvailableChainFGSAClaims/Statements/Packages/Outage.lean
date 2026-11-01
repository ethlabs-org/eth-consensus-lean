module
public import AvailableChainFGSAClaims.Statements.Regimes
public import AvailableChainFGSAClaims.Statements.Windows

@[expose] public section

namespace AvailableChain.FGSA.Run

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V] [Fintype V]

/-- Family (4) premises at the outage point. -/
structure OutagePrem (fast : Bool) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (pt : PtOut) (ΔF : Time := E.Δ) : Prop where
  set : OutageSet p c fast E rho pt.T pt.b₀ pt.b₁ ΔF

end AvailableChain.FGSA.Run
end
