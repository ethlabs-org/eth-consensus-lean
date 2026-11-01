module
public import AvailableChainFGSAClaims.Statements.OutageContinuation

@[expose] public section

namespace AvailableChain.FGSA.Run

/-- P17: continuation uses the sleep premises and the scoped conclusion. -/
def OutageContinuationClaim (p : Params) : Prop :=
  ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (fast : Bool)
    (T b₀ b₁ ΔF : Time),
    OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF →
      OutageContinuationConcl p c E rho fast T b₀ b₁

end AvailableChain.FGSA.Run
end
