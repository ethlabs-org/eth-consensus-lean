module
public import AvailableChainFGSAClaims.Statements.OutageContinuation

@[expose] public section

namespace AvailableChain.FGSA.Run

def OutagePrefixReceiptDerivedClaim (p : Params) : Prop :=
  ∀ {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (fast : Bool) (T b₀ b₁ ΔF : Time),
    OutageSleep₂ p c fast E rho T b₀ b₁ ΔF →
    OutagePrefixReceipt p c E rho fast T b₀

def OutageContinuationReceiptDerivedClaim (p : Params) : Prop :=
  ∀ {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (fast : Bool) (T b₀ b₁ ΔF : Time),
    OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF →
    OutageContinuationReceipt p c E rho fast T b₀ b₁

def OutageE1DerivedClaim (p : Params) : Prop :=
  ∀ {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (fast : Bool) (b₀ b₁ : Time),
    Base₂ p c E rho → OutageE p E rho fast b₀ b₁ →
    OutageE1 p E rho fast b₀ b₁

end AvailableChain.FGSA.Run
end
