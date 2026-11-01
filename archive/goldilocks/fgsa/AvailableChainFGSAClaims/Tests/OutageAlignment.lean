module
public import AvailableChainFGSAClaims.FGSAClaims -- shake: keep (test environment)

public section

namespace AvailableChain.FGSA.Run.Tests.WeakContinuationLive

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]

-- Claims imports are permitted in this audit module. Check the neutral bodies.
example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : PtSP) :
    ServedFromGateAt p c E rho pt = InclusionAt p c E rho pt := rfl

example (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (t d : Time) :
    JointGrowthAt p c E rho t d = AvailableGrowthConcl p c E rho t d := rfl

end AvailableChain.FGSA.Run.Tests.WeakContinuationLive
end
