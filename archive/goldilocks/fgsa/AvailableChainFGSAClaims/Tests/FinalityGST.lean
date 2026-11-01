module
public import AvailableChainFGSAClaims.Statements.Packages.FinalityGST -- shake: keep (GST examples)

public section

namespace AvailableChain.FGSA.Run.Tests.FinalityGST
open Gen.Pure

variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V] [Fintype V]
    (G ΔF : Time) (g : Nat) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

example (pt : PtT) (hs : FinalitySet_W p c E rho G ΔF .recFE g)
    (hl : recoveryStart p E + B_HF p ΔF G ≤ pt.t)
    (hh : pt.t + W_W p ΔF g ≤ rho.horizon) :
    FinalityLivenessGSTPrem_W p c G ΔF .recFE g E rho pt :=
  { set := hs, late := hl, hhor := hh }

example (pt : PtT) (hs : FinalitySet_W p c E rho G ΔF .recF4 g)
    (hl : recoveryStart p E + B_HF p ΔF G ≤ pt.t)
    (hh : pt.t + W_W p ΔF g ≤ rho.horizon) :
    FinalityLivenessGSTPrem_W p c G ΔF .recF4 g E rho pt :=
  { set := hs, late := hl, hhor := hh }

example (pt : PtSX) (hs : FinalitySet_W p c E rho G ΔF .recFE g)
    (hp : HonestProposal E rho (fgsaInterface p c) pt.s pt.X)
    (hl : recoveryStart p E + B_HF p ΔF G ≤ V2.D.proposalTime (fgsaInterface p c) pt.s)
    (hh : V2.D.proposalTime (fgsaInterface p c) pt.s + W_W p ΔF g ≤ rho.horizon) :
    ProposalFinalGSTPrem_W p c G ΔF .recFE g E rho pt :=
  { set := hs, prop := hp, late := hl, hhor := hh }

example (pt : PtSX) (hs : FinalitySet_W p c E rho G ΔF .recF4 g)
    (hp : HonestProposal E rho (fgsaInterface p c) pt.s pt.X)
    (hl : recoveryStart p E + B_HF p ΔF G ≤ V2.D.proposalTime (fgsaInterface p c) pt.s)
    (hh : V2.D.proposalTime (fgsaInterface p c) pt.s + W_W p ΔF g ≤ rho.horizon) :
    ProposalFinalGSTPrem_W p c G ΔF .recF4 g E rho pt :=
  { set := hs, prop := hp, late := hl, hhor := hh }

example (pt : PtT) (hs : FinalitySet_W p c E rho G ΔF .recFE g)
    (hl : recoveryStart p E + B_HF p ΔF G ≤ pt.t)
    (hh : pt.t + 2 * W_W p ΔF g ≤ rho.horizon) :
    AboveFrontierGSTPrem_W p c G ΔF .recFE g E rho pt :=
  { set := hs, late := hl, hhor := hh }

example (pt : PtT) (hs : FinalitySet_W p c E rho G ΔF .recF4 g)
    (hl : recoveryStart p E + B_HF p ΔF G ≤ pt.t)
    (hh : pt.t + 2 * W_W p ΔF g ≤ rho.horizon) :
    AboveFrontierGSTPrem_W p c G ΔF .recF4 g E rho pt :=
  { set := hs, late := hl, hhor := hh }

end AvailableChain.FGSA.Run.Tests.FinalityGST
end
