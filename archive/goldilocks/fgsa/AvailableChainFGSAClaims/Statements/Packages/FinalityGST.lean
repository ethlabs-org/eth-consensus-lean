module
public import AvailableChainFGSAClaims.Statements.Packages.Finality

@[expose] public section

namespace AvailableChain.FGSA.Run
open Gen.Pure

variable (p : Params) {In V : Type} (c : AppCodec In)
  [DecidableEq V] [Fintype V]

/-- Blueprint 22:1371–1380. DC: INTENTIONAL GST form; no healing output as premise;
DC finalized (Generic/Claims.lean:39–44). -/
structure FinalityLivenessGSTPrem_W
    (G ΔF : Time) (form : FinFormW) (g : Nat)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (pt : PtT) : Prop where
  set : FinalitySet_W p c E rho G ΔF form g
  late : recoveryStart p E + B_HF p ΔF G ≤ pt.t
  hhor : pt.t + W_W p ΔF g ≤ rho.horizon

/-- Blueprint 22:1421–1430. DC: INTENTIONAL GST form; no healing output as premise;
DC finalized (Generic/Claims.lean:39–44). -/
structure ProposalFinalGSTPrem_W
    (G ΔF : Time) (form : FinFormW) (g : Nat)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (pt : PtSX) : Prop where
  set : FinalitySet_W p c E rho G ΔF form g
  prop : HonestProposal E rho (fgsaInterface p c) pt.s pt.X
  late : recoveryStart p E + B_HF p ΔF G ≤
    V2.D.proposalTime (fgsaInterface p c) pt.s
  hhor : V2.D.proposalTime (fgsaInterface p c) pt.s +
    W_W p ΔF g ≤ rho.horizon

/-- Blueprint 22:1434–1451. DC: INTENTIONAL GST form; no healing output as premise;
DC finalized (Generic/Claims.lean:39–44). -/
structure AboveFrontierGSTPrem_W
    (G ΔF : Time) (form : FinFormW) (g : Nat)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (pt : PtT) : Prop where
  set : FinalitySet_W p c E rho G ΔF form g
  late : recoveryStart p E + B_HF p ΔF G ≤ pt.t
  hhor : pt.t + 2 * W_W p ΔF g ≤ rho.horizon

end AvailableChain.FGSA.Run
end
