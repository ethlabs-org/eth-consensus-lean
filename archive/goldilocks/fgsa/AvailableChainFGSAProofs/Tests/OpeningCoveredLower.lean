module
public import AvailableChainFGSAProofs.Proofs.Foundations.OpeningCoveredLower -- shake: keep (consumer contract example)

set_option linter.privateModule false

public section
namespace AvailableChain.FGSA.Run.Tests.OpeningCoveredLower
open AvailableChain.SimplexFG

-- The lower branch accepts the consumer's hOf premise through the bridge.
-- J is arbitrary: this checks the gap and the uncontested top-J cases.
example {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G ΔF : Time) (h : HealingPrem p c G ΔF E rho ())
    (u : Time) (m : Nat) (J : Option (FGBlock (Fin p.n)))
    (r : Nat) (Q : Block) (Qfg : FGBlock (Fin p.n))
    (hGST : E.t_GST ≤ u) (hQ : eraseFG Qfg = Q)
    (hh : hOf p.E p.cfg Qfg = m - 1)
    (hservice : ExactService p c E rho (r * p.R) Q)
    (hu : u ≤ SA.proposalTime p.toParams (r * p.R))
    (hphase : PhaseInterval p c E rho u (p.actionTime r) m J false) :
    OpeningCovered p c E rho r Q := by
  apply openingCovered_lower_gate E rho G ΔF h u m J r Q Qfg hGST hQ
    (by rwa [KitFG.hOf_of_bridge p.E p.cfg (heightView p) (heightView_bridge p)] at hh)
    hservice hu hphase

end AvailableChain.FGSA.Run.Tests.OpeningCoveredLower
