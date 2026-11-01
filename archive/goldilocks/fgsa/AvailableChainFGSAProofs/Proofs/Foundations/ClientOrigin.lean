module
public import AvailableChainFGSAProofs.Proofs.Foundations.FGSafetyBridge

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
ROOT-DIGEST W2b. DC `ReviewTheorem.lean:298` uses authentic stored rows for honestNeverSlashed.
Port of the d35bac1 read-chain route to W and fixed FG seats (F-H).
Replay the inclusive time filter to find a delivery in the original run.
Unforgeability then gives each honest signer's emission. No event order,
horizon, or execution-validity premise is needed. -/
theorem readAt_chain_row_origin (p : Params) {In V : Type} [DecidableEq V]
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hU : V2.D.UnforgeableSignatures E rho)
    (t : Time) (x : V) (W : FGBlock (Fin p.n))
    (hW : W ∈ (V2.D.Run.readAt E rho t x).st.fg.TF)
    (u : Row (Fin p.n)) (hu : u ∈ chainRows W) :
    ∃ a : RowWire p.n,
      RowWire.toRow? a = some u ∧ a.auth = .seat .fg u.signer ∧
      ∀ z, RowSigner p c rho a z → z ∈ rho.honest → EmitsRow p c E rho z a :=
  fgsa_bridge_read_row_origin p c E rho hU t x W hW u hu

end AvailableChain.FGSA.Run
end
