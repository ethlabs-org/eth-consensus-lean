module
public import AvailableChainFGSAProofs.Proofs.Assembly.Foundations -- shake: keep (export examples)

public section

namespace AvailableChain.FGSA.Run.Tests.FoundationsExport
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (hroots : NamedRootCollisionFree p c E rho)

example (hL : V2.D.Linked (fgsaFamilies p c).linked rho)
    (hX : Gen.Pure.FaultX p.n (Gen.V2.Duty.faulty rho).card)
    (hU : V2.D.UnforgeableSignatures E rho) : RXing p c E rho :=
  fgsa_rXing (hroots := hroots) p c E rho hL hX hU

example (hL : V2.D.Linked (fgsaFamilies p c).linked rho)
    (hv : V2.D.ExecutionValid E rho)
    (hQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card) : RCap p c E rho :=
  fgsa_rCap_channel p c E rho hL hv hQ

example (hL : V2.D.Linked (fgsaFamilies p c).linked rho)
    (hv : V2.D.ExecutionValid E rho)
    (hQ : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card)
    (y i : Nat) (x : V) (W : FGBlock (Fin p.n))
    (hW : HeldAt p c E rho i x W) (hh : y + 2 ≤ (heightView p W).h) :
    ∃ (z : V) (r : Nat) (a : RowWire p.n) (u : Row (Fin p.n))
      (T : BlockId) (timeout : Bool),
      HonestRowBefore p c E rho i z r a ∧ RowSigner p c rho a z ∧
      a.toRow? = some u ∧ u ∈ chainRows W ∧ u.height_pair = .vote (y + 1) T timeout :=
  fgsa_rCap_heightView p c E rho hL hv hQ y i x W hW hh

end AvailableChain.FGSA.Run.Tests.FoundationsExport
end
