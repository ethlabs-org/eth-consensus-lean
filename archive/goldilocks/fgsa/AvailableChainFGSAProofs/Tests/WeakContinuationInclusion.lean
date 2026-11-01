module
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.Inclusion

public section

/-! WC J3, plan §§6.10–6.11; DC proposal service contract tests. -/

namespace AvailableChain.FGSA.Run.Tests.WeakContinuationInclusion

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- WC J3, plan §6.11; DC persistent service: no extra continuation premise. -/
theorem inclusionContract (ΔF : Time) (w : HealingWitness) (iStar : Nat)
    (hframe : WCSeededFrameLiveStatement p c E rho ΔF w iStar) :
    WCInclusion6Statement p c E rho ΔF w iStar :=
  wc_inclusion6 ΔF w iStar hframe

omit [Fintype V] in
/-- WC J3, plan §6.11; DC finite endpoint: the covered gate read is inclusive. -/
theorem atGateEndpoint (pt : PtSP) (hserved : ServedFromGateAt p c E rho pt)
    (hgate : SA.gateTime p.toParams pt.s = rho.horizon)
    (g : V2.D.Output (fgsa p c))
    (hg : g ∈ [(fgsaInterface p c).stable, (fgsaInterface p c).confirmed])
    (x : V) (hx : confirmedReader p c E rho x (SA.gateTime p.toParams pt.s)) :
    Block.Preceq pt.P (V2.D.outputAt E rho g x (SA.gateTime p.toParams pt.s)) :=
  hserved g hg _ x ⟨le_rfl, hgate.le⟩ hx

end AvailableChain.FGSA.Run.Tests.WeakContinuationInclusion
end

#print axioms AvailableChain.FGSA.Run.Tests.WeakContinuationInclusion.inclusionContract

#print axioms AvailableChain.FGSA.Run.Tests.WeakContinuationInclusion.atGateEndpoint
