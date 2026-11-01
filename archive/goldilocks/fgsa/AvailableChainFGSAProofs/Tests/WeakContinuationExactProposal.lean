module
public import AvailableChainFGSAProofs.Proofs.WeakContinuation.ExactProposal

public section

/-! WC J3, plan §§6.10–6.11; DC proposal service contract tests. -/

namespace AvailableChain.FGSA.Run.Tests.WeakContinuationExactProposal

variable {p : Params} {In V : Type} [DecidableEq V] [Fintype V] {c : AppCodec In}
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- WC J3, plan §6.10; DC full admission: preserve the exact reviewed contract. -/
theorem admissionContract (ΔF : Time) (w : HealingWitness) (iStar : Nat) :
    WCProposalAdmissionStatement p c E rho ΔF w iStar :=
  wc_proposalAdmission ΔF w iStar

/-- WC J3, plan §6.10; DC exact HEAD: joined honest readers. -/
theorem exactContract (ΔF : Time) (w : HealingWitness) (iStar : Nat) :
    WCExactProposalStatement p c E rho ΔF w iStar :=
  wc_exactProposal ΔF w iStar

end AvailableChain.FGSA.Run.Tests.WeakContinuationExactProposal
end
