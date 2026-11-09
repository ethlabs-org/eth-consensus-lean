module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Trace

@[expose] public section

namespace Consensus.Goldilocks

variable {P : Params} {FGP : Type} {A : ACInterface P FGP}

/-- An actual candidate source output at a call, without a parent-handler equation. -/
def ACToFGAt (tr : ACTrace A) (x : Fin P.n) (i : Nat)
    (ℓ : ACLabel A) (C : A.Blk) : Prop :=
  tr.CallAt x i ℓ ∧ ℓ.call = .toFG ∧
    (A.toFG (tr.state x i) ℓ.frame (tr.time i)).2 = some C

/-- An actual candidate proposal, including its entire duty head and payload. -/
def ACProposalAt (tr : ACTrace A) (x : Fin P.n) (i : Nat)
    (ℓ : ACLabel A) (d : DutyHead P.n FGP A.Payload) (p : A.Payload) : Prop :=
  tr.CallAt x i ℓ ∧ ℓ.call = .proposal ∧
    (A.proposal (tr.state x i) ℓ.frame (tr.time i)).2 = some (d, p)

end Consensus.Goldilocks

end
