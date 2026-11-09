module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Trace

@[expose] public section

namespace Consensus.Goldilocks

/-- A source returned by the actual AC, independently of any observation or source rule. -/
def ACToFGAt {P : Params} {FGP : Type} {A : ACInterface P FGP}
    (tr : ACTrace A) (x : Fin P.n) (i : Nat) (ℓ : ACLabel A) (C : A.Blk) : Prop :=
  tr.CallAt x i ℓ ∧ ℓ.call = .toFG ∧ (A.toFG (tr.state x i) ℓ.frame (tr.time i)).2 = some C

end Consensus.Goldilocks

end
