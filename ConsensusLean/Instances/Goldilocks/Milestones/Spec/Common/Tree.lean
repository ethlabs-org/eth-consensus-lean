module
public import ConsensusLean.Instances.Goldilocks.Spec.Common.Tree

@[expose] public section

/-! # Goldilocks milestone vocabulary: coherent block sets

The part of `Spec/Common/Tree` that no Challenge statement reaches (`docs/decisions.md`
§"Trusted surface and Challenge scope"): the milestone statements use it; it is not on the trusted
surface. Names and bodies are unchanged.

`Coherent S` is what makes `S` a tree (claims F.2, F.3): roots are injective on `S` and slots
strictly increase along its parent edges. -/

namespace Consensus.Goldilocks

variable {n : Nat} {FGP ACP : Type}

/-- `S` is a coherent set of blocks: roots are injective on `S`, and along every parent edge
inside `S` the slot strictly increases (the assertion of `state_transition`). -/
def Coherent (S : Set (Block n FGP ACP)) : Prop :=
  Set.InjOn Block.root S ∧ ∀ B ∈ S, ∀ C ∈ S, C.parent = some B.root → B.slot < C.slot

end Consensus.Goldilocks

end
