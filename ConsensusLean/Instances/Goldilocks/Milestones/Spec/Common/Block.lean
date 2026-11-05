module
public import ConsensusLean.Instances.Goldilocks.Spec.Common.Block

@[expose] public section

/-! # Goldilocks milestone vocabulary: block digests

The part of `Spec/Common/Block` that no Challenge statement reaches (`docs/decisions.md`
§"Trusted surface and Challenge scope"): the milestone statements use it; it is not on the trusted
surface. Names and bodies are unchanged.

`Digest` is the digest of a block's content `(parent root, slot, input, FG payload, AC payload)`;
`Block.RootOk` says that a block's root is that digest (the wire check). -/

namespace Consensus.Goldilocks

/-- A block digest: the root of the content `(parent root, slot, input, FG payload, AC
payload)`. -/
abbrev Digest (FGP ACP : Type) := Option Nat → Nat → Nat → FGP → ACP → Nat

/-- The root of `B` is the digest of its content (composition.tex §"Blocks": `B.root` is the
fixed digest of `(B.parent.root, B.slot, B.attestations, B.acp)`, the input inside `B.acp`). -/
def Block.RootOk {n : Nat} {FGP ACP : Type} (dg : Digest FGP ACP) (B : Block n FGP ACP) : Prop :=
  B.root = dg B.parent B.slot B.input B.fgPayload B.acPayload

end Consensus.Goldilocks

end
