module
public import ConsensusLean.Instances.Goldilocks.Spec.Common.Params

@[expose] public section

/-! # Goldilocks milestone vocabulary: the quorum

The part of `Spec/Common/Params` that no Challenge statement reaches (docs/decisions.md,
2026-11-04): the milestone statements use it; it is not on the trusted surface. Names and bodies are
unchanged.

`Params.q` is the quorum `q = ⌈2n/3⌉` on the shared parameters. -/

namespace Consensus.Goldilocks

namespace Params

variable (P : Params)

/-- The quorum `q = ⌈2n/3⌉`. -/
def q : Nat := (2 * P.n + 2) / 3

end Params

end Consensus.Goldilocks

end
