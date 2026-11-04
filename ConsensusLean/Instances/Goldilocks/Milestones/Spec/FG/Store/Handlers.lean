module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.Handlers

@[expose] public section

/-! # Goldilocks milestone vocabulary: store steps

The part of `Spec/FG/Store/Handlers` that no Challenge statement reaches (docs/decisions.md,
2026-11-04): the milestone statements use it; it is not on the trusted surface. Names and bodies are
unchanged.

`Store.Step`: one FG store step (an accepted block or a processed attestation); `Reachable`: the
FG states that the handlers reach from the initial state. -/

namespace Consensus.Goldilocks.Store

variable {P : Params} {ACP : Type}

/-- One FG store step: an accepted block, or a processed attestation (from the wire or the
node's own `attest`). A restart keeps `Σ` (composition.tex §"State"), so it is no step. -/
def Step (st st' : Store P ACP) : Prop :=
  (∃ B, onBlock st B = some st') ∨ ∃ a, st' = onAttestation st a

/-- An FG state is reachable when the handlers reach it from the initial state with genesis AC
payload `acp₀`. (Which blocks and attestations a node is given is a node fact, C0.5.) -/
def Reachable (acp₀ : ACP) : Store P ACP → Prop := Relation.ReflTransGen Step (init acp₀)

end Consensus.Goldilocks.Store

end
