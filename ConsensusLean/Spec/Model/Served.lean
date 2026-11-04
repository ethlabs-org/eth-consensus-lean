module
public import ConsensusLean.Spec.Model.System

@[expose] public section

/-! # Engine holding (L1)

`Run.Served`: the engine's form of holding a message (moved from
`ConsensusLean/Proofs/Faithful/Main.lean`, where `Run.held_iff_served` relates it to L0 holding). -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}

namespace Run

/-- Node `w` holds `o` at deadline `d` (engine form): it released or received
`o` at some `t' ≤ d` and has not restarted in `(t', d]`. A receipt before a
sleep does not serve after the wake. Receipt means raw arrival, not protocol admission. -/
def Served (rho : Run F E) (w : V) (o : (protoOf F E).Object) (d : Time) : Prop :=
  ∃ t', t' ≤ d ∧ (rho.releases w o t' ∨ rho.receives w o t') ∧
    ∀ u, Event.restart w u ∈ rho.events → ¬ (t' < u ∧ u ≤ d)

end Run

end Consensus.Model

end
