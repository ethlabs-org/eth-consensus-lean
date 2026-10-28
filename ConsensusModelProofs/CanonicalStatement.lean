module
public import ConsensusModel.System

@[expose] public section
namespace Consensus.Model

/-- The run with fixed environment data and the supplied schedule. -/
def mkRun {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}
    (honest : Finset V) (horizon : Time) (key : Fin (Fintype.card V) ≃ V)
    (sel : (protoOf F E).Role → Finset (Fin (Fintype.card V)))
    (submit relay : V → Time → List Tx) (hash : (protoOf F E).Item → Nat)
    (events : List (Event V (protoOf F E).Object)) : Run F E :=
  ⟨honest, horizon, events, key, sel, submit, relay, hash⟩
end Consensus.Model
end
