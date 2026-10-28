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

/-- Every PKI, admissible selection, submission function and hash admits a
valid, partially synchronous schedule that is healthy at every cut. -/
def CanonicalRun : Prop :=
  ∀ (O : OutputSchema) (F : Family O) (V : Type) [Fintype V] [DecidableEq V] (E : Env V)
    (honest : Finset V) (horizon : Time), 0 ≤ horizon →
    ∀ (key : Fin (Fintype.card V) ≃ V)
      (sel : (protoOf F E).Role → Finset (Fin (Fintype.card V))),
      (∀ r, ((protoOf F E).selSpec r).Admits (sel r)) →
    ∀ (submit : V → Time → List Tx) (hash : (protoOf F E).Item → Nat),
    ∃ (relay : V → Time → List Tx) (events : List (Event V (protoOf F E).Object)),
      let rho := mkRun (F := F) (E := E) honest horizon key sel submit relay hash events
      rho.ExecutionValid ∧ rho.PartialSynchrony ∧ ∀ cut, rho.HealthyPrefixDelivery cut
end Consensus.Model
end
