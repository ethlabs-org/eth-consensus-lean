module
public import ConsensusModel.System

@[expose] public section
namespace Consensus.Model
open AvailableChain (Time)
open AvailableChain.Generic (Env)

/-- The run with fixed environment data and the supplied schedule. -/
def mkRun {V : Type} [Fintype V] [DecidableEq V] {F : Family} {E : Env V}
    (honest : Finset V) (horizon : Time)
    (holder : (ℓ : (protoOf F E).Label) → Fin ((protoOf F E).seats ℓ) → V)
    (submit : V → Time → List Tx) (hash : (protoOf F E).Item → Nat)
    (events : List (Event V (protoOf F E).Object)) : Run F E :=
  ⟨honest, horizon, events, holder, submit, hash⟩

/-- Every fixed assignment, submission function and hash admits a valid,
partially synchronous schedule that is healthy at every cut. -/
def CanonicalRun : Prop :=
  ∀ (F : Family) (V : Type) [Fintype V] [DecidableEq V] (E : Env V)
    (honest : Finset V) (horizon : Time), 0 ≤ horizon →
    ∀ (holder : (ℓ : (protoOf F E).Label) → Fin ((protoOf F E).seats ℓ) → V)
      (submit : V → Time → List Tx) (hash : (protoOf F E).Item → Nat),
    ∃ events : List (Event V (protoOf F E).Object),
      let rho := mkRun (F := F) (E := E) honest horizon holder submit hash events
      rho.ExecutionValid ∧ rho.PartialSynchrony ∧ ∀ cut, rho.HealthyPrefixDelivery cut
end Consensus.Model
end
