module
public import AvailableChainContract.Claims

@[expose] public section

/-! # Non-vacuity: the statement

`CanonicalRun`: for every protocol family, every finite nonempty validator
set, every environment, every honest set, every horizon `≥ 0`, every seat map,
proposer map, input and hash function, there is an event list that makes the run valid,
partially synchronous, and synchronous on every prefix. So the execution part
of every regime is satisfiable for every protocol: no protocol can make a
regime vacuous. (Whether the environment part holds is a property of the
environment alone.) Proved as `canonical_run` in `Canonical.lean`. -/

namespace AvailableChain.Contract

open AvailableChain.Generic

/-- The run with the given data and events. -/
def mkRun {V : Type} [Fintype V] [DecidableEq V] {F : Family} {E : Env V}
    (honest : Finset V) (horizon : Time)
    (seat : (protoOf F E).Label → Fin (Fintype.card V) ≃ V)
    (proposer : Slot → V) (input : V → Time → Nat) (hash : Header → Nat)
    (events : List (Event V (protoOf F E).Object)) : Run F E :=
  ⟨honest, horizon, events, seat, proposer, input, hash⟩

/-- Every protocol, environment and run data has a valid, partially synchronous
event list that is also synchronous on every prefix. -/
def CanonicalRun : Prop :=
  ∀ (F : Family) (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (E : Env V)
    (honest : Finset V) (horizon : Time), 0 ≤ horizon →
    ∀ (seat : (protoOf F E).Label → Fin (Fintype.card V) ≃ V)
      (proposer : Slot → V) (input : V → Time → Nat) (hash : Header → Nat),
    ∃ events : List (Event V (protoOf F E).Object),
      let rho := mkRun (F := F) (E := E) honest horizon seat proposer input hash events
      rho.ExecutionValid ∧ rho.PartialSynchrony ∧ ∀ cut, rho.HealthyPrefixDelivery cut

end AvailableChain.Contract

end
