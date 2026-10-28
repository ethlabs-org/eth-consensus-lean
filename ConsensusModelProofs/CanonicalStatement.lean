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
valid synchronous schedule (L0 `CommLog.PSync` with GST `0`, and synchrony up
to every cut). -/
def CanonicalRun : Prop :=
  ∀ (O : OutputSchema) (F : Family O) (V : Type) [Fintype V] [DecidableEq V] (E : Env V)
    (honest : Finset V) (horizon : Time), 0 ≤ horizon →
    ∀ (key : Fin (Fintype.card V) ≃ V)
      (sel : (protoOf F E).Role → Finset (Fin (Fintype.card V))),
      (∀ r, ((protoOf F E).selSpec r).Admits (sel r)) →
    ∀ (submit : V → Time → List Tx) (hash : (protoOf F E).Item → Nat),
    ∃ (relay : V → Time → List Tx) (events : List (Event V (protoOf F E).Object)),
      let rho := mkRun (F := F) (E := E) honest horizon key sel submit relay hash events
      rho.ExecutionValid ∧ CommLog.PSync rho.point rho.log 0 ∧
        ∀ cut, CommLog.SyncUntil rho.point rho.log cut

/-- Every PKI, admissible selection, submission function, hash and GST `g`
admits a valid run whose log is eager from `g` (L0 `CommLog.EagerFrom`): no
message is received before `g`, and from `g` on every honest send is received
by every awake honest node. `g ≤ 0` is a synchronous run; `g` past the horizon
is a silent run (no receipts at all); in between, the network is asynchronous
before `g`. -/
def CanonicalRunFrom : Prop :=
  ∀ (O : OutputSchema) (F : Family O) (V : Type) [Fintype V] [DecidableEq V] (E : Env V)
    (honest : Finset V) (horizon : Time), 0 ≤ horizon →
    ∀ (key : Fin (Fintype.card V) ≃ V)
      (sel : (protoOf F E).Role → Finset (Fin (Fintype.card V))),
      (∀ r, ((protoOf F E).selSpec r).Admits (sel r)) →
    ∀ (submit : V → Time → List Tx) (hash : (protoOf F E).Item → Nat) (g : Time),
    ∃ (relay : V → Time → List Tx) (events : List (Event V (protoOf F E).Object)),
      let rho := mkRun (F := F) (E := E) honest horizon key sel submit relay hash events
      rho.ExecutionValid ∧ CommLog.EagerFrom rho.point rho.log g
end Consensus.Model
end
