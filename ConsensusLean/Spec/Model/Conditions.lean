module
public import ConsensusLean.Spec.Model.Run
public import ConsensusLean.Spec.Problem.Network

@[expose] public section

/-! # Conditions (L1)

Conditions on runs. None of them mentions anything the protocol supplies:
they speak about the environment, the run data, and what the engine did
(ticks, releases, receipts, restarts). Participation (readiness, majorities,
fault bounds) is environment vocabulary, defined once in L0
(`Consensus.EnvPoint`) and applied to `Run.point`. -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}

namespace Run

variable (rho : Run F E)

/-- Unforgeable signatures: every object signed by an honest validator that
occurs anywhere inside a delivered object was released by that validator at an
earlier event. Faulty validators sign anything. -/
def Unforgeable : Prop :=
  ∀ (i : Nat) (w : V) (o : (protoOf F E).Object) (t : Time),
    rho.events[i]? = some (Event.deliver w o t) →
    ∀ o', Obj.Contains o o' → ∀ u ∈ rho.honest, rho.signerOf o' = some u →
      ∃ (j : Nat) (t' : Time), j < i ∧ rho.events[j]? = some (Event.tick u t') ∧
        o' ∈ rho.releasesAt j

/-- The run's selection is admissible for every role. -/
def SelValid : Prop := (protoOf F E).SelAdmits rho.sel

/-- Credentials: every signed object inside a delivered object is signed by a
key selected for its role, faulty signers included. This is the soundness of
the deployed membership mechanism (a public committee list, VRF proofs, …): a
model-adequacy binding, not something honest code checks. -/
def Credentials : Prop :=
  ∀ (i : Nat) (w : V) (o : (protoOf F E).Object) (t : Time),
    rho.events[i]? = some (Event.deliver w o t) →
    ∀ o', Obj.Contains o o' → ∀ k r, o'.auth = .signed k r → k ∈ rho.sel r

/-- A valid execution.

Schedule: events are in time order, finite, honest only, and every awake
honest node ticks at every integer time of `[0, horizon]` (unit ticks).
Sleep: an asleep node has no events; a node restarts exactly when it wakes
(after time 0). Then unforgeable signatures, an admissible selection, and
credentials. -/
structure ExecutionValid : Prop where
  -- Schedule.
  horizon_nonneg : 0 ≤ rho.horizon
  sorted : rho.events.Pairwise Event.keyLe
  nodup : rho.events.Nodup
  in_horizon : ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon
  honest_only : ∀ e ∈ rho.events, e.node ∈ rho.honest
  tick_total : ∀ v ∈ rho.honest, ∀ t, 0 ≤ t → t ≤ rho.horizon →
    E.awake v t = true → Event.tick v t ∈ rho.events
  -- Sleep.
  tick_awake : ∀ v t, Event.tick v t ∈ rho.events → E.awake v t = true
  deliver_awake : ∀ v o t, Event.deliver v o t ∈ rho.events → E.awake v t = true
  restart_at_wake : ∀ v t, Event.restart v t ∈ rho.events → 0 < t ∧ Wakes E v t
  wake_restart : ∀ v ∈ rho.honest, ∀ t, 0 < t → t ≤ rho.horizon →
    Wakes E v t → Event.restart v t ∈ rho.events
  -- Bindings.
  unforgeable : Unforgeable rho
  selValid : SelValid rho
  credentials : Credentials rho

/-- The run's communication log (L0 `CommLog`): engine releases, deliveries
and inboxes. Network conditions are the L0 ones (`CommLog.PSync`,
`CommLog.SyncUntil`, …) on `rho.point` and `rho.log`. -/
def log : CommLog V (protoOf F E).Object := ⟨rho.releases, rho.receives, rho.inbox⟩

end Run

end Consensus.Model

end
