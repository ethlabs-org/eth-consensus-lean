module
public import ConsensusLean.Spec.Model.Run
public import ConsensusLean.Spec.Problem.Network

@[expose] public section

/-! # Conditions (L1)

Conditions on runs speak about the environment, the run data, and what the engine did
(ticks, releases, raw arrivals, restarts). Arrivals enter the protocol's total
`process` handler regardless of dependency readiness; buffering and admission belong
to the protocol, not to execution validity. Participation (readiness, majorities,
fault bounds) is environment vocabulary, defined once in L0
(`Consensus.EnvPoint`) and applied to `Run.point`. -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
    {E : Env V}

namespace Run

variable (rho : Run F E)

/-- Unforgeable signatures: every signed object inside an object delivered at
time `t` whose signer is honest at `t` was released by that signer at an earlier
event. A key compromised by `t` signs anything, including objects that claim an
earlier slot or role: the claimed slot is not the signing time (ordinary keys, no
forward security). A genuine earlier release keeps its provenance after its
signer is compromised. -/
def Unforgeable : Prop :=
  ∀ (i : Nat) (w : V) (o : (protoOf F E).Object) (t : Time),
    rho.events[i]? = some (Event.deliver w o t) →
    ∀ o', Obj.Contains o o' → ∀ u, rho.signerOf o' = some u → u ∉ rho.faultyAt t →
      ∃ (j : Nat) (t' : Time), j < i ∧ rho.SendsAt u j t' ∧ o' ∈ rho.releasesAt j

/-- The run's selection is admissible for every role. -/
def SelValid : Prop := (protoOf F E).SelAdmits rho.sel

/-- Credentials: every signed object inside a delivered object is signed by a
key selected for its role, faulty and compromised signers included (a compromise
creates no credential the selection did not give). This is the soundness of
the deployed membership mechanism (a public committee list, VRF proofs, …): a
model-adequacy binding, not something honest code checks. -/
def Credentials : Prop :=
  ∀ (i : Nat) (w : V) (o : (protoOf F E).Object) (t : Time),
    rho.events[i]? = some (Event.deliver w o t) →
    ∀ o', Obj.Contains o o' → ∀ k r, o'.auth = .signed k r → k ∈ rho.sel r

/-- A valid execution.

Schedule: events are in time order, finite, and each at a node honest at the
event's time; every node honest and awake at an integer time of `[0, horizon]`
ticks there (unit ticks). From its compromise on, a node has no engine events:
what it does is adversarial injection (deliveries of the objects its key signs);
its engine state stays where it was and is no longer a read of the property
table. Compromise is neither a wake nor a restart and removes nothing from
another node's `seen`. Sleep: an asleep node has no events; a node honest at a
wake (after time 0) restarts exactly then. Then unforgeable signatures, an admissible selection, and
credentials. -/
structure ExecutionValid : Prop where
  -- Schedule.
  horizon_nonneg : 0 ≤ rho.horizon
  sorted : rho.events.Pairwise Event.keyLe
  nodup : rho.events.Nodup
  in_horizon : ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon
  honest_only : ∀ e ∈ rho.events, e.node ∉ rho.faultyAt e.time
  tick_total : ∀ v t, 0 ≤ t → t ≤ rho.horizon → v ∉ rho.faultyAt t →
    E.awake v t = true → Event.tick v t ∈ rho.events
  -- Sleep.
  tick_awake : ∀ v t, Event.tick v t ∈ rho.events → E.awake v t = true
  deliver_awake : ∀ v o t, Event.deliver v o t ∈ rho.events → E.awake v t = true
  restart_at_wake : ∀ v t, Event.restart v t ∈ rho.events → 0 < t ∧ Wakes E v t
  wake_restart : ∀ v t, 0 < t → t ≤ rho.horizon → v ∉ rho.faultyAt t →
    Wakes E v t → Event.restart v t ∈ rho.events
  -- Bindings.
  unforgeable : Unforgeable rho
  selValid : SelValid rho
  credentials : Credentials rho

/-- Schedule and sleep alone: the structural fields of `ExecutionValid`, with
no signature, selection-admissibility or credential binding. -/
structure StructuralValid : Prop where
  horizon_nonneg : 0 ≤ rho.horizon
  sorted : rho.events.Pairwise Event.keyLe
  nodup : rho.events.Nodup
  in_horizon : ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon
  honest_only : ∀ e ∈ rho.events, e.node ∉ rho.faultyAt e.time
  tick_total : ∀ v t, 0 ≤ t → t ≤ rho.horizon → v ∉ rho.faultyAt t →
    E.awake v t = true → Event.tick v t ∈ rho.events
  tick_awake : ∀ v t, Event.tick v t ∈ rho.events → E.awake v t = true
  deliver_awake : ∀ v o t, Event.deliver v o t ∈ rho.events → E.awake v t = true
  restart_at_wake : ∀ v t, Event.restart v t ∈ rho.events → 0 < t ∧ Wakes E v t
  wake_restart : ∀ v t, 0 < t → t ≤ rho.horizon → v ∉ rho.faultyAt t →
    Wakes E v t → Event.restart v t ∈ rho.events

/-- A failed execution binding: a delivered forgery, an unsound membership
credential, or an inadmissible selection. Selection is included as a deployment
binding, without claiming that committee admissibility itself is cryptographic.
`SelValid` ranges over every selection role, including slots beyond the horizon.
Selection is external data fixed before execution: its failure is a concrete
fact about the run data, not necessarily an observed event. -/
def BindingFailure : Prop :=
  ¬ rho.Unforgeable ∨ ¬ rho.Credentials ∨ ¬ rho.SelValid

/-- Execution validity splits into exactly the structural conditions and the
three bindings. Both directions enumerate the fields to detect validity drift. -/
theorem executionValid_iff_structuralValid :
    rho.ExecutionValid ↔
      rho.StructuralValid ∧ rho.Unforgeable ∧ rho.Credentials ∧ rho.SelValid := by
  constructor
  · intro h
    rcases h with ⟨horizon, sorted, nodup, within, honest, total, tick, deliver,
      restart, wake, unforgeable, selection, credentials⟩
    exact ⟨⟨horizon, sorted, nodup, within, honest, total, tick, deliver, restart, wake⟩,
      unforgeable, credentials, selection⟩
  · rintro ⟨⟨horizon, sorted, nodup, within, honest, total, tick, deliver, restart, wake⟩,
      unforgeable, credentials, selection⟩
    exact ⟨horizon, sorted, nodup, within, honest, total, tick, deliver, restart, wake,
      unforgeable, selection, credentials⟩

/-- The run's communication log (L0 `CommLog`): engine releases, raw arrivals
and inboxes, independently of handler admission. Network conditions are the L0 ones
(`CommLog.PSync`, `CommLog.SyncUntil`, …) on `rho.point` and `rho.log`. -/
def log : CommLog V (protoOf F E).Object :=
  ⟨rho.releases, rho.receives, rho.inbox, (protoOf F E).isFGAtt⟩

end Run

end Consensus.Model

end
