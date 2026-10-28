module
public import ConsensusModel.Run

@[expose] public section

/-! # Conditions (layer ½)

Premises about runs. None of them mentions anything the protocol supplies:
they speak about the environment, the run data, and what the engine did
(ticks, releases, receipts, restarts). Participation (readiness, majorities,
fault bounds) is environment vocabulary, defined once in layer 0
(`Consensus.EnvPoint`) and applied to `Run.point`. -/

namespace Consensus.Model



variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}

namespace Run

variable (rho : Run F E)

/-- Events are in time order, finite, honest only, and every awake honest node
ticks at every integer time of `[0, horizon]` (unit ticks). -/
structure ScheduleWellFormed : Prop where
  horizon_nonneg : 0 ≤ rho.horizon
  sorted : rho.events.Pairwise Event.keyLe
  nodup : rho.events.Nodup
  in_horizon : ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon
  honest_only : ∀ e ∈ rho.events, e.node ∈ rho.honest
  tick_total : ∀ v ∈ rho.honest, ∀ t, 0 ≤ t → t ≤ rho.horizon →
    E.awake v t = true → Event.tick v t ∈ rho.events

/-- Sleep: an asleep node has no events; a node restarts exactly when it
wakes (after time 0). -/
structure SleepWellFormed : Prop where
  tick_awake : ∀ v t, Event.tick v t ∈ rho.events → E.awake v t = true
  deliver_awake : ∀ v o t, Event.deliver v o t ∈ rho.events → E.awake v t = true
  restart_at_wake : ∀ v t, Event.restart v t ∈ rho.events → 0 < t ∧ Wakes E v t
  wake_restart : ∀ v ∈ rho.honest, ∀ t, 0 < t → t ≤ rho.horizon →
    Wakes E v t → Event.restart v t ∈ rho.events

/-- Unforgeable signatures: every object signed by an honest validator that
occurs anywhere inside a delivered object was released by that validator at an
earlier event. Faulty validators sign anything. -/
def Unforgeable : Prop :=
  ∀ (i : Nat) (w : V) (o : (protoOf F E).Object) (t : Time),
    rho.events[i]? = some (Event.deliver w o t) →
    ∀ o', Obj.Contains o o' → ∀ u ∈ rho.honest, rho.signerOf o'.auth = some u →
      ∃ (j : Nat) (t' : Time), j < i ∧ rho.events[j]? = some (Event.tick u t') ∧
        o' ∈ rho.releasesAt j

/-- The run's selection is admissible for every role. -/
def SelValid : Prop := ∀ r, ((protoOf F E).selSpec r).Admits (rho.sel r)

/-- Credentials: every signed object inside a delivered object is signed by a
key selected for its role, faulty signers included. This is the soundness of
the deployed membership mechanism (a public committee list, VRF proofs, …): a
model-adequacy binding, not something honest code checks. -/
def Credentials : Prop :=
  ∀ (i : Nat) (w : V) (o : (protoOf F E).Object) (t : Time),
    rho.events[i]? = some (Event.deliver w o t) →
    ∀ o', Obj.Contains o o' → ∀ k r, o'.auth = .signed k r → k ∈ rho.sel r

/-- A valid execution. -/
structure ExecutionValid : Prop extends
  ScheduleWellFormed rho, SleepWellFormed rho where
  unforgeable : Unforgeable rho
  selValid : SelValid rho
  credentials : Credentials rho

/-- Node `w` holds `o` at deadline `d`: it released or received `o` at some
`t' < d` and has not restarted in `(t', d)`. A receipt before a sleep does not
serve after the wake. -/
def Served (w : V) (o : (protoOf F E).Object) (d : Time) : Prop :=
  ∃ t', t' < d ∧ (rho.releases w o t' ∨ rho.receives w o t') ∧
    ∀ u, Event.restart w u ∈ rho.events → ¬ (t' < u ∧ u < d)

/-- Delivery with deadline function `dl` up to `cut`: what an honest node
releases at `t` is held, by `dl a`, by every honest node awake on `[a, dl a)`,
for every `a ≥ t`. Only released objects are flooded; relay of received
objects is protocol gossip. Transactions submitted to awake honest sources
are held strictly before the same deadlines; their cumulative inbox survives
restarts, so transaction service needs no restart exclusion. -/
def TxHeld (w : V) (x : Tx) (d : Time) : Prop :=
  ∃ τ, 0 ≤ τ ∧ τ < d ∧ x ∈ rho.inbox w τ

structure Delivers (dl : Time → Time) (cut : Time) : Prop where
  objects : ∀ v ∈ rho.honest, ∀ o t, rho.releases v o t → ∀ w ∈ rho.honest, ∀ a, t ≤ a →
    dl a ≤ cut → dl a ≤ rho.horizon → AwakeOn E w a (dl a) → rho.Served w o (dl a)
  txs : ∀ u ∈ rho.honest, ∀ x τ, 0 ≤ τ → E.awake u τ = true → x ∈ rho.submit u τ →
    ∀ w ∈ rho.honest, ∀ a, τ ≤ a → dl a ≤ cut → dl a ≤ rho.horizon →
      AwakeOn E w a (dl a) → rho.TxHeld w x (dl a)

/-- Partial synchrony: delivery within `Δ` after `max a GST`. -/
def PartialSynchrony : Prop :=
  rho.Delivers (fun a => max a E.gst + E.Δ) rho.horizon

/-- Synchrony up to `cut`: delivery within `Δ`, for deadlines up to `cut`. -/
def HealthyPrefixDelivery (cut : Time) : Prop :=
  rho.Delivers (fun a => a + E.Δ) cut

end Run

end Consensus.Model

end
