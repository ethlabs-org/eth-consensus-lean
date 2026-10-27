module
public import AvailableChainContract.Run
public import AvailableChainContract.Constants

@[expose] public section

/-! # Conditions

Premises about runs. None of them mentions anything the protocol supplies:
they speak about the environment, the run data, and what the engine did
(ticks, releases, receipts, restarts). -/

namespace AvailableChain.Contract

open AvailableChain.Generic

variable {V : Type} [Fintype V] [DecidableEq V] {F : Family} {E : Env V}

/-- A public time is a nonnegative multiple of `Δ`. -/
def PublicTime (E : Env V) (t : Time) : Prop := ∃ k : Nat, t = (k : Time) * E.Δ

/-- `v` wakes at `t`: awake at `t`, asleep at `t − 1`. -/
def Wakes (E : Env V) (v : V) (t : Time) : Prop :=
  E.awake v t = true ∧ E.awake v (t - 1) = false

/-- `v` is awake on `[a, b)`. -/
def AwakeOn (E : Env V) (v : V) (a b : Time) : Prop :=
  ∀ u, a ≤ u → u < b → E.awake v u = true

/-- `v` is awake on `[a, b]`. -/
def AwakeOnClosed (E : Env V) (v : V) (a b : Time) : Prop :=
  ∀ u, a ≤ u → u ≤ b → E.awake v u = true

namespace Run

variable (rho : Run F E)

/-- Events are in time order, finite, honest only, and every awake honest node
ticks at every public time of the horizon. -/
structure ScheduleWellFormed : Prop where
  horizon_nonneg : 0 ≤ rho.horizon
  sorted : rho.events.Pairwise Event.keyLe
  nodup : rho.events.Nodup
  in_horizon : ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon
  honest_only : ∀ e ∈ rho.events, e.node ∈ rho.honest
  tick_public : ∀ v t, Event.tick v t ∈ rho.events → PublicTime E t
  tick_total : ∀ v ∈ rho.honest, ∀ t, PublicTime E t → t ≤ rho.horizon →
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
    ∀ o', Obj.Contains o o' → ∀ u ∈ rho.honest, rho.holder o'.auth = some u →
      ∃ (j : Nat) (t' : Time), j < i ∧ rho.events[j]? = some (Event.tick u t') ∧
        o' ∈ rho.releasesAt j

/-- A valid execution. -/
structure ExecutionValid : Prop extends
  ScheduleWellFormed rho, SleepWellFormed rho where
  unforgeable : Unforgeable rho

/-- Node `w` holds `o` at deadline `d`: it released or received `o` at some
`t' < d` and has not restarted in `(t', d)`. A receipt before a sleep does not
serve after the wake. -/
def Served (w : V) (o : (protoOf F E).Object) (d : Time) : Prop :=
  ∃ t', t' < d ∧ (rho.releases w o t' ∨ rho.receives w o t') ∧
    ∀ u, Event.restart w u ∈ rho.events → ¬ (t' < u ∧ u < d)

/-- Delivery with deadline function `dl` up to `cut`: what an honest node
releases at `t` is held, by `dl a`, by every honest node awake on `[a, dl a)`,
for every `a ≥ t`. Only released objects are flooded; relay of received
objects is protocol gossip. -/
def Delivers (dl : Time → Time) (cut : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ o t, rho.releases v o t → ∀ w ∈ rho.honest, ∀ a, t ≤ a →
    dl a ≤ cut → dl a ≤ rho.horizon → AwakeOn E w a (dl a) → rho.Served w o (dl a)

/-- Partial synchrony: delivery within `Δ` after `max a GST`. -/
def PartialSynchrony : Prop :=
  rho.Delivers (fun a => max a E.t_GST + E.Δ) rho.horizon

/-- Synchrony up to `cut`: delivery within `Δ`, for deadlines up to `cut`. -/
def HealthyPrefixDelivery (cut : Time) : Prop :=
  rho.Delivers (fun a => a + E.Δ) cut

/-- Faulty validators: the complement of the honest set. -/
def faulty : Finset V := Finset.univ \ rho.honest

/-- Honest validators awake at `t`. -/
def awakeAt (t : Time) : Finset V := rho.honest.filter (fun v => E.awake v t = true)

/-- Honest validators awake at some time in `[a, b]`. -/
noncomputable def awakeIn (a b : Time) : Finset V := by
  classical
  exact rho.honest.filter (fun v => ∃ u, a ≤ u ∧ u ≤ b ∧ E.awake v u = true)

/-- `v` is ready at `t`: honest and awake throughout
`[t − catchUp·Δ − 1, t]`. It therefore did not wake, so did not restart, in
`[t − catchUp·Δ, t]`. Participation premises count ready nodes. -/
def Ready (C : Constants) (v : V) (t : Time) : Prop :=
  v ∈ rho.honest ∧ AwakeOnClosed E v (t - (C.catchUp : Time) * E.Δ - 1) t

/-- The ready honest validators at `t`. -/
noncomputable def readyAt (C : Constants) (t : Time) : Finset V := by
  classical
  exact rho.honest.filter (fun v => rho.Ready C v t)

/-- More ready honest validators than faulty ones. -/
def ReadyMajority (C : Constants) (t : Time) : Prop :=
  rho.faulty.card < (rho.readyAt C t).card

/-- `|ready_t| > θ · |H_[t−η,t] ∪ A|`. -/
def EtaSleepy (C : Constants) (t : Time) : Prop :=
  C.θ * ((rho.awakeIn (t - (C.η : Time) * E.Δ) t ∪ rho.faulty).card : ℚ) <
    ((rho.readyAt C t).card : ℚ)

/-- Every honest validator is awake from `start` to the horizon. -/
def FullParticipation (start : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ t, start ≤ t → t ≤ rho.horizon → E.awake v t = true

/-- Fewer than a quarter of the validators are faulty. -/
def BelowQuarter : Prop := 4 * rho.faulty.card < Fintype.card V

/-- Fewer than a third of the validators are faulty. -/
def BelowOneThird : Prop := 3 * rho.faulty.card < Fintype.card V

/-- The proposer of slot `s` is ready at its proposal time. -/
def ReadyProposer (C : Constants) (s : Slot) : Prop :=
  rho.Ready C (rho.proposer s) ((protoOf F E).proposalTime s)

/-- Recurrence with gap `k` slots from `start`: every window `(t, t + k·slot]`
with `start ≤ t` that ends by the horizon contains the proposal time of a slot
with a ready proposer. (`k = 0` is unsatisfiable.) -/
def Recurrence (C : Constants) (start : Time) (k : Nat) : Prop :=
  ∀ t, start ≤ t → t + (k : Time) * (protoOf F E).slotLen ≤ rho.horizon →
    ∃ s : Slot, t < (protoOf F E).proposalTime s ∧
      (protoOf F E).proposalTime s ≤ t + (k : Time) * (protoOf F E).slotLen ∧
      rho.ReadyProposer C s

end Run

end AvailableChain.Contract

end
