module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Shape

public section

/-! # Goldilocks Refinement: the simulating trace is a run, and the engine agrees with it

The steps of `EngineSimulatesNode` over the trace `simTrace` and the cut map `cutMap` built from
a valid engine run (`Trace`): one theorem per field of `GoldilocksRun` (the trace is a run of the
Goldilocks protocol at the engine's digest, for the honest keys) and one per field of
`Simulates` (the engine's events are the trace's groups, the engine's node states are the trace's
states, the engine releases and relays what the trace signs, emits and admits). The engine-side
facts they rest on are the steps of `Steps`; the shape's pure facts those of `Shape`.

Each theorem is a named step; the `sorry` ones are open. `Simulation` assembles them. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload blockVotes)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

/-! ## `LocalRun` -/

/-- Each honest node starts from the initial node state. -/
theorem simTrace_init :
    ∀ y ∈ honestKeys S rho, (simTrace S rho hn).init y = Node.init _ :=
  fun y _ => simTrace_init_eq S rho hn y

/-- Every labelled cut of an honest node lies in the group of a top-level event. -/
theorem simTrace_grouped (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i c, (simTrace S rho hn).CallAt y i c →
      ∃ j e, (simTrace S rho hn).InGroup (digestOf S rho) y j i ((simTrace S rho hn).time i) e := by
  sorry

/-- Every labelled cut of an honest node obeys the cut law. -/
theorem simTrace_cutLaw (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i c, (simTrace S rho hn).CallAt y i c →
      CutStep y ((simTrace S rho hn).time i) ((simTrace S rho hn).state y i) c
        ((simTrace S rho hn).post i) := by
  sorry

/-- A delivery to an honest node passes the wire checks. -/
theorem simTrace_wire (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ j t e, (simTrace S rho hn).GroupAt (digestOf S rho) y j t e →
      WireOK (digestOf S rho) e := by
  sorry

/-- Cuts are at times from `0` on. -/
theorem simTrace_time_nonneg (hv : rho.ExecutionValid) :
    ∀ i, 0 ≤ (simTrace S rho hn).time i := by
  sorry

/-- The cut order is by time. -/
theorem simTrace_time_mono (hv : rho.ExecutionValid) : Monotone (simTrace S rho hn).time := by
  sorry

/-- Finitely many labelled cuts in every bounded interval. -/
theorem simTrace_finite (hv : rho.ExecutionValid) :
    ∀ T : Time,
      {i | (simTrace S rho hn).label i ≠ none ∧ (simTrace S rho hn).time i ≤ T}.Finite := by
  sorry

/-- At one time, across the honest nodes, the groups are in phase order. -/
theorem simTrace_phase_order (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ y' ∈ honestKeys S rho, ∀ j j' t e e',
      (simTrace S rho hn).GroupAt (digestOf S rho) y j t e →
      (simTrace S rho hn).GroupAt (digestOf S rho) y' j' t e' → j < j' →
        e.phase ≤ e'.phase := by
  sorry

/-- A tick is at a public time. -/
theorem simTrace_tick_public (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ j t, (simTrace S rho hn).TickAt (digestOf S rho) y j t →
      (S.params (pubOf E) hn).toParams.IsPublic t := by
  sorry

/-- One tick per node and time. -/
theorem simTrace_tick_unique (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ j j' t, (simTrace S rho hn).TickAt (digestOf S rho) y j t →
      (simTrace S rho hn).TickAt (digestOf S rho) y j' t → j = j' := by
  sorry

/-- An honest node awake at a public time (from `0` on) ticks there. -/
theorem simTrace_tick_of_awake (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ t, 0 ≤ t → (S.params (pubOf E) hn).toParams.IsPublic t →
      (simTrace S rho hn).awake y t → ∃ j, (simTrace S rho hn).TickAt (digestOf S rho) y j t := by
  sorry

/-- An honest node is called only while awake. -/
theorem simTrace_awake_of_call (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i, (simTrace S rho hn).IsCall y i →
      (simTrace S rho hn).awake y ((simTrace S rho hn).time i) := by
  sorry

/-- The first call of an honest node after it was asleep is a restart. -/
theorem simTrace_restart_of_sleep (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i (u : Time), (simTrace S rho hn).IsCall y i → 0 ≤ u →
      u < (simTrace S rho hn).time i → ¬ (simTrace S rho hn).awake y u →
      (∀ j < i, (simTrace S rho hn).IsCall y j → (simTrace S rho hn).time j < u) →
        (simTrace S rho hn).RestartAt y i := by
  sorry

/-- A wake is a restart. -/
theorem simTrace_restart_at_wake (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ u v : Time, 0 ≤ u → u < v → ¬ (simTrace S rho hn).awake y u →
      (simTrace S rho hn).awake y v →
        ∃ k, (simTrace S rho hn).RestartAt y k ∧ u < (simTrace S rho hn).time k ∧
          (simTrace S rho hn).time k ≤ v := by
  sorry

/-- A restart is a wake. -/
theorem simTrace_sleep_of_restart (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i, (simTrace S rho hn).RestartAt y i →
      ∃ u : Time, 0 ≤ u ∧ u < (simTrace S rho hn).time i ∧ ¬ (simTrace S rho hn).awake y u ∧
        ∀ j < i, (simTrace S rho hn).IsCall y j → (simTrace S rho hn).time j < u := by
  sorry

/-- A block of an honest proposer that an honest node processes is the proposer's own block,
processed by the proposer at or before (the engine's `Credentials`: a delivered block object
signed by an honest key was released by that key's node). -/
theorem simTrace_block_unforgeable (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i B, (simTrace S rho hn).BlockCallAt y i B →
      B.proposer ∈ honestKeys S rho → ∃ j ≤ i, (simTrace S rho hn).OwnBlockAt B.proposer j B := by
  sorry

/-- An attestation of an honest signer that an honest node processes was signed by that signer
at an earlier cut. -/
theorem simTrace_att_unforgeable (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i a,
      ((simTrace S rho hn).AttCallAt y i a ∨
        ∃ B, (simTrace S rho hn).BlockCallAt y i B ∧ a ∈ B.fgPayload) →
      a.val ∈ honestKeys S rho → ∃ j < i, (simTrace S rho hn).SignAt a.val j a := by
  sorry

/-- An AC message of an honest signer that an honest node receives was emitted by that signer's
node at an earlier cut. -/
theorem simTrace_msg_unforgeable (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i (m : Vote (Fintype.card V)),
      (simTrace S rho hn).MsgCallAt y i m → m.val ∈ honestKeys S rho →
        ∃ j < i, (simTrace S rho hn).EmitAt m.val j m := by
  sorry

/-! ## `GoldilocksRun` -/

omit [DecidableEq V] in
/-- The genesis block's root is the digest of its content: `dgOf` at `none` is the genesis
root. -/
theorem simTrace_genesis_root_ok :
    ((S.params (pubOf E) hn).toParams.genesisBlock
      (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload).RootOk
        (digestOf S rho) := by
  sorry

/-- A vote of an honest validator carried by a block that an honest node processes was emitted
by that validator's node at an earlier cut. -/
theorem simTrace_carried_vote_unforgeable (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i B, (simTrace S rho hn).BlockCallAt y i B →
      ∀ v ∈ blockVotes B, v.val ∈ honestKeys S rho →
        ∃ j < i, (simTrace S rho hn).EmitAt v.val j v := by
  sorry

/-- **The simulating trace is a Goldilocks run** at the engine's digest, for the honest keys:
the fields above. -/
theorem simTrace_goldilocksRun (hv : rho.ExecutionValid) :
    GoldilocksRun (digestOf S rho) (honestKeys S rho) (simTrace S rho hn) where
  init := simTrace_init S rho hn
  grouped := simTrace_grouped S rho hn hv
  cutLaw := simTrace_cutLaw S rho hn hv
  wire := simTrace_wire S rho hn hv
  time_nonneg := simTrace_time_nonneg S rho hn hv
  time_mono := simTrace_time_mono S rho hn hv
  finite := simTrace_finite S rho hn hv
  phase_order := simTrace_phase_order S rho hn hv
  tick_public := simTrace_tick_public S rho hn hv
  tick_unique := simTrace_tick_unique S rho hn hv
  tick_of_awake := simTrace_tick_of_awake S rho hn hv
  awake_in_horizon := simTrace_awake_in_horizon S rho hn
  awake_of_call := simTrace_awake_of_call S rho hn hv
  restart_of_sleep := simTrace_restart_of_sleep S rho hn hv
  restart_at_wake := simTrace_restart_at_wake S rho hn hv
  sleep_of_restart := simTrace_sleep_of_restart S rho hn hv
  block_unforgeable := simTrace_block_unforgeable S rho hn hv
  att_unforgeable := simTrace_att_unforgeable S rho hn hv
  msg_unforgeable := simTrace_msg_unforgeable S rho hn hv
  genesis_root_ok := simTrace_genesis_root_ok S rho hn
  carried_vote_unforgeable := simTrace_carried_vote_unforgeable S rho hn hv

/-! ## `Simulates`: the engine agrees with the trace -/

/-- Every labelled node cut lies in the range of some engine event. -/
theorem simTrace_covered :
    ∀ k, (simTrace S rho hn).label k ≠ none →
      ∃ i < rho.events.length, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) := by
  sorry

/-- The node state inside the shape's state is the trace's state at the mapped cut (by induction
on the events, from `node_of_tick_public`, `node_of_tick_other`, `node_of_deliver`,
`node_of_restart` and `state_of_other`). -/
theorem simTrace_state (hv : rho.ExecutionValid) :
    ∀ v ∈ rho.honest, ∀ i ≤ rho.events.length,
      (stateAt S rho hn v i).node =
        (simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i) := by
  sorry

/-- An engine tick of an honest node at a public time is the node's tick with the engine's input,
one group. -/
theorem simTrace_tick_public_group (hv : rho.ExecutionValid) :
    ∀ v ∈ rho.honest, ∀ i t, rho.events[i]? = some (.tick v t) →
      (S.params (pubOf E) hn).toParams.IsPublic t →
        (simTrace S rho hn).GroupAt (digestOf S rho) (rho.ownKey v) (cutMap S rho hn i) t
            (.tick (encodeTxs (Model.mempool rho.inbox v t))) ∧
          cutMap S rho hn (i + 1) = cutMap S rho hn i + (Node.exec (digestOf S rho) (rho.ownKey v)
            ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)) t
            (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2.length := by
  sorry

/-- An engine tick at a non-public time has no cut. -/
theorem simTrace_tick_other (hv : rho.ExecutionValid) :
    ∀ v ∈ rho.honest, ∀ i t, rho.events[i]? = some (.tick v t) →
      ¬ (S.params (pubOf E) hn).toParams.IsPublic t →
        cutMap S rho hn (i + 1) = cutMap S rho hn i := by
  sorry

/-- An engine delivery to an honest node is the groups of the canonical objects it delivers. -/
theorem simTrace_deliver (hv : rho.ExecutionValid) :
    ∀ v ∈ rho.honest, ∀ i o t, rho.events[i]? = some (.deliver v o t) →
      DeliverSeq (simTrace S rho hn) (digestOf S rho) (Model.digests rho.hash o) (rho.ownKey v) t
        (delivered (S.params (pubOf E) hn) o) (cutMap S rho hn i) (cutMap S rho hn (i + 1)) := by
  sorry

/-- An engine restart of an honest node is the node's restart group. -/
theorem simTrace_restart (hv : rho.ExecutionValid) :
    ∀ v ∈ rho.honest, ∀ i t, rho.events[i]? = some (.restart v t) →
      (simTrace S rho hn).GroupAt (digestOf S rho) (rho.ownKey v) (cutMap S rho hn i) t .restart ∧
        cutMap S rho hn (i + 1) = cutMap S rho hn i + (Node.exec (digestOf S rho) (rho.ownKey v)
          ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)) t .restart).2.length := by
  sorry

/-- An honest node awake in the trace is awake in the environment, within `[0, horizon]`: the
trace's horizon is within the engine's, as every cut's time is an event's. -/
theorem simTrace_awake_of (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ t, (simTrace S rho hn).awake y t →
      E.awake (rho.key y) t = true ∧ 0 ≤ t ∧ t ≤ rho.horizon := by
  sorry

/-- The engine releases an honest node's own block at the tick that proposes it (the proposal
duty's candidate is `blockObj` of the block, `releasable` by `proposal_releasable`, passed by
`protects_blockObj`). -/
theorem simTrace_block_released (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ k B, (simTrace S rho hn).OwnBlockAt y k B →
      rho.releases (rho.key y) (blockObj (S.params (pubOf E) hn) B)
        ((simTrace S rho hn).time k) := by
  sorry

/-- The engine releases an honest node's vote from its emission on (the vote is queued in the
outbox and released by a poll step of the next tick at which the node is awake; `outbox_le_two`
gives that two poll steps suffice). -/
theorem simTrace_vote_released (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ k m, (simTrace S rho hn).EmitAt y k m →
      ReleasedFrom S rho (rho.key y) (voteObj m) ((simTrace S rho hn).time k) := by
  sorry

/-- The engine releases an honest node's attestation from its signing on (queued by `fgUpdate`,
released by the tick's last poll steps; `protects_own_att` passes it). -/
theorem simTrace_att_released (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ k a, (simTrace S rho hn).SignAt y k a →
      ReleasedFrom S rho (rho.key y) (attObj a) ((simTrace S rho hn).time k) := by
  sorry

/-- An honest node relays a block it accepts from the wire. -/
theorem simTrace_block_relayed (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ k B, (simTrace S rho hn).AcceptAt y k B →
      (simTrace S rho hn).pos k = 0 →
        RelayedFrom S rho (rho.key y) (blockObj (S.params (pubOf E) hn) B)
          ((simTrace S rho hn).time k) := by
  sorry

/-- An honest node relays a vote it admits from the wire. -/
theorem simTrace_vote_relayed (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ k m, (simTrace S rho hn).MsgCallAt y k m →
      m ∈ ((simTrace S rho hn).post k).ac.pool m.slot →
        RelayedFrom S rho (rho.key y) (voteObj m) ((simTrace S rho hn).time k) := by
  sorry

/-- An honest node relays an attestation it receives from the wire. -/
theorem simTrace_att_relayed (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ k a, (simTrace S rho hn).AttCallAt y k a →
      (simTrace S rho hn).pos k = 0 →
        RelayedFrom S rho (rho.key y) (attObj a) ((simTrace S rho hn).time k) := by
  sorry

end Consensus.Goldilocks.Refinement

end
