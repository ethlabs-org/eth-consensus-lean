module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Interface
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Goldilocks

public section

/-! # Growing engine-to-node simulation contract

Event correspondence is unconditional: execution validity already requires each event's
node to be honest at that event. State observations and publication laws instead test
honesty at their own cut. The construction remains the canonical event expansion.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape
open Consensus.Model (pubOf)
open SA (Vote)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- The canonical engine expansion obeys the node laws with time-indexed honesty. -/
structure SimulatesAt (tr : GoldilocksTrace (S.params (pubOf E) hn) (S.ro _))
    (ι : Nat → Nat) : Prop where
  run : Growing.GoldilocksRun (runProposer S rho hn) (digestOf S rho)
    (honestKeysAt S rho) tr
  ι_zero : ι 0 = 0
  ι_mono : Monotone ι
  covered : ∀ k, tr.label k ≠ none →
    ∃ i < rho.events.length, ι i ≤ k ∧ k < ι (i + 1)
  state : ∀ v i, i ≤ rho.events.length → v ∉ rho.faultyAt (rho.cutTime i) →
    (stateAt S rho hn v i).node = tr.state (rho.ownKey v) (ι i)
  now : ∀ v i, (stateAt S rho hn v i).now = lastClock S rho v i
  tick_public : ∀ v i t, rho.events[i]? = some (.tick v t) →
    (S.params (pubOf E) hn).toParams.IsPublic t →
      tr.GroupAt (runProposer S rho hn) (digestOf S rho) (rho.ownKey v) (ι i) t
          (.tick (encodeTxs (Model.mempool rho.inbox v t))) ∧
        ι (i + 1) = ι i + (Node.exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
          (tr.state (rho.ownKey v) (ι i)) t
          (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2.length
  tick_other : ∀ v i t, rho.events[i]? = some (.tick v t) →
    ¬ (S.params (pubOf E) hn).toParams.IsPublic t → ι (i + 1) = ι i
  deliver : ∀ v i o t, rho.events[i]? = some (.deliver v o t) →
    DeliverSeq (runProposer S rho hn) tr (digestOf S rho)
      (Model.digests rho.hash o) (rho.ownKey v) t
      (delivered (S.params (pubOf E) hn) o) (ι i) (ι (i + 1))
  restart : ∀ v i t, rho.events[i]? = some (.restart v t) →
    tr.GroupAt (runProposer S rho hn) (digestOf S rho) (rho.ownKey v) (ι i) t .restart ∧
      ι (i + 1) = ι i + (Node.exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (tr.state (rho.ownKey v) (ι i)) t .restart).2.length
  awake_of : ∀ y t, y ∈ honestKeysAt S rho t → tr.awake y t →
    E.awake (rho.key y) t = true ∧ 0 ≤ t ∧ t ≤ rho.horizon
  awake_to : ∀ y t, y ∈ honestKeysAt S rho t → E.awake (rho.key y) t = true →
    0 ≤ t → tr.InHorizon t → tr.awake y t
  block_released : ∀ y k B, y ∈ honestKeysAt S rho (tr.time k) → tr.OwnBlockAt y k B →
    rho.releases (rho.key y) (blockObj (S.params (pubOf E) hn) B) (tr.time k)
  vote_released : ∀ y k m, y ∈ honestKeysAt S rho (tr.time k) → tr.EmitAt y k m →
    ReleasedFrom S rho (rho.key y) (voteObj m) (tr.time k)
  att_released : ∀ y k a, y ∈ honestKeysAt S rho (tr.time k) → tr.SignAt y k a →
    ReleasedFrom S rho (rho.key y) (attObj a) (tr.time k)
  block_relayed : ∀ y k B, y ∈ honestKeysAt S rho (tr.time k) →
    tr.AcceptAt y k B → tr.pos k = 0 →
      RelayedFrom S rho (rho.key y) (blockObj (S.params (pubOf E) hn) B) (tr.time k)
  vote_forwarded : ∀ y k (m : Vote (Fintype.card V)), y ∈ honestKeysAt S rho (tr.time k) →
    (tr.EmitAt y k m ∨
      ((tr.MsgCallAt y k m ∨ ∃ ℓ B, tr.CallAt y k (.ac ℓ) ∧ ℓ.call = .block B ∧
          m ∈ SA.blockVotes B) ∧
        m ∉ (tr.state y k).ac.pool m.slot ∧ m ∈ (tr.post k).ac.pool m.slot)) →
    let envelope : (Model.protoOf (compiled (goldilocks S)) E).Object :=
      .mk (.signed y .poll) (.data (.voteForward (tr.time k) (encodeVote m))) [voteObj m]
    ∃ i, ι i ≤ k ∧ k < ι (i + 1) ∧ rho.SendsAt (rho.key y) i (tr.time k) ∧
      envelope ∈ rho.releasesAt i ∧ ∀ j < i, envelope ∉ rho.releasesAt j
  att_relayed : ∀ y k a, y ∈ honestKeysAt S rho (tr.time k) →
    tr.AttCallAt y k a → tr.pos k = 0 →
      RelayedFrom S rho (rho.key y) (attObj a) (tr.time k)

variable (V) in
/-- Every valid growing-fault engine run has a simulating node trace. -/
def EngineSimulatesNodeAt : Prop :=
  ∀ (E : Env V) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V),
    rho.ExecutionValid → ∃ tr ι, SimulatesAt S rho hn tr ι

variable (V) in
/-- Collision freedom transports to the canonical growing trace. -/
def NoCollTransportAt : Prop :=
  ∀ (E : Env V) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V),
    rho.ExecutionValid → ¬ rho.HashCollision →
      Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn)

end Consensus.Goldilocks.Simulation
