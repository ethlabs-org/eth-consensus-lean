module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Outbox
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Frame
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Agree.Pool
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Lemmas.Problem.Constant
public import Mathlib.Tactic.IntervalCases

public section

/-! # Vote-forward envelopes in the vote pool

Every pending admission envelope keeps its vote in the stored pool: through the shape handlers,
every duty prefix (`runDuties_voteForward_in_pool`) and delivery processing
(`delivery_voteForward_in_pool`); the stored pool only grows along a duty prefix
(`runDuties_pool_subset`). Also the poll-attestation protection premise `PollAttProtected` of the
engine inventory (`Queue`), with its characterisation `pollAttProtected_iff`. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload SAState)

variable {binding : VoteBinding}

section ShapeInventory

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- Every pending admission envelope still has its vote in the stored pool. -/
private def QueuedInPool (st : State sp ro binding) : Prop :=
  ∀ tv ∈ st.voteForwards, tv.2 ∈ st.node.ac.pool tv.2.slot

private theorem apply_queuedInPool (st : State sp ro binding) r (h : QueuedInPool st)
    (hg : ∀ σ, st.node.ac.pool σ ⊆ r.1.ac.pool σ) : QueuedInPool (apply st r) := by
  intro tv htv
  by_cases hold : tv ∈ st.voteForwards
  · exact hg _ (h tv hold)
  · exact (apply_voteForward_fresh st r tv.1 tv.2 htv hold).2.2

private theorem block_queuedInPool (st : State sp ro binding) (B : Blk sp) (h : QueuedInPool st) :
    QueuedInPool (apply st (Node.onBlock st.self st.node st.now B)) := by
  apply apply_queuedInPool st _ h
  unfold Node.onBlock
  split_ifs
  · exact fun _ => List.Subset.refl _
  · split
    · exact fun _ => List.Subset.refl _
    · exact SA.step_pool_subset st.self st.node.ac _ st.now (.block B) (by simp)

private theorem processOne_queuedInPool hs (st : State sp ro binding) o (h : QueuedInPool st) :
    QueuedInPool (processOne hs st o) := by
  unfold processOne
  split
  · dsimp only
    unfold relayIf
    split <;> exact block_queuedInPool st _ h
  · apply apply_queuedInPool st _ h
    exact SA.step_pool_subset st.self st.node.ac _ st.now (.message _) (by simp)
  · unfold relayIf
    split <;> apply apply_queuedInPool st _ h <;> exact fun _ => List.Subset.refl _
  · exact h

private theorem process_queuedInPool (st : State sp ro binding) o hs (h : QueuedInPool st) :
    QueuedInPool (process st o hs) := by
  unfold process
  generalize delivered sp o = os
  induction os generalizing st with
  | nil => exact h
  | cons o os ih => exact ih _ (processOne_queuedInPool hs st o h)

private theorem record_queuedInPool (st : State sp ro binding) o hs (h : QueuedInPool st) :
    QueuedInPool (recordOwn st o hs) := by
  unfold recordOwn
  split
  · exact h
  · split
    · exact block_queuedInPool st _ h
    · exact h
  · exact h

private theorem propose_queuedInPool (st : State sp ro binding) s (h : QueuedInPool st) :
    QueuedInPool (propose st s).1 := by
  have hp : (Node.acProposal st.node st.now).1.ac.pool = st.node.ac.pool := by
    change (SA.acProposal sp st.node.ac (frame st.node) st.now).1.pool = _
    unfold SA.acProposal
    split_ifs <;> rfl
  unfold propose
  dsimp only
  split <;> intro tv htv <;> rw [hp] <;> exact h tv htv

private theorem nodeTick_queuedInPool (st : State sp ro binding) (h : QueuedInPool st) :
    QueuedInPool (nodeTick st) := by
  unfold nodeTick
  split
  · apply apply_queuedInPool st _ h
    exact SA.step_pool_subset st.self st.node.ac _ st.now .tick (by simp)
  · exact h

private theorem poll_queuedInPool (st : State sp ro binding) t : QueuedInPool (poll st t).1 := by
  intro tv htv
  rw [poll_voteForwards] at htv
  cases htv

private theorem block_pool_subset (st : State sp ro binding) (B : Blk sp) (σ : Nat) :
    st.node.ac.pool σ ⊆ (apply st (Node.onBlock st.self st.node st.now B)).node.ac.pool σ := by
  unfold apply Node.onBlock
  dsimp only
  split_ifs
  · exact List.Subset.refl _
  · split
    · exact List.Subset.refl _
    · exact SA.step_pool_subset st.self st.node.ac _ st.now (.block B) (by simp) σ

private theorem record_pool_subset (st : State sp ro binding) o hs (σ : Nat) :
    st.node.ac.pool σ ⊆ (recordOwn st o hs).node.ac.pool σ := by
  unfold recordOwn
  split
  · exact List.Subset.refl _
  · split
    · exact block_pool_subset st _ σ
    · exact List.Subset.refl _
  · exact List.Subset.refl _

private theorem propose_pool_eq (st : State sp ro binding) s :
    (propose st s).1.node.ac.pool = st.node.ac.pool := by
  have hp : (Node.acProposal st.node st.now).1.ac.pool = st.node.ac.pool := by
    change (SA.acProposal sp st.node.ac (frame st.node) st.now).1.pool = _
    unfold SA.acProposal
    split_ifs <;> rfl
  unfold propose
  dsimp only
  split <;> exact hp

private theorem nodeTick_pool_subset (st : State sp ro binding) (σ : Nat) :
    st.node.ac.pool σ ⊆ (nodeTick st).node.ac.pool σ := by
  unfold nodeTick
  split
  · exact SA.step_pool_subset st.self st.node.ac _ st.now .tick (by simp) σ
  · exact List.Subset.refl _

/-- Polling, including the due FG update, leaves vote pools unchanged. -/
theorem poll_pool_eq (st : State sp ro binding) t :
    (poll st t).1.node.ac.pool = st.node.ac.pool := by
  have hp : (Node.acToFG st.node st.now).1.ac.pool = st.node.ac.pool := by
    change (SA.acToFG sp st.node.ac (frame st.node) st.now).1.pool = _
    unfold SA.acToFG
    split_ifs
    · split
      · rfl
      · split_ifs <;> rfl
    · rfl
  have hg : (fgUpdate st).node.ac.pool = st.node.ac.pool := by
    unfold fgUpdate
    dsimp only
    split
    · exact hp
    · split <;> exact hp
  unfold poll
  split_ifs <;> dsimp only <;> split <;> first | exact hg | rfl
end ShapeInventory

section EngineInventory

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
/-- Every duty prefix preserves the fact that queued vote envelopes name stored
votes. In particular this applies to the polls of a tick, not only deliveries. -/
theorem runDuties_voteForward_in_pool (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocksWith S)) E))
    (ds : List (Model.protoOf (compiled (goldilocksWith S)) E).Duty)
    (h : ∀ tv ∈ (shapeOf S hn nd).voteForwards,
      tv.2 ∈ (shapeOf S hn nd).node.ac.pool tv.2.slot) :
    ∀ tv ∈ (shapeOf S hn (rho.runDuties v nd ds).1).voteForwards,
      tv.2 ∈ (shapeOf S hn (rho.runDuties v nd ds).1).node.ac.pool tv.2.slot := by
  exact runDuties_pres S rho hn QueuedInPool record_queuedInPool propose_queuedInPool
    nodeTick_queuedInPool (fun st t _ => poll_queuedInPool st t) v nd ds h

omit [DecidableEq V] in
/-- A single duty preserves queue backing, including its own released blocks. -/
theorem dutyStep_voteForward_in_pool (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocksWith S)) E))
    (d : (Model.protoOf (compiled (goldilocksWith S)) E).Duty)
    (h : ∀ tv ∈ (shapeOf S hn nd).voteForwards,
      tv.2 ∈ (shapeOf S hn nd).node.ac.pool tv.2.slot) :
    ∀ tv ∈ (shapeOf S hn (rho.dutyStep v nd d).1).voteForwards,
      tv.2 ∈ (shapeOf S hn (rho.dutyStep v nd d).1).node.ac.pool tv.2.slot := by
  exact dutyStep_pres S rho hn QueuedInPool record_queuedInPool propose_queuedInPool
    nodeTick_queuedInPool (fun st t _ => poll_queuedInPool st t) v nd d h

omit [DecidableEq V] in
/-- A single duty retains stored votes through its own-object release callbacks. -/
theorem dutyStep_pool_subset (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocksWith S)) E))
    (d : (Model.protoOf (compiled (goldilocksWith S)) E).Duty) (σ : Nat) :
    (shapeOf S hn nd).node.ac.pool σ ⊆
      (shapeOf S hn (rho.dutyStep v nd d).1).node.ac.pool σ := by
  intro m hm
  exact dutyStep_pres S rho hn (fun st => m ∈ st.node.ac.pool σ)
    (fun st o hs h => record_pool_subset st o hs σ h)
    (fun st s h => by rw [propose_pool_eq]; exact h)
    (fun st h => nodeTick_pool_subset st σ h)
    (fun st t h => by rw [poll_pool_eq]; exact h) v nd d hm

omit [DecidableEq V] in
/-- Duty execution never removes a stored vote; only restart replay can do so. -/
theorem runDuties_pool_subset (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocksWith S)) E))
    (ds : List (Model.protoOf (compiled (goldilocksWith S)) E).Duty) (σ : Nat) :
    (shapeOf S hn nd).node.ac.pool σ ⊆
      (shapeOf S hn (rho.runDuties v nd ds).1).node.ac.pool σ := by
  intro m hm
  exact runDuties_pres S rho hn (fun st => m ∈ st.node.ac.pool σ)
    (fun st o hs h => record_pool_subset st o hs σ h)
    (fun st s h => by rw [propose_pool_eq]; exact h)
    (fun st h => nodeTick_pool_subset st σ h)
    (fun st t h => by rw [poll_pool_eq]; exact h) v nd ds hm

/-- **Poll-attestation protection**: at every actual duty cut of a key not faulty at `0`, the
ordinary attestation of a scheduled poll passes the own-signature guard. Under constant faults it
is `engine_poll_att_protected`; under growing faults, `engine_poll_att_protected_at`. -/
def PollAttProtected : Prop :=
  ∀ (v : V), v ∉ rho.faultyAt 0 → ∀ {i p : Nat} {nd} {k : Nat}, EngineDutyCut S rho v i p nd →
    ((∃ t, rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
        ((Model.protoOf (compiled (goldilocksWith S)) E).duties t)[p]? = some (.poll k)) ∨
      ∃ t o, rho.events[i]? = some (.deliver v o t) ∧
        ((Model.protoOf (compiled (goldilocksWith S)) E).deliverDuties t)[p]? = some (.poll k)) →
    rho.ownKey v ∈ rho.sel .poll → ∀ {w cs}, (poll (nd.st.1 hn) k).2 = some (.att w, cs) →
    Model.protects (Model.protoOf (compiled (goldilocksWith S)) E) (rho.ownKey v) nd.seen
      (.mk (.signed (rho.ownKey v) .poll) (.data (.att w)) []) = true

theorem pollAttProtected_iff : PollAttProtected S rho hn ↔
    ∀ (v : V), v ∉ rho.faultyAt 0 → ∀ {i p : Nat} {nd} {k : Nat}, EngineDutyCut S rho v i p nd →
      ((∃ t, rho.events[i]? = some (.tick v t) ∧ E.awake v t = true ∧
          ((Model.protoOf (compiled (goldilocksWith S)) E).duties t)[p]? = some (.poll k)) ∨
        ∃ t o, rho.events[i]? = some (.deliver v o t) ∧
          ((Model.protoOf (compiled (goldilocksWith S)) E).deliverDuties t)[p]? = some (.poll k)) →
      rho.ownKey v ∈ rho.sel .poll → ∀ {w cs}, (poll (nd.st.1 hn) k).2 = some (.att w, cs) →
      Model.protects (Model.protoOf (compiled (goldilocksWith S)) E) (rho.ownKey v) nd.seen
        (.mk (.signed (rho.ownKey v) .poll) (.data (.att w)) []) = true := Iff.rfl

/-- Delivery processing keeps every queued admission's vote in the final pool. The actual
event-boundary queue is empty, and none of the delivery handlers restarts the AC. -/
theorem delivery_voteForward_in_pool (hv : rho.ExecutionValid) (v : V) (i : Nat)
    (o : (Model.protoOf (compiled (goldilocksWith S)) E).Object)
    (tv : Time × Vote (Fintype.card V))
    (htv : tv ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).voteForwards) :
    tv.2 ∈ (process (stateAt S rho hn v i) o
      (Model.digests rho.hash o)).node.ac.pool tv.2.slot := by
  apply process_queuedInPool (stateAt S rho hn v i) o (Model.digests rho.hash o) ?_ tv htv
  intro q hq
  rw [voteForwards_empty S rho hn hv v i] at hq
  cases hq
end EngineInventory

end Consensus.Goldilocks.Simulation

end
