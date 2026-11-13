module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ForwardingDecodeBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ForwardingInvariant
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ForwardingChain
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationDecode
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Forwarding decoder correspondence

Relate the durable wrapper's decoded child to the actual held block, rather than
identifying blocks by equal roots without a store correspondence proof. The state invariants and
their preservation by each engine transition are in `Obligations/ForwardingDecodeBase`; here every
reachable honest engine state satisfies them, and every acceptance publishes its decoded wrapper.
-/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open Shape Blocks
open Consensus.Model

/-- A scheduled honest proposal's actual pre-record state supplies canonical child validity. -/
theorem scheduled_proposal_child_decodes {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    (v : V) (hh : v ∉ rho.faultyAt 0) (i : Nat) (t : Time)
    (he : rho.events[i]? = some (.tick v t))
    (hp : Node.Proposes (P := (S.params (pubOf E) hn).toParams)
      (runProposer S rho hn) (rho.ownKey v) t) :
    let nd := atProposal S rho v (rho.stateBefore i v) t
    let r := Node.acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now
    ∀ d p, r.2.2 = some (d, p) →
      let B := Node.mkBlock (digestOf S rho) (rho.ownKey v) r.1.fg
        (shapeOf S hn nd).now (encodeTxs nd.st.2) d.head p
      decodeBlock (S.params (pubOf E) hn) (binding := stock) (digests rho.hash (blockObj _ B))
        (blockObj _ B) = some B := by
  have run := simTrace_goldilocksRun S rho hn hf hv
  have hhon : rho.ownKey v ∈ honestKeys S rho := by
    rw [mem_honestKeys_iff]
    have hk : rho.key (rho.ownKey v) = v := rho.key.apply_symm_apply v
    rwa [hk]
  have hpub := (S.params (pubOf E) hn).toParams.slotTime_public
    ((S.params (pubOf E) hn).toParams.slotOf t)
  rw [← hp.2.1] at hpub
  have hg := (simTrace_tick_public_group S rho hn hf hv v hh i t he hpub).1
  obtain ⟨cfg, hr, hst, hs⟩ := Compose.group_step run.toLocalRun hhon hg
  have hstate := simTrace_state S rho hn hf hv v hh i
    (Nat.le_of_lt (List.getElem?_eq_some_iff.mp he).1)
  exact scheduled_proposal_child_decodes_of_step S rho hn hv v i t hp hr
    (hst.trans hstate.symm) hs run.genesis_root_ok

/-- At a scheduled honest tick, the proposal duty preserves the joint invariant without
assuming child decoding: reachable proposal execution supplies it. -/
theorem decoded_held_scheduled_proposal {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    (v : V) (hhon : v ∉ rho.faultyAt 0) (i : Nat) (t : Time)
    (he : rho.events[i]? = some (.tick v t)) (s : Slot) (hs : 0 < s)
    (ht : t = (S.params (pubOf E) hn).toParams.slotTime s)
    (hd : WrappersDecoded (digests rho.hash)
      (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)))
    (hh : WrappersHeld (digests rho.hash)
      (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t))) :
    let nd := atProposal S rho v (rho.stateBefore i v) t
    let st' := shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1
    WrappersDecoded (digests rho.hash) st' ∧ WrappersHeld (digests rho.hash) st' := by
  exact decoded_held_scheduled_proposal_of_own S rho hn hv v i t he s hs ht hd hh
    ⟨scheduled_proposal_child_decodes S rho hn hf hv v hhon⟩

/-- Every actual honest tick preserves the joint invariant, including its own proposal. -/
theorem decoded_held_tick {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    (v : V) (hhon : v ∉ rho.faultyAt 0) (i : Nat) (t : Time)
    (he : rho.events[i]? = some (.tick v t))
    (hd : WrappersDecoded (digests rho.hash) (stateAt S rho hn v i))
    (hh : WrappersHeld (digests rho.hash) (stateAt S rho hn v i)) :
    let st' := shapeOf S hn (rho.tick (rho.stateBefore i v) v t).1
    WrappersDecoded (digests rho.hash) st' ∧ WrappersHeld (digests rho.hash) st' := by
  exact decoded_held_tick_of_own S rho hn hv v i t he hd hh
    ⟨scheduled_proposal_child_decodes S rho hn hf hv v hhon⟩

/-- Every reachable honest engine state has decoded wrappers corresponding to held blocks.
No decoder, parent-slot, payload-validity or clock premise is assumed. -/
theorem stateAt_decoded_held {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    (v : V) (hh : v ∉ rho.faultyAt 0) (i : Nat) :
    WrappersDecoded (digests rho.hash) (stateAt S rho hn v i) ∧
    WrappersHeld (digests rho.hash) (stateAt S rho hn v i) := by
  exact stateAt_decoded_held_of_own S rho hn hv v
    ⟨scheduled_proposal_child_decodes S rho hn hf hv v hh⟩ i

/-- Receipt acceptances publish a wrapper that decodes, not merely a candidate with the
right syntactic shape. The queue and decoder witnesses use the same processed state. -/
theorem delivery_acceptance_decoded_publication {V : Type} [Fintype V] [DecidableEq V]
    {E : Env V} (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {v : V} (hhon : v ∉ rho.faultyAt 0)
    {i : Nat} {o : (protoOf (compiled (goldilocks S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (r : CutRec (S.params (pubOf E) hn) (S.ro _)) (B : Blk (S.params (pubOf E) hn))
    (hr : r ∈ eventCuts S rho hn i) (hb : r.label = .fg (.block B true))
    (hchild : decodeBlock (S.params (pubOf E) hn) (binding := stock)
      (digests rho.hash (blockObj _ B))
      (blockObj _ B) = some B) :
    ∃ p q, (publisherExecution S rho).actual q ∧ q.event = i ∧
      q.origin = rho.ownKey v ∧
      q.object = forwardObj (S.params (pubOf E) hn) (rho.ownKey v) t p B ∧
      decodeForward (S.params (pubOf E) hn) (digests rho.hash q.object) q.object =
        some (rho.ownKey v, t, p, B) := by
  exact delivery_acceptance_decoded_publication_of_held S rho hn hv he r B hr hb hchild
    ⟨scheduled_proposal_child_decodes S rho hn hf hv v hhon⟩

/-- Scheduled proposal acceptance publishes its exact decoded wrapper in the same tick. -/
theorem tick_proposal_acceptance_decoded_publication {V : Type} [Fintype V] [DecidableEq V]
    {E : Env V} (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    (v : V) (hh : v ∉ rho.faultyAt 0)
    (i : Nat) (t : Time) (he : rho.events[i]? = some (.tick v t)) (s : Slot) (hs : 0 < s)
    (hone : (skeleton (pubOf E)).proposeAt t = [.propose s hs])
    (ht : t = (S.params (pubOf E) hn).toParams.slotTime s)
    (B : Blk (S.params (pubOf E) hn))
    (ha : .fg (.block B true) ∈ (Node.tickStep (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) t)).node
      t (encodeTxs (mempool rho.inbox v t)) .proposal).2)
    (hchild : decodeBlock (S.params (pubOf E) hn) (binding := stock)
      (digests rho.hash (blockObj _ B))
      (blockObj _ B) = some B) :
    ∃ p q, (publisherExecution S rho).actual q ∧ q.event = i ∧
      q.origin = rho.ownKey v ∧
      q.object = forwardObj (S.params (pubOf E) hn) (rho.ownKey v) t p B ∧
      decodeForward (S.params (pubOf E) hn) (digests rho.hash q.object) q.object =
        some (rho.ownKey v, t, p, B) := by
  exact tick_proposal_acceptance_decoded_publication_of_queued S rho hn hv v i t he s hs hone
    ht B hchild ⟨scheduled_proposal_child_decodes S rho hn hf hv v hh⟩
    (tick_proposal_acceptance_queued S rho hn hf hv v hh i t he s hs hone ht B ha)

/-- Every accepting cut of an honest tick has a successfully decoded publication. -/
theorem tick_acceptance_decoded_publication {V : Type} [Fintype V] [DecidableEq V]
    {E : Env V} (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    (v : V) (hh : v ∉ rho.faultyAt 0)
    (i : Nat) (t : Time) (he : rho.events[i]? = some (.tick v t))
    (r : CutRec (S.params (pubOf E) hn) (S.ro _)) (B : Blk (S.params (pubOf E) hn))
    (hr : r ∈ eventCuts S rho hn i) (hb : r.label = .fg (.block B true))
    (hchild : decodeBlock (S.params (pubOf E) hn) (binding := stock)
      (digests rho.hash (blockObj _ B))
      (blockObj _ B) = some B) :
    ∃ p q, (publisherExecution S rho).actual q ∧ q.event = i ∧
      q.origin = rho.ownKey v ∧
      q.object = forwardObj (S.params (pubOf E) hn) (rho.ownKey v) t p B ∧
      decodeForward (S.params (pubOf E) hn) (digests rho.hash q.object) q.object =
        some (rho.ownKey v, t, p, B) := by
  exact tick_acceptance_decoded_publication_of_queued S rho hn hv v i t he r B hr hb hchild
    ⟨scheduled_proposal_child_decodes S rho hn hf hv v hh⟩
    (fun s hs hone ht => tick_proposal_acceptance_queued S rho hn hf hv v hh i t he s hs hone ht B)

/-- Every honest acceptance has an actual, exactly decoded same-event publication.
All decoding premises follow from execution validity and reachable state invariants. -/
theorem forwardAtAcceptance {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid) :
    ForwardAtAcceptance S rho hn (simTrace S rho hn) (cutMap S rho hn)
      (publisherExecution S rho) := by
  rw [forwardAtAcceptance_iff]
  intro x hx k B ha
  have hchild := accepted_child_decodes S rho hn hf hv x hx k B ha
  have hhon (v : V) (hxv : rho.ownKey v = x) : v ∉ rho.faultyAt 0 := by
    have hi : rho.key (rho.ownKey v) = v := rho.key.apply_symm_apply _
    rw [mem_honestKeys_iff] at hx
    rwa [← hxv, hi] at hx
  exact forward_publication_of_events S rho hn ha
    (fun v i t r he hxv hr hb =>
      tick_acceptance_decoded_publication S rho hn hf hv v (hhon v hxv) i t he r B hr hb hchild)
    (fun v i o t r he hxv hr hb =>
      delivery_acceptance_decoded_publication S rho hn hf hv (hhon v hxv) he r B hr hb hchild)

end Consensus.Goldilocks.Obligations
