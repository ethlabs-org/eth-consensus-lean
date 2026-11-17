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
their preservation by each engine transition are in `Obligations/ForwardingDecodeBase`; here
every acceptance publishes its decoded wrapper.
-/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open Shape Blocks
open Consensus.Model

/-- A scheduled honest proposal's actual pre-record state supplies canonical child validity. -/
theorem scheduled_proposal_child_decodes {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks { S with vote := stock })) E)
    (hn : 1 ≤ Fintype.card V)
    (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    (v : V) (hh : v ∉ rho.faultyAt 0) (i : Nat) (t : Time)
    (he : rho.events[i]? = some (.tick v t))
    (hp : Node.Proposes
      (P := (({ S with vote := AsChainShape.stock } : Setup).params (pubOf E) hn).toParams)
      (runProposer { S with vote := stock } rho hn) (rho.ownKey v) t) :
    let nd := atProposal { S with vote := stock } rho v (rho.stateBefore i v) t
    let r := Node.acProposal (shapeOf { S with vote := stock } hn nd).node
      (shapeOf { S with vote := stock } hn nd).now
    ∀ d p, r.2.2 = some (d, p) →
      let B := Node.mkBlock (digestOf { S with vote := stock } rho) (rho.ownKey v) r.1.fg
        (shapeOf { S with vote := stock } hn nd).now (encodeTxs nd.st.2) d.head p
      decodeBlock (({ S with vote := AsChainShape.stock } : Setup).params (pubOf E) hn)
        (binding := stock) (digests rho.hash (blockObj _ B))
        (blockObj _ B) = some B := by
  have run := simTrace_goldilocksRun S rho hn hf hv
  have hhon : rho.ownKey v ∈ honestKeys { S with vote := stock } rho := by
    rw [mem_honestKeys_iff { S with vote := stock } rho]
    have hk : rho.key (rho.ownKey v) = v := rho.key.apply_symm_apply v
    rwa [hk]
  have hpub := (({ S with vote := AsChainShape.stock } : Setup).params
    (pubOf E) hn).toParams.slotTime_public
    ((({ S with vote := AsChainShape.stock } : Setup).params (pubOf E) hn).toParams.slotOf t)
  rw [← hp.2.1] at hpub
  have hg := (simTrace_tick_public_group { S with vote := stock } rho hn hf hv v hh i t he hpub).1
  obtain ⟨cfg, hr, hst, hs⟩ := Compose.group_step run.toLocalRun hhon hg
  have hstate := simTrace_state { S with vote := stock } rho hn hf hv v hh i
    (Nat.le_of_lt (List.getElem?_eq_some_iff.mp he).1)
  exact scheduled_proposal_child_decodes_of_step { S with vote := stock } rho hn hv v i t hp hr
    (SA.voteStart_initial _) (hst.trans hstate.symm) hs run.genesis_root_ok

/-- Receipt acceptances publish a wrapper that decodes, not merely a candidate with the
right syntactic shape. The queue and decoder witnesses use the same processed state. -/
theorem delivery_acceptance_decoded_publication {V : Type} [Fintype V] [DecidableEq V]
    {E : Env V} (S : Setup) (rho : Model.Run (compiled (goldilocks { S with vote := stock })) E)
    (hn : 1 ≤ Fintype.card V) (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {v : V} (hhon : v ∉ rho.faultyAt 0)
    {i : Nat} {o : (protoOf (compiled (goldilocks { S with vote := stock })) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (r : CutRec (({ S with vote := AsChainShape.stock } : Setup).params (pubOf E) hn) (S.ro _))
    (B : Blk (({ S with vote := AsChainShape.stock } : Setup).params (pubOf E) hn))
    (hr : r ∈ eventCuts { S with vote := stock } rho hn i) (hb : r.label = .fg (.block B true))
    (hchild : decodeBlock (({ S with vote := AsChainShape.stock } : Setup).params (pubOf E) hn)
      (binding := stock)
      (digests rho.hash (blockObj _ B))
      (blockObj _ B) = some B) :
    ∃ p q, (publisherExecution { S with vote := stock } rho).actual q ∧ q.event = i ∧
      q.origin = rho.ownKey v ∧
      q.object = forwardObj (({ S with vote := AsChainShape.stock } : Setup).params (pubOf E) hn)
        (rho.ownKey v) t p B ∧
      decodeForward (({ S with vote := AsChainShape.stock } : Setup).params (pubOf E) hn)
        (digests rho.hash q.object) q.object =
        some (rho.ownKey v, t, p, B) := by
  exact delivery_acceptance_decoded_publication_of_held
    { S with vote := stock } rho hn hv he r B hr hb hchild
    ⟨scheduled_proposal_child_decodes S rho hn hf hv v hhon⟩

/-- Every accepting cut of an honest tick has a successfully decoded publication. -/
theorem tick_acceptance_decoded_publication {V : Type} [Fintype V] [DecidableEq V]
    {E : Env V} (S : Setup) (rho : Model.Run (compiled (goldilocks { S with vote := stock })) E)
    (hn : 1 ≤ Fintype.card V) (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    (v : V) (hh : v ∉ rho.faultyAt 0)
    (i : Nat) (t : Time) (he : rho.events[i]? = some (.tick v t))
    (r : CutRec (({ S with vote := AsChainShape.stock } : Setup).params (pubOf E) hn) (S.ro _))
    (B : Blk (({ S with vote := AsChainShape.stock } : Setup).params (pubOf E) hn))
    (hr : r ∈ eventCuts { S with vote := stock } rho hn i) (hb : r.label = .fg (.block B true))
    (hchild : decodeBlock (({ S with vote := AsChainShape.stock } : Setup).params (pubOf E) hn)
      (binding := stock)
      (digests rho.hash (blockObj _ B))
      (blockObj _ B) = some B) :
    ∃ p q, (publisherExecution { S with vote := stock } rho).actual q ∧ q.event = i ∧
      q.origin = rho.ownKey v ∧
      q.object = forwardObj (({ S with vote := AsChainShape.stock } : Setup).params (pubOf E) hn)
        (rho.ownKey v) t p B ∧
      decodeForward (({ S with vote := AsChainShape.stock } : Setup).params (pubOf E) hn)
        (digests rho.hash q.object) q.object =
        some (rho.ownKey v, t, p, B) := by
  exact tick_acceptance_decoded_publication_of_queued
    { S with vote := stock } rho hn hv v i t he r B hr hb hchild
    ⟨scheduled_proposal_child_decodes S rho hn hf hv v hh⟩
    (fun s hs hone ht => tick_proposal_acceptance_queued
        { S with vote := stock } rho hn hf hv v hh i t he s hs
        hone ht B)

/-- Every honest acceptance has an actual, exactly decoded same-event publication.
All decoding premises follow from execution validity and reachable state invariants. -/
theorem forwardAtAcceptance {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks { S with vote := stock })) E)
    (hn : 1 ≤ Fintype.card V)
    (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid) :
    ForwardAtAcceptance { S with vote := stock } rho hn (simTrace { S with vote := stock } rho hn)
      (cutMap { S with vote := stock } rho hn)
      (publisherExecution { S with vote := stock } rho) := by
  rw [forwardAtAcceptance_iff { S with vote := stock } rho hn]
  intro x hx k B ha
  have hchild := accepted_child_decodes S rho hn hf hv x hx k B ha
  have hhon (v : V) (hxv : rho.ownKey v = x) : v ∉ rho.faultyAt 0 := by
    have hi : rho.key (rho.ownKey v) = v := rho.key.apply_symm_apply _
    rw [mem_honestKeys_iff { S with vote := stock } rho] at hx
    rwa [← hxv, hi] at hx
  exact forward_publication_of_events { S with vote := stock } rho hn ha
    (fun v i t r he hxv hr hb =>
      tick_acceptance_decoded_publication S rho hn hf hv v (hhon v hxv) i t he r B hr hb hchild)
    (fun v i o t r he hxv hr hb =>
      delivery_acceptance_decoded_publication S rho hn hf hv (hhon v hxv) he r B hr hb hchild)

end Consensus.Goldilocks.Obligations
