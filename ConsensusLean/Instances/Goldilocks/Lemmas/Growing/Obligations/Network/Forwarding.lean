module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Interface
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ForwardingInvariant
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationProvenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Simulates
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.NoColl
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Attestations
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Forward.Receipt
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Forward.Accepted
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Forward.Tick
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Forward.AtAcceptance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ForwardingDecode
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ForwardingChain

public section

/-! # Forwarding at acceptance under growing faults

`forwardAtAcceptance_at`: every acceptance of the canonical growing trace by a node honest at its
cut has an actual, exactly decoded same-event forwarding publication (the growing form of
`Obligations/ForwardingDecode.forwardAtAcceptance`). The decoder invariant of a node's engine
state (`stateAt_decoded_held_at`) needs no honesty premise: every engine event's node is honest at
the event (`ExecutionValid.honest_only`), and the node-local run facts of an event are read on the
prefix through its time. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation Obligations

open Shape Blocks
open Consensus.Model

/-- The engine cut before an event is at a time no later than the event. -/
theorem cutTime_le_of_event {V : Type} [Fintype V] [DecidableEq V] {E : Env V} {S : BoundSetup}
    (rho : Model.Run (compiled (goldilocksWith S)) E) (hv : rho.ExecutionValid) {i : Nat}
    {e : Model.Event V (protoOf (compiled (goldilocksWith S)) E).Object}
    (he : rho.events[i]? = some e) : rho.cutTime i ≤ e.time := by
  cases i with
  | zero => exact (hv.in_horizon _ (List.mem_of_getElem? he)).1
  | succ k =>
    have hk : k < rho.events.length :=
      Nat.lt_of_succ_lt (List.getElem?_eq_some_iff.mp he).1
    have hf : rho.events[k]? = some rho.events[k] := List.getElem?_eq_getElem hk
    simp only [Model.Run.cutTime, hf]
    rcases keyLe_of_lt S rho hv hf he (Nat.lt_succ_self k) with h | ⟨h, _⟩
    · exact h.le
    · exact h.le

/-- Every acceptance of the canonical growing trace by a node honest at its cut has a valid
canonical child wire. Receipt validity and own-proposal validity are the run laws on the prefix
through the cut. -/
theorem accepted_child_decodes_at {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : BoundSetup) (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) [Fact (S.vote.participationKind = none)] -- TEMP(C2)
    (y : Fin (Fintype.card V)) (i : Nat)
    (hy : y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i))
    (B : Blk (S.params (pubOf E) hn))
    (hc : (simTraceAt S rho hn).CallAt y i (.fg (.block B true))) :
    decodeBlock (S.params (pubOf E) hn) (binding := S.vote) (digests rho.hash (blockObj _ B))
      (blockObj _ B) = some B := by
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  have run := hrun.upTo (hrun.time_nonneg i)
  have hc' := (Trace.upTo_callAt_of_le _ le_rfl).mpr hc
  rcases Compose.blockCall_cases run.toLocalRun hy hc' with hg |
    ⟨j, x, _, hg, hp, d, p, hdp, hB, _, _, _, _⟩
  · have hw := run.wire y hy i _ _ hg
    have ha := (run.cutLaw y hy i _ hc').2.1
    obtain ⟨root, _, hr, _, _, _, _, _⟩ := Store.onBlock_eq_some ha
    exact canonical_block_decodes S rho hn B (by rw [hr]; simp) hw.1 hw.2.1 hw.2.2
  · obtain ⟨cfg, hr, hst, hs⟩ := Compose.group_step run.toLocalRun hy hg
    have req := SA.interface_requirements (S.params (pubOf E) hn)
      (List (FG.Att (Fintype.card V))) (S.ro _)
    have hd := own_proposal_decodes S rho hn (runProposer S rho hn) y cfg _ _ x
      ⟨req.1, req.2.1, req.2.2.1, req.2.2.2, SA.proposal_payload_valid _ _ _⟩
      run.genesis_root_ok hr hs hp d p (by rw [hst]; exact hdp)
    simpa only [hst, Node.acProposal, Node.tickStep, Node.acCall, hB] using hd

/-- A scheduled honest proposal's actual pre-record state supplies canonical child validity. -/
theorem scheduled_proposal_child_decodes_at {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : BoundSetup) (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) [Fact (S.vote.participationKind = none)] -- TEMP(C2)
    (v : V) (i : Nat) (t : Time)
    (he : rho.events[i]? = some (.tick v t))
    (hp : Node.Proposes (P := (S.params (pubOf E) hn).toParams)
      (runProposer S rho hn) (rho.ownKey v) t) :
    let nd := atProposal S rho v (rho.stateBefore i v) t
    let r := Node.acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now
    ∀ d p, r.2.2 = some (d, p) →
      let B := Node.mkBlock (digestOf S rho) (rho.ownKey v) r.1.fg
        (shapeOf S hn nd).now (encodeTxs nd.st.2) d.head p
      decodeBlock (S.params (pubOf E) hn) (binding := S.vote) (digests rho.hash (blockObj _ B))
        (blockObj _ B) = some B := by
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  have hsim := simTraceAt_simulates S rho hn hv
  have ht0 : 0 ≤ t := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  have hth : t ≤ rho.horizon := (hv.in_horizon _ (List.mem_of_getElem? he)).2
  have hvt : v ∉ rho.faultyAt t := hv.honest_only _ (List.mem_of_getElem? he)
  have run := hrun.upTo ht0
  have hhon : rho.ownKey v ∈ honestKeysAt S rho t := honest_ownKey_at S rho hvt hth
  have hpub := (S.params (pubOf E) hn).toParams.slotTime_public
    ((S.params (pubOf E) hn).toParams.slotOf t)
  rw [← hp.2.1] at hpub
  have hg₀ := (hsim.tick_public v i t he hpub).1
  have hcn : (simTraceAt S rho hn).time (cutMap S rho hn i) = t :=
    (hg₀.2.1 0 (List.length_pos_of_ne_nil hg₀.1)).2.1
  have hg := (RunTrace.upTo_groupAt hrun.time_mono (d := t)).mpr ⟨le_rfl, hg₀⟩
  obtain ⟨cfg, hr, hst, hs⟩ := Compose.group_step run.toLocalRun hhon hg
  rw [RunTrace.upTo_state_of_le hrun.time_mono hcn.le] at hst
  have hstate := hsim.state v i (Nat.le_of_lt (List.getElem?_eq_some_iff.mp he).1)
    (fun h => hvt (rho.faultyAt_mono (cutTime_le_of_event rho hv he) h))
  exact scheduled_proposal_child_decodes_of_step S rho hn hv v i t hp hr
    (hst.trans hstate.symm) hs run.genesis_root_ok

/-- At a scheduled honest tick, the proposal duty preserves the joint invariant without
assuming child decoding: reachable proposal execution supplies it. -/
theorem decoded_held_scheduled_proposal_at {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid)
    (v : V) (i : Nat) (t : Time)
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
    ⟨scheduled_proposal_child_decodes_at S rho hn hv v⟩

/-- Every actual honest tick preserves the joint invariant, including its own proposal. -/
theorem decoded_held_tick_at {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid)
    (v : V) (i : Nat) (t : Time)
    (he : rho.events[i]? = some (.tick v t))
    (hd : WrappersDecoded (digests rho.hash) (stateAt S rho hn v i))
    (hh : WrappersHeld (digests rho.hash) (stateAt S rho hn v i)) :
    let st' := shapeOf S hn (rho.tick (rho.stateBefore i v) v t).1
    WrappersDecoded (digests rho.hash) st' ∧ WrappersHeld (digests rho.hash) st' := by
  exact decoded_held_tick_of_own S rho hn hv v i t he hd hh
    ⟨scheduled_proposal_child_decodes_at S rho hn hv v⟩

/-- Every reachable honest engine state has decoded wrappers corresponding to held blocks.
No decoder, parent-slot, payload-validity or clock premise is assumed. -/
theorem stateAt_decoded_held_at {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid)
    (v : V) (i : Nat) :
    WrappersDecoded (digests rho.hash) (stateAt S rho hn v i) ∧
    WrappersHeld (digests rho.hash) (stateAt S rho hn v i) := by
  exact stateAt_decoded_held_of_own S rho hn hv v
    ⟨scheduled_proposal_child_decodes_at S rho hn hv v⟩ i

/-- Receipt acceptances publish a wrapper that decodes, not merely a candidate with the
right syntactic shape. The queue and decoder witnesses use the same processed state. -/
theorem delivery_acceptance_decoded_publication_at {V : Type} [Fintype V] [DecidableEq V]
    {E : Env V} (S : BoundSetup) (rho : Model.Run (compiled (goldilocksWith S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    [Fact (S.vote.participationKind = none)] -- TEMP(C2)
    {v : V}
    {i : Nat} {o : (protoOf (compiled (goldilocksWith S)) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (r : CutRec (S.params (pubOf E) hn) (S.ro _)) (B : Blk (S.params (pubOf E) hn))
    (hr : r ∈ eventCuts S rho hn i) (hb : r.label = .fg (.block B true))
    (hchild : decodeBlock (S.params (pubOf E) hn) (binding := S.vote)
      (digests rho.hash (blockObj _ B))
      (blockObj _ B) = some B) :
    ∃ p q, (publisherExecution S rho).actual q ∧ q.event = i ∧
      q.origin = rho.ownKey v ∧
      q.object = forwardObj (S.params (pubOf E) hn) (rho.ownKey v) t p B ∧
      decodeForward (S.params (pubOf E) hn) (digests rho.hash q.object) q.object =
        some (rho.ownKey v, t, p, B) := by
  exact delivery_acceptance_decoded_publication_of_held S rho hn hv he r B hr hb hchild
    ⟨scheduled_proposal_child_decodes_at S rho hn hv v⟩

/-- Scheduled proposal acceptance publishes its exact decoded wrapper in the same tick. -/
theorem tick_proposal_acceptance_decoded_publication_at {V : Type} [Fintype V] [DecidableEq V]
    {E : Env V} (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    (v : V)
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
    ht B hchild ⟨scheduled_proposal_child_decodes_at S rho hn hv v⟩
    (tick_proposal_acceptance_queued_at S rho hn hv v i t he s hs hone ht B ha)

/-- Every accepting cut of an honest tick has a successfully decoded publication. -/
theorem tick_acceptance_decoded_publication_at {V : Type} [Fintype V] [DecidableEq V]
    {E : Env V} (S : BoundSetup) (rho : Model.Run (compiled (goldilocksWith S)) E)
    (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    [Fact (S.vote.participationKind = none)] -- TEMP(C2)
    (v : V)
    (i : Nat) (t : Time) (he : rho.events[i]? = some (.tick v t))
    (r : CutRec (S.params (pubOf E) hn) (S.ro _)) (B : Blk (S.params (pubOf E) hn))
    (hr : r ∈ eventCuts S rho hn i) (hb : r.label = .fg (.block B true))
    (hchild : decodeBlock (S.params (pubOf E) hn) (binding := S.vote)
      (digests rho.hash (blockObj _ B))
      (blockObj _ B) = some B) :
    ∃ p q, (publisherExecution S rho).actual q ∧ q.event = i ∧
      q.origin = rho.ownKey v ∧
      q.object = forwardObj (S.params (pubOf E) hn) (rho.ownKey v) t p B ∧
      decodeForward (S.params (pubOf E) hn) (digests rho.hash q.object) q.object =
        some (rho.ownKey v, t, p, B) := by
  exact tick_acceptance_decoded_publication_of_queued S rho hn hv v i t he r B hr hb hchild
    ⟨scheduled_proposal_child_decodes_at S rho hn hv v⟩
    (fun s hs hone ht => tick_proposal_acceptance_queued_at S rho hn hv v i t he s hs hone ht B)

/-- Every acceptance by a node honest at its cut has an actual, exactly decoded same-event
publication. All decoding premises follow from execution validity and reachable state invariants. -/
theorem forwardAtAcceptance_at {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : BoundSetup) (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) [Fact (S.vote.participationKind = none)] : -- TEMP(C2)
    ForwardAtAcceptanceAt S rho hn (simTraceAt S rho hn) (cutMap S rho hn)
      (publisherExecution S rho) := by
  rw [forwardAtAcceptanceAt_iff]
  intro x k B hx ha
  have hchild := accepted_child_decodes_at S rho hn hv x k hx B ha
  rw [simTraceAt_eq] at ha ⊢
  exact forward_publication_of_events S rho hn ha
    (fun v i t r he _ hr hb =>
      tick_acceptance_decoded_publication_at S rho hn hv v i t he r B hr hb hchild)
    (fun v i o t r he _ hr hb =>
      delivery_acceptance_decoded_publication_at S rho hn hv he r B hr hb hchild)

end Consensus.Goldilocks.Obligations.Growing

end
