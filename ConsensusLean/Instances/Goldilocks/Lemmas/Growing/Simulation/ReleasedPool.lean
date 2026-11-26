module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.AdmitsAtTick
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.HeldSign
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.HeldFlush
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.HeldRefusal
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeOpLawsLawful
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeOpLawsInstance
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Release
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.EngineSteps
import ConsensusLean.Lemmas.Model.Constant
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EventGroups
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.GoldilocksStateAgreement
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OwnReleaseProcessing
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Trace.UpTo

public section

/-! # Goldilocks Simulation: a released own attestation is in the releaser's pool

An own attestation enters the node's pool when it is released, not when it is signed. An engine
event releases an attestation only at a tick: a held attestation that the tick's first trailing
poll flushes, or the attestation that poll's FG update signs at a time the release schedule
allows. That poll processes both by the own `on_attestation`
(`pollBatch_node_eq`), and the rest of the tick keeps the pool (`tick_node_rel`), so the
attestation is in the node's pool after the event (`released_att_mem_pool`).

Every step is proved. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

omit [Fintype V] [DecidableEq V] in
/-- Processing attestations keeps the pool and adds each processed attestation. -/
private theorem mem_foldl_onAttestation {sp : AC.ACParams}
    {ro : AC.ReplayOrder sp (List (FG.Att sp.n))} {a : FG.Att sp.n} :
    ∀ (l : List (FG.Att sp.n)) (n : NodeState (goldilocksNode sp ro)),
      a ∈ l ∨ a ∈ n.fg.atts →
        a ∈ (l.foldl (fun n a => (Node.onAttestation n a).1) n).fg.atts
  | [], _, h => h.resolve_left List.not_mem_nil
  | b :: l, n, h => by
    rw [List.foldl_cons]
    refine mem_foldl_onAttestation l _ ?_
    by_cases hb : b ∈ n.fg.atts
    · have hn : (Node.onAttestation n b).1 = n := by
        simp [Node.onAttestation, Store.onAttestation, hb]
      rw [hn]
      rcases h with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr hb
        · exact Or.inl h
      · exact Or.inr h
    · have hn : (Node.onAttestation n b).1 =
          { n with fg := { n.fg with atts := n.fg.atts ++ [b] } } := by
        simp [Node.onAttestation, Store.onAttestation, hb]
      rw [hn]
      rcases h with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr (by simp)
        · exact Or.inl h
      · exact Or.inr (by simp [h])

/-- The engine node before the first trailing poll of a tick of `v` at `t` (engine event `i`):
after the clock, the two leading polls, the proposal poll and the slot proposal. -/
private noncomputable def trailNode (v : V) (i : Nat) (t : Time) :
    Model.Node (Model.protoOf (compiled (goldilocks S)) E) :=
  (rho.runDuties v (rho.runDuties v
    ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
      (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
    ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] :
      List (Model.protoOf (compiled (goldilocks S)) E).Duty)).1
    ((skeleton (pubOf E) S.vote).proposeAt t)).1

/-- What the first trailing poll of a tick processes by the own `on_attestation`: the held
attestations it flushes, then the attestation its FG update signs when the release schedule
allows. -/
private noncomputable def trailingAdmits (v : V) (i : Nat) (t : Time) :
    List (FG.Att (Fintype.card V)) :=
  pollFlush (shapeOf S hn (trailNode S rho v i t)) (S.release (pubOf E)) ++
    if ((shapeOf S hn (trailNode S rho v i t)).fgDue &&
        S.release (pubOf E) (shapeOf S hn (trailNode S rho v i t)).self
          (shapeOf S hn (trailNode S rho v i t)).now) = true then
      (fgSigned (shapeOf S hn (trailNode S rho v i t))).toList
    else []

/-- What the first trailing poll of a tick processes is in the node's pool after the tick. -/
private theorem trailingAdmits_mem_pool (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) {a : FG.Att (Fintype.card V)}
    (ha : a ∈ trailingAdmits S rho hn v i t) :
    a ∈ (stateAt S rho hn v (i + 1)).node.fg.atts := by
  have h := NodeAsChainShape.CanonicalTrace.Encoding.OpLaws.tick_node_rel
    (traceEncoding_opLaws S hn) (goldilocks_ready S hn) rho hv he (trailingAdmits S rho hn v i t)
    (by
      apply traceEncoding_induction S hn (fun e due _ =>
        let pre := (rho.runDuties v (NodeAsChainShape.CanonicalTrace.afterClock rho
          (rho.stateBefore i v) v t) ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat].map
            (NodeAsChainShape.CanonicalTrace.engineDuty e))).1
        let post := NodeAsChainShape.CanonicalTrace.envelope e (rho.runDuties v pre
          ((e.skel.proposeAt t).map (NodeAsChainShape.CanonicalTrace.engineDuty e))).1
        e.adapter.node ((e.ops hn).pollBatch post t.toNat).1 =
          (trailingAdmits S rho hn v i t).foldl (fun n a => (Node.onAttestation n a).1)
            (if due post then (Node.tickStep (NodeAsChainShape.CanonicalTrace.runProposer rho hn)
                (NodeAsChainShape.CanonicalTrace.digestOf e rho) (e.adapter.self post)
                (e.adapter.node post) (e.adapter.now post)
                (encodeTxs (Model.mempool rho.inbox v t)) .fgUpdate).1
              else e.adapter.node post))
      intro e _
      have hsk : e.skel.proposeAt t = (skeleton (pubOf E) S.vote).proposeAt t := rfl
      simp only [NodeAsChainShape.CanonicalTrace.afterClock_eq,
        NodeAsChainShape.CanonicalTrace.envelope_eq, List.map_cons, List.map_nil,
        NodeAsChainShape.CanonicalTrace.engineDuty_eq, hsk, trailNode, trailingAdmits]
      rcases Skeleton.proposeAt_cases (skeleton (pubOf E) S.vote) t with ⟨hnil, -⟩ |
        ⟨s, hs, hone, -⟩
      · simp only [hnil, List.map_nil, rho.runDuties_nil]
        exact pollBatch_node_eq (sp := S.params (pubOf E) hn) (release := S.release (pubOf E)) _ _
          (encodeTxs (Model.mempool rho.inbox v t)) _ t.toNat
      · simp only [hone, List.map_cons, List.map_nil,
          NodeAsChainShape.CanonicalTrace.engineDuty_eq]
        exact pollBatch_node_eq (sp := S.params (pubOf E) hn) (release := S.release (pubOf E)) _ _
          (encodeTxs (Model.mempool rho.inbox v t)) _ t.toNat)
  have hstate : (stateAt S rho hn v (i + 1)).node =
      (traceEncoding S hn).adapter.node
        (NodeAsChainShape.CanonicalTrace.stateAt (traceEncoding S hn) rho v (i + 1)) := by
    rw [stateAt_eq]
    exact traceEncoding_induction S hn (fun e _ _ =>
      ((rho.stateBefore (i + 1) v).st.1 hn).node =
        e.adapter.node (NodeAsChainShape.CanonicalTrace.stateAt e rho v (i + 1))) fun _ => by
      rw (config := { transparency := .default })
        [NodeAsChainShape.CanonicalTrace.stateAt_eq, cast_eq]
      rfl
  rw [hstate, h]
  exact mem_foldl_onAttestation _ _ (Or.inl ha)

/-- A held attestation of `v` is flushed by the first trailing poll of a tick of `v` at a time the
release schedule allows. -/
private theorem held_mem_trailing (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    {a : FG.Att (Fintype.card V)}
    (ha : a ∈ (stateAt S rho hn v i).held)
    (hr : S.release (pubOf E) (rho.ownKey v) t = true) :
    a ∈ trailingAdmits S rho hn v i t := by
  have hsel := poll_selected S rho hv v
  set nd := rho.stateBefore i v
  have hk := self_eq_ownKey S rho hn v i
  rw [stateAt_eq] at hk ha
  set Pr : List (Model.protoOf (compiled (goldilocks S)) E).Duty :=
    (skeleton (pubOf E) S.vote).proposeAt t
  have hT : trailNode S rho v i t = (rho.runDuties v (atProposal S rho v nd t) Pr).1 := by
    rw [atProposal_eq]; rfl
  have hA : (shapeOf S hn (atProposal S rho v nd t)).self = rho.ownKey v ∧
      (shapeOf S hn (atProposal S rho v nd t)).now = t ∧
      (shapeOf S hn (atProposal S rho v nd t)).ticked = true ∧
      a ∈ (shapeOf S hn (atProposal S rho v nd t)).held := by
    refine ⟨(atProposal_self S rho hn v nd t hsel).trans hk, atProposal_now S rho hn v nd t hsel,
      by rw [atProposal_shape S rho hn v nd t hsel], ?_⟩
    rw [atProposal_shape S rho hn v nd t hsel]
    simp only [nodeTick_held, pollBatch_held, pollBatch_ticked, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte]
    exact List.mem_append_left _ (List.mem_append_left _ ha)
  have hP : ∀ (Q : State (S.params (pubOf E) hn) (S.ro _) S.vote → Prop),
      (∀ st o hs, Q st → Q (recordOwn st o hs)) → (∀ st s, Q st → Q (propose st s).1) →
      Q (shapeOf S hn (atProposal S rho v nd t)) →
      Q (shapeOf S hn (rho.runDuties v (atProposal S rho v nd t) Pr).1) := by
    intro Q h1 h2 h
    rcases Skeleton.proposeAt_cases (skeleton (pubOf E) S.vote) t with ⟨hnil, -⟩ | ⟨s, hs, hone, -⟩
    · rw [show Pr = [] from hnil]
      exact h
    · rw [show Pr = [.propose s hs] from hone]
      refine (congrArg (fun n => Q (shapeOf S hn n))
        (runDuties_fst_cons S rho v _ (.propose s hs) [])).mpr ?_
      exact dutyStep_propose_pres S rho hn Q h1 h2 v _ s hs h
  obtain ⟨hs₁, hn₁, ht₁, ha₁⟩ := hA
  unfold trailingAdmits
  rw [hT]
  refine List.mem_append_left _ ?_
  rw [pollFlush_eq, hP (fun st => st.self = rho.ownKey v)
      (fun st o hs h => (recordOwn_self st o hs).trans h)
      (fun st s h => (propose_self st s).trans h) hs₁,
    hP (fun st => st.now = t) (fun st o hs h => (recordOwn_now st o hs).trans h)
      (fun st s h => (propose_now st s).trans h) hn₁,
    hP (fun st => st.ticked = true) (fun st o hs h => (recordOwn_ticked st o hs).trans h)
      (fun st s h => (propose_ticked st s).trans h) ht₁, hr]
  exact hP (fun st => a ∈ st.held) (fun st o hs h => (recordOwn_held st o hs).symm ▸ h)
    (fun st s h => (propose_held st s).symm ▸ h) ha₁

/-- A signing of a public tick at a time the release schedule allows is processed by the tick's
first trailing poll. -/
private theorem sign_mem_trailing (hv : rho.ExecutionValid) {i : Nat} {v : V} {s : Time}
    (he : rho.events[i]? = some (.tick v s))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic s)
    {C} {a : FG.Att (Fintype.card V)}
    (hc : Cut.fg (.attest C (some a)) ∈ (exec (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (stateAt S rho hn v i).node s
      (.tick (encodeTxs (Model.mempool rho.inbox v s)) (S.sign (pubOf E) (rho.ownKey v) s))).2)
    (hr : S.release (pubOf E) (rho.ownKey v) s = true) :
    a ∈ trailingAdmits S rho hn v i s := by
  have hpre := preNode_releasable_at S rho hn hv he
  have hm := List.mem_of_getElem? he
  have hsel := poll_selected S rho hv v
  obtain ⟨hamo, -⟩ := outbox_inv S rho hn hv v i
  obtain ⟨-, hlen⟩ := (atMostOneVote_iff _).1 hamo
  have hf := fgDue_eq_false S rho hn v i
  have hself0 := self_eq_ownKey S rho hn v i
  set nd := rho.stateBefore i v with hnd
  have hσ : stateAt S rho hn v i = shapeOf S hn nd := stateAt_eq S rho hn v i
  rw [hσ] at hlen hf hself0 hc
  obtain ⟨-, -, -, -, hS3, hout2, hnode2, hself2, hnow2, -, -⟩ :=
    leading_polls S rho hn v nd s hsel hf hlen
      (by simpa only [hσ] using forwards_empty S rho hn hv v i)
      (by simpa only [hσ] using voteForwards_empty S rho hn hv v i)
  set X := encodeTxs (Model.mempool rho.inbox v s)
  set dg := digestOf S rho
  set n1 := (Node.acCall (rho.ownKey v) (shapeOf S hn nd).node s .tick).1
  set sg := S.sign (pubOf E) (rho.ownKey v) s with hsg
  set N3 := (rho.dutyStep v (rho.dutyStep v (rho.dutyStep v
      ⟨(Model.protoOf (compiled (goldilocks S)) E).clock nd.st s (Model.mempool rho.inbox v s),
        nd.seen⟩ (.poll s.toNat)).1 (.poll s.toNat)).1 (.pollPropose s.toNat)).1 with hN3
  have hp2 : (S.params (pubOf E) hn).toParams.IsPublic
      (shapeOf S hn (rho.dutyStep v (rho.dutyStep v
        ⟨(Model.protoOf (compiled (goldilocks S)) E).clock nd.st s
            (Model.mempool rho.inbox v s),
          nd.seen⟩ (.poll s.toNat)).1 (.poll s.toNat)).1).now :=
    by rw [hnow2]; exact hp
  obtain ⟨hn3, -, hf3, hs3, hw3⟩ := nodeTick_public S hn _ hp2 hout2
  rw [hnode2, hself2, hnow2, hself0] at hn3
  rw [hself2, hself0] at hs3
  rw [hnow2] at hw3
  rw [hself2, hself0, hnow2] at hf3
  have hselfN3 : (shapeOf S hn N3).self = rho.ownKey v := by rw [hS3]; exact hs3
  have hnowN3 : (shapeOf S hn N3).now = s := by rw [hS3]; exact hw3
  have hnodeN3 : (shapeOf S hn N3).node = n1 := by rw [hS3]; exact hn3
  have hfgN3 : (shapeOf S hn N3).fgDue = sg := by rw [hS3]; exact hf3
  have hcuts : (exec (runProposer S rho hn) dg (rho.ownKey v)
      (shapeOf S hn nd).node s (.tick X sg)).2 =
      [(Node.acCall (rho.ownKey v) (shapeOf S hn nd).node s .tick).2] ++
        (Node.tickStep (runProposer S rho hn) dg (rho.ownKey v) n1 s X .proposal).2 ++
        (if sg then (Node.tickStep (runProposer S rho hn) dg (rho.ownKey v)
          (Node.tickStep (runProposer S rho hn) dg (rho.ownKey v) n1 s X .proposal).1 s X
          .fgUpdate).2 else []) :=
    onTick_cuts (sp := S.params (pubOf E) hn) (ro := S.ro _)
      (runProposer S rho hn) dg (rho.ownKey v) _ s X sg
  have hc' : Cut.fg (.attest C (some a)) ∈ (exec (runProposer S rho hn) dg (rho.ownKey v)
      (shapeOf S hn nd).node s (.tick X sg)).2 := hc
  rw [hcuts] at hc'
  have hprop : Cut.fg (.attest C (some a)) ∉
      (Node.tickStep (runProposer S rho hn) dg (rho.ownKey v) n1 s X .proposal).2 := by
    intro h
    have hpb := tickStep_proposal_attBodies (sp := S.params (pubOf E) hn) (ro := S.ro _)
      (runProposer S rho hn) dg (rho.ownKey v) n1 s X
    have hat : Body.att (encodeAtt a) ∈ attBodies
        (Node.tickStep (runProposer S rho hn) dg (rho.ownKey v) n1 s X .proposal).2 := by
      rw [attBodies_eq, List.mem_flatMap]; exact ⟨_, h, by simp⟩
    rw [hpb] at hat
    exact absurd hat List.not_mem_nil
  have hsg : sg = true ∧ Cut.fg (.attest C (some a)) ∈ (Node.tickStep (runProposer S rho hn) dg
      (rho.ownKey v) (Node.tickStep (runProposer S rho hn) dg (rho.ownKey v) n1 s X .proposal).1
        s X .fgUpdate).2 := by
    rcases List.mem_append.mp hc' with hc' | hc'
    · rcases List.mem_append.mp hc' with hc' | hc'
      · simp only [List.mem_singleton] at hc'
        cases hc'
      · exact absurd hc' hprop
    · cases hsgv : sg
      · rw [hsgv] at hc'; exact absurd hc' List.not_mem_nil
      · rw [hsgv] at hc'; exact ⟨rfl, hc'⟩
  obtain ⟨hsgt, hcf⟩ := hsg
  have finish : ∀ N4 : Model.Node (Model.protoOf (compiled (goldilocks S)) E),
      (shapeOf S hn N4).fgDue = true → (shapeOf S hn N4).self = rho.ownKey v →
      (shapeOf S hn N4).now = s →
      (shapeOf S hn N4).node =
        (Node.tickStep (runProposer S rho hn) dg (rho.ownKey v) n1 s X .proposal).1 →
      trailNode S rho v i s = N4 → a ∈ trailingAdmits S rho hn v i s := by
    intro N4 hf4 hs4 hw4 hn4 hT
    unfold trailingAdmits
    rw [hT]
    refine List.mem_append_right _ ?_
    rw [hf4, hs4, hw4, hr, Bool.and_self, ite_eq_left rfl,
      fgSigned_of_attest (runProposer S rho hn) dg X (shapeOf S hn N4) (C := C)
        (by rw [hs4, hw4, hn4]; exact hcf)]
    exact List.mem_singleton_self _
  rcases Skeleton.proposeAt_cases (skeleton (pubOf E) S.vote) s with
    ⟨hnil, hno⟩ | ⟨sl, hs, hone, hts⟩
  · have hnp : ¬ Proposes (P := (S.params (pubOf E) hn).toParams)
        (runProposer S rho hn) (rho.ownKey v) s :=
      not_proposes S hn (runProposer S rho hn) _ s
        (fun s hs h => hno s hs (h.trans (slotTime_eq S hn s)))
    have hc2 := tickStep_proposal_not' (runProposer S rho hn) dg (rho.ownKey v) n1 s X hnp
    refine finish N3 (hfgN3.trans hsgt) hselfN3 hnowN3 (by rw [hnodeN3, hc2]) ?_
    unfold trailNode
    rw [hnil]
    rfl
  · have hts' : s = (S.params (pubOf E) hn).toParams.slotTime sl :=
      hts.trans (slotTime_eq S hn sl).symm
    have hmem : N3.st.2 = Model.mempool rho.inbox v s :=
      runDuties_mempool S rho v [.poll s.toNat, .poll s.toNat, .pollPropose s.toNat]
        ⟨(Model.protoOf (compiled (goldilocks S)) E).clock nd.st s
            (Model.mempool rho.inbox v s),
          nd.seen⟩
    have hsp := selValid_proposer S rho hn hv.selValid sl
    have hslot : (S.params (pubOf E) hn).toParams.slotOf (shapeOf S hn N3).now = sl := by
      rw [hnowN3, hts']; exact slotOf_slotTime _ sl
    have hst : (shapeOf S hn N3).now = (S.params (pubOf E) hn).toParams.slotTime sl :=
      hnowN3.trans hts'
    have hpN : preNode S rho v nd s = N3 := by
      rw [preNode_eq_atProposal, atProposal_eq]; rfl
    have hrel := hpre sl hs hone
    rw [hpN] at hrel
    have hn4 := dutyStep_propose_node S rho hn v N3 sl hs hsp hselfN3 hslot hst hrel
    rw [hnodeN3, hnowN3, hmem] at hn4
    have hf4 := dutyStep_propose_pres S rho hn (fun st => st.fgDue = sg)
      (fun st o hs h => (recordOwn_fgDue st o hs).trans h)
      (fun st s h => (propose_fgDue st s).trans h) v N3 sl hs hfgN3
    have hs4 := dutyStep_propose_pres S rho hn (fun st => st.self = rho.ownKey v)
      (fun st o hs h => (recordOwn_self st o hs).trans h)
      (fun st s h => (propose_self st s).trans h) v N3 sl hs hselfN3
    have hw4 := dutyStep_propose_pres S rho hn (fun st => st.now = s)
      (fun st o hs h => (recordOwn_now st o hs).trans h)
      (fun st s h => (propose_now st s).trans h) v N3 sl hs hnowN3
    refine finish _ (hf4.trans hsgt) hs4 hw4 hn4 ?_
    unfold trailNode
    rw [hone]
    rfl

omit [DecidableEq V] in
/-- No attestation body is an emitted vote. -/
private theorem att_not_mem_emitted {io : VoteAuth (S.params (pubOf E) hn).n S.vote}
    {cs : List (Cut (goldilocksNode (S.params (pubOf E) hn) (S.ro _)))} {w : WireAtt} :
    Body.att w ∉ emitted io cs := by
  intro h
  obtain ⟨c, -, hc⟩ := List.mem_flatMap.mp h
  match c with
  | .ac ℓ =>
    obtain ⟨e, -, he⟩ := List.mem_filterMap.mp hc
    obtain ⟨_, -, he⟩ := Option.map_eq_some_iff.mp he
    cases he
  | .fg _ => exact absurd hc List.not_mem_nil

/-- An attestation a tick releases is a held attestation the schedule allows to release, or a
signing of the public tick at a time the schedule allows. -/
private theorem att_release_cases (hv : rho.ExecutionValid)
    {j : Nat} {v : V} {t : Time} (he : rho.events[j]? = some (.tick v t))
    {b : FG.Att (Fintype.card V)}
    (hb : (attObj b : (Model.protoOf (compiled (goldilocks S)) E).Object) ∈ rho.releasesAt j) :
    S.release (pubOf E) (rho.ownKey v) t = true ∧ (b ∈ (stateAt S rho hn v j).held ∨
      (S.params (pubOf E) hn).toParams.IsPublic t ∧ ∃ C,
        Cut.fg (.attest C (some b)) ∈ (exec (runProposer S rho hn) (digestOf S rho)
          (rho.ownKey v) (stateAt S rho hn v j).node t
          (.tick (encodeTxs (Model.mempool rho.inbox v t))
            (S.sign (pubOf E) (rho.ownKey v) t))).2) := by
  have hv' : v ∉ rho.faultyAt 0 := event_honest_zero S rho hv he
  obtain ⟨hamo, -⟩ := outbox_inv S rho hn hv v j
  obtain ⟨hvote, -⟩ := (atMostOneVote_iff _).1 hamo
  have hnotpend : (attObj b : (Model.protoOf (compiled (goldilocks S)) E).Object) ∉
      relHead S rho v (stateAt S rho hn v j).outbox.head? := by
    intro h
    obtain ⟨q, hq, hqo⟩ := mem_relHead S rho h
    obtain ⟨w, z, rfl⟩ := hvote q (List.mem_of_mem_head? hq)
    exact absurd (attObj_eq_pollObj S rho hqo).1 (by simp)
  have hflush : (attObj b : (Model.protoOf (compiled (goldilocks S)) E).Object) ∈
      relFlush S rho hn v (stateAt S rho hn v j) t →
      S.release (pubOf E) (rho.ownKey v) t = true ∧ b ∈ (stateAt S rho hn v j).held := by
    intro h
    rw [relFlush_eq, self_eq_ownKey S rho hn v j] at h
    obtain ⟨a, ha, heq⟩ := List.mem_map.mp h
    injection heq with _ h₂
    injection h₂ with h₃
    injection h₃ with h₄
    obtain rfl := encodeAtt_inj h₄
    split_ifs at ha with hr
    · exact ⟨hr, ha⟩
    · exact absurd ha List.not_mem_nil
  by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
  · obtain ⟨N4, N5, Q, R4, F, G, heq, -, -, hF, hG, -, hQ, hR4, -⟩ :=
      tick_public_analysis S rho hn hv hv' he hp (preNode_releasable_at S rho hn hv he)
    rw [heq] at hb
    have hQmem : ∀ ob, ob ∈ [Q.head?, Q.tail.head?] →
        (attObj b : (Model.protoOf (compiled
            (goldilocks S)) E).Object) ∈ relHead S rho v ob →
        S.release (pubOf E) (rho.ownKey v) t = true ∧ ∃ C, Cut.fg (.attest C (some b)) ∈
          (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
            (stateAt S rho hn v j).node t
            (.tick (encodeTxs (Model.mempool rho.inbox v t))
              (S.sign (pubOf E) (rho.ownKey v) t))).2 := by
      intro ob hob h
      obtain ⟨q, rfl, hqo⟩ := mem_relHead S rho h
      obtain ⟨hq, -⟩ := attObj_eq_pollObj S rho hqo
      have hqQ : q ∈ Q := by
        rcases List.mem_pair.mp hob with h' | h'
        · exact List.mem_of_mem_head? h'.symm
        · exact List.mem_of_mem_tail (List.mem_of_mem_head? h'.symm)
      rw [hQ, hq] at hqQ
      split_ifs at hqQ with hr
      · obtain ⟨C, a, hc, hw⟩ := att_mem_bodies S hn hqQ
        obtain rfl := encodeAtt_inj hw
        exact ⟨hr, C, hc⟩
      · rw [List.append_nil] at hqQ
        exact absurd hqQ (att_not_mem_emitted S hn)
    rcases List.mem_append.mp hb with hb | h
    swap
    · exact absurd (hG _ h) (by simp [attObj, Model.Obj.auth])
    rcases List.mem_append.mp hb with hb | h
    swap
    · obtain ⟨hr, C, hc⟩ := hQmem _ (by simp) h
      exact ⟨hr, Or.inr ⟨hp, C, hc⟩⟩
    rcases List.mem_append.mp hb with hb | h
    swap
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · obtain ⟨hr, C, hc⟩ := hQmem _ (by simp) h
          exact ⟨hr, Or.inr ⟨hp, C, hc⟩⟩
        · rcases hF _ h with ⟨τ, cs, heq⟩ | ⟨τ, m, w, heq⟩
          all_goals have hm := congrArg Model.Obj.msg heq; cases hm
      · obtain ⟨hr, h⟩ := hflush h
        exact ⟨hr, Or.inl h⟩
    rcases List.mem_append.mp hb with hb | h
    swap
    · rw [hR4] at h; exact absurd h (attObj_not_mem_blockObjs S hn b _)
    exact absurd hb hnotpend
  · rcases tick_other_releases S rho hn hv hv' he hp _ hb with h | h | h
    · exact absurd h hnotpend
    · obtain ⟨hr, h⟩ := hflush h
      exact ⟨hr, Or.inl h⟩
    · exact absurd h (by simp [attObj, Model.Obj.auth])

/-- **A released own attestation is in the releaser's pool.** An attestation an engine event
releases is in the pool of the event's node after the event: the event is a tick, and the tick's
first trailing poll processes it, as a held attestation it flushes or as the attestation its FG
update signs at a time the schedule allows release. -/
private theorem released_att_mem_pool (hv : rho.ExecutionValid) {i : Nat}
    {ev : Model.Event V (Model.protoOf (compiled (goldilocks S)) E).Object}
    (he : rho.events[i]? = some ev) {a : FG.Att (Fintype.card V)}
    (ho : (attObj a : (Model.protoOf (compiled (goldilocks S)) E).Object) ∈ rho.releasesAt i) :
    a ∈ (stateAt S rho hn ev.node (i + 1)).node.fg.atts := by
  cases ev with
  | tick v t =>
    refine trailingAdmits_mem_pool S rho hn hv he ?_
    obtain ⟨hr, h | ⟨hp, C, hc⟩⟩ := att_release_cases S rho hn hv he ho
    · exact held_mem_trailing S rho hn hv h hr
    · exact sign_mem_trailing S rho hn hv he hp hc hr
  | deliver v o t => exact absurd ho (deliver_not_att S rho hn hv he a)
  | restart v t =>
    simp only [Model.Run.releasesAt, he] at ho
    exact absurd ho List.not_mem_nil

omit [Fintype V] [DecidableEq V] in
/-- An attestation in the pool after processing a list was in the pool before or in the list. -/
private theorem mem_of_mem_foldl_onAttestation {sp : AC.ACParams}
    {ro : AC.ReplayOrder sp (List (FG.Att sp.n))} {a : FG.Att sp.n} :
    ∀ (l : List (FG.Att sp.n)) (n : NodeState (goldilocksNode sp ro)),
      a ∈ (l.foldl (fun n a => (Node.onAttestation n a).1) n).fg.atts → a ∈ n.fg.atts ∨ a ∈ l
  | [], _, h => Or.inl h
  | b :: l, n, h => by
    rw [List.foldl_cons] at h
    rcases mem_of_mem_foldl_onAttestation l _ h with h | h
    · by_cases hb : b ∈ n.fg.atts
      · have hn : (Node.onAttestation n b).1 = n := by
          simp [Node.onAttestation, Store.onAttestation, hb]
        rw [hn] at h
        exact Or.inl h
      · have hn : (Node.onAttestation n b).1 =
            { n with fg := { n.fg with atts := n.fg.atts ++ [b] } } := by
          simp [Node.onAttestation, Store.onAttestation, hb]
        rw [hn] at h
        simp only [List.mem_append, List.mem_singleton] at h
        rcases h with h | rfl
        · exact Or.inl h
        · exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- The engine node of `v` is the generic replay's engine node. -/
private theorem stateAt_node_trace (v : V) (i : Nat) : (stateAt S rho hn v i).node =
    (traceEncoding S hn).adapter.node
      (NodeAsChainShape.CanonicalTrace.stateAt (traceEncoding S hn) rho v i) := by
  rw [stateAt_eq]
  exact traceEncoding_induction S hn (fun e _ _ =>
    ((rho.stateBefore i v).st.1 hn).node =
      e.adapter.node (NodeAsChainShape.CanonicalTrace.stateAt e rho v i)) fun _ => by
    rw (config := { transparency := .default })
      [NodeAsChainShape.CanonicalTrace.stateAt_eq, cast_eq]
    rfl

/-- **A tick grows the pool only by its own admissions.** An attestation in `v`'s pool after its
tick was in the pool before it or is an own admission of the tick. -/
private theorem tick_pool_split (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) {a : FG.Att (Fintype.card V)}
    (ha : a ∈ (stateAt S rho hn v (i + 1)).node.fg.atts) :
    a ∈ (stateAt S rho hn v i).node.fg.atts ∨ a ∈ admitsAt S rho hn v i := by
  have h := (traceEncoding_lawful S hn).tick_admits rho hv he
  change _ = (NodeAsChainShape.CanonicalTrace.admitsAt (traceEncoding S hn) rho v i).foldl
    (fun n a => (Node.onAttestation n a).1) _ at h
  rw [stateAt_node_trace S rho hn, h] at ha
  simp only [admitsAt_eq, stateAt_node_trace S rho hn]
  rw [← NodeAsChainShape.CanonicalTrace.admitsAt_eq]
  rcases mem_of_mem_foldl_onAttestation _ _ ha with h | h
  · left
    rw [NodeAsChainShape.CanonicalTrace.postTick_eq] at h
    split at h
    · rwa [NodeAsChainShape.CanonicalTrace.exec_tick_atts] at h
    · exact h
  · exact Or.inr h

/-- **An own attestation is processed by its releaser no later than its release.** The released
attestation is in the releaser's pool after the releasing tick (`released_att_mem_pool`): an own
admission of that tick, processed at the tick's time (`admit_processAt`), or already in the pool
before the tick, whose agreement with the trace (`simTrace_state_of`) makes it an attestation the
node processed at an earlier cut of the trace's prefix through that time (`pool_processed`). -/
theorem released_att_processAt (hv : rho.ExecutionValid) {v : V}
    {a : FG.Att (Fintype.card V)} {t : Time} (hs : rho.releases v (attObj a) t) :
    ∃ k, (simTrace S rho hn).ProcessAttAt (rho.ownKey v) k a ∧
      (simTrace S rho hn).time k ≤ t := by
  obtain ⟨i, he, ho⟩ := hs
  rcases he with he | ⟨o, he⟩
  swap
  · exact absurd ho (deliver_not_att S rho hn hv he a)
  have hpool := released_att_mem_pool S rho hn hv he ho
  rcases tick_pool_split S rho hn hv he hpool with hold | hadm
  swap
  · obtain ⟨k, hk, ht⟩ := Obligations.admit_processAt S rho hn he hadm
    exact ⟨k, hk, ht.le⟩
  have hi : i ≤ rho.events.length := (List.getElem?_eq_some_iff.mp he).1.le
  have hm := List.mem_of_getElem? he
  have hstate := simTrace_state_of S rho hn hv (v := v)
    (fun he' hnode => hnode ▸ event_honest_zero S rho hv he') i hi
  rw [hstate] at hold
  have hlaws := (Model.sysOf_laws schema (compiled (goldilocks S)) V).trace ⟨E, rho⟩ hv
  have hct : rho.cutTime i ≤ t := by
    have h := hlaws.cutTime_mono i (i + 1) (Nat.le_succ i)
      ((List.getElem?_eq_some_iff.mp he).1)
    change rho.cutTime i ≤ rho.cutTime (i + 1) at h
    simpa only [Model.Run.cutTime, he, Model.Event.time] using h
  have h0 : 0 ≤ rho.cutTime i := by
    have h := hlaws.cutTime_mono 0 i (Nat.zero_le i) hi
    change rho.cutTime 0 ≤ rho.cutTime i at h
    exact h
  have hth : t ≤ rho.horizon := (hv.in_horizon _ hm).2
  have hfa : v ∉ rho.faultyAt (rho.cutTime i) := fun hf =>
    hv.honest_only _ hm (rho.faultyAt_mono hct hf)
  have hrun := (simTraceAt_goldilocksRun S rho hn hv).upTo h0
  have hy := honest_ownKey_at S rho hfa (hct.trans hth)
  have hcut : ∀ k < cutMap S rho hn i, (simTraceAt S rho hn).time k ≤ rho.cutTime i := by
    rw [simTraceAt_eq, (simTrace_encoding S rho hn).1, (simTrace_encoding S rho hn).2]
    exact (NodeAsChainShape.CanonicalTrace.cutMap_time_bounds (traceEncoding S hn) rho hv hi).1
  rw [← simTraceAt_eq S rho hn, ← Trace.upTo_state _ _ hcut] at hold
  obtain ⟨k, -, hk⟩ := Healing.pool_processed hrun.toLocalRun hy hold
  rw [← simTraceAt_eq S rho hn]
  rcases hk with hk | ⟨B, hB, hB'⟩
  · obtain ⟨hkt, hk⟩ := (Trace.upTo_callAt _).mp hk
    exact ⟨k, Or.inl hk, hkt.trans hct⟩
  · obtain ⟨hkt, hk⟩ := (Trace.upTo_callAt _).mp hB
    exact ⟨k, Or.inr ⟨B, hk, hB'⟩, hkt.trans hct⟩

end Consensus.Goldilocks.Simulation

end
