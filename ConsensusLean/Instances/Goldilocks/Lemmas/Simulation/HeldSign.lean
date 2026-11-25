module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ReleaseTick
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Goldilocks Simulation: a signing the schedule refuses to release is held

The step that puts an attestation into the held queue. The FG update's signing cut signs
`fgSigned` (`fgSigned_of_attest`), so a batch poll with the FG update due at a time the release
schedule refuses holds it (`pollBatch_held_of_attest`). At the engine, a public tick whose node's
tick signs `a` (an `fg_attest` cut of the tick event) at a time the
schedule refuses release leaves `a` in the node's held queue after the event (`tick_sign_held`).
With `held_flush` (`HeldFlush`) this closes the `hflush` premise from the signing tick.

Every step is proved. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)
open AC (ACParams ReplayOrder Vote Payload)

section ShapeSign

variable {binding : VoteBinding} {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

/-- The FG update step's signing cut signs the attestation `fgSigned` names. -/
theorem fgSigned_of_attest (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (x : Nat)
    (st : State sp ro binding) {C} {a : FG.Att sp.n}
    (hc : Cut.fg (.attest C (some a)) ∈
      (Node.tickStep proposer dg st.self st.node st.now x .fgUpdate).2) :
    fgSigned st = some a := by
  rw [fgSigned_eq]
  have h0 : Cut.fg (.attest C (some a)) ≠ (Node.acToFG st.node st.now).2.1 := by
    simp [Node.acToFG]
  simp only [Node.tickStep] at hc
  rcases h : (Node.acToFG st.node st.now).2.2 with _ | C'
  · simp [h] at hc
    exact absurd hc h0
  · unfold Node.attest at hc
    rcases h' : (Node.acToFG st.node st.now).1.fg.attest (Node.acToFG st.node st.now).1.record
      st.self C' with _ | ⟨a', Λ'⟩
    · simp [h, h'] at hc
      exact absurd hc h0
    · simp only [Option.bind_some, h', Option.map_some]
      simp [h, h'] at hc
      rcases hc with hc | ⟨-, rfl⟩
      · exact absurd hc h0
      · rfl

/-- A batch poll with the FG update due at a time the schedule refuses release holds the
attestation of the FG update step's signing cut. -/
theorem pollBatch_held_of_attest {release : Fin sp.n → Time → Bool}
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (x : Nat)
    (st : State sp ro binding) (k : Time) (hf : st.fgDue = true)
    (hr : release st.self st.now = false) {C} {a : FG.Att sp.n}
    (hc : Cut.fg (.attest C (some a)) ∈
      (Node.tickStep proposer dg st.self st.node st.now x .fgUpdate).2) :
    a ∈ (pollBatch st k release).1.held := by
  rw [pollBatch_held, fgSigned_of_attest proposer dg x st hc]
  simp [hf, hr]

/-- A batch poll at a time the schedule refuses release keeps the held queue. -/
theorem pollBatch_held_keep {release : Fin sp.n → Time → Bool} (st : State sp ro binding)
    (k : Time) (hr : release st.self st.now = false) {a : FG.Att sp.n} (ha : a ∈ st.held) :
    a ∈ (pollBatch st k release).1.held := by
  rw [pollBatch_held]
  simp [hr, ha]

end ShapeSign

section TickSign

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **A signing the schedule refuses to release is held.** A public tick of `v` at `s` whose
node's tick has a signing cut of `a`, at a time the release schedule refuses release, leaves `a`
in `v`'s held queue after the event: the held signing changes only the record, and `a` enters the
pool at its release. Premise `hpre` as for `tick_public_analysis`. -/
theorem tick_sign_held (hv : rho.ExecutionValid) {i : Nat} {v : V} {s : Time}
    (he : rho.events[i]? = some (.tick v s))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic s)
    (hpre : ∀ sl (hs : 0 < sl), (skeleton (pubOf E) S.vote).proposeAt s = [.propose sl hs] →
      rho.ownKey v ∈ rho.sel (.proposer sl) → ∀ par info cs,
      (propose (shapeOf S hn (preNode S rho v (rho.stateBefore i v) s)) sl).2 =
        some (par, info, cs) →
      ∀ o ∈ cs, o ∈ Model.closure (preNode S rho v (rho.stateBefore i v) s).seen)
    {C} {a : FG.Att (Fintype.card V)}
    (hc : Cut.fg (.attest C (some a)) ∈ (exec (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (stateAt S rho hn v i).node s
      (.tick (encodeTxs (Model.mempool rho.inbox v s)) (S.sign (pubOf E) (rho.ownKey v) s))).2)
    (hr : S.release (pubOf E) (rho.ownKey v) s = false) :
    a ∈ (stateAt S rho hn v (i + 1)).held := by
  have hm := List.mem_of_getElem? he
  have ht : 0 ≤ s := (hv.in_horizon _ hm).1
  have hw := hv.tick_awake v s hm
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
  -- the signing cut is the FG update step's, after the proposal step
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
  -- from the node `N4` before the trailing polls to the end of the tick
  have finish : ∀ N4 : Model.Node (Model.protoOf (compiled (goldilocks S)) E),
      (shapeOf S hn N4).fgDue = true → (shapeOf S hn N4).self = rho.ownKey v →
      (shapeOf S hn N4).now = s →
      (shapeOf S hn N4).node =
        (Node.tickStep (runProposer S rho hn) dg (rho.ownKey v) n1 s X .proposal).1 →
      shapeOf S hn (rho.tick nd v s).1 = shapeOf S hn (Model.releaseAll
        (Model.protoOf (compiled (goldilocks S)) E) rho.hash (rho.ownKey v)
        (rho.dutyStep v (rho.dutyStep v N4 (.poll s.toNat)).1 (.poll s.toNat)).1
        (Model.gossipCandidates (Model.protoOf (compiled (goldilocks S)) E)
          (rho.dutyStep v (rho.dutyStep v N4 (.poll s.toNat)).1 (.poll s.toNat)).1.st s)).1 →
      a ∈ (stateAt S rho hn v (i + 1)).held := by
    intro N4 hf4 hs4 hw4 hn4 htick
    have hS5 := dutyStep_poll S rho hn v N4 s.toNat hsel
    have h5 : a ∈ (shapeOf S hn (rho.dutyStep v N4 (.poll s.toNat)).1).held := by
      rw [hS5]
      refine pollBatch_held_of_attest (runProposer S rho hn) dg X _ _ hf4
        (by rw [hs4, hw4]; exact hr) (C := C) ?_
      rw [hs4, hw4, hn4]; exact hcf
    have hS6 := dutyStep_poll S rho hn v (rho.dutyStep v N4 (.poll s.toNat)).1 s.toNat hsel
    have h6 : a ∈ (shapeOf S hn (rho.dutyStep v (rho.dutyStep v N4 (.poll s.toNat)).1
        (.poll s.toNat)).1).held := by
      rw [hS6]
      refine pollBatch_held_keep _ _ ?_ h5
      rw [hS5, pollBatch_self, pollBatch_now, hs4, hw4]; exact hr
    rw [stateAt_tick S rho hn v he, htick]
    exact releaseAll_pres S rho hn (fun st => a ∈ st.held)
      (fun st o hs h => (recordOwn_held st o hs).symm ▸ h) _ _ _ h6
  rcases Skeleton.proposeAt_cases (skeleton (pubOf E) S.vote) s with
    ⟨hnil, hno⟩ | ⟨sl, hs, hone, hts⟩
  · have hnp : ¬ Proposes (P := (S.params (pubOf E) hn).toParams)
        (runProposer S rho hn) (rho.ownKey v) s :=
      not_proposes S hn (runProposer S rho hn) _ s
        (fun s hs h => hno s hs (h.trans (slotTime_eq S hn s)))
    have hc2 := tickStep_proposal_not' (runProposer S rho hn) dg (rho.ownKey v) n1 s X hnp
    refine finish N3 (hfgN3.trans hsgt) hselfN3 hnowN3 (by rw [hnodeN3, hc2]) ?_
    rw [rho.tick_of_awake nd v s hw]
    dsimp only
    rw [duties_eq S s ht]
    unfold dutiesInit
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
    rw [rho.tick_of_awake nd v s hw]
    dsimp only
    rw [duties_eq S s ht]
    unfold dutiesInit
    rw [hone]
    rfl

end TickSign

end Consensus.Goldilocks.Simulation

end
