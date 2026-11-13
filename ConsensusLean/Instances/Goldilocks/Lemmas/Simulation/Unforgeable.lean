module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Shape
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ReleaseTick

public section

/-! # Own cuts behind released and processed blocks and votes

A block or vote that an engine event releases genuinely comes from a cut of that event, and a
block or AC message processed while its signer is honest comes from an earlier own cut of the
signer. These arguments read only the engine run and its simulating trace. The fault model
enters through premises: the ticking node's honesty at time zero and its proposal's
releasability for a release, and the signer's release analysis for a processed object.
Constant faults (`RunSchedule`) and growing faults (`Growing/Simulation/Blocks`,
`Growing/Simulation/Votes`) supply them. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

private theorem tick_block_fields {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (Payload sp.n))
    (self : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time) (x : Nat)
    {B : Blk sp} {acc : Bool} {k : Nat}
    (hk : k < (exec proposer dg self st t (.tick x)).2.length)
    (hc : (exec proposer dg self st t (.tick x)).2[k] = .fg (.block B acc)) :
    B.proposer = self ∧ B.RootOk dg ∧ B.parent ≠ none ∧ k ≠ 0 := by
  have hzero : k ≠ 0 := by
    intro h
    subst k
    simp [exec, onTick, runSteps, tickSteps, tickStep, acCall] at hc
  have hm := List.getElem_mem hk
  rw [hc] at hm
  rw [show (exec proposer dg self st t (.tick x)).2 = (onTick proposer dg self st t x).2
    from rfl, onTick_cuts] at hm
  rcases List.mem_append.mp hm with hm | hm
  · rcases List.mem_append.mp hm with hm | hm
    · simp [tickStep, acCall] at hm
    · simp only [tickStep] at hm
      split_ifs at hm
      · split at hm
        · simp [acProposal] at hm
        · rename_i d p hdp
          simp only [proposeBlock, onBlock] at hm
          split_ifs at hm
          · simp [acProposal] at hm
          · split at hm <;> simp [acCall, acProposal] at hm <;>
              obtain ⟨rfl, _⟩ := hm <;> exact ⟨rfl, rfl, by simp [mkBlock], hzero⟩
      · simp at hm
  · simp only [tickStep] at hm
    split at hm
    · simp [acToFG] at hm
    · simp only [attest, List.mem_cons, acToFG, reduceCtorEq, false_or] at hm
      split at hm <;> simp [onAttestation] at hm

private theorem ownBlock_of_tick_cut {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t)
    {B : Blk (S.params (pubOf E) hn)} {acc : Bool}
    (hc : Cut.fg (.block B acc) ∈ (exec (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (stateAt S rho hn v i).node t
      (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2) :
    ∃ k < cutMap S rho hn (i + 1), (simTrace S rho hn).OwnBlockAt B.proposer k B := by
  obtain ⟨m, hm, hcm⟩ := List.getElem_of_mem hc
  obtain ⟨hself, _, _, hm0⟩ := tick_block_fields _ _ _ _ _ _ hm hcm
  have hEC := eventCuts_tick_public S rho hn i v t he hp
  have hm' : m < (eventCuts S rho hn i).length := by
    rw [hEC, length_groupRecs]; exact hm
  have hr := allCuts_getElem?_add S rho hn i m (List.getElem?_eq_some_iff.mp he).1 hm'
  rw [List.getElem?_eq_getElem hm'] at hr
  have hgr := getElem_groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
    (stateAt S rho hn v i).node t (Nat.pair i 0)
    (.tick (encodeTxs (Model.mempool rho.inbox v t))) m
    (show m < _ from by rw [length_groupRecs]; exact hm)
  have hr' : (allCuts S rho hn)[cutMap S rho hn i + m]? = some
      ((groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t (Nat.pair i 0)
        (.tick (encodeTxs (Model.mempool rho.inbox v t))))[m]'
          (by rw [length_groupRecs]; exact hm)) :=
    by simpa only [hEC] using hr
  refine ⟨cutMap S rho hn i + m, ?_, ⟨acc, ?_, ?_⟩, ?_⟩
  · rw [cutMap_succ]; omega
  · rw [simTrace_node, hr']; exact hgr.1.trans hself.symm
  · rw [simTrace_label, hr']; exact congrArg some (hgr.2.2.2.2.trans hcm)
  · rw [simTrace_pos, hr']; simpa only [Option.elim_some, hgr.2.2.2.1] using hm0

/-- A block that an engine event releases genuinely is an own block of a tick cut of that
event. Premises: `hv'`, a ticking node is honest at time zero; `hpre`, its proposal carries
only objects it has seen (`preNode_releasable` for constant faults, `preNode_releasable_at`
for growing faults); `huniq`, `B` is the only rooted block with a parent that has its wire
object (`blockObj_fields`). -/
theorem released_block_cut_of (hv : rho.ExecutionValid)
    {i : Nat} {v : V} {t : Time} (hs : rho.SendsAt v i t)
    (hv' : rho.events[i]? = some (.tick v t) → v ∉ rho.faultyAt 0)
    (hpre : rho.events[i]? = some (.tick v t) →
      ∀ s (hs : 0 < s), (skeleton (pubOf E) S.vote).proposeAt t = [.propose s hs] →
        rho.ownKey v ∈ rho.sel (.proposer s) → ∀ par info cs,
        (propose (shapeOf S hn (preNode S rho v (rho.stateBefore i v) t)) s).2 =
          some (par, info, cs) →
        ∀ o ∈ cs, o ∈ Model.closure (preNode S rho v (rho.stateBefore i v) t).seen)
    {B : Blk (S.params (pubOf E) hn)}
    (huniq : ∀ C : Blk (S.params (pubOf E) hn), C.parent ≠ none →
      C.RootOk (digestOf S rho) →
      blockObj (S.params (pubOf E) hn) (binding := S.vote) B =
        blockObj (S.params (pubOf E) hn) C → B = C)
    (hb : blockObj (S.params (pubOf E) hn) B ∈ rho.releasesAt i) :
    ∃ k < cutMap S rho hn (i + 1), (simTrace S rho hn).OwnBlockAt B.proposer k B := by
  have hhead : ∀ seen ob,
      blockObj (S.params (pubOf E) hn) B ∉ relHead S rho v seen ob := by
    intro seen ob h
    obtain ⟨q, _, heq⟩ := mem_relHead S rho h
    have hh := congrArg Model.Obj.msg heq
    cases hh
  rcases hs with he | ⟨o, he⟩
  · by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
    · obtain ⟨N4, N5, Q, R4, F, G, hr, _, _, hF, hG, _, _, hR4, _⟩ :=
        tick_public_analysis S rho hn hv (hv' he) he hp (hpre he)
      rw [hr] at hb
      have hb4 : blockObj (S.params (pubOf E) hn) B ∈ R4 := by
        rcases List.mem_append.mp hb with hb | hb
        · rcases List.mem_append.mp hb with hb | hb
          · rcases List.mem_append.mp hb with hb | hb
            · rcases List.mem_append.mp hb with hb | hb
              · exact False.elim (hhead _ _ hb)
              · exact hb
            · rcases List.mem_append.mp hb with hb | hb
              · exact False.elim (hhead _ _ hb)
              · rcases hF _ hb with ⟨τ, cs, heq⟩ | ⟨τ, m, heq⟩
                all_goals have hh := congrArg Model.Obj.msg heq; cases hh
          · exact False.elim (hhead _ _ hb)
        · have hh := hG _ hb
          cases hh
      rw [hR4] at hb4
      obtain ⟨C, acc, hc, hb⟩ := mem_blockObjs.mp hb4
      obtain ⟨m, hm, hcm⟩ := List.getElem_of_mem hc
      obtain ⟨_, hrC, hpC, _⟩ := tick_block_fields _ _ _ _ _ _ hm hcm
      have hBC := huniq C hpC hrC hb
      subst C
      exact ownBlock_of_tick_cut S rho hn he hp hc
    · rcases tick_other_releases S rho hn hv (hv' he) he hp _ hb with h | h
      · exact False.elim (hhead _ _ h)
      · cases h
  · have ht := (hv.in_horizon _ (List.mem_of_getElem? he)).1
    simp only [Model.Run.releasesAt, he, Model.Run.deliver] at hb
    rcases List.mem_append.mp hb with hb | hb
    · rw [deliverDuties_eq S t ht] at hb
      erw [Model.Run.runDuties_cons, Model.Run.runDuties_nil] at hb
      simp only [List.append_nil] at hb
      rcases dutyStep_poll_sub S rho hn v _ _ _ hb with
        ⟨b, _, heq⟩ | ⟨τ, cs, heq⟩ | ⟨τ, m, heq⟩
      all_goals have hh := congrArg Model.Obj.msg heq; cases hh
    · have hh := gossip_unsigned S rho _ _ _ _ hb
      cases hh

/-- A block that a node processes at cut `k`, while its proposer is honest at the cut's time,
is the proposer's own block at or before `k`. Premise `hrel`: a release of the block's wire
object at an engine event of the proposer comes from an own block cut of that event
(`released_block_cut_of`, with the fault model's premises). -/
theorem blockCall_ownBlock_of_released (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)}
    {k : Nat} {B : Blk (S.params (pubOf E) hn)} (hc : (simTrace S rho hn).BlockCallAt y k B)
    (hhon : rho.key B.proposer ∉ rho.faultyAt ((simTrace S rho hn).time k))
    (hrel : ∀ {j t}, rho.SendsAt (rho.key B.proposer) j t → B.parent ≠ none →
      B.RootOk (digestOf S rho) → blockObj (S.params (pubOf E) hn) B ∈ rho.releasesAt j →
      ∃ q < cutMap S rho hn (j + 1), (simTrace S rho hn).OwnBlockAt B.proposer q B) :
    ∃ j ≤ k, (simTrace S rho hn).OwnBlockAt B.proposer j B := by
  obtain ⟨acc, hnode, hlab⟩ := hc
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, _, he, hstart, _, hidx, hn', htime, hpos, hlab'⟩ :=
    simTrace_cut S rho hn hl
  have hrl : r.label = .fg (.block B acc) := Option.some.inj (hlab'.symm.trans hlab)
  have hmem := List.mem_of_getElem? hidx
  cases ev with
  | tick v t =>
    have hp : (S.params (pubOf E) hn).toParams.IsPublic t := by
      by_contra hp
      rw [eventCuts_tick_other S rho hn i v t he hp] at hmem
      simp at hmem
    rw [eventCuts_tick_public S rho hn i v t he hp] at hmem
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨_, _, _, hp', hc⟩ := getElem_groupRecs _ _ _ _ _ _ _ m hm
    obtain ⟨hself, _, _, hm0⟩ := tick_block_fields _ _ _ _ _ _
      (by rwa [length_groupRecs] at hm) (hc.symm.trans hrl)
    exact ⟨k, le_rfl, ⟨acc, hn'.trans hself.symm, hlab⟩, by rwa [hpos, hp']⟩
  | deliver v o t =>
    rw [eventCuts_deliver S rho hn i v o t he] at hmem
    obtain ⟨o', e, st', ho, hce, m, hm, hc, _⟩ := mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ hmem
    have hcut := hc.symm.trans hrl
    have heq : e = .block B := by
      have hmem := List.getElem_mem hm
      rw [hcut] at hmem
      cases e with
      | tick x => exact False.elim (canonEvent_ne_tick hce x rfl)
      | block B' =>
        simp only [exec, onBlock] at hmem
        split_ifs at hmem
        · simp at hmem
        · split at hmem <;>
            simp only [acCall, List.mem_cons, Cut.fg.injEq, FGLabel.block.injEq, reduceCtorEq,
              List.not_mem_nil, or_self, or_false] at hmem <;>
            simp_all only [ne_eq, reduceCtorEq, not_false_eq_true, not_lt]
      | message => simp [exec, onMessage, acCall] at hmem
      | attestation => simp [exec, onAttestation] at hmem
      | restart => simp [exec, Node.restart, acCall] at hmem
    subst e
    obtain rfl := eq_blockObj_of_decodeBlock (decodeBlock_of_canonEvent hce)
    obtain ⟨hroot, hpar, _⟩ := decodeBlock_wire (decodeBlock_of_canonEvent hce)
    have hh : rootOf (Model.digests rho.hash o) (headerOf _ B) =
        some (rho.hash (headerOf _ B)) := by
      apply rootOf_digests_of_mem
      exact List.mem_filterMap.mpr ⟨blockObj _ B, mem_delivered ho, rfl⟩
    rw [hh, Option.map_some, Option.some.injEq] at hroot
    have hroot' : B.RootOk (digestOf S rho) := by
      obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp hpar
      rw [digestOf_eq]
      change B.root = dgOf rho.hash S.genesisRoot B.parent B.slot B.input B.fgPayload B.acPayload
      erw [dgOf_eq, ← hroot]
      simp only [headerOf, hp]
    have hsign : rho.signerOf (blockObj (S.params (pubOf E) hn) B) =
        some (rho.key B.proposer) := rfl
    have hhon' : rho.key B.proposer ∉ rho.faultyAt t := by
      rw [htime] at hhon
      exact hhon
    obtain ⟨j, t', hj, hs, hb⟩ := hv.unforgeable i v o t he _
      (contains_of_mem_delivered ho) (rho.key B.proposer) hsign hhon'
    obtain ⟨q, hq, hown⟩ := hrel hs hpar hroot' hb
    have hle : cutMap S rho hn (j + 1) ≤ cutMap S rho hn i :=
      cutMap_mono S rho hn (Nat.succ_le_of_lt hj)
    exact ⟨q, by omega, hown⟩
  | restart v t =>
    rw [eventCuts_restart S rho hn i v t he] at hmem
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨_, _, _, _, hc⟩ := getElem_groupRecs _ _ _ _ _ _ _ m hm
    have hcut := List.getElem_mem (lt_of_lt_of_eq hm (length_groupRecs _ _ _ _ _ _ _))
    rw [← hc, hrl] at hcut
    simp [exec, Node.restart, acCall] at hcut

private theorem emit_of_record {i : Nat} {ev}
    (he : rho.events[i]? = some ev) {r : CutRec (S.params (pubOf E) hn) (S.ro _)}
    (hr : r ∈ eventCuts S rho hn i) {ℓ} (hl : r.label = .ac ℓ)
    {em} (hem : em ∈ ℓ.emits) :
    ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).EmitAt (rho.ownKey ev.node) k em.msg := by
  have hnode := (mem_eventCuts S rho hn he hr).1
  obtain ⟨m, hm, hrm⟩ := List.getElem_of_mem hr
  have hk := allCuts_getElem?_add S rho hn i m (List.getElem?_eq_some_iff.mp he).1 hm
  rw [List.getElem?_eq_getElem hm, hrm] at hk
  refine ⟨cutMap S rho hn i + m, ?_, ℓ, ⟨?_, ?_⟩, em, hem, rfl⟩
  · rw [cutMap_succ]; omega
  · rw [simTrace_node, hk]; exact hnode
  · rw [simTrace_label, hk]; exact congrArg some hl

private theorem emit_of_tick_body {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t) {m : Vote (Fintype.card V)}
    (hm : Body.vote (encodeVote m) ∈ emitted (exec (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (stateAt S rho hn v i).node t
      (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2) :
    ∃ k < cutMap S rho hn (i + 1), (simTrace S rho hn).EmitAt (rho.ownKey v) k m := by
  obtain ⟨ℓ, hc, em, hem, rfl⟩ := mem_emitted.mp hm
  obtain ⟨q, hq, hcq⟩ := List.getElem_of_mem hc
  have hq' : q < (groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
      (stateAt S rho hn v i).node t (Nat.pair i 0)
      (.tick (encodeTxs (Model.mempool rho.inbox v t)))).length := by
    rwa [length_groupRecs]
  apply emit_of_record S rho hn he (r := (groupRecs (runProposer S rho hn) (digestOf S rho)
    (rho.ownKey v) (stateAt S rho hn v i).node t (Nat.pair i 0)
    (.tick (encodeTxs (Model.mempool rho.inbox v t))))[q]) ?_ ?_ hem
  · rw [eventCuts_tick_public S rho hn i v t he hp]; exact List.getElem_mem hq'
  · exact (getElem_groupRecs _ _ _ _ _ _ _ q hq').2.2.2.2.trans hcq

/-- A vote that an engine event releases genuinely comes from an emission of that event
before its end cut. Premises `hv'` and `hpre` as for `released_block_cut_of`. -/
theorem released_vote_cut_of (hv : rho.ExecutionValid)
    {i : Nat} {v : V} {t : Time} (hs : rho.SendsAt v i t)
    (hv' : rho.events[i]? = some (.tick v t) → v ∉ rho.faultyAt 0)
    (hpre : rho.events[i]? = some (.tick v t) →
      ∀ s (hs : 0 < s), (skeleton (pubOf E) S.vote).proposeAt t = [.propose s hs] →
        rho.ownKey v ∈ rho.sel (.proposer s) → ∀ par info cs,
        (propose (shapeOf S hn (preNode S rho v (rho.stateBefore i v) t)) s).2 =
          some (par, info, cs) →
        ∀ o ∈ cs, o ∈ Model.closure (preNode S rho v (rho.stateBefore i v) t).seen)
    {m : Vote (Fintype.card V)} (hb : voteObj m ∈ rho.releasesAt i) :
    ∃ k < cutMap S rho hn (i + 1), (simTrace S rho hn).EmitAt (rho.ownKey v) k m := by
  have hbody : ∀ b, voteObj m = pollObj S rho v b → b = Body.vote (encodeVote m) := by
    intro b heq
    exact (Model.Msg.data.inj (congrArg Model.Obj.msg heq)).symm
  rcases hs with he | ⟨o, he⟩
  · have hnil := outbox_empty S rho hn hv v i
    by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
    · obtain ⟨N4, N5, Q, R4, F, G, hr, _, _, hF, hG, _, hQ, hR4, _⟩ :=
        tick_public_analysis S rho hn hv (hv' he) he hp (hpre he)
      have hq : ∀ seen ob, (∀ b, ob = some b → b ∈ Q) →
          voteObj m ∈ relHead S rho v seen ob →
          ∃ k < cutMap S rho hn (i + 1), (simTrace S rho hn).EmitAt (rho.ownKey v) k m := by
        intro seen ob hmem hb
        obtain ⟨b, hob, heq⟩ := mem_relHead S rho hb
        have hbq := hmem b hob
        rw [hbody b heq, hQ] at hbq
        rcases List.mem_append.mp hbq with hbq | hbq
        · exact emit_of_tick_body S rho hn he hp hbq
        · exact False.elim (vote_not_mem_attBodies _ _ hbq)
      rw [hr] at hb
      rcases List.mem_append.mp hb with hb | hb
      · rcases List.mem_append.mp hb with hb | hb
        · rcases List.mem_append.mp hb with hb | hb
          · rcases List.mem_append.mp hb with hb | hb
            · obtain ⟨b, hb, _⟩ := mem_relHead S rho hb
              simp [hnil] at hb
            · rw [hR4] at hb
              obtain ⟨B, acc, _, heq⟩ := mem_blockObjs.mp hb
              have hh := congrArg Model.Obj.msg heq
              cases hh
          · rcases List.mem_append.mp hb with hb | hb
            · exact hq _ _ (fun _ h => List.mem_of_mem_head? h) hb
            · rcases hF _ hb with ⟨τ, cs, heq⟩ | ⟨τ, m, heq⟩
              all_goals have hh := congrArg Model.Obj.msg heq; cases hh
        · exact hq _ _ (fun _ h => List.mem_of_mem_tail (List.mem_of_mem_head? h)) hb
      · have hh := hG _ hb; cases hh
    · rcases tick_other_releases S rho hn hv (hv' he) he hp _ hb with hb | hb
      · obtain ⟨b, hb, _⟩ := mem_relHead S rho hb
        simp [hnil] at hb
      · cases hb
  · have ht0 := (hv.in_horizon _ (List.mem_of_getElem? he)).1
    have hnow : (stateAt S rho hn v i).now = t :=
      (now_eq_lastClock S rho hn hv v i).trans (lastClock_of_deliver S rho hv v he)
    simp only [Model.Run.releasesAt, he, Model.Run.deliver] at hb
    rcases List.mem_append.mp hb with hb | hb
    · rw [deliverDuties_eq S t ht0] at hb
      erw [Model.Run.runDuties_cons, Model.Run.runDuties_nil] at hb
      simp only [List.append_nil] at hb
      rcases dutyStep_poll_sub S rho hn v _ _ _ hb with
        ⟨b, hb, heq⟩ | ⟨τ, cs, heq⟩ | ⟨τ, m, heq⟩
      · have hf : (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).fgDue = false :=
          (process_fgDue _ _ _).trans (fgDue_eq_false S rho hn v i)
        change (pollPre (process ((rho.stateBefore i v).st.1 hn) o
          (Model.digests rho.hash o))).outbox.head? = some b at hb
        rw [← stateAt_eq S rho hn v i] at hb
        rw [pollPre_eq, hf] at hb
        have hb' := List.mem_of_mem_head? hb
        rw [hbody b heq] at hb'
        rcases process_outbox_source (runProposer S rho hn) (digestOf S rho)
          (Model.digests rho.hash o) t i _ (stateAt S rho hn v i) 0 hnow _ hb' with
          hb | ⟨r, hr, ℓ, hl, em, hem, heq⟩
        · rw [outbox_empty S rho hn hv v i] at hb; cases hb
        · have hm := congrArg (decodeVote (Fintype.card V)) (Body.vote.inj heq)
          rw [decodeVote_encodeVote, decodeVote_encodeVote] at hm
          have hm := Option.some.inj hm
          rw [hm]
          apply emit_of_record S rho hn he (r := r) ?_ hl hem
          rw [eventCuts_deliver S rho hn i v o t he, ← self_eq_ownKey S rho hn v i]
          exact hr
      · have hh := congrArg Model.Obj.msg heq; cases hh
      · have hh := congrArg Model.Obj.msg heq; cases hh
    · have hh := gossip_unsigned S rho _ _ _ _ hb; cases hh

/-- **A received AC message was delivered**: the cut `k` of a message call is a cut of a
delivery event `i` at the cut's time, whose delivered object contains the vote. -/
theorem msgCall_delivered {y : Fin (Fintype.card V)} {k : Nat} {m : Vote (Fintype.card V)}
    (hc : (simTrace S rho hn).MsgCallAt y k m) :
    ∃ i v o t, rho.events[i]? = some (.deliver v o t) ∧ Model.Obj.Contains o (voteObj m) ∧
      cutMap S rho hn i ≤ k ∧ (simTrace S rho hn).time k = t := by
  obtain ⟨ℓ, ⟨hnode, hlab⟩, hcall⟩ := hc
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, _, he, hstart, _, hidx, _, htime, _, hlab'⟩ := simTrace_cut S rho hn hl
  have hrl : r.label = .ac ℓ := Option.some.inj (hlab'.symm.trans hlab)
  have hmem := List.mem_of_getElem? hidx
  obtain ⟨v, o, t, rfl⟩ := eq_deliver_of_cut S rho hn he hmem (Or.inr ⟨ℓ, m, hrl, hcall⟩)
  rw [eventCuts_deliver S rho hn i v o t he] at hmem
  obtain ⟨o', e, st', ho, hce, q, hq, hc, _⟩ := mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ hmem
  have hcut := List.getElem_mem hq
  rw [← hc, hrl] at hcut
  have heq : e = .message m := by
    cases e with
    | tick x => exact False.elim (canonEvent_ne_tick hce x rfl)
    | message m' =>
      simp only [exec, onMessage, acCall, List.mem_singleton, Cut.ac.injEq] at hcut
      subst ℓ
      cases hcall
      rfl
    | block B =>
      simp only [exec, onBlock] at hcut
      split_ifs at hcut
      · simp at hcut
      · split at hcut <;> simp [acCall] at hcut
        subst ℓ
        cases hcall
    | attestation => simp [exec, onAttestation] at hcut
    | restart =>
      simp only [exec, Node.restart, acCall, List.mem_singleton, Cut.ac.injEq] at hcut
      subst ℓ
      cases hcall
  subst e
  have ho' : o' = voteObj m := by
    rcases canonEvent_eq_some hce with ⟨_, h, _⟩ | ⟨m', h, ho⟩ | ⟨_, h, _⟩
    · cases h
    · cases h; exact ho
    · cases h
  subst o'
  exact ⟨i, v, o, t, he, contains_of_mem_delivered ho, hstart, htime⟩

/-- An AC message that a node receives at cut `k`, while its signer is honest at the cut's
time, was emitted by the signer at an earlier cut. Premise `hrel`: a release of the vote at an
engine event of the signer comes from an own emission cut of that event
(`released_vote_cut_of`, with the fault model's premises). -/
theorem msgCall_emit_of_released (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)}
    {k : Nat} {m : Vote (Fintype.card V)} (hc : (simTrace S rho hn).MsgCallAt y k m)
    (hhon : rho.key m.val ∉ rho.faultyAt ((simTrace S rho hn).time k))
    (hrel : ∀ {j t}, rho.SendsAt (rho.key m.val) j t → voteObj m ∈ rho.releasesAt j →
      ∃ q < cutMap S rho hn (j + 1), (simTrace S rho hn).EmitAt m.val q m) :
    ∃ j < k, (simTrace S rho hn).EmitAt m.val j m := by
  obtain ⟨i, v, o, t, he, ho, hstart, htime⟩ := msgCall_delivered S rho hn hc
  rw [htime] at hhon
  obtain ⟨j, t', hj, hs, hb⟩ := hv.unforgeable i v o t he _ ho (rho.key m.val) rfl hhon
  obtain ⟨q, hq, hem⟩ := hrel hs hb
  have hle : cutMap S rho hn (j + 1) ≤ cutMap S rho hn i :=
    cutMap_mono S rho hn (Nat.succ_le_of_lt hj)
  exact ⟨q, by omega, hem⟩

end Consensus.Goldilocks.Simulation
