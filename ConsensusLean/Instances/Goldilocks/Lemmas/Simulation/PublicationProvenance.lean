module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationQueue
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Successful acceptance provenance of forwarding publications -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node

section Trace

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

private theorem tick_forward_queue (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {u t : Time} {o : Wire (Fintype.card V) S.vote} {p : Option (Wire (Fintype.card V) S.vote)}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.tick v u)) (ho : o ∈ rho.releasesAt i)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey v, t, p, B)) :
    ∃ s hs, (skeleton (Model.pubOf E) S.vote).proposeAt u = [.propose s hs] ∧
      (t, p.toList ++ [blockObj (S.params (Model.pubOf E) hn) B]) ∈
        (shapeOf S hn (rho.dutyStep v
          (atProposal S rho v (rho.stateBefore i v) u) (.propose s hs)).1).forwards := by
  have hu := (hv.in_horizon _ (List.mem_of_getElem? he)).1
  have hw := hv.tick_awake v u (List.mem_of_getElem? he)
  have hsel := poll_selected S rho hv v
  have noPoll (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
      (hempty : (shapeOf S hn nd).forwards = [])
      (h : o ∈ (rho.dutyStep v nd (.poll u.toNat)).2) : False := by
    have hq := poll_release_forward_queue S rho hn v nd u.toNat h hd
    rw [hempty] at hq
    exact List.not_mem_nil hq
  have noGossip (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
      (h : o ∈ (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E)
        rho.hash (rho.ownKey v) nd
        (Model.gossipCandidates (Model.protoOf (compiled (goldilocks S)) E) nd.st u)).2) : False
            :=
    gossip_not_forward S rho hn nd u (Model.releaseAll_subset _ _ _ _ o h) hd
  have hclock : (shapeOf S hn
      (⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st u
        (Model.mempool rho.inbox v u), (rho.stateBefore i v).seen⟩ :
        Model.Node (Model.protoOf (compiled (goldilocks S)) E))).forwards = [] := by
    have h := forwards_empty S rho hn hv v i
    rw [stateAt_eq] at h
    exact h
  have hpoll (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) :
      (shapeOf S hn (rho.dutyStep v nd (.poll u.toNat)).1).forwards = [] := by
    rw [dutyStep_poll S rho hn v nd u.toNat hsel, poll_forwards]
  simp only [Model.Run.releasesAt, he] at ho
  rcases Skeleton.proposeAt_cases (skeleton (Model.pubOf E) S.vote) u with
    ⟨hnil, _⟩ | ⟨s, hs, hone, _⟩
  · obtain ⟨N1, N3, N5, N6, rfl, rfl, rfl, rfl, hrel⟩ :=
      tick_unroll_nil S rho v (rho.stateBefore i v) u hu hw hnil
    rw [hrel] at ho
    rcases List.mem_append.mp ho with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · rcases List.mem_append.mp h with h | h
            · exact False.elim (noPoll _ hclock h)
            · exact False.elim (noPoll _ (hpoll _) h)
          · rw [dutyStep_pollPropose_snd S rho hn] at h
            exact False.elim (List.not_mem_nil h)
        · have hz := atProposal_forwards_nil S rho hn hv v (rho.stateBefore i v) u
          rw [atProposal_eq] at hz
          exact False.elim (noPoll _ hz h)
      · exact False.elim (noPoll _ (hpoll _) h)
    · exact False.elim (noGossip _ h)
  · obtain ⟨N1, N3, N4, N5, N6, rfl, rfl, rfl, rfl, rfl, hrel⟩ :=
      tick_unroll_propose S rho v (rho.stateBefore i v) u hu hw s hs hone
    rw [hrel] at ho
    rcases List.mem_append.mp ho with h | h
    · rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · rcases List.mem_append.mp h with h | h
            · rcases List.mem_append.mp h with h | h
              · exact False.elim (noPoll _ hclock h)
              · exact False.elim (noPoll _ (hpoll _) h)
            · rw [dutyStep_pollPropose_snd S rho hn] at h
              exact False.elim (List.not_mem_nil h)
          · unfold Model.Run.dutyStep at h
            split at h
            · obtain ⟨m, cs, _, _, _, ho⟩ := rho.mem_signedCandidate.mp
                (Model.releaseAll_subset _ _ _ _ o h)
              have he := ho.symm.trans (forwardObj_of_decodeForward _ _ _ _ _ _ hd)
              injection he with hauth hmsg _
              subst hmsg
              have hh : (ShapeRole.proposer s : ShapeRole S.vote.Kind) = .poll := by
                injection hauth with _ h
                exact (propose_candidateRole_of_not_vote S s hs fun _ h => by cases h).symm.trans h
              cases hh
            · exact False.elim (List.not_mem_nil h)
        · refine ⟨s, hs, hone, ?_⟩
          rw [atProposal_eq]
          exact poll_release_forward_queue S rho hn v _ u.toNat h hd
      · exact False.elim (noPoll _ (hpoll _) h)
    · exact False.elim (noGossip _ h)

private theorem tick_forward_acceptance_wire (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {u t : Time} {o : Wire (Fintype.card V) S.vote} {p : Option (Wire (Fintype.card V) S.vote)}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.tick v u)) (ho : o ∈ rho.releasesAt i)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey v, t, p, B)) :
    ∃ C, ∃ parent : Option (Wire (Fintype.card V) S.vote),
      .fg (.block C true) ∈ (exec (runProposer S rho hn) (digestOf S rho)
        (rho.ownKey v) (stateAt S rho hn v i).node u
        (.tick (encodeTxs (Model.mempool rho.inbox v u)))).2 ∧
      (t, p.toList ++ [blockObj (S.params (Model.pubOf E) hn) B]) =
        (u, parent.toList ++ [blockObj (S.params (Model.pubOf E) hn) C]) ∧
      (S.params (Model.pubOf E) hn).toParams.IsPublic u := by
  obtain ⟨s, hs, hone, hq⟩ := tick_forward_queue S rho hn hv he ho hd
  have htime : u = (S.params (Model.pubOf E) hn).toParams.slotTime s := by
    rcases Skeleton.proposeAt_cases (skeleton (Model.pubOf E) S.vote) u with
      ⟨hno, _⟩ | ⟨s', hs', hyes, ht⟩
    · rw [hno] at hone
      cases hone
    · have hh := List.singleton_inj.mp (hone.symm.trans hyes)
      cases hh
      exact ht.trans (slotTime_eq S hn s).symm
  have hpub : (S.params (Model.pubOf E) hn).toParams.IsPublic u := by
    rw [htime]
    exact (S.params (Model.pubOf E) hn).toParams.slotTime_public s
  have hsel := poll_selected S rho hv v
  have hself : (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) u)).self =
      rho.ownKey v := by
    rw [atProposal_self S rho hn v _ u hsel]
    simpa only [stateAt_eq] using self_eq_ownKey S rho hn v i
  have hnow := atProposal_now S rho hn v (rho.stateBefore i v) u hsel
  rcases proposal_duty_forward_origin S rho hn v _ s hs
      (selValid_proposer S rho hn hv.selValid s) hself
      (by rw [hnow, htime]; exact slotOf_slotTime _ s) (hnow.trans htime) _ hq with
    hq | ⟨C, parent, hc, hq⟩
  · rw [atProposal_forwards_nil S rho hn hv] at hq
    exact False.elim (List.not_mem_nil hq)
  · rw [hnow] at hc hq
    rw [atProposal_mempool] at hc
    have hnode : (shapeOf S hn (atProposal S rho v (rho.stateBefore i v) u)).node =
        (Node.acCall (rho.ownKey v) (stateAt S rho hn v i).node u .tick).1 := by
      rw [atProposal_node S rho hn v _ u
        (by simpa only [stateAt_eq] using fgDue_eq_false S rho hn v i) hsel,
        nodeTick_node_public _ hpub, ← stateAt_eq S rho hn v i]
      exact congrArg (fun k => (Node.acCall k _ u .tick).1) (self_eq_ownKey S rho hn v i)
    rw [hnode] at hc
    refine ⟨C, parent, ?_, hq, hpub⟩
    change _ ∈ (Node.onTick _ _ _ _ _ _).2
    rw [onTick_cuts (sp := S.params (Model.pubOf E) hn) (ro := S.ro _)]
    exact List.mem_append_left _ (List.mem_append_right _ hc)

private theorem tick_accepted_root {sp : SA.SAParams}
    {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    (proposer : Nat → Fin sp.n) (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n))
    (self : Fin sp.n) (st : NodeState (goldilocksNode sp ro)) (t : Time) (x : Nat)
    {B : Blk sp}
    (hm : .fg (.block B true) ∈ (exec proposer dg self st t (.tick x)).2) :
    B.RootOk dg ∧ B.parent ≠ none := by
  change _ ∈ (onTick (A := goldilocksNode sp ro) proposer dg self st t x).2 at hm
  rw [onTick_cuts (sp := sp) (ro := ro)] at hm
  rcases List.mem_append.mp hm with hm | hm
  · rcases List.mem_append.mp hm with hm | hm
    · simp [tickStep, acCall] at hm
    · simp only [tickStep] at hm
      split_ifs at hm
      · split at hm
        · simp [acProposal] at hm
        · simp only [proposeBlock, onBlock] at hm
          split_ifs at hm
          · simp [acProposal] at hm
          · split at hm <;> simp [acCall, acProposal] at hm
            obtain ⟨rfl, _⟩ := hm
            exact ⟨rfl, by simp [mkBlock]⟩
      · simp at hm
  · simp only [tickStep] at hm
    split at hm
    · simp [acToFG] at hm
    · simp only [attest, List.mem_cons, acToFG, reduceCtorEq, false_or] at hm
      split at hm <;> simp [onAttestation] at hm

omit [DecidableEq V] in
private theorem decoded_block_root {o : Wire (Fintype.card V) S.vote}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (hc : Model.Obj.Contains o (blockObj (S.params (Model.pubOf E) hn) B))
    (hd : decodeBlock (S.params (Model.pubOf E) hn) (binding := S.vote) (Model.digests rho.hash o)
      (blockObj (S.params (Model.pubOf E) hn) B) = some B) :
    B.RootOk (digestOf S rho) ∧ B.parent ≠ none := by
  obtain ⟨hroot, hpar, _, _⟩ := decodeBlock_wire hd
  have hh := rootOf_digests_of_mem S rho o _ (List.mem_filterMap.mpr ⟨_, hc, rfl⟩)
  rw [hh, Option.map_some, Option.some.injEq] at hroot
  refine ⟨?_, hpar⟩
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hpar
  rw [digestOf_eq]
  change B.root = dgOf rho.hash S.genesisRoot B.parent B.slot B.input B.fgPayload B.acPayload
  erw [dgOf_eq, ← hroot]
  simp only [headerOf, hr]

/-- A forwarding release during a tick identifies an actual successful proposal cut,
including the digest-backed root rather than just the serialized block fields. -/
theorem tick_released_forward_acceptance (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {u t : Time} {o : Wire (Fintype.card V) S.vote} {p : Option (Wire (Fintype.card V) S.vote)}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.tick v u)) (ho : o ∈ rho.releasesAt i)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey v, t, p, B)) :
    ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).AcceptAt (rho.ownKey v) k B ∧
      (simTrace S rho hn).time k = t := by
  obtain ⟨C, parent, hc, hq, hpub⟩ := tick_forward_acceptance_wire S rho hn hv he ho hd
  have ht : t = u := congrArg Prod.fst hq
  have hw : blockObj (S.params (Model.pubOf E) hn) (binding := S.vote) B = blockObj _ C := by
    have hlast := congrArg List.getLast? (congrArg Prod.snd hq)
    cases p <;> cases parent <;> simpa using hlast
  have hcontains : Model.Obj.Contains o (blockObj (S.params (Model.pubOf E) hn) B) := by
    rw [forwardObj_of_decodeForward _ _ _ _ _ _ hd]
    exact Model.Obj.Contains.step (List.mem_append_right _ (List.mem_singleton_self _))
      (Model.Obj.Contains.refl _)
  obtain ⟨hrB, hpB⟩ := decoded_block_root S rho hn hcontains (decodeForward_child hd).1
  obtain ⟨hrC, hpC⟩ := tick_accepted_root _ _ _ _ _ _ hc
  have hBC := Simulation.blockObj_fields S rho hn hpB hpC hrB hrC hw
  subst C
  obtain ⟨m, hm, hcm⟩ := List.getElem_of_mem hc
  have hm' : m < (groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
      (stateAt S rho hn v i).node u (Nat.pair i 0)
      (.tick (encodeTxs (Model.mempool rho.inbox v u)))).length := by
    rw [length_groupRecs]; exact hm
  have hf := getElem_groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
    (stateAt S rho hn v i).node u (Nat.pair i 0)
    (.tick (encodeTxs (Model.mempool rho.inbox v u))) m hm'
  have hmrec := List.getElem_mem hm'
  have hr := (congrArg (fun rs =>
    (groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
      (stateAt S rho hn v i).node u (Nat.pair i 0)
      (.tick (encodeTxs (Model.mempool rho.inbox v u))))[m]'hm' ∈ rs)
    (eventCuts_tick_public S rho hn i v u he hpub)).mpr hmrec
  obtain ⟨k, hk, ha, htime⟩ := acceptAt_of_eventCuts S rho hn
    (List.getElem?_eq_some_iff.mp he).1 hr (hf.2.2.2.2.trans hcm)
  exact ⟨k, hk, hf.1 ▸ ha, htime.trans (hf.2.1.trans ht.symm)⟩

omit [DecidableEq V] in
/-- A nested forwarding parse uses the same digest-backed roots whether decoded
under its enclosing receipt's digests or its own recursively collected digests. -/
theorem decodeForward_receipt_iff {receipt o : Wire (Fintype.card V) S.vote}
    {x : Fin (Fintype.card V)} {t : Time} {p : Option (Wire (Fintype.card V) S.vote)}
    {B : Blk (S.params (Model.pubOf E) hn)} (hc : Model.Obj.Contains receipt o) :
    decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash receipt) o =
      some (x, t, p, B) ↔
    decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B) := by
  have roots (C : Blk (S.params (Model.pubOf E) hn))
      (hC : Model.Obj.Contains o (blockObj _ C)) :
      rootOf (Model.digests rho.hash o) (headerOf _ C) =
        rootOf (Model.digests rho.hash receipt) (headerOf _ C) := by
    rw [rootOf_digests_of_mem S rho o _ (List.mem_filterMap.mpr ⟨_, hC, rfl⟩),
      rootOf_digests_of_mem S rho receipt _ (List.mem_filterMap.mpr ⟨_, hc.trans hC, rfl⟩)]
  exact ⟨fun hd => decodeForward_transport B o x t p hd roots,
    fun hd => decodeForward_transport B o x t p hd (fun C hC => (roots C hC).symm)⟩

/-- A top-level signed vote envelope can only be released by its signer. Other nodes may
carry it in unsigned gossip, but cannot account for an earlier top-level release of it. -/
theorem voteForward_release_sender {i : Nat} {x : Fin (Fintype.card V)} {t : Time}
    {m : SA.Vote (Fintype.card V)}
    (h : Model.Obj.mk (.signed x .poll) (.data (.voteForward t (encodeVote m))) [voteObj m] ∈
      rho.releasesAt i) : ∃ u, rho.SendsAt (rho.key x) i u := by
  cases he : rho.events[i]? with
  | none =>
    simp only [Model.Run.releasesAt, he] at h
    exact False.elim (List.not_mem_nil h)
  | some ev =>
    cases ev with
    | restart v u =>
      simp only [Model.Run.releasesAt, he] at h
      exact False.elim (List.not_mem_nil h)
    | tick v u =>
      simp only [Model.Run.releasesAt, he] at h
      rcases rho.tick_auth _ _ _ h with ha | ⟨r, ha, _⟩
      · cases ha
      · have hx : x = rho.ownKey v := (Model.Auth.signed.inj ha).1
        subst x
        have hk : rho.key (rho.ownKey v) = v := rho.key.apply_symm_apply v
        exact ⟨u, Or.inl (by rw [hk]; exact he)⟩
    | deliver v o u =>
      simp only [Model.Run.releasesAt, he] at h
      rcases rho.deliver_auth _ _ _ _ h with ha | ⟨r, ha, _⟩
      · cases ha
      · have hx : x = rho.ownKey v := (Model.Auth.signed.inj ha).1
        subst x
        have hk : rho.key (rho.ownKey v) = v := rho.key.apply_symm_apply v
        exact ⟨u, Or.inr ⟨o, by rw [hk]; exact he⟩⟩

end Trace

end Consensus.Goldilocks.Simulation
