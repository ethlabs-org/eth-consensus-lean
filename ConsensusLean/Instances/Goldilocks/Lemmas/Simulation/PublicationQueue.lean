module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PublicationDecode
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Forwarding queues, release stamps and receipt calls -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node

variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}

/-- A canonical, nonfuture block in a recursive receipt produces an actual block-call
record even when the store refuses it. -/
theorem deliverRecs_block_call (proposer : Nat → Fin sp.n)
    (dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n))
    (hs : List (Header Info × Nat)) (self : Fin sp.n) (t : Time) (i : Nat)
    (B : Blk sp) (hslot : B.slot ≤ sp.toParams.slotOf t) :
    ∀ (os : List (Wire sp.n)) (st : NodeState (goldilocksNode sp ro)) (sub : Nat),
    (∃ o ∈ os, canonEvent sp ro hs o = some (.block B)) →
    ∃ r ∈ deliverRecs proposer dg hs self t i os st sub,
      ∃ accepted, r.label = .fg (.block B accepted) := by
  intro os
  induction os with
  | nil => intro st sub h; simp at h
  | cons o os ih =>
    intro st sub ⟨x, hx, he⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ _ he]
      have hcuts : ∃ accepted cs,
          (exec proposer dg self st t (.block B)).2 = .fg (.block B accepted) :: cs := by
        simp only [exec, onBlock, show ¬ sp.toParams.slotOf t < B.slot from not_lt.mpr hslot,
          ↓reduceIte]
        split <;> exact ⟨_, _, rfl⟩
      obtain ⟨accepted, cs, hcuts⟩ := hcuts
      have hlen : 0 < (groupRecs proposer dg self st t (Nat.pair i sub) (.block B)).length := by
        rw [length_groupRecs, hcuts]
        exact Nat.zero_lt_succ _
      refine ⟨_, List.mem_append_left _ (List.getElem_mem hlen), accepted, ?_⟩
      rw [(getElem_groupRecs proposer dg self st t (Nat.pair i sub) (.block B) 0 hlen).2.2.2.2]
      simp only [List.getElem_of_eq hcuts, List.getElem_cons_zero]
    · cases ho : canonEvent sp ro hs o with
      | none =>
        rw [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ _ ho]
        exact ih st (sub + 1) ⟨x, hx, he⟩
      | some e =>
        rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ _ ho]
        obtain ⟨r, hr, accepted, ha⟩ := ih (exec proposer dg self st t e).1
          (sub + 1) ⟨x, hx, he⟩
        exact ⟨r, List.mem_append_right _ hr, accepted, ha⟩

private def QueueStamped (t : Time) (st : State sp ro) : Prop :=
  st.now = t ∧ ∀ q ∈ st.forwards, q.1 = t

private theorem nodeTick_forwards (st : State sp ro) :
    (nodeTick st).forwards = st.forwards := by
  unfold nodeTick
  split
  · simp only [apply, acCall, List.foldl_cons, List.foldl_nil, List.flatMap_cons, List.nil_append,
      List.flatMap_nil, List.append_nil]
  · rfl

private theorem stamped_apply (t : Time) (st : State sp ro) r
    (h : QueueStamped t st) : QueueStamped t (apply st r) := by
  refine ⟨h.1, ?_⟩
  intro q hq
  rcases apply_forward_origin st r q hq with hq | ⟨B, p, _, rfl⟩
  · exact h.2 q hq
  · exact h.1

private theorem stamped_recordOwn (t : Time) (st : State sp ro) o hs
    (h : QueueStamped t st) : QueueStamped t (recordOwn st o hs) := by
  unfold recordOwn
  split
  · exact h
  · split
    · exact stamped_apply t st _ h
    · exact h
  · exact h

private theorem stamped_propose (t : Time) (st : State sp ro) s
    (h : QueueStamped t st) : QueueStamped t (propose st s).1 := by
  unfold propose
  dsimp only
  split <;> exact h

private theorem stamped_nodeTick (t : Time) (st : State sp ro)
    (h : QueueStamped t st) : QueueStamped t (nodeTick st) := by
  unfold nodeTick
  split
  · exact stamped_apply t st _ h
  · exact h

private theorem stamped_poll (t : Time) (st : State sp ro) u
    (h : QueueStamped t st) : QueueStamped t (poll st u).1 := by
  refine ⟨(poll_now st u).trans h.1, ?_⟩
  intro q hq
  rw [poll_forwards] at hq
  exact False.elim (List.not_mem_nil hq)

private theorem stamped_process (t : Time) (st : State sp ro) o hs
    (h : QueueStamped t st) : QueueStamped t (process st o hs) := by
  refine ⟨(process_now st o hs).trans h.1, ?_⟩
  intro q hq
  rcases foldl_processOne_forward_origin (fun _ => st.self)
      (fun _ _ _ _ _ => 0) hs 0 q _ st 0 hq with
    hq | ⟨B, p, r, _, _, _, _, he, _⟩
  · exact h.2 q hq
  · rw [he]
    exact h.1

section Trace

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

theorem atProposal_forwards_nil (hv : rho.ExecutionValid) (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (t : Time) :
    (shapeOf S hn (atProposal S rho v nd t)).forwards = [] := by
  rw [atProposal_shape S rho hn v nd t (poll_selected S rho hv v), nodeTick_forwards,
    poll_forwards]

omit [DecidableEq V] in
/-- A proposal duty creates forwarding entries only for successful cuts of the
corresponding proposal step. Rejected release guards create no new entries. -/
theorem proposal_duty_forward_origin (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (s : Slot) (hs : 0 < s)
    (hsel : rho.sel (.proposer s) = {runProposer S rho hn s})
    (hself : (shapeOf S hn nd).self = rho.ownKey v)
    (hslot : (S.params (Model.pubOf E) hn).toParams.slotOf (shapeOf S hn nd).now = s)
    (hst : (shapeOf S hn nd).now = (S.params (Model.pubOf E) hn).toParams.slotTime s)
    (q : Time × List (Wire (Fintype.card V)))
    (hq : q ∈ (shapeOf S hn (rho.dutyStep v nd (.propose s hs)).1).forwards) :
    q ∈ (shapeOf S hn nd).forwards ∨ ∃ B, ∃ p : Option (Wire (Fintype.card V)),
      .fg (.block B true) ∈ (Node.tickStep (runProposer S rho hn) (digestOf S rho)
        (rho.ownKey v) (shapeOf S hn nd).node (shapeOf S hn nd).now
        (encodeTxs nd.st.2) .proposal).2 ∧
      q = ((shapeOf S hn nd).now, p.toList ++ [blockObj (S.params (Model.pubOf E) hn) B]) := by
  have hact2 := act_propose_snd S hn nd s hs
  have hact1 := shapeOf_act_propose S hn nd.st s hs
  unfold Model.Run.dutyStep at hq
  split at hq
  · rename_i hselected
    change rho.ownKey v ∈ rho.sel (.proposer s) at hselected
    have hp : Proposes (P := (S.params (Model.pubOf E) hn).toParams)
        (runProposer S rho hn) (rho.ownKey v) (shapeOf S hn nd).now := by
      rw [hst, proposes_iff S hn _ _ s hs]
      exact (Finset.mem_singleton.mp (hsel ▸ hselected)).symm
    generalize (Model.protoOf (compiled (goldilocks S)) E).act nd.st (.propose s hs) = a
      at hact1 hact2 hq
    dsimp only at hq
    simp only [propose] at hact1 hact2
    simp only [Node.tickStep, hp, ite_true]
    rcases hr : (acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now).2.2 with _ | ⟨d, p⟩
    · simp only [hr] at hact1 hact2
      erw [hact2] at hq
      simp only [Option.map_none, Option.toList_none, Model.Run.signedCandidate] at hq
      split at hq
      all_goals
        change q ∈ (a.1.1 hn).forwards at hq
        rw [hact1] at hq
        exact Or.inl hq
    · simp only [hr] at hact1 hact2
      erw [hact2] at hq
      have hrole : (Model.protoOf (compiled (goldilocks S)) E).role (.propose s hs) =
          .proposer s := rfl
      simp only [Option.map, Option.toList_some, Model.Run.signedCandidate, hrole,
        hselected, ↓reduceIte] at hq
      dsimp only [List.map] at hq
      unfold Model.releaseAll at hq
      split at hq
      · change q ∈ (recordOwn (a.1.1 hn) _ _).forwards at hq
        rw [hact1] at hq
        simp only [recordOwn, decodeInfo_encodeInfo] at hq
        erw [rootOf_digests_item] at hq
        dsimp only at hq
        have hb := blockOf_eq_mkBlock S rho hn (rho.ownKey v)
          (acProposal (shapeOf S hn nd).node (shapeOf S hn nd).now).1.fg
          (shapeOf S hn nd).now (encodeTxs nd.st.2) d.head p s hslot
        erw [hb] at hq
        rcases apply_forward_origin (sp := S.params (Model.pubOf E) hn) (ro := S.ro _)
            _ _ q hq with hq | ⟨B, parent, hB, hq⟩
        · exact Or.inl hq
        · refine Or.inr ⟨B, parent, ?_, hq⟩
          simp only [Node.proposeBlock]
          exact List.mem_cons_of_mem _ (by simpa only [hself] using hB)
      · exact Or.inl (by change q ∈ (a.1.1 hn).forwards at hq; simpa [hact1] using hq)
  · exact Or.inl hq

omit [DecidableEq V] in
/-- A decoded envelope's child is decoded identically inside any enclosing receipt.
Both roots are obtained from the engine hash of the child's header. -/
theorem decoded_forward_child_in_receipt
    {o receipt : Wire (Fintype.card V)} {x : Fin (Fintype.card V)} {t : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hc : Model.Obj.Contains receipt o)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) :
    blockObj (S.params (Model.pubOf E) hn) B ∈ receipt.parts ∧
      decodeBlock (S.params (Model.pubOf E) hn) (Model.digests rho.hash receipt)
        (blockObj (S.params (Model.pubOf E) hn) B) = some B := by
  have hchild : Model.Obj.Contains o (blockObj (S.params (Model.pubOf E) hn) B) := by
    rw [forwardObj_of_decodeForward _ _ _ _ _ _ hd]
    apply Model.Obj.Contains.step (c := blockObj _ B)
    · exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact Model.Obj.Contains.refl _
  have hreceipt := hc.trans hchild
  refine ⟨hreceipt, decodeBlock_transport (decodeForward_child hd).1 ?_⟩
  rw [rootOf_digests_of_mem S rho receipt _
    (List.mem_filterMap.mpr ⟨blockObj _ B, hreceipt, rfl⟩)]
  rw [rootOf_digests_of_mem S rho o _
    (List.mem_filterMap.mpr ⟨blockObj _ B, hchild, rfl⟩)]

omit [DecidableEq V] in
/-- A decodable forwarding candidate of a poll comes from its pre-duty forwarding
queue, not the ordinary outbox emission (which carries no child). -/
theorem poll_candidate_forward_queue (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (u : Nat)
    {o : Wire (Fintype.card V)} {t : Time} {p : Option (Wire (Fintype.card V))}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (ho : o ∈ rho.signedCandidate v (.poll u)
      ((Model.protoOf (compiled (goldilocks S)) E).act nd.st (.poll u)).2)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey v, t, p, B)) :
    (t, p.toList ++ [blockObj (S.params (Model.pubOf E) hn) B]) ∈
      (shapeOf S hn nd).forwards := by
  obtain ⟨m, cs, hm, _, rfl⟩ := rho.mem_signedCandidate.mp ho
  rw [act_poll_snd S hn, (poll_outbox _ _).2] at hm
  rcases List.mem_append.mp hm with hm | hm
  swap
  · obtain ⟨⟨stamp, vote⟩, _, he⟩ := List.mem_map.mp hm
    cases he
    have heq := forwardObj_of_decodeForward _ _ _ _ _ _ hd
    have hmsg := congrArg Model.Obj.msg heq
    cases hmsg
  rcases List.mem_append.mp hm with hm | hm
  · cases hh : (pollPre (shapeOf S hn nd)).outbox.head? with
    | none =>
      simp only [hh, Option.map_none, Option.toList_none] at hm
      exact False.elim (List.not_mem_nil hm)
    | some b =>
      simp only [hh, Option.map_some, Option.toList_some] at hm
      have he := List.mem_singleton.mp hm
      cases he
      have heq := forwardObj_of_decodeForward _ _ _ _ _ _ hd
      have hc := congrArg Model.Obj.carried heq
      change [] = p.toList ++ [blockObj (S.params (Model.pubOf E) hn) B] at hc
      cases p <;> simp at hc
  · obtain ⟨⟨stamp, children⟩, hq, he⟩ := List.mem_map.mp hm
    cases he
    have heq := forwardObj_of_decodeForward (Model.digests rho.hash
      (.mk (.signed (rho.ownKey v) .poll) (.data (.forward stamp)) children))
      _ _ _ _ _ hd
    simp [forwardObj] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact hq

omit [DecidableEq V] in
/-- A released poll envelope retains its pre-duty queue witness. -/
theorem poll_release_forward_queue (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (u : Nat)
    {o : Wire (Fintype.card V)} {t : Time} {p : Option (Wire (Fintype.card V))}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (ho : o ∈ (rho.dutyStep v nd (.poll u)).2)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey v, t, p, B)) :
    (t, p.toList ++ [blockObj (S.params (Model.pubOf E) hn) B]) ∈
      (shapeOf S hn nd).forwards := by
  unfold Model.Run.dutyStep at ho
  split at ho
  · exact poll_candidate_forward_queue S rho hn v nd u
      (Model.releaseAll_subset _ _ _ _ o ho) hd
  · exact False.elim (List.not_mem_nil ho)

/-- An honestly signed forwarding envelope in seen closure has an actual prior release
by that signer. This is authentication provenance, not yet an acceptance witness. -/
theorem decoded_forward_seen_released (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {i : Nat} {v : V} (hi : i ≤ rho.events.length)
    {o : Wire (Fintype.card V)} {x : Fin (Fintype.card V)} {t : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (ho : o ∈ Model.closure (rho.stateBefore i v).seen)
    (hx : rho.key x ∉ rho.faultyAt 0)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) :
    ∃ j < i, ∃ u, rho.SendsAt (rho.key x) j u ∧ o ∈ rho.releasesAt j := by
  apply rho.signed_seen_released hv hi ho
    (by simpa only [rho.faultyAt_eq_zero hf] using hx)
  change o.signer?.map rho.key = some (rho.key x)
  rw [decodeForward_signer hd]
  rfl

omit [DecidableEq V] in
private theorem duty_forward_stamp (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
    (d : (Model.protoOf (compiled (goldilocks S)) E).Duty) (u : Time)
    (hs : QueueStamped u (shapeOf S hn nd))
    {o : Wire (Fintype.card V)} {t : Time} {p : Option (Wire (Fintype.card V))}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (ho : o ∈ rho.signedCandidate v d ((Model.protoOf (compiled (goldilocks S)) E).act nd.st d).2)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey v, t, p, B)) : t = u := by
  cases d with
  | poll n => exact hs.2 _ (poll_candidate_forward_queue S rho hn v nd n ho hd)
  | act s k => exact k.elim
  | propose s hpos =>
    obtain ⟨m, cs, _, _, rfl⟩ := rho.mem_signedCandidate.mp ho
    have he := forwardObj_of_decodeForward _ _ _ _ _ _ hd
    have ha := congrArg Model.Obj.auth he
    change Model.Auth.signed (rho.ownKey v) (ShapeRole.proposer (Kind := Empty) s) =
      .signed (rho.ownKey v) ShapeRole.poll at ha
    cases ha
  | pollPropose n =>
    have hempty : ((Model.protoOf (compiled (goldilocks S)) E).act nd.st (.pollPropose n)).2 =
        [] := by
      simp only [Model.protoOf, compiled, compile, goldilocks, dite_eq_left hn, goldilocksShape]
      rfl
    obtain ⟨m, cs, hm, _, _⟩ := rho.mem_signedCandidate.mp ho
    rw [hempty] at hm
    exact False.elim (List.not_mem_nil hm)

omit [DecidableEq V] in
theorem gossip_not_forward
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (u : Time)
    {o : Wire (Fintype.card V)} {x : Fin (Fintype.card V)} {t : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (ho : o ∈ Model.gossipCandidates (Model.protoOf (compiled (goldilocks S)) E) nd.st u)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) : False := by
  obtain ⟨mc, _, rfl⟩ := Model.mem_gossipCandidates.mp ho
  have hsign := decodeForward_signer hd
  change none = some x at hsign
  cases hsign

private theorem dutyBatches_forward_stamp (v : V) (u : Time) :
    ∀ (ds : List (Model.protoOf (compiled (goldilocks S)) E).Duty)
      (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)),
    QueueStamped u (shapeOf S hn nd) →
    ∀ b ∈ dutyBatches rho v nd ds, ∀ o ∈ b.candidates,
    ∀ t p B, decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey v, t, p, B) → t = u := by
  intro ds
  induction ds with
  | nil => intro nd hs b hb; rw [dutyBatches_nil] at hb; exact False.elim (List.not_mem_nil hb)
  | cons d ds ih =>
    intro nd hs b hb o ho t p B hd
    rw [dutyBatches_cons] at hb
    rcases List.mem_cons.mp hb with rfl | hb
    · split at ho
      · exact duty_forward_stamp S rho hn v nd d u hs ho hd
      · exact False.elim (List.not_mem_nil ho)
    · exact ih _ (dutyStep_pres S rho hn (QueueStamped u)
        (stamped_recordOwn u) (stamped_propose u) (stamped_nodeTick u) (stamped_poll u)
        v nd d hs) b hb o ho t p B hd

private theorem runDuties_candidate_batch (v : V) :
    ∀ ds (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) o,
    o ∈ (rho.runDuties v nd ds).2 →
    ∃ b ∈ dutyBatches rho v nd ds, o ∈ b.candidates := by
  intro ds
  induction ds with
  | nil => intro nd o ho; rw [rho.runDuties_nil] at ho; exact False.elim (List.not_mem_nil ho)
  | cons d ds ih =>
    intro nd o ho
    rw [rho.runDuties_cons] at ho
    rcases List.mem_append.mp ho with ho | ho
    · rw [dutyBatches_cons]
      unfold Model.Run.dutyStep at ho
      split at ho
      · rename_i hsel
        refine ⟨_, List.mem_cons_self, ?_⟩
        simp only [hsel, ↓reduceIte]
        exact Model.releaseAll_subset _ _ _ _ o ho
      · exact False.elim (List.not_mem_nil ho)
    · obtain ⟨b, hb, ho⟩ := ih _ o ho
      rw [dutyBatches_cons]
      exact ⟨b, List.mem_cons_of_mem _ hb, ho⟩

/-- Every engine release belongs to a concrete event batch. This inverse needs no
acceptance or provenance premise. -/
theorem released_candidate_batch {i : Nat} {v : V} {u : Time}
    (he : rho.SendsAt v i u) {o : Wire (Fintype.card V)} (ho : o ∈ rho.releasesAt i) :
    ∃ b ∈ eventBatches rho i, o ∈ b.candidates := by
  rcases he with he | ⟨receipt, he⟩
  · rw [eventBatches_eq, he]
    simp only [Model.Run.releasesAt, he, Model.Run.tick] at ho
    split at ho
    · rename_i hw
      simp only [hw, ↓reduceIte]
      rcases List.mem_append.mp ho with ho | ho
      · obtain ⟨b, hb, ho⟩ := runDuties_candidate_batch S rho v _ _ o ho
        exact ⟨b, List.mem_append_left _ hb, ho⟩
      · exact ⟨_, List.mem_append_right _ List.mem_cons_self,
          Model.releaseAll_subset (P := Model.protoOf (compiled (goldilocks S)) E) _ _ _ _ o ho⟩
    · exact False.elim (List.not_mem_nil ho)
  · rw [eventBatches_eq, he]
    simp only [Model.Run.releasesAt, he, Model.Run.deliver] at ho
    rcases List.mem_append.mp ho with ho | ho
    · obtain ⟨b, hb, ho⟩ := runDuties_candidate_batch S rho v _ _ o ho
      exact ⟨b, List.mem_append_left _ hb, ho⟩
    · exact ⟨_, List.mem_append_right _ List.mem_cons_self,
        Model.releaseAll_subset (P := Model.protoOf (compiled (goldilocks S)) E) _ _ _ _ o ho⟩

/-- A forwarding candidate in an actual event batch has that event's timestamp. -/
theorem eventBatches_forward_stamp (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {u : Time} (he : rho.SendsAt v i u)
    (b : ReleaseBatch (Model.protoOf (compiled (goldilocks S)) E))
    (hb : b ∈ eventBatches rho i) {o : Wire (Fintype.card V)} (ho : o ∈ b.candidates)
    {t : Time} {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey v, t, p, B)) : t = u := by
  rcases he with he | ⟨receipt, he⟩
  · rw [eventBatches_eq, he] at hb
    simp only at hb
    split at hb
    · rcases List.mem_append.mp hb with hb | hb
      · apply dutyBatches_forward_stamp S rho hn v u _ _ ?_ b hb o ho t p B hd
        change QueueStamped u { (rho.stateBefore i v).st.1 hn with now := u }
        rw [← stateAt_eq S rho hn v i]
        refine ⟨rfl, ?_⟩
        intro q hq
        change q ∈ (stateAt S rho hn v i).forwards at hq
        rw [forwards_empty S rho hn hv v i] at hq
        exact False.elim (List.not_mem_nil hq)
      · have heq := List.mem_singleton.mp hb
        subst b
        exact False.elim (gossip_not_forward S rho hn _ u ho hd)
    · exact False.elim (List.not_mem_nil hb)
  · rw [eventBatches_eq, he] at hb
    rcases List.mem_append.mp hb with hb | hb
    · apply dutyBatches_forward_stamp S rho hn v u _ _ ?_ b hb o ho t p B hd
      change QueueStamped u
        (process ((rho.stateBefore i v).st.1 hn) receipt (Model.digests rho.hash receipt))
      rw [← stateAt_eq S rho hn v i]
      apply stamped_process
      refine ⟨(now_eq_lastClock S rho hn hv v i).trans (lastClock_deliver S rho hv he), ?_⟩
      intro q hq
      rw [forwards_empty S rho hn hv v i] at hq
      exact False.elim (List.not_mem_nil hq)
    · have heq := List.mem_singleton.mp hb
      subst b
      exact False.elim (gossip_not_forward S rho hn _ u ho hd)

/-- An actually released forwarding envelope has the sending event's timestamp. -/
theorem released_forward_stamp (hv : rho.ExecutionValid) {i : Nat} {v : V} {u : Time}
    (he : rho.SendsAt v i u) {o : Wire (Fintype.card V)} (ho : o ∈ rho.releasesAt i)
    {t : Time} {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey v, t, p, B)) : t = u := by
  obtain ⟨b, hb, ho⟩ := released_candidate_batch S rho he ho
  exact eventBatches_forward_stamp S rho hn hv he b hb ho hd

/-- Every actual forwarding publication bears its own event's time. -/
theorem publication_forward_stamp (hv : rho.ExecutionValid)
    (r : Publication (Model.protoOf (compiled (goldilocks S)) E))
    (hr : (publisherExecution S rho).actual r) {t : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash r.object) r.object =
      some (r.origin, t, p, B)) : t = (publisherExecution S rho).eventTime r.event := by
  apply released_forward_stamp S rho hn hv ((publisherExecution S rho).actual_event r hr)
    ((publisherExecution S rho).actual_release r hr) (p := p) (B := B)
  have hk : rho.ownKey (rho.key r.origin) = r.origin := rho.key.symm_apply_apply _
  rw [hk]
  exact hd

/-- An indexed successful canonical cut supplies acceptance at its actual recorded time.
In particular this bridge never turns a refused block call into acceptance. -/
theorem acceptAt_of_allCuts {k : Nat} {r : CutRec (S.params (Model.pubOf E) hn) (S.ro _)}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (hr : (allCuts S rho hn)[k]? = some r) (hb : r.label = .fg (.block B true)) :
    (simTrace S rho hn).AcceptAt r.node k B ∧ (simTrace S rho hn).time k = r.time := by
  constructor
  · exact ⟨by simp [simTrace_node, hr], by simp [simTrace_label, hr, hb]⟩
  · simp [simTrace_time, hr]

/-- An acceptance in an actual event's record list gives the required strict event-prefix
bound; no search for a merely similar successful label is involved. -/
theorem acceptAt_of_eventCuts {i : Nat} (hi : i < rho.events.length)
    {r : CutRec (S.params (Model.pubOf E) hn) (S.ro _)}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (hr : r ∈ eventCuts S rho hn i) (hb : r.label = .fg (.block B true)) :
    ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).AcceptAt r.node k B ∧
      (simTrace S rho hn).time k = r.time := by
  obtain ⟨j, hj, he⟩ := List.getElem_of_mem hr
  have hk : (allCuts S rho hn)[cutMap S rho hn i + j]? = some r := by
    rw [allCuts_getElem?_add S rho hn i j hi hj, List.getElem?_eq_getElem hj, he]
  refine ⟨cutMap S rho hn i + j, ?_, acceptAt_of_allCuts S rho hn hk hb⟩
  rw [cutMap_succ]
  omega

/-- The processing phase of an actual delivery queues only wrappers for acceptances in
that delivery, at its actual time. The event-boundary queue is empty, not a premise. -/
theorem delivery_forward_acceptance_decoded (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {o : Wire (Fintype.card V)} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (q : Time × List (Wire (Fintype.card V)))
    (hq : q ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).forwards) :
    ∃ B, ∃ p : Option (Wire (Fintype.card V)), ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).AcceptAt (rho.ownKey v) k B ∧
      (simTrace S rho hn).time k = t ∧
      q = (t, p.toList ++ [blockObj (S.params (Model.pubOf E) hn) B]) ∧
      decodeBlock (S.params (Model.pubOf E) hn) (Model.digests rho.hash o)
        (blockObj (S.params (Model.pubOf E) hn) B) = some B ∧
      Model.Obj.Contains o (blockObj (S.params (Model.pubOf E) hn) B) := by
  have ht : (stateAt S rho hn v i).now = t :=
    (now_eq_lastClock S rho hn hv v i).trans (lastClock_deliver S rho hv he)
  rcases foldl_processOne_forward_origin (runProposer S rho hn) (digestOf S rho)
      (Model.digests rho.hash o) i q _ (stateAt S rho hn v i) 0 hq with
    h | ⟨B, p, r, hr, hb, hn', ht', hq, hd, ho⟩
  · rw [forwards_empty S rho hn hv v i] at h
    exact False.elim (List.not_mem_nil h)
  · simp only [self_eq_ownKey, ht] at hr hn' ht' hq
    have hr' : r ∈ eventCuts S rho hn i := by
      rw [eventCuts_deliver S rho hn i v o t he]
      exact hr
    obtain ⟨k, hk, ha, htime⟩ := acceptAt_of_eventCuts S rho hn
      (List.getElem?_eq_some_iff.mp he).1 hr' hb
    exact ⟨B, p, k, hk, hn' ▸ ha, htime.trans ht', hq, hd,
      contains_of_mem_delivered ho⟩

/-- The queue-only projection of exact delivery acceptance provenance. -/
theorem delivery_forward_acceptance (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {o : Wire (Fintype.card V)} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (q : Time × List (Wire (Fintype.card V)))
    (hq : q ∈ (process (stateAt S rho hn v i) o (Model.digests rho.hash o)).forwards) :
    ∃ B, ∃ p : Option (Wire (Fintype.card V)), ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).AcceptAt (rho.ownKey v) k B ∧
      (simTrace S rho hn).time k = t ∧
      q = (t, p.toList ++ [blockObj (S.params (Model.pubOf E) hn) B]) := by
  obtain ⟨B, p, k, hk, ha, ht, hq, _⟩ :=
    delivery_forward_acceptance_decoded S rho hn hv he q hq
  exact ⟨B, p, k, hk, ha, ht, hq⟩

/-- Digest-backed decoding identifies the exact accepted block behind a delivery queue
entry. Wire equality supplies its header, not its root. -/
theorem delivery_decoded_forward_acceptance (hv : rho.ExecutionValid)
    {i : Nat} {v : V} {receipt o : Wire (Fintype.card V)} {u t : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.deliver v receipt u))
    (hq : (t, p.toList ++ [blockObj (S.params (Model.pubOf E) hn) B]) ∈
      (process (stateAt S rho hn v i) receipt (Model.digests rho.hash receipt)).forwards)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey v, t, p, B)) :
    ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).AcceptAt (rho.ownKey v) k B ∧
      (simTrace S rho hn).time k = t := by
  obtain ⟨C, p', k, hk, ha, ht, heq, hc, hcontains⟩ :=
    delivery_forward_acceptance_decoded S rho hn hv he _ hq
  have htime : t = u := congrArg Prod.fst heq
  have hwire : blockObj (S.params (Model.pubOf E) hn) B = blockObj _ C := by
    have hlast := congrArg List.getLast? (congrArg Prod.snd heq)
    cases p <;> cases p' <;> simpa using hlast
  have hBC : B = C := by
    have hchild : Model.Obj.Contains o (blockObj (S.params (Model.pubOf E) hn) C) := by
      rw [← hwire, forwardObj_of_decodeForward _ _ _ _ _ _ hd]
      apply Model.Obj.Contains.step
        (List.mem_append_right _ (List.mem_singleton_self _)) (Model.Obj.Contains.refl _)
    have hroot (r : Wire (Fintype.card V))
        (h : Model.Obj.Contains r (blockObj (S.params (Model.pubOf E) hn) C)) :
        rootOf (Model.digests rho.hash r) (headerOf (S.params (Model.pubOf E) hn) C) =
          some (rho.hash (headerOf (S.params (Model.pubOf E) hn) C)) := by
      exact rootOf_digests_of_mem S rho r _ (List.mem_filterMap.mpr ⟨_, h, rfl⟩)
    have hc' := decodeBlock_transport hc ((hroot o hchild).trans (hroot receipt hcontains).symm)
    rw [← hwire, (decodeForward_child hd).1] at hc'
    exact Option.some.inj hc'
  subst C
  exact ⟨k, hk, ha, ht.trans htime.symm⟩

/-- A decoded forwarding object released by a delivery originates in an actual
acceptance in that delivery, with the same root and timestamp. -/
theorem delivery_released_forward_acceptance (hv : rho.ExecutionValid)
    {i : Nat} {v : V} {receipt o : Wire (Fintype.card V)} {u t : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.deliver v receipt u))
    (ho : o ∈ rho.releasesAt i)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey v, t, p, B)) :
    ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).AcceptAt (rho.ownKey v) k B ∧
      (simTrace S rho hn).time k = t := by
  obtain ⟨b, hb, ho⟩ := released_candidate_batch S rho (Or.inr ⟨receipt, he⟩) ho
  rw [eventBatches_eq, he] at hb
  rcases List.mem_append.mp hb with hb | hb
  · have hu := (hv.in_horizon _ (List.mem_of_getElem? he)).1
    rw [deliverDuties_eq S u hu] at hb
    erw [dutyBatches_cons, dutyBatches_nil] at hb
    have hb' := List.mem_singleton.mp hb
    subst b
    split at ho
    · have hq := poll_candidate_forward_queue S rho hn v _ u.toNat ho hd
      apply delivery_decoded_forward_acceptance S rho hn hv he _ hd
      rw [stateAt_eq]
      exact hq
    · exact False.elim (List.not_mem_nil ho)
  · have hb' := List.mem_singleton.mp hb
    subst b
    exact False.elim (gossip_not_forward S rho hn _ u ho hd)

/-- Receipt witnesses require only a block call, including a refused call. -/
theorem blockCallAt_of_allCuts {k : Nat}
    {r : CutRec (S.params (Model.pubOf E) hn) (S.ro _)}
    {B : Blk (S.params (Model.pubOf E) hn)} {accepted : Bool}
    (hr : (allCuts S rho hn)[k]? = some r)
    (hb : r.label = .fg (.block B accepted)) :
    (simTrace S rho hn).BlockCallAt r.node k B ∧
      (simTrace S rho hn).time k = r.time := by
  constructor
  · exact ⟨accepted, by simp [simTrace_node, hr], by simp [simTrace_label, hr, hb]⟩
  · simp [simTrace_time, hr]

/-- Once its authenticated stamp is no later than receipt, a forwarding envelope's
child has a real processing call in that receipt, whether accepted or refused. -/
theorem received_forward_blockCall {i : Nat} {v : V}
    {receipt o : Wire (Fintype.card V)} {x : Fin (Fintype.card V)} {t u : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.deliver v receipt u))
    (hc : Model.Obj.Contains receipt o)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) (htu : t ≤ u) :
    ∃ k < cutMap S rho hn (i + 1),
      (simTrace S rho hn).BlockCallAt (rho.ownKey v) k B ∧
      (simTrace S rho hn).time k = u := by
  obtain ⟨hmem, hdecode⟩ := decoded_forward_child_in_receipt S rho hn hc hd
  have hs : (S.params (Model.pubOf E) hn).toParams.slotTime B.slot ≤ u :=
    (decodeForward_child hd).2.trans htu
  have hslot : B.slot ≤ (S.params (Model.pubOf E) hn).toParams.slotOf u := by
    apply Nat.le_findGreatest _ hs
    have hcast := (le_slotTime (S.params (Model.pubOf E) hn).toParams B.slot).trans hs
    exact (Int.le_toNat (le_trans (Int.natCast_nonneg _) hcast)).2 hcast
  obtain ⟨r, hr, accepted, hb⟩ := deliverRecs_block_call (runProposer S rho hn)
    (digestOf S rho) (Model.digests rho.hash receipt) (rho.ownKey v) u i B hslot
    (delivered _ receipt) (stateAt S rho hn v i).node 0
    ⟨blockObj _ B, hmem, by simp only [canonEvent, hdecode]⟩
  obtain ⟨hn', ht', _⟩ := mem_deliverRecs (sp := S.params (Model.pubOf E) hn)
    (ro := S.ro _) (runProposer S rho hn) (digestOf S rho)
    (rho.ownKey v) (Model.digests rho.hash receipt) u i hr
  have hr' : r ∈ eventCuts S rho hn i := by
    rw [eventCuts_deliver S rho hn i v receipt u he]
    exact hr
  obtain ⟨j, hj, heq⟩ := List.getElem_of_mem hr'
  have hk : (allCuts S rho hn)[cutMap S rho hn i + j]? = some r := by
    rw [allCuts_getElem?_add S rho hn i j (List.getElem?_eq_some_iff.mp he).1 hj,
      List.getElem?_eq_getElem hj, heq]
  obtain ⟨hcall, htime⟩ := blockCallAt_of_allCuts S rho hn hk hb
  refine ⟨cutMap S rho hn i + j, ?_, hn' ▸ hcall, htime.trans ht'⟩
  rw [cutMap_succ]
  omega

/-- Authentication and event order bound an honest forwarding envelope's stamp by
its receipt time, even when the envelope is nested inside the delivered object. -/
theorem received_forward_stamp_le (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {i : Nat} {v : V}
    {receipt o : Wire (Fintype.card V)} {x : Fin (Fintype.card V)} {t u : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (he : rho.events[i]? = some (.deliver v receipt u))
    (hc : Model.Obj.Contains receipt o) (hx : rho.key x ∉ rho.faultyAt 0)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) : t ≤ u := by
  have hsign : rho.signerOf o = some (rho.key x) := by
    change o.signer?.map rho.key = some (rho.key x)
    rw [decodeForward_signer hd]
    rfl
  obtain ⟨j, s, hj, hs, ho⟩ := hv.unforgeable i v receipt u he o hc (rho.key x) hsign
    (by simpa only [rho.faultyAt_eq_zero hf] using hx)
  have hd' : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (rho.ownKey (rho.key x), t, p, B) := by
    simpa only [Model.Run.ownKey, Equiv.symm_apply_apply] using hd
  have ht := released_forward_stamp S rho hn hv hs ho hd'
  rw [ht]
  obtain ⟨hi, hei⟩ := List.getElem?_eq_some_iff.mp he
  rcases hs with hs | ⟨receipt', hs⟩
  all_goals
    obtain ⟨hj', hej⟩ := List.getElem?_eq_some_iff.mp hs
    have horder := List.pairwise_iff_getElem.mp hv.sorted j i hj' hi hj
    rw [hej, hei] at horder
    rcases horder with hlt | ⟨heq, _⟩
    · exact le_of_lt hlt
    · exact le_of_eq heq

omit [DecidableEq V] in
private theorem batch_closure_source (v : V)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (cs)
    {o : Wire (Fintype.card V)}
    (ho : o ∈ Model.closure (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E)
      rho.hash (rho.ownKey v) nd cs).1.seen) :
    o ∈ Model.closure nd.seen ∨
      o ∈ (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E)
        rho.hash (rho.ownKey v) nd cs).2 := by
  let Q := fun c => c = o → o ∈ Model.closure nd.seen ∨
    o ∈ (Model.releaseAll (Model.protoOf (compiled (goldilocks S)) E)
      rho.hash (rho.ownKey v) nd cs).2
  have h := Model.releaseAll_preserves rho.hash (rho.ownKey v) Q nd cs
    (fun c hc b hb he => Or.inl (he ▸ (Model.mem_closure_iff _ _).mpr ⟨c, hc, hb⟩))
    (fun c hc he => Or.inr (he ▸ hc))
  obtain ⟨c, hc, hco⟩ := (Model.mem_closure_iff _ _).mp ho
  exact h.1 c hc o hco rfl

omit [DecidableEq V] in
private theorem duties_closure_source (v : V) :
    ∀ ds (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
      (o : Wire (Fintype.card V)),
    o ∈ Model.closure (rho.runDuties v nd ds).1.seen →
      o ∈ Model.closure nd.seen ∨ o ∈ (rho.runDuties v nd ds).2 := by
  intro ds
  induction ds with
  | nil => intro nd o ho; exact Or.inl ho
  | cons d ds ih =>
    intro nd o ho
    rw [rho.runDuties_cons] at ho ⊢
    rcases ih _ o ho with ho | ho
    · unfold Model.Run.dutyStep at ho ⊢
      split at ho
      · rename_i hsel
        simp only [hsel, ↓reduceIte]
        rcases batch_closure_source S rho v _ _ ho with ho | ho
        · exact Or.inl ho
        · exact Or.inr (List.mem_append_left _ ho)
      · rename_i hsel
        exact Or.inl ho
    · exact Or.inr (List.mem_append_right _ ho)

/-- A held object originates in an exact local release or an enclosing receipt. Nested
release payloads do not create a third case: the release guard required them earlier. -/
theorem held_release_or_receipt {v : V} {i : Nat} {o : Wire (Fintype.card V)}
    (ho : o ∈ Model.closure (rho.stateBefore i v).seen) :
    ∃ j < i, ∃ t, (rho.SendsAt v j t ∧ o ∈ rho.releasesAt j) ∨
      ∃ receipt, rho.events[j]? = some (.deliver v receipt t) ∧
        Model.Obj.Contains receipt o := by
  induction i with
  | zero => exact False.elim (List.not_mem_nil ho)
  | succ i ih =>
    have old (h : o ∈ Model.closure (rho.stateBefore i v).seen) :
        ∃ j < i + 1, ∃ t, (rho.SendsAt v j t ∧ o ∈ rho.releasesAt j) ∨
          ∃ receipt, rho.events[j]? = some (.deliver v receipt t) ∧
            Model.Obj.Contains receipt o := by
      obtain ⟨j, hj, t, h⟩ := ih h
      exact ⟨j, by omega, t, h⟩
    cases he : rho.events[i]? with
    | none =>
      have hh : rho.stateBefore (i + 1) = rho.stateBefore i := by
        simp [Model.Run.stateBefore, List.take_add_one, he]
      exact old (hh ▸ ho)
    | some ev =>
      rw [rho.stateBefore_succ he] at ho
      by_cases hnode : ev.node = v
      · cases ev with
        | restart w t =>
          simp only [Model.Event.node] at hnode
          subst w
          exact old (by simpa only [Model.Run.step, Function.update_self] using ho)
        | tick w t =>
          simp only [Model.Event.node] at hnode
          subst w
          simp only [Model.Run.step, Function.update_self, Model.Run.tick] at ho
          split at ho
          · rcases batch_closure_source S rho v _ _ ho with ho | ho
            · rcases duties_closure_source S rho v _ _ o ho with ho | ho
              · exact old ho
              · refine ⟨i, by omega, t, Or.inl ⟨Or.inl he, ?_⟩⟩
                simp only [Model.Run.releasesAt, he, Model.Run.tick]
                split
                · exact List.mem_append_left _ ho
                · next hn => exact (hn ‹_›).elim
            · refine ⟨i, by omega, t, Or.inl ⟨Or.inl he, ?_⟩⟩
              simp only [Model.Run.releasesAt, he, Model.Run.tick]
              split
              · exact List.mem_append_right _ ho
              · next hn => exact (hn ‹_›).elim
          · exact old ho
        | deliver w receipt t =>
          simp only [Model.Event.node] at hnode
          subst w
          simp only [Model.Run.step, Function.update_self, Model.Run.deliver] at ho
          rcases batch_closure_source S rho v _ _ ho with ho | ho
          · rcases duties_closure_source S rho v _ _ o ho with ho | ho
            · rw [Model.closure_append] at ho
              rcases List.mem_append.mp ho with ho | ho
              · exact old ho
              · obtain ⟨r, hr, hc⟩ := (Model.mem_closure_iff _ _).mp ho
                have hr' := List.mem_singleton.mp hr
                subst r
                exact ⟨i, by omega, t, Or.inr ⟨receipt, he, hc⟩⟩
            · refine ⟨i, by omega, t, Or.inl ⟨Or.inr ⟨receipt, he⟩, ?_⟩⟩
              simp only [Model.Run.releasesAt, he, Model.Run.deliver]
              exact List.mem_append_left _ ho
          · refine ⟨i, by omega, t, Or.inl ⟨Or.inr ⟨receipt, he⟩, ?_⟩⟩
            simp only [Model.Run.releasesAt, he, Model.Run.deliver]
            exact List.mem_append_right _ ho
      · cases ev with
        | tick w t | deliver w receipt t | restart w t =>
          simp only [Model.Event.node] at hnode
          exact old (by
            simpa only [Model.Run.step, Function.update_of_ne (Ne.symm hnode)] using ho)

/-- Held honest forwarding envelopes either were released locally, or already have a
real receipt call before the requested cut. The latter may be a refused block call. -/
theorem held_forward_release_or_call (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {v : V} {i : Nat}
    {o : Wire (Fintype.card V)} {x : Fin (Fintype.card V)} {t : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (ho : o ∈ Model.closure (rho.stateBefore i v).seen) (hx : rho.key x ∉ rho.faultyAt 0)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) :
    (∃ j < i, ∃ u, rho.SendsAt v j u ∧ o ∈ rho.releasesAt j) ∨
      ∃ k < cutMap S rho hn i, t ≤ (simTrace S rho hn).time k ∧
        (simTrace S rho hn).BlockCallAt (rho.ownKey v) k B := by
  obtain ⟨j, hj, u, h⟩ := held_release_or_receipt S rho ho
  rcases h with ⟨he, hr⟩ | ⟨receipt, he, hc⟩
  · exact Or.inl ⟨j, hj, u, he, hr⟩
  · have htu := received_forward_stamp_le S rho hn hf hv he hc hx hd
    obtain ⟨k, hk, hcall, htime⟩ := received_forward_blockCall S rho hn he hc hd htu
    exact Or.inr ⟨k, hk.trans_le (cutMap_mono S rho hn (Nat.succ_le_of_lt hj)),
      htime ▸ htu, hcall⟩

private theorem dutyBatches_signer (v : V) :
    ∀ ds (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) b,
    b ∈ dutyBatches rho v nd ds → ∀ o ∈ b.candidates,
      o.signer? = some (rho.ownKey v) := by
  intro ds
  induction ds with
  | nil => intro nd b hb; rw [dutyBatches_nil] at hb; exact False.elim (List.not_mem_nil hb)
  | cons d ds ih =>
    intro nd b hb o ho
    rw [dutyBatches_cons] at hb
    rcases List.mem_cons.mp hb with rfl | hb
    · split at ho
      · obtain ⟨m, cs, _, _, rfl⟩ := rho.mem_signedCandidate.mp ho
        rfl
      · exact False.elim (List.not_mem_nil ho)
    · exact ih _ b hb o ho

/-- A signed forwarding object released locally is signed by that node. Carried
forwarding objects are deliberately not claimed to have the local signer. -/
theorem released_forward_signer {i : Nat} {v : V} {u : Time}
    (he : rho.SendsAt v i u) {o : Wire (Fintype.card V)} (ho : o ∈ rho.releasesAt i)
    {x : Fin (Fintype.card V)} {t : Time} {p : Option (Wire (Fintype.card V))}
    {B : Blk (S.params (Model.pubOf E) hn)}
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) : x = rho.ownKey v := by
  obtain ⟨b, hb, ho⟩ := released_candidate_batch S rho he ho
  have hsign : o.signer? = some (rho.ownKey v) := by
    rcases he with he | ⟨receipt, he⟩
    all_goals
      rw [eventBatches_eq, he] at hb
      simp only at hb
    · split at hb
      · rcases List.mem_append.mp hb with hb | hb
        · exact dutyBatches_signer S rho v _ _ b hb o ho
        · have heq := List.mem_singleton.mp hb
          subst b
          obtain ⟨mc, _, rfl⟩ := Model.mem_gossipCandidates.mp ho
          have hsign := decodeForward_signer hd
          change none = some x at hsign
          cases hsign
      · exact False.elim (List.not_mem_nil hb)
    · rcases List.mem_append.mp hb with hb | hb
      · exact dutyBatches_signer S rho v _ _ b hb o ho
      · have heq := List.mem_singleton.mp hb
        subst b
        obtain ⟨mc, _, rfl⟩ := Model.mem_gossipCandidates.mp ho
        have hsign := decodeForward_signer hd
        change none = some x at hsign
        cases hsign
  exact Option.some.inj ((decodeForward_signer hd).symm.trans hsign)

/-- Holdings of another honest node's forwarding envelope always have an earlier
receipt call; only the self-signed case needs the own-publication acceptance join. -/
theorem held_other_forward_call (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {v : V} {i : Nat}
    {o : Wire (Fintype.card V)} {x : Fin (Fintype.card V)} {t : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (ho : o ∈ Model.closure (rho.stateBefore i v).seen) (hx : rho.key x ∉ rho.faultyAt 0)
    (hne : x ≠ rho.ownKey v)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) :
    ∃ k < cutMap S rho hn i, t ≤ (simTrace S rho hn).time k ∧
      (simTrace S rho hn).BlockCallAt (rho.ownKey v) k B := by
  rcases held_forward_release_or_call S rho hn hf hv ho hx hd with ⟨j, _, u, he, hr⟩ | h
  · exact False.elim (hne (released_forward_signer S rho hn he hr hd))
  · exact h

/-- The only remaining origin case for held honest forwarding envelopes is a local
tick publication. All receipts and local delivery publications already have trace witnesses. -/
theorem held_forward_tick_or_processed (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {v : V} {i : Nat}
    {o : Wire (Fintype.card V)} {x : Fin (Fintype.card V)} {t : Time}
    {p : Option (Wire (Fintype.card V))} {B : Blk (S.params (Model.pubOf E) hn)}
    (ho : o ∈ Model.closure (rho.stateBefore i v).seen) (hx : rho.key x ∉ rho.faultyAt 0)
    (hd : decodeForward (S.params (Model.pubOf E) hn) (Model.digests rho.hash o) o =
      some (x, t, p, B)) :
    (x = rho.ownKey v ∧ ∃ j < i, ∃ u,
      rho.events[j]? = some (.tick v u) ∧ o ∈ rho.releasesAt j) ∨
    ∃ k < cutMap S rho hn i, t ≤ (simTrace S rho hn).time k ∧
      ((simTrace S rho hn).BlockCallAt (rho.ownKey v) k B ∨
        x = rho.ownKey v ∧ (simTrace S rho hn).AcceptAt (rho.ownKey v) k B) := by
  rcases held_forward_release_or_call S rho hn hf hv ho hx hd with ⟨j, hj, u, he, hr⟩ | h
  · have hxv := released_forward_signer S rho hn he hr hd
    subst x
    rcases he with he | ⟨receipt, he⟩
    · exact Or.inl ⟨rfl, j, hj, u, he, hr⟩
    · obtain ⟨k, hk, ha, ht⟩ := delivery_released_forward_acceptance S rho hn hv he hr hd
      exact Or.inr ⟨k, hk.trans_le (cutMap_mono S rho hn (Nat.succ_le_of_lt hj)),
        le_of_eq ht.symm, Or.inr ⟨rfl, ha⟩⟩
  · obtain ⟨k, hk, ht, hc⟩ := h
    exact Or.inr ⟨k, hk, ht, Or.inl hc⟩

end Trace

end Consensus.Goldilocks.Simulation
