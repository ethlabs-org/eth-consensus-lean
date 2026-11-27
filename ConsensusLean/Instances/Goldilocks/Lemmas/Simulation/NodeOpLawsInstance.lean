module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeOpLawsLawful
import ConsensusLean.Lemmas.Model.DutyFold
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EngineSteps
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeDeliveryOrigin
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeRunSchedule

public section

/-! # Own-block release and Goldilocks' local operation laws

Consequences of the operation laws for released own blocks, and Goldilocks' instance of the laws
(`traceEncoding_opLaws`), split from `NodeOpLaws`. -/

namespace Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

open Blocks Shape Node
open Model (pubOf)

variable {V : Type} [Fintype V] {E : Env V}
variable {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
variable {F : ChainShapeFamily O I} {p : Params} {hN : p.n = Fintype.card V}
variable {hn : 1 ≤ Fintype.card V}
variable {A : NodeAC (paramsAtCount p (Fintype.card V) hN hn)}
variable {e : Encoding F E p hN hn A} {due : e.State hn → Bool}

open Encoding.OpLaws

private theorem tick_proposal_release [DecidableEq V] (L : e.OpLaws due)
    (rho : Model.Run (compiled F) E) (hv : rho.ExecutionValid) {j : Nat} {v : V} {t : Time}
    (he : rho.events[j]? = some (.tick v t)) {s : Slot} {hs : 0 < s}
    (hone : e.skel.proposeAt t = [.propose s hs])
    (o : (Model.protoOf (compiled F) E).Object)
    (hr : o ∈ (rho.dutyStep v (rho.runDuties v (afterClock rho (rho.stateBefore j v) v t)
      ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat].map (engineDuty e))).1
      (engineDuty e (.propose s hs))).2) : o ∈ rho.releasesAt j := by
  have hw := hv.tick_awake v t (List.mem_of_getElem? he)
  have ht := (hv.in_horizon (.tick v t) (List.mem_of_getElem? he)).1
  unfold Model.Run.releasesAt
  rw [he]
  change o ∈ (rho.tick (rho.stateBefore j v) v t).2
  rw [rho.tick_of_awake _ v t hw, L.tick_schedule t ht, hone, ← afterClock_eq]
  simp only [List.append_assoc, List.map_append, List.singleton_append]
  rw [rho.runDuties_append]
  apply List.mem_append_left
  apply List.mem_append_right
  conv in List.map (engineDuty e) (.propose s hs :: _) => rw [List.map_cons]
  rw [rho.runDuties_cons]
  exact List.mem_append_left _ hr

open Classical in
/-- Each own block cut of a public tick comes from a block released by its propose duty.
Kept for a downstream consumer. -/
theorem tick_block_released [DecidableEq V] (e : Encoding F E p hN hn A)
    (rho : Model.Run (compiled F) E) {due : e.State hn → Bool}
    (L : e.OpLaws due) (ready : e.ProposalReady) (hv : rho.ExecutionValid)
    {j : Nat} {v : V} {t : Time}
    (he : rho.events[j]? = some (.tick v t))
    (hp : (paramsAtCount p (Fintype.card V) hN hn).IsPublic t) :
    ∀ r ∈ eventCuts e rho j, ∀ b acc, r.label = .fg (.block b acc) → r.pos ≠ 0 →
      engineObj e (blockObj e.codec.encode e.codec.carried b) ∈ rho.releasesAt j := by
  open Encoding.OpLaws in
  intro r hr b acc hl _
  rw [eventCuts_tick e rho j v t he, ite_eq_left hp] at hr
  rcases List.mem_append.1 hr with hr | hr
  swap
  · -- a tail cut is an own admission, labelled by its attestation
    obtain ⟨a, _, st', _, _, hm⟩ := mem_admitRecs _ _ _ _ _ _ _ _ _ hr
    rw [groupRecs_eq] at hm
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hm
    rw [List.getElem_mapIdx, List.getElem_zip] at hl
    simp [exec, onAttestation] at hl
  rw [groupRecs_eq] at hr
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
  rw [List.getElem_mapIdx, List.getElem_zip] at hl
  have hcut : Cut.fg (.block b acc) ∈
      (exec (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
        (e.adapter.node (stateAt e rho v j)) t
        (.tick (encodeTxs (Model.mempool rho.inbox v t)) (e.adapter.sign (rho.ownKey v) t))).2 :=
    hl ▸ List.getElem_mem _
  let clk := afterClock rho (rho.stateBefore j v) v t
  let ds : List (ShapeDuty e.skel.Kind) := [.poll t.toNat, .poll t.toNat, .pollPropose t.toNat]
  let pre := (rho.runDuties v clk (ds.map (engineDuty e))).1
  let pr := runProposer rho hn
  let dg := digestOf e rho
  let y := rho.ownKey v
  let x := encodeTxs (Model.mempool rho.inbox v t)
  let st := e.adapter.node (stateAt e rho v j)
  have hpref := tick_prefix L rho hv he
  rw [ite_eq_left hp] at hpref
  have hpre : e.adapter.node (envelope e pre) = (acCall y st t .tick).1 := hpref.1
  change Cut.fg (.block b acc) ∈ (onTick pr dg y st t x (e.adapter.sign y t)).2 at hcut
  have hprop : Cut.fg (.block b acc) ∈
      (tickStep pr dg y (e.adapter.node (envelope e pre)) t x .proposal).2 := by
    rw [hpre]
    generalize e.adapter.sign y t = sg at hcut
    cases sg
    · simp only [onTick, runSteps, tickSteps, List.foldl_cons, List.foldl_nil,
        Bool.false_eq_true, ite_false, List.nil_append] at hcut
      rcases List.mem_append.mp hcut with h | h
      · simp [tickStep, acCall] at h
      · exact h
    simp only [onTick, runSteps, tickSteps, List.foldl_cons, List.foldl_nil,
      ite_true, List.nil_append] at hcut
    rcases List.mem_append.mp hcut with h | h
    · rcases List.mem_append.mp h with h | h
      · simp [tickStep, acCall] at h
      · exact h
    · simp only [tickStep] at h
      split at h
      · simp [acToFG] at h
      · unfold attest at h
        split at h <;> simp [acToFG] at h
  rcases Simulation.Skeleton.proposeAt_cases e.skel t with ⟨_, hno⟩ | ⟨s, hs, hone, htime⟩
  · have hnop : ¬ Proposes pr y t := fun h => hno _ h.1 (h.2.1.trans (L.grid_time _).symm)
    simp [tickStep, hnop] at hprop
  have ⟨hk', hclock⟩ := proposal_clock L rho v j t ds
  have hm : pre.st.2 = Model.mempool rho.inbox v t := by
    dsimp only [pre, clk]
    rw [duties_mempool, afterClock_eq]
    rfl
  have hrel := (proposal_step L rho v pre s hs hk' (hclock.trans (htime.trans (L.grid_time s)))
    (selValid_proposer e rho hv.selValid s (L.proposer_selection s))
    (fun h => Encoding.proposalReady_iff.mp ready rho hv he s hs hone h)).2
  change e.adapter.now (envelope e pre) = t at hclock
  rw [hclock, hm] at hrel
  exact tick_proposal_release L rho hv he hone _ (hrel b acc hprop)

/-- Identity step for the converse of proposal release: once the proposal cut and the
released block have equal canonical objects, they are the same rooted block. Only the
stored parent reference is used; the parent block itself need not be identified. -/
theorem rooted_block_eq_of_blockObj_eq (L : e.OpLaws due) (rho : Model.Run (compiled F) E)
    {B C : A.Blk} (hpB : B.parent ≠ none) (hpC : C.parent ≠ none)
    (hrB : B.RootOk (digestOf e rho)) (hrC : C.RootOk (digestOf e rho))
    (he : engineObj e (blockObj e.codec.encode e.codec.carried B) =
      engineObj e (blockObj e.codec.encode e.codec.carried C)) : B = C := by
  have h := congrArg (wireOf e) he
  simp only [wireOf_engineObj] at h
  have hh := congrArg Model.Obj.msg h
  have ha := congrArg Model.Obj.auth h
  simp only [blockObj, Model.Obj.msg, Model.Msg.item.injEq] at hh
  simp only [blockObj, Model.Obj.auth, Model.Auth.signed.injEq] at ha
  have hs := congrArg Header.pos hh
  have hx := congrArg Header.input hh
  have hi := congrArg (fun hd => e.codec.decode hd.info) hh
  change B.slot = C.slot at hs
  change B.input = C.input at hx
  simp only [headerOf, L.decode_encode, Option.some.injEq, Prod.mk.injEq] at hi
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hpB
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hpC
  have hp := congrArg (fun hd => parentRoot p.genesisRoot hd.parent) hh
  have hparent : B.parent = C.parent := by
    simp only [headerOf, hb, hc] at hp ⊢
    change AsChainShape.parentRoot _ (AsChainShape.parentRef _ (some b)) =
      AsChainShape.parentRoot _ (AsChainShape.parentRef _ (some c)) at hp
    simpa only [Simulation.parentRoot_parentRef] using hp
  have hroot : B.root = C.root := by
    change B.root = digestOf e rho B.parent B.slot B.input B.fgPayload B.acPayload at hrB
    rw [hrB, hparent, hs, hx, hi.1, hi.2]
    exact hrC.symm
  have hv := ha.1
  cases B
  cases C
  simp_all

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape
open Model (pubOf)

/-- The FG update keeps the vote authentication. -/
private theorem fgUpdate_voteIO {sp binding} {release} (st : State sp binding) :
    (AsChainShape.fgUpdate st release).voteIO = st.voteIO := by
  rw [fgUpdate_eq st release]; simp only; split
  · rfl
  · split
    · rfl
    · split <;> rfl

/-- A batch poll keeps the vote authentication. -/
theorem poll_voteIO {sp binding} {release} (st : State sp binding) t :
    (AsChainShape.pollBatch st t release).1.voteIO = st.voteIO := by
  refine pollBatch_pres (Q := fun x => x.voteIO = st.voteIO) (fun x hx => ?_)
    (fun x h => by obtain ⟨atts, he⟩ := heldDrain_eq x; rw [he]; exact h) rfl
  refine Eq.trans ?_ hx
  unfold AsChainShape.poll; simp only; split <;> split <;> simp [fgUpdate_voteIO]

/-- Recording an own object keeps the vote authentication. -/
theorem recordOwn_voteIO {sp binding} (st : State sp binding) o hs :
    (AsChainShape.recordOwn st o hs).voteIO = st.voteIO := by
  rw [AsChainShape.recordOwn_eq]; split <;> (try split) <;> rfl

/-- The proposal poll keeps the vote authentication. -/
private theorem pollPropose_voteIO {sp binding} {sign} (st : State sp binding) :
    ({ AsChainShape.nodeTick st sign with ticked := true } : State sp binding).voteIO =
      st.voteIO := by
  change (AsChainShape.nodeTick st sign).voteIO = _
  rw [nodeTick_eq (sign := _)]; split <;> rfl

/-- Processing a delivery keeps the tick flag. -/
private theorem process_ticked {sp binding} (st : State sp binding) o hs :
    (AsChainShape.process st o hs).ticked = st.ticked := by
  rw [process_eq]
  generalize delivered st.voteIO hs st o = os
  suffices ∀ st', st'.ticked = st.ticked →
      (os.foldl (processOne st.voteIO hs) st').ticked = st.ticked from this st rfl
  induction os with
  | nil => exact fun _ h => h
  | cons o os ih =>
    refine fun st' h => ih _ (Eq.trans ?_ h)
    rw [processOne_eq]
    split <;> (try dsimp only) <;> (try unfold AsChainShape.relayIf) <;> (try split) <;> rfl

/-- A state with the key, clock, held queue and tick flag of another flushes the same. -/
private theorem pollFlush_congr {sp binding} {release} {st st' : State sp binding}
    (hs : st'.self = st.self) (hn : st'.now = st.now) (hh : st'.held = st.held)
    (hk : st'.ticked = st.ticked) : pollFlush st' release = pollFlush st release := by
  rw [pollFlush_eq, pollFlush_eq, hs, hn, hh, hk]

/-- After a batch poll, the next batch poll flushes nothing. -/
private theorem pollFlush_pollBatch {sp binding} {release} (st : State sp binding) t :
    pollFlush (AsChainShape.pollBatch st t release).1 release = [] := by
  rw [pollFlush_eq, pollBatch_ticked, pollBatch_self, pollBatch_now, pollBatch_held]
  cases hr : release st.self st.now <;> cases hk : st.ticked <;> simp

/-- A batch poll that flushes nothing runs the FG update when due. -/
private theorem pollBatch_node_quiet {sp binding} {release} (st : State sp binding) t
    (h : pollFlush st release = []) : (AsChainShape.pollBatch st t release).1.node =
      (if st.fgDue then AsChainShape.fgUpdate st release else st).node := by
  rw [pollBatch_node_eq (fun _ => st.self) (fun _ _ _ _ _ => 0) 0, h, List.nil_append]
  cases hd : st.fgDue
  · simp
  · simp only [Bool.true_and, ↓reduceIte]
    rw [fgUpdate_node (fun _ => st.self) (fun _ _ _ _ _ => 0) 0]

/-- Goldilocks' vote authentication laws: the envelope's `voteIO` is the receiver's. -/
theorem traceEncoding_ioLaws {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (hn : 1 ≤ Fintype.card V) : (traceEncoding (E := E) S hn).IOLaws (traceVoteIO S hn) :=
  traceEncoding_induction S hn (fun e _ io => e.IOLaws io) <| by
  intro e _
  exact {
    init_io := fun _ _ _ => rfl
    setNode_io := fun _ _ => rfl
    setDue_io := fun _ _ => rfl
    applyCuts_io := fun _ _ _ => rfl
    relayIf_io := fun st c _ o => by
      change (AsChainShape.relayIf st c o).voteIO = _
      unfold AsChainShape.relayIf; split <;> rfl
    attest_io := fun st _ _ => by
      change (if _ then _ else _ : State _ _).voteIO = st.voteIO
      split <;> rfl
    wake_io := fun _ _ _ => rfl
    clock_io := fun _ _ => rfl
    pollBatch_io := fun st t => poll_voteIO st t
    pollPropose_io := fun st _ => pollPropose_voteIO st
    recordOwn_io := fun st o hs => recordOwn_voteIO st o hs
    process_eq := fun st => by
      funext o hs
      exact (process_nodeAdapter_sign _ _ st o hs).symm }

/-- Goldilocks' local replay equations. Candidate readiness is proved separately on the run. -/
theorem traceEncoding_opLaws {V : Type} [Fintype V] {E : Env V} (S : Setup)
    (hn : 1 ≤ Fintype.card V) : (traceEncoding (E := E) S hn).OpLaws (traceDue S hn) :=
  traceEncoding_induction S hn
    (fun e due io => e.IOLaws io → e.OpLaws due) (fun _ hio => {
    setNode_obs := fun _ _ => ⟨rfl, rfl, rfl, rfl⟩
    setDue_obs := fun _ _ => ⟨rfl, rfl, rfl, rfl⟩
    applyCuts_obs := fun _ _ _ => ⟨rfl, rfl, rfl, rfl⟩
    relayIf_obs := fun st c _ o => by
      exact ⟨relayIf_node st c o, relayIf_self st c o, relayIf_now st c o, relayIf_fgDue st c o⟩
    attest_obs := fun st _ _ => by
      change let r := (if _ then _ else _ : State _ _)
        (∃ l : List (FG.Att _), r.node = l.foldl (fun n a => (Node.onAttestation n a).1) _) ∧
          r.self = st.self ∧ r.now = st.now
      dsimp only
      split <;> first | exact ⟨⟨[], rfl⟩, rfl, rfl⟩ | exact ⟨⟨[_], rfl⟩, rfl, rfl⟩
    wake_obs := fun _ _ _ => ⟨rfl, rfl⟩
    init_obs := fun _ _ _ => ⟨rfl, rfl⟩
    clock_obs := fun _ _ => ⟨rfl, rfl, rfl, rfl⟩
    voteIO := ⟨_, hio⟩
    propose_eq := rfl
    restore_eq := rfl
    pollPropose_obs := fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
    pollBatch_obs := fun st t => by
      refine ⟨?_, ?_, pollBatch_fgDue st t⟩
      · change (pollBatch st t (S.release (pubOf E))).1.self =
          (if st.fgDue then fgUpdate st (S.release (pubOf E)) else st).self
        rw [pollBatch_self]
        split
        · exact (fgUpdate_self st).symm
        · rfl
      · change (pollBatch st t (S.release (pubOf E))).1.now =
          (if st.fgDue then fgUpdate st (S.release (pubOf E)) else st).now
        rw [pollBatch_now]
        split
        · exact (fgUpdate_now st).symm
        · rfl
    released := ⟨fun st => pollFlush st (S.release (pubOf E)) ++
        if (st.fgDue && S.release (pubOf E) st.self st.now) = true then (fgSigned st).toList
        else [], fun st t pr dg x => pollBatch_node_eq pr dg x st t⟩
    quiet := ⟨fun st => pollFlush st (S.release (pubOf E)) = [],
      fun _ _ _ => pollFlush_of_unticked _ rfl, fun _ _ => pollFlush_of_unticked _ rfl,
      fun st t => pollFlush_pollBatch st t,
      fun st o hs h => (pollFlush_congr (recordOwn_self st o hs) (recordOwn_now st o hs)
        (recordOwn_held st o hs) (recordOwn_ticked st o hs)).trans h,
      fun st o hs h => (pollFlush_congr (process_self st o hs) (process_now st o hs)
        (process_held st o hs) (process_ticked st o hs)).trans h,
      fun st t h => pollBatch_node_quiet st t h⟩
    recordOwn_obs := fun st o hs => by
      obtain ⟨auth, msg, cs⟩ := o
      cases auth with
      | none => cases msg with
        | item => exact ⟨rfl, rfl, rfl, rfl⟩
        | data b => cases b <;> exact ⟨rfl, rfl, rfl, rfl⟩
      | signed k role => cases role <;> cases msg <;> exact ⟨rfl, rfl, rfl, rfl⟩
    tick_order := rfl
    deliver_order := rfl
    poll_selection := rfl
    proposer_selection := fun _ => rfl
    grid_time := fun s => (slotTime_eq S hn s).symm
    proposer_role := fun s hs h => congrArg (Option.getD · (.proposer s))
      (candidateRole_item S.vote _ (.propose s hs) h)
    decode_encode := decodeInfo_encodeInfo }) (traceEncoding_ioLaws S hn)

end Consensus.Goldilocks.Simulation
