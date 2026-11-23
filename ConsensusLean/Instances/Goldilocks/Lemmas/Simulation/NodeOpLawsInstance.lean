module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeOpLaws
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
  rw [eventCuts_tick e rho j v t he, ite_eq_left hp, groupRecs_eq] at hr
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
  rw [List.getElem_mapIdx, List.getElem_zip] at hl
  have hcut : Cut.fg (.block b acc) ∈
      (exec (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
        (e.adapter.node (stateAt e rho v j)) t
        (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2 :=
    hl ▸ List.getElem_mem _
  let clk := afterClock rho (rho.stateBefore j v) v t
  let ds : List (ShapeDuty e.skel.Kind) := [.poll t.toNat, .poll t.toNat, .pollPropose t.toNat]
  let pre := (rho.runDuties v clk (ds.map (engineDuty e))).1
  let pr := runProposer rho hn
  let dg := digestOf e rho
  let y := rho.ownKey v
  let x := encodeTxs (Model.mempool rho.inbox v t)
  let st := e.adapter.node (stateAt e rho v j)
  have hpref := (L.toLawful ready).tick_prefix rho hv he
  rw [ite_eq_left hp] at hpref
  have hpre : e.adapter.node (envelope e pre) = (acCall y st t .tick).1 := hpref.1
  change Cut.fg (.block b acc) ∈ (onTick pr dg y st t x).2 at hcut
  have hprop : Cut.fg (.block b acc) ∈
      (tickStep pr dg y (e.adapter.node (envelope e pre)) t x .proposal).2 := by
    simp only [onTick, runSteps, tickSteps, List.foldl_cons, List.foldl_nil,
      List.nil_append] at hcut
    rw [hpre]
    rcases List.mem_append.mp hcut with h | h
    · rcases List.mem_append.mp h with h | h
      · simp [tickStep, acCall] at h
      · exact h
    · simp only [tickStep] at h
      split at h
      · simp [acToFG] at h
      · unfold attest at h
        split at h <;> simp [acToFG, onAttestation] at h
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
private theorem fgUpdate_voteIO {sp ro binding} (st : State sp ro binding) :
    (AsChainShape.fgUpdate st).voteIO = st.voteIO := by
  rw [fgUpdate_eq]; simp only; split
  · rfl
  · split <;> rfl

/-- A poll step keeps the vote authentication. -/
theorem poll_voteIO {sp ro binding} (st : State sp ro binding) t :
    (AsChainShape.poll st t).1.voteIO = st.voteIO := by
  unfold AsChainShape.poll; simp only; split <;> split <;> simp [fgUpdate_voteIO]

/-- Recording an own object keeps the vote authentication. -/
theorem recordOwn_voteIO {sp ro binding} (st : State sp ro binding) o hs :
    (AsChainShape.recordOwn st o hs).voteIO = st.voteIO := by
  rw [AsChainShape.recordOwn_eq]; split <;> (try split) <;> rfl

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
    attest_io := fun _ _ _ => rfl
    wake_io := fun _ _ _ => rfl
    clock_io := fun _ _ => rfl
    pollBatch_io := fun st t => poll_voteIO st t
    recordOwn_io := fun st o hs => recordOwn_voteIO st o hs
    process_eq := fun _ => rfl }

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
    attest_obs := fun _ _ _ => ⟨rfl, rfl, rfl⟩
    wake_obs := fun _ _ _ => ⟨rfl, rfl⟩
    init_obs := fun _ _ _ => ⟨rfl, rfl⟩
    clock_obs := fun _ _ => ⟨rfl, rfl, rfl, rfl⟩
    voteIO := ⟨_, hio⟩
    propose_eq := rfl
    restore_eq := rfl
    pollPropose_eq := fun _ _ => rfl
    pollBatch_obs := fun st t => by
      change let u := if st.fgDue then fgUpdate st else st
        (poll st t).1.node = u.node ∧ (poll st t).1.self = u.self ∧
          (poll st t).1.now = u.now ∧ (poll st t).1.fgDue = false
      refine ⟨?_, ?_, ?_, poll_fgDue st t⟩
      · cases h : st.fgDue
        · exact poll_node_of_fgDue st t h
        · exact poll_node_of_fgDue_true st t h
      · cases h : st.fgDue
        · exact poll_self st t
        · exact (poll_self st t).trans (fgUpdate_self st).symm
      · cases h : st.fgDue
        · exact poll_now st t
        · exact (poll_now st t).trans (fgUpdate_now st).symm
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
