module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeOpLaws
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EngineSteps
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeDeliveryOrigin
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodePool
import ConsensusLean.Lemmas.Model.DutyFold

public section

/-! # The replay laws from the local operation laws

`toLawful` derives the replay equations of `Encoding.Lawful` from the local observations of
`Encoding.OpLaws` and the instance's proposal guards; split from `NodeOpLaws`. A tick's node
is the node's tick followed by the own `on_attestation`s of what the engine admitted to the pool
during it (`tick_admits`): the trailing polls run the FG update and release, possibly by a
flush, own attestations, and processing an attestation appends it to the pool when new. -/

namespace Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

open Blocks Shape Node
open Model (pubOf)

variable {V : Type} [Fintype V] {E : Env V}
variable {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
variable {F : ChainShapeFamily O I} {p : Params} {hN : p.n = Fintype.card V}
variable {hn : 1 ≤ Fintype.card V}
variable {A : NodeAC (paramsAtCount p (Fintype.card V) hN hn)}
variable {e : Encoding F E p hN hn A} {due : e.State hn → Bool}


/-- The instance's own-admission guard: every attestation the engine admits to a node's pool
during its tick carries the node's own key. -/
def Encoding.AdmitsOwn [DecidableEq V] (e : Encoding F E p hN hn A) : Prop :=
  ∀ (rho : Model.Run (compiled F) E), rho.ExecutionValid →
    ∀ {i v t}, rho.events[i]? = some (.tick v t) →
      ∀ a ∈ admitsAt e rho v i, a.val = rho.ownKey v

/-- `AdmitsOwn` unfolded. -/
theorem Encoding.admitsOwn_iff [DecidableEq V] (e : Encoding F E p hN hn A) : e.AdmitsOwn ↔
    ∀ (rho : Model.Run (compiled F) E), rho.ExecutionValid →
      ∀ {i v t}, rho.events[i]? = some (.tick v t) →
        ∀ a ∈ admitsAt e rho v i, a.val = rho.ownKey v := Iff.rfl

namespace Encoding.OpLaws

open Classical in
/-- The envelope effect of a selected slot proposal. Kept for a downstream consumer. -/
theorem proposal_step (L : e.OpLaws due) (rho : Model.Run (compiled F) E)
    (v : V) (nd : Model.Node (Model.protoOf (compiled F) E)) (s : Slot) (hs : 0 < s)
    (hk : e.adapter.self (envelope e nd) = rho.ownKey v)
    (ht : e.adapter.now (envelope e nd) = (paramsAtCount p (Fintype.card V) hN hn).slotTime s)
    (hsel : rho.sel (engineRole e (.proposer s)) = {runProposer rho hn s})
    (hready : rho.ownKey v ∈ rho.sel (engineRole e (.proposer s)) →
      ∀ par info cs, ((e.ops hn).propose (envelope e nd) s).2 = some (par, info, cs) →
      let o := engineObj e (.mk (.signed (rho.ownKey v) (.proposer s))
        (.item ⟨par, s, encodeTxs nd.st.2, info⟩) cs)
      Model.releasable nd.seen o = true ∧
        (Model.protoOf (compiled F) E).dependencies.ready (Model.closure nd.seen) o = true) :
    e.adapter.node (envelope e (rho.dutyStep v nd (engineDuty e (.propose s hs))).1) =
      (tickStep (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
        (e.adapter.node (envelope e nd)) (e.adapter.now (envelope e nd))
        (encodeTxs nd.st.2) .proposal).1 ∧
    ∀ b acc, Cut.fg (.block b acc) ∈ (tickStep (runProposer rho hn) (digestOf e rho)
        (rho.ownKey v) (e.adapter.node (envelope e nd)) (e.adapter.now (envelope e nd))
        (encodeTxs nd.st.2) .proposal).2 →
      engineObj e (blockObj e.codec.encode e.codec.carried b) ∈
        (rho.dutyStep v nd (engineDuty e (.propose s hs))).2 := by
  let st := envelope e nd
  let t := e.adapter.now st
  let r := acProposal (e.adapter.node st) t
  let d := engineDuty e (.propose s hs)
  change e.adapter.self st = rho.ownKey v at hk
  have hslot : (paramsAtCount p (Fintype.card V) hN hn).slotOf t = s := by
    change (paramsAtCount p (Fintype.card V) hN hn).slotOf (e.adapter.now st) = s
    rw [ht, Simulation.slotOf_slotTime]
  have hrole : (Model.protoOf (compiled F) E).role d = engineRole e (.proposer s) :=
    role_engineDuty (.propose s hs)
  have hiff : Proposes (P := paramsAtCount p (Fintype.card V) hN hn)
        (runProposer rho hn) (rho.ownKey v) t ↔
      rho.ownKey v ∈ rho.sel (engineRole e (.proposer s)) := by
    unfold Proposes
    rw [hslot, hsel, Finset.mem_singleton]
    exact ⟨fun h => h.2.2.symm, fun h => ⟨hs, ht, h.symm⟩⟩
  by_cases hmem : rho.ownKey v ∈ rho.sel (engineRole e (.proposer s))
  · have hact : envelope e ⟨((Model.protoOf (compiled F) E).act nd.st d).1, nd.seen⟩ =
        ((e.ops hn).propose st s).1 := envelope_act nd (.propose s hs)
    have hcand := proposal_candidates L rho v nd s hs hmem
    dsimp only at hcand
    change rho.signedCandidate v d ((Model.protoOf (compiled F) E).act nd.st d).2 = _ at hcand
    have hyes : Proposes (P := paramsAtCount p (Fintype.card V) hN hn)
        (runProposer rho hn) (rho.ownKey v) (e.adapter.now (envelope e nd)) :=
      hiff.mpr hmem
    change e.adapter.node (envelope e (rho.dutyStep v nd d).1) = _ ∧ _
    simp only [tickStep, ite_eq_left hyes]
    generalize hr : (acProposal (e.adapter.node (envelope e nd))
      (e.adapter.now (envelope e nd))).2.2 = q
    change r.2.2 = q at hr
    cases q with
    | none =>
      have hp : (e.ops hn).propose st s = (e.adapter.setNode st r.1, none) := by
        rw [L.propose_eq]
        unfold NodeAsChainShape.propose
        dsimp only
        rw (config := { transparency := .default }) [hr]
      rw [rho.dutyStep_eq, hrole, ite_eq_left hmem, hcand, hp]
      refine ⟨?_, by simp [acProposal]⟩
      change e.adapter.node (envelope e ⟨((Model.protoOf (compiled F) E).act nd.st d).1,
        nd.seen⟩) = r.1
      rw [hact, hp]
      exact (L.setNode_obs _ _).1
    | some ab =>
      obtain ⟨head, payload⟩ := ab
      let atts := r.1.fg.proposalAttestations head.head
      let par := parentRef (paramsAtCount p (Fintype.card V) hN hn).genesisRoot
        (some head.head.root)
      let info := e.codec.encode atts payload
      let cs := e.codec.carried atts payload
      let header : Header I := ⟨par, s, encodeTxs nd.st.2, info⟩
      let o := engineObj e (.mk (.signed (rho.ownKey v) (.proposer s)) (.item header) cs)
      have hp : (e.ops hn).propose st s = (e.adapter.setNode st r.1, some (par, info, cs)) := by
        rw [L.propose_eq]
        unfold NodeAsChainShape.propose
        dsimp only
        rw (config := { transparency := .default }) [hr]
      have hguards := hready hmem par info cs (congrArg Prod.snd hp)
      have hsign : rho.signedCandidate v d ((Model.protoOf (compiled F) E).act nd.st d).2 =
          [o] := by
        rw [hcand, hp]; rfl
      rw [dutyStep_release_singleton rho v nd d o (hrole ▸ hmem) hsign hguards.1 hguards.2]
      have hrw := envelope_recordOwn (e := e)
        ⟨((Model.protoOf (compiled F) E).act nd.st d).1, nd.seen⟩ o (Model.digests rho.hash o)
      rw [hrw, hact, hp, wireOf_engineObj]
      -- The first digest is for the candidate itself, even if it carries another copy.
      have hdigest : rootOf (Model.digests rho.hash o) header = some (rho.hash header) := by
        unfold rootOf Model.digests
        have hi : o.item? = some header := engineObj_item e _
        cases ho : o with
        | mk auth msg carried =>
          have hitem : (Model.Obj.mk auth msg carried).item? = some header := ho ▸ hi
          rw [Model.Obj.parts, List.filterMap_cons, hitem]
          dsimp only
          rw (config := { transparency := .default }) [List.map_cons,
            List.find?_cons_of_pos (by simp)]
          rfl
      have hb : blockOf (P := paramsAtCount p (Fintype.card V) hN hn) (rho.hash header)
          header (rho.ownKey v) atts payload =
          mkBlock (digestOf e rho) (rho.ownKey v) r.1.fg t (encodeTxs nd.st.2)
            head.head payload := by
        simp only [blockOf, mkBlock, hslot, digestOf_eq, header, info, par, atts]
        have hp : parentRoot p.genesisRoot (parentRef p.genesisRoot (some head.head.root)) =
            some head.head.root := Simulation.parentRoot_parentRef _ _
        rw (config := { transparency := .default }) [hp]
      have hrec := (L.recordOwn_obs (e.adapter.setNode st r.1)
        (.mk (.signed (rho.ownKey v) (.proposer s)) (.item header) cs) (Model.digests rho.hash o)).1
      refine ⟨?_, ?_⟩
      swap
      · intro b acc h
        simp only [List.mem_cons] at h
        rcases h with h | h
        · simp [acProposal] at h
        · simp only [proposeBlock, onBlock] at h
          split at h
          · simp at h
          · split at h <;> simp [acCall] at h <;> rw [h.1] <;>
              simp [o, blockObj, header, headerOf, mkBlock, atts, info, par, cs] <;>
              exact congrArg (fun k => engineObj e (.mk (.signed (rho.ownKey v) (.proposer k))
                (.item ⟨par, k, encodeTxs nd.st.2, info⟩) cs)) hslot
      refine hrec.trans ?_
      change e.adapter.node (recordBlock e.codec e.adapter (e.adapter.setNode st r.1)
        (rho.ownKey v) header (Model.digests rho.hash o)) = _
      have hdec := L.decode_encode atts payload
      change e.codec.decode header.info = some (atts, payload) at hdec
      simp only [recordBlock, hdec, hdigest, L.applyCuts_obs, L.setNode_obs, hk, hb, proposeBlock]
      rfl
  · rw [rho.dutyStep_eq, hrole, ite_eq_right hmem]
    have hno : ¬ Proposes (P := paramsAtCount p (Fintype.card V) hN hn)
        (runProposer rho hn) (rho.ownKey v) (e.adapter.now (envelope e nd)) :=
      hiff.not.mpr hmem
    simp [tickStep, hno]

open Classical in
/-- The node at the end of a tick's proposal duty: the slot proposal of the node after the
leading polls and the node's tick. -/
private theorem tick_proposal_at [DecidableEq V] (L : e.OpLaws due) (ready : e.ProposalReady)
    (rho : Model.Run (compiled F) E) (hv : rho.ExecutionValid) {i v t}
    (he : rho.events[i]? = some (.tick v t)) :
    let pre := (rho.runDuties v (afterClock rho (rho.stateBefore i v) v t)
      ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat].map (engineDuty e))).1
    let post := (rho.runDuties v pre ((e.skel.proposeAt t).map (engineDuty e))).1
    due (envelope e post) = due (envelope e pre) ∧
    e.adapter.node (envelope e post) = (Node.tickStep (runProposer rho hn) (digestOf e rho)
      (rho.ownKey v) (e.adapter.node (envelope e pre)) t
      (encodeTxs (Model.mempool rho.inbox v t)) .proposal).1 ∧
    (¬ (paramsAtCount p (Fintype.card V) hN hn).IsPublic t →
      e.adapter.node (envelope e post) = e.adapter.node (envelope e pre)) := by
  let clk := afterClock rho (rho.stateBefore i v) v t
  let ds : List (ShapeDuty e.skel.Kind) := [.poll t.toNat, .poll t.toNat, .pollPropose t.toNat]
  let pre := (rho.runDuties v clk (ds.map (engineDuty e))).1
  let post := (rho.runDuties v pre ((e.skel.proposeAt t).map (engineDuty e))).1
  let P := paramsAtCount p (Fintype.card V) hN hn
  change due (envelope e post) = due (envelope e pre) ∧
    e.adapter.node (envelope e post) = (tickStep (runProposer rho hn) (digestOf e rho)
      (rho.ownKey v) (e.adapter.node (envelope e pre)) t
      (encodeTxs (Model.mempool rho.inbox v t)) .proposal).1 ∧
    (¬ P.IsPublic t → e.adapter.node (envelope e post) = e.adapter.node (envelope e pre))
  dsimp only [post]
  rcases Simulation.Skeleton.proposeAt_cases e.skel t with ⟨hnil, hno⟩ | ⟨s, hs, hone, htime⟩
  · rw [hnil, List.map_nil, rho.runDuties_nil]
    have hp : ¬ Proposes (P := P) (runProposer rho hn) (rho.ownKey v) t :=
      fun h => hno _ h.1 (h.2.1.trans (L.grid_time _).symm)
    simp only [tickStep, ite_eq_right hp, and_self, implies_true]
  · rw [hone, List.map_cons, List.map_nil, rho.runDuties_cons, rho.runDuties_nil]
    have ht : t = P.slotTime s := htime.trans (L.grid_time s)
    have ⟨hk, hclock⟩ := proposal_clock L rho v i t ds
    have hm : pre.st.2 = Model.mempool rho.inbox v t := by
      dsimp only [pre, clk]
      rw [duties_mempool, afterClock_eq]
      rfl
    refine ⟨?_, ?_, fun h => (h (ht ▸ P.slotTime_public s)).elim⟩
    · rw [rho.dutyStep_eq]
      split
      · apply releaseAll_pres rho (fun st => due st = due (envelope e pre))
        · intro o _ st digests h
          exact (recordOwn_pres L st (wireOf e o) digests).2.2.trans h
        · rw [envelope_act]
          exact (propose_pres L (envelope e pre) s).2.2
      · rfl
    · have step := proposal_step L rho v pre s hs hk (hclock.trans ht)
        (selValid_proposer e rho hv.selValid s (L.proposer_selection s))
        (fun h => Encoding.proposalReady_iff.1 ready rho hv he s hs hone h)
      change e.adapter.now (envelope e pre) = t at hclock
      rw [hclock, hm] at step
      exact step.1

open Classical in
/-- The node after an engine tick: the node's tick (`postTick`), then the own
`on_attestation`s of what the first trailing poll releases (`relOf`, at the state after the
proposal duty); the second trailing poll is quiet and not due. -/
theorem tick_node_rel [DecidableEq V] (L : e.OpLaws due) (ready : e.ProposalReady)
    (rho : Model.Run (compiled F) E) (hv : rho.ExecutionValid) {i v t}
    (he : rho.events[i]? = some (.tick v t)) (l : List (FG.Att (Fintype.card V)))
    (hl : let pre := (rho.runDuties v (afterClock rho (rho.stateBefore i v) v t)
      ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat].map (engineDuty e))).1
      let post := envelope e (rho.runDuties v pre ((e.skel.proposeAt t).map (engineDuty e))).1
      e.adapter.node ((e.ops hn).pollBatch post t.toNat).1 =
        l.foldl (fun n a => (Node.onAttestation n a).1) (if due post then
          (tickStep (runProposer rho hn) (digestOf e rho) (e.adapter.self post)
            (e.adapter.node post) (e.adapter.now post)
            (encodeTxs (Model.mempool rho.inbox v t)) .fgUpdate).1
        else e.adapter.node post)) :
    e.adapter.node (stateAt e rho v (i + 1)) =
      l.foldl (fun n a => (Node.onAttestation n a).1) (postTick e rho e.adapter.sign v i t) := by
  have hm := List.mem_of_getElem? he
  have ⟨hk, ht⟩ := proposal_finish L rho v i t
  have hl := tick_finish_at L rho v _ t (poll_selected L rho hv v) hk ht l hl
  rw [cut_envelope rho v (i + 1), rho.stateBefore_succ he]
  simp only [Model.Run.step, Function.update_self]
  rw [rho.tick_of_awake _ _ _ (hv.tick_awake v t hm)]
  refine (gossip_obs L rho v _ t).1.trans ?_
  rw [tick_schedule L t (hv.in_horizon _ hm).1]
  simp only [List.map_append, rho.runDuties_append_fst, ← afterClock_eq]
  refine hl.trans ?_
  congr 1
  have hpre := tick_prefix L rho hv he
  have hprop := tick_proposal_at L ready rho hv he
  dsimp only at hpre hprop
  rw [hprop.1, postTick_eq]
  by_cases hpub : (paramsAtCount p (Fintype.card V) hN hn).IsPublic t
  · rw [ite_eq_left hpub] at hpre
    simp only [ite_eq_left hpub, hpre.2, hprop.2.1, hpre.1]
    cases e.adapter.sign (rho.ownKey v) t <;> rfl
  · rw [ite_eq_right hpub] at hpre
    simp only [ite_eq_right hpub, hpre.2, Bool.false_eq_true, ↓reduceIte, hprop.2.2 hpub,
      hpre.1]

open Classical in
/-- **The node after an engine tick** is the node's tick (`postTick`) followed by the own
`on_attestation` of every attestation the engine admitted to the pool during it, in order
(`admitsAt`). The trailing polls run the FG update and then the own `on_attestation`s of what
they release (`tick_node_rel`); the node's tick keeps the pool (`exec_tick_atts`), so the
attestations processed are the pool's growth (`foldl_onAttestation_growth`). -/
theorem tick_admits [DecidableEq V] (L : e.OpLaws due) (ready : e.ProposalReady)
    (rho : Model.Run (compiled F) E) (hv : rho.ExecutionValid) {i v t}
    (he : rho.events[i]? = some (.tick v t)) :
    e.adapter.node (stateAt e rho v (i + 1)) =
      (admitsAt e rho v i).foldl
        (fun n a => (exec (runProposer rho hn) (digestOf e rho) (rho.ownKey v) n t
          (.attestation a)).1)
        (postTick e rho e.adapter.sign v i t) := by
  change _ = (admitsAt e rho v i).foldl (fun n a => (Node.onAttestation n a).1) _
  rw [admitsAt_eq, tick_node_rel L ready rho hv he _ (relOf_spec L _ _ _ _ _),
    ← postTick_atts rho v i t]
  exact foldl_onAttestation_growth (N := A) _ _

open Classical in
/-- **An attestation admitted during a tick is one the first trailing poll releases**, for any
list `l` that poll releases (by the instance: a flushed held attestation or the attestation the
FG update signs and releases at once). -/
theorem mem_admitsAt_rel [DecidableEq V] (L : e.OpLaws due) (ready : e.ProposalReady)
    (rho : Model.Run (compiled F) E) (hv : rho.ExecutionValid) {i v t}
    (he : rho.events[i]? = some (.tick v t)) (l : List (FG.Att (Fintype.card V)))
    (hl : let pre := (rho.runDuties v (afterClock rho (rho.stateBefore i v) v t)
      ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat].map (engineDuty e))).1
      let post := envelope e (rho.runDuties v pre ((e.skel.proposeAt t).map (engineDuty e))).1
      e.adapter.node ((e.ops hn).pollBatch post t.toNat).1 =
        l.foldl (fun n a => (Node.onAttestation n a).1) (if due post then
          (tickStep (runProposer rho hn) (digestOf e rho) (e.adapter.self post)
            (e.adapter.node post) (e.adapter.now post)
            (encodeTxs (Model.mempool rho.inbox v t)) .fgUpdate).1
        else e.adapter.node post))
    {a : FG.Att (Fintype.card V)} (ha : a ∈ admitsAt e rho v i) : a ∈ l := by
  rw [admitsAt_eq, tick_node_rel L ready rho hv he l hl, ← postTick_atts rho v i t] at ha
  exact mem_growth (N := A) _ _ ha

open Classical in
/-- Derive the frozen replay equations from local observations and the instance's two guards
for its actual proposal candidate. -/
theorem toLawful [DecidableEq V] (L : e.OpLaws due) (ready : e.ProposalReady)
    (own : e.AdmitsOwn) : e.Lawful due where
  init_due k sel x := (L.init_obs k sel x).2
  set_due st b := (L.setDue_obs st b).2.2.2
  clock_due st t := (L.clock_obs st t).2.2.2
  process_due st o hs := (process_pres L st o hs).2.2
  restore_due k st t := (restore_obs L k st t).2.2.2
  cut_due rho v i := (cut_obs L rho v i).2
  tick_schedule := tick_schedule L
  tick_prefix := fun rho hv _ _ _ he => tick_prefix L rho hv he
  tick_proposal rho hv _ _ _ he := tick_proposal_at L ready rho hv he
  tick_admits rho hv _ _ _ he := tick_admits L ready rho hv he
  admits_own rho hv _ _ _ he := (Encoding.admitsOwn_iff e).1 own rho hv he
  gossip_node rho v nd t := (gossip_obs L rho v nd t).1
  delivery_process := fun rho hv _ _ _ _ he => delivery_process L rho hv he
  delivery_publish := fun rho hv _ _ _ _ he hd => delivery_publish L rho hv he hd
  restore_node k st t := (restore_obs L k st t).1

end Encoding.OpLaws

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace
