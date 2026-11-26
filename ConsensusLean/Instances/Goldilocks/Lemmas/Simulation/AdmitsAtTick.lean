module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.GoldilocksReady
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeOpLawsLawful
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EngineState
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.HeldQueue
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EngineSteps

public section

/-! # Goldilocks Simulation: the own admissions of a tick

An attestation the engine admits to a node's pool during a tick (`admitsAt`) is released by the
tick's first trailing poll: a held attestation that poll flushes, or the attestation its FG
update signs at a time the release schedule allows (`mem_admitsAt_tick`). Either way the engine
signed it at that tick or earlier (`admitsAt_tick_signed`).

Every step is proved. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape
open Model (pubOf)
open NodeAsChainShape.CanonicalTrace (afterClock_eq engineDuty_eq envelope_eq Encoding)

variable {V : Type} [Fintype V] {E : Env V} [DecidableEq V] (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- The engine node before a tick's first trailing poll: after the clock, the two leading polls,
the proposal poll and the slot proposal. -/
noncomputable def beforeTrailing (v : V) (i : Nat) (t : Time) :
    Model.Node (Model.protoOf (compiled (goldilocks S)) E) :=
  (rho.runDuties v (rho.runDuties v
    ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
      (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
    ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] :
      List (Model.protoOf (compiled (goldilocks S)) E).Duty)).1
    ((skeleton (pubOf E) S.vote).proposeAt t)).1

/-- `beforeTrailing` unfolded. -/
theorem beforeTrailing_eq (v : V) (i : Nat) (t : Time) : beforeTrailing S rho v i t =
    (rho.runDuties v (rho.runDuties v
      ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
        (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
      ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] :
        List (Model.protoOf (compiled (goldilocks S)) E).Duty)).1
      ((skeleton (pubOf E) S.vote).proposeAt t)).1 := by rfl

/-- The first trailing poll of a tick releases a flush and the attestation its FG update signs
(`pollBatch_node_eq`), stated at the generic canonical trace. -/
theorem trailing_rel {i : Nat} {v : V} {t : Time} :
    let pre := (rho.runDuties v (NodeAsChainShape.CanonicalTrace.afterClock rho
      (rho.stateBefore i v) v t) ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat].map
        (NodeAsChainShape.CanonicalTrace.engineDuty (traceEncoding S hn)))).1
    let post := NodeAsChainShape.CanonicalTrace.envelope (traceEncoding S hn)
      (rho.runDuties v pre (((traceEncoding S hn).skel.proposeAt t).map
        (NodeAsChainShape.CanonicalTrace.engineDuty (traceEncoding S hn)))).1
    (traceEncoding S hn).adapter.node (((traceEncoding S hn).ops hn).pollBatch post t.toNat).1 =
      (pollFlush (shapeOf S hn (beforeTrailing S rho v i t)) (S.release (pubOf E)) ++
        if ((shapeOf S hn (beforeTrailing S rho v i t)).fgDue &&
            S.release (pubOf E) (shapeOf S hn (beforeTrailing S rho v i t)).self
              (shapeOf S hn (beforeTrailing S rho v i t)).now) = true then
          (fgSigned (shapeOf S hn (beforeTrailing S rho v i t))).toList
        else []).foldl (fun n a => (Node.onAttestation n a).1)
        (if traceDue S hn post then
          (Node.tickStep (NodeAsChainShape.CanonicalTrace.runProposer rho hn)
            (NodeAsChainShape.CanonicalTrace.digestOf (traceEncoding S hn) rho)
            ((traceEncoding S hn).adapter.self post)
            ((traceEncoding S hn).adapter.node post) ((traceEncoding S hn).adapter.now post)
            (encodeTxs (Model.mempool rho.inbox v t)) .fgUpdate).1
          else (traceEncoding S hn).adapter.node post) := by
  apply traceEncoding_induction S hn (fun e due _ =>
    let pre := (rho.runDuties v (NodeAsChainShape.CanonicalTrace.afterClock rho
      (rho.stateBefore i v) v t) ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat].map
        (NodeAsChainShape.CanonicalTrace.engineDuty e))).1
    let post := NodeAsChainShape.CanonicalTrace.envelope e (rho.runDuties v pre
      ((e.skel.proposeAt t).map (NodeAsChainShape.CanonicalTrace.engineDuty e))).1
    e.adapter.node ((e.ops hn).pollBatch post t.toNat).1 =
      (pollFlush (shapeOf S hn (beforeTrailing S rho v i t)) (S.release (pubOf E)) ++
        if ((shapeOf S hn (beforeTrailing S rho v i t)).fgDue &&
            S.release (pubOf E) (shapeOf S hn (beforeTrailing S rho v i t)).self
              (shapeOf S hn (beforeTrailing S rho v i t)).now) = true then
          (fgSigned (shapeOf S hn (beforeTrailing S rho v i t))).toList
        else []).foldl (fun n a => (Node.onAttestation n a).1)
        (if due post then (Node.tickStep (NodeAsChainShape.CanonicalTrace.runProposer rho hn)
            (NodeAsChainShape.CanonicalTrace.digestOf e rho) (e.adapter.self post)
            (e.adapter.node post) (e.adapter.now post)
            (encodeTxs (Model.mempool rho.inbox v t)) .fgUpdate).1
          else e.adapter.node post))
  intro e _
  have hsk : e.skel.proposeAt t = (skeleton (pubOf E) S.vote).proposeAt t := rfl
  simp only [afterClock_eq, envelope_eq, List.map_cons, List.map_nil, engineDuty_eq, hsk,
    beforeTrailing]
  rcases Skeleton.proposeAt_cases (skeleton (pubOf E) S.vote) t with ⟨hnil, -⟩ |
    ⟨s, hs, hone, -⟩
  · simp only [hnil, List.map_nil, rho.runDuties_nil]
    exact pollBatch_node_eq (sp := S.params (pubOf E) hn) (release := S.release (pubOf E)) _ _
      (encodeTxs (Model.mempool rho.inbox v t)) _ t.toNat
  · simp only [hone, List.map_cons, List.map_nil, engineDuty_eq]
    exact pollBatch_node_eq (sp := S.params (pubOf E) hn) (release := S.release (pubOf E)) _ _
      (encodeTxs (Model.mempool rho.inbox v t)) _ t.toNat

/-- An attestation admitted during a tick is released by the tick's first trailing poll. -/
theorem mem_admitsAt_rel_tick (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) {a : FG.Att (Fintype.card V)}
    (ha : a ∈ admitsAt S rho hn v i) :
    a ∈ pollFlush (shapeOf S hn (beforeTrailing S rho v i t)) (S.release (pubOf E)) ++
      if ((shapeOf S hn (beforeTrailing S rho v i t)).fgDue &&
          S.release (pubOf E) (shapeOf S hn (beforeTrailing S rho v i t)).self
            (shapeOf S hn (beforeTrailing S rho v i t)).now) = true then
        (fgSigned (shapeOf S hn (beforeTrailing S rho v i t))).toList
      else [] := by
  exact NodeAsChainShape.CanonicalTrace.Encoding.OpLaws.mem_admitsAt_rel
    (traceEncoding_opLaws S hn) (goldilocks_ready S hn) rho hv he _ (trailing_rel S rho hn)
    (by rw [← admitsAt_trace]; exact ha)

/-- The engine node before a tick's first trailing poll is the engine duty cut of that poll
(duty `p`, a `.poll` of an awake node). -/
theorem beforeTrailing_dutyCut (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) :
    ∃ p, EngineDutyCut S rho v i p (beforeTrailing S rho v i t) ∧ E.awake v t = true ∧
      ((Model.protoOf (compiled (goldilocks S)) E).duties t)[p]? = some (.poll t.toNat) := by
  have hm := List.mem_of_getElem? he
  have ht := (hv.in_horizon _ hm).1
  have hw := hv.tick_awake v t hm
  let ds := (Model.protoOf (compiled (goldilocks S)) E).duties t
  let pa := (skeleton (pubOf E) S.vote).proposeAt t
  let p := 3 + pa.length
  have key : ∀ {α : Type} (x y z : α) (l : List α),
      (([x, x, y] ++ l) ++ [x, z]).take (3 + l.length) = [x, x, y] ++ l ∧
        3 + l.length ≤ (([x, x, y] ++ l) ++ [x, z]).length ∧
        (([x, x, y] ++ l) ++ [x, z])[3 + l.length]? = some x := by
    intro α x y z l
    refine ⟨List.take_left' (by simp; omega), by simp; omega, ?_⟩
    rw [List.getElem?_append_right (by simp; omega)]
    simp [show 3 + l.length - (l.length + 1 + 1 + 1) = 0 by omega]
  have hds : ds = ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] ++ pa) ++
      [.poll t.toNat, .poll t.toNat] := by
    change (Model.protoOf (compiled (goldilocks S)) E).duties t = _
    rw [duties_eq S t ht]
    exact List.append_assoc _ _ _
  have hk := key (ShapeDuty.poll t.toNat : (Model.protoOf (compiled
    (goldilocks S)) E).Duty) (.pollPropose t.toNat) (.poll t.toNat) pa
  have htake : ds.take p = [.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] ++ pa := by
    rw [hds]; exact hk.1
  have hp : p ≤ ds.length := by rw [hds]; exact hk.2.1
  have hpoll : ds[p]? = some (.poll t.toNat) := by rw [hds]; exact hk.2.2
  have hcut : EngineDutyCut S rho v i p (beforeTrailing S rho v i t) := by
    have h := EngineDutyCut.tick (S := S) (rho := rho) (v := v) (i := i) (p := p) he hw hp
    rw [htake] at h
    exact cast (congrArg (EngineDutyCut S rho v i p) (runDuties_fst_append S rho v
      ⟨(Model.protoOf (compiled (goldilocks S)) E).clock (rho.stateBefore i v).st t
        (Model.mempool rho.inbox v t), (rho.stateBefore i v).seen⟩
      [.poll t.toNat, .poll t.toNat, .pollPropose t.toNat] pa)) h
  exact ⟨p, hcut, hw, hpoll⟩

/-- The attestation that the FG update of a tick's first trailing poll signs, when it is due, is
an engine signing of that poll. -/
theorem engineSignsAt_of_fgSigned (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) {p : Nat}
    (hcut : EngineDutyCut S rho v i p (beforeTrailing S rho v i t)) (hw : E.awake v t = true)
    (hpoll : ((Model.protoOf (compiled (goldilocks S)) E).duties t)[p]? = some (.poll t.toNat))
    (hdue : (shapeOf S hn (beforeTrailing S rho v i t)).fgDue = true)
    {a : FG.Att (Fintype.card V)}
    (ha : fgSigned (shapeOf S hn (beforeTrailing S rho v i t)) = some a) :
    EngineSignsAt S rho hn v i p a := by
  rw [fgSigned_eq] at ha
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at ha
  obtain ⟨C, hC, ⟨a', Λ'⟩, hatt, rfl⟩ := ha
  exact (engineSignsAt_iff S rho hn v i p _).2 ⟨_, hcut, t.toNat, Or.inl ⟨t, he, hw, hpoll⟩,
    poll_selected S rho hv v, hdue, C, Λ', hC, hatt⟩

/-- **An attestation the engine admits to a node's pool during a tick is released by the tick's
first trailing poll** (duty `p`, at the engine node `nd` before it): a held attestation that poll
flushes, or the attestation that poll's FG update signs at a time the schedule allows. -/
private theorem mem_admitsAt_tick (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) {a : FG.Att (Fintype.card V)}
    (ha : a ∈ admitsAt S rho hn v i) :
    ∃ p nd, EngineDutyCut S rho v i p nd ∧
      (a ∈ (nd.st.1 hn).held ∨ EngineSignsAt S rho hn v i p a) := by
  obtain ⟨p, hcut, hw, hpoll⟩ := beforeTrailing_dutyCut S rho hv he
  refine ⟨p, beforeTrailing S rho v i t, hcut, ?_⟩
  rcases List.mem_append.1 (mem_admitsAt_rel_tick S rho hn hv he ha) with h | h
  · left
    rw [pollFlush_eq] at h
    split at h
    · exact h
    · cases h
  · right
    split at h
    · rename_i hc
      obtain ⟨hdue, -⟩ := Bool.and_eq_true_iff.1 hc
      exact engineSignsAt_of_fgSigned S rho hn hv he hcut hw hpoll hdue
        (Option.mem_toList.1 h)
    · cases h

/-- **An attestation admitted during a tick was signed by the engine** at that tick or earlier. -/
theorem admitsAt_tick_signed (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) {a : FG.Att (Fintype.card V)}
    (ha : a ∈ admitsAt S rho hn v i) :
    ∃ j ≤ i, ∃ q, EngineSignsAt S rho hn v j q a := by
  obtain ⟨p, nd, hc, h | h⟩ := mem_admitsAt_tick S rho hn hv he ha
  · obtain ⟨-, j, q, hj, hs⟩ := engine_held_att_signed S rho hn hc h
    exact ⟨j, by rcases hj with hj | ⟨rfl, -⟩ <;> omega, q, hs⟩
  · exact ⟨i, le_rfl, p, h⟩

/-- **A tick admits only the node's own attestations**: a flushed held attestation and a fresh
signing both carry the node's own key. -/
private theorem admitsAt_tick_own (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) {a : FG.Att (Fintype.card V)}
    (ha : a ∈ admitsAt S rho hn v i) : a.val = rho.ownKey v := by
  obtain ⟨p, nd, hc, h | h⟩ := mem_admitsAt_tick S rho hn hv he ha
  · exact (engine_held_att_signed S rho hn hc h).1.trans (cut_self S rho hn hc)
  · obtain ⟨nd', hc', -, -, -, -, C, Λ', -, hat⟩ := (engineSignsAt_iff S rho hn v i p a).1 h
    exact (createAtt_val (by simpa only [Store.attest] using hat)).trans (cut_self S rho hn hc')

/-- Goldilocks' own-admission guard. -/
theorem goldilocks_admitsOwn : (traceEncoding (E := E) S hn).AdmitsOwn :=
  (Encoding.admitsOwn_iff _).2 fun rho hv _ _ _ he a ha =>
    admitsAt_tick_own S rho hn hv he (by rw [admitsAt_trace]; exact ha)

end Consensus.Goldilocks.Simulation
