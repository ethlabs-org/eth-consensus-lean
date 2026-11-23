module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Groups
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeDeliveryOrigin
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeRunSchedule

public section

/-! # A node processes what it releases at the release time: the event-local steps

The attestations a node signs and the votes it sends or freshly admits are processed by the node
at the time of their release. The steps below read the simulating trace's events and the node's
own cuts only, not the fault model; each fault model supplies the tick group of the node and its
run, and the release or source facts of its own.

* `tick_attest_processAt`: an attestation signed in a public tick's group is processed by the
  node at the tick. -/

namespace Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

open Blocks Shape Node

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
variable {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
variable {F : ChainShapeFamily O I} {p : Params} {hN : p.n = Fintype.card V}
variable {hn : 1 ≤ Fintype.card V}
variable {A : NodeAC (paramsAtCount p (Fintype.card V) hN hn)}
variable (e : Encoding F E p hN hn A) (rho : Model.Run (compiled F) E)

private theorem tick_attest_next {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t))
    (hp : (paramsAtCount p (Fintype.card V) hN hn).IsPublic t)
    (hlenEq : cutMap e rho (i + 1) = cutMap e rho i +
      (exec (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
        (e.adapter.node (stateAt e rho v i)) t
        (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2.length)
    {m : Nat} {C : A.Blk} {a : FG.Att (Fintype.card V)}
    (hc : (exec (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
      (e.adapter.node (stateAt e rho v i)) t
      (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2[m]? = some (.fg (.attest C (some a)))) :
    (simTrace e rho).AttCallAt (rho.ownKey v) (cutMap e rho i + (m + 1)) a ∧
      (simTrace e rho).time (cutMap e rho i + (m + 1)) = t ∧
      cutMap e rho i + (m + 1) < cutMap e rho (i + 1) := by
  let st := e.adapter.node (stateAt e rho v i)
  let ev : Node.Event A := .tick (encodeTxs (Model.mempool rho.inbox v t))
  let cs := (exec (runProposer rho hn) (digestOf e rho) (rho.ownKey v) st t ev).2
  have hnxt := Compose.exec_attest_next (A := A) (C := C) (a := a)
    (runProposer rho hn) (digestOf e rho) (rho.ownKey v) st t ev hc
  have hEC := eventCuts_tick e rho i v t he
  rw [ite_eq_left hp, groupRecs_eq] at hEC
  change eventCuts e rho i = (cs.zip (cutPosts (rho.ownKey v) t cs st)).mapIdx _ at hEC
  have hlen : m + 1 < (eventCuts e rho i).length := by
    have h := (List.getElem?_eq_some_iff.mp hnxt).1
    change m + 1 < cs.length at h
    change _ = cutMap e rho i + cs.length at hlenEq
    rw [cutMap_succ] at hlenEq
    omega
  have hk := allCuts_getElem?_add e rho i (m + 1) (List.getElem?_eq_some_iff.mp he).1 hlen
  rw [List.getElem?_eq_getElem hlen, List.getElem_of_eq hEC hlen,
    List.getElem_mapIdx, List.getElem_zip] at hk
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [simTrace_node, hk]; rfl
  · rw [simTrace_label, hk, Option.map_some, Option.some.injEq]
    exact (List.getElem?_eq_some_iff.mp hnxt).2
  · rw [simTrace_time, hk]; rfl
  · rw [cutMap_succ]; omega

/-- A signing cut is immediately followed by processing the same attestation, within the
same public tick group. The handler's successful successor lookup rules out a final signing cut. -/
theorem tick_attest_processAt {due : e.State hn → Bool} (laws : e.Lawful due)
    (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)} {k : Nat} {a : FG.Att (Fintype.card V)}
    (hc : (simTrace e rho).SignAt y k a) :
    (simTrace e rho).AttCallAt y (k + 1) a ∧ (simTrace e rho).ProcessAttAt y (k + 1) a ∧
      (simTrace e rho).time (k + 1) = (simTrace e rho).time k ∧
      ∃ i v t, rho.events[i]? = some (.tick v t) ∧ cutMap e rho i ≤ k ∧
        k + 1 < cutMap e rho (i + 1) := by
  obtain ⟨C, hy, hl⟩ := hc
  obtain ⟨i, ev, r, he, hlo, hr, hrl, ht, hnode, _, _, _⟩ := labelled_cut_origin e rho hl
  cases ev with
  | restart v t =>
    rw [eventCuts_restart e rho i v t he, groupRecs_eq, List.getElem?_eq_some_iff] at hr
    obtain ⟨_, rfl⟩ := hr
    simp [exec, Node.restart, acCall] at hrl
  | deliver v o t =>
    obtain ⟨w, ev, st, _, hevent, hm⟩ := delivery_origin e rho he (List.mem_of_getElem? hr)
    obtain ⟨x, rfl⟩ := Compose.signed_only_in_ticks (A := A) (runProposer rho hn)
      (digestOf e rho) (rho.ownKey v) st t ev C a (hrl ▸ hm)
    unfold canonEvent at hevent
    split at hevent <;> cases hevent
  | tick v t =>
    rw [eventCuts_tick e rho i v t he] at hr
    split at hr
    · rename_i hp
      rw [groupRecs_eq, List.getElem?_eq_some_iff] at hr
      obtain ⟨hm, rfl⟩ := hr
      simp only [List.getElem_mapIdx, List.getElem_zip] at hrl
      have hsig := (List.getElem?_eq_getElem _).trans (congrArg some hrl)
      have hlen := (tick_public_group e rho laws hv he hp).2
      rw [← stateAgreement_all laws hv v i (List.getElem?_eq_some_iff.mp he).1.le] at hlen
      obtain ⟨hcall, htime, hhi⟩ := tick_attest_next e rho he hp hlen hsig
      have hindex : cutMap e rho i + (k - cutMap e rho i + 1) = k + 1 := by omega
      rw [hindex] at hcall htime hhi
      rw [hy.symm.trans hnode]
      exact ⟨hcall, Or.inl hcall, htime.trans ht.symm, i, v, t, he, hlo, hhi⟩
    · simp at hr

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation
open Shape Blocks

section Events

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **An attestation signed in a public tick is processed at the tick.** The tick event `i` of
`v` at a public time `t` whose group has the signing cut `fg_attest(C)` of `a` has a cut of
`rho.ownKey v` processing `a` at time `t`. -/
theorem tick_attest_processAt {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (Model.pubOf E) hn).toParams.IsPublic t)
    {a : FG.Att (Fintype.card V)} {C : Blk (S.params (Model.pubOf E) hn)}
    (hc : Cut.fg (.attest C (some a)) ∈ (Node.exec (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (stateAt S rho hn v i).node t
      (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2) :
    ∃ k, (simTrace S rho hn).ProcessAttAt (rho.ownKey v) k a ∧
      (simTrace S rho hn).time k = t := by
  have hlen := cutMap_succ S rho hn i
  rw [eventCuts_tick_public S rho hn i v t he hp, length_groupRecs] at hlen
  obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hc
  obtain ⟨hpr, hdg⟩ := runProposer_digestOf S rho hn
  have htrace := simTrace_encoding S rho hn
  have hstate : (stateAt S rho hn v i).node =
      (traceEncoding S hn).adapter.node
        (NodeAsChainShape.CanonicalTrace.stateAt (traceEncoding S hn) rho v i) := by
    rw [stateAt_eq]
    exact traceEncoding_induction S hn (fun e _ _ =>
      ((rho.stateBefore i v).st.1 hn).node =
        e.adapter.node (NodeAsChainShape.CanonicalTrace.stateAt e rho v i)) fun _ => by
      rw (config := { transparency := .default })
        [NodeAsChainShape.CanonicalTrace.stateAt_eq, cast_eq]
      rfl
  rw [hpr, hdg, hstate] at hm
  rw [htrace.2, hpr, hdg, hstate] at hlen
  obtain ⟨hcall, htime, _⟩ := NodeAsChainShape.CanonicalTrace.tick_attest_next
    (traceEncoding S hn) rho he hp hlen (C := C) (a := a) hm
  rw [htrace.1]
  exact ⟨_, Or.inl hcall, htime⟩

end Events

end Consensus.Goldilocks.Obligations

end
