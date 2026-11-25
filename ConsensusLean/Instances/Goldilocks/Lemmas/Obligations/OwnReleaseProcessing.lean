module
public import ConsensusLean.Instances.Goldilocks.Results.Spec.CanonicalTrace
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeDeliveryOrigin

public section

/-! # A node processes its own attestations at their admission

An own attestation enters the node's pool when the engine releases it: at its signing when the
release schedule allows it at once, at the poll that flushes it otherwise. The canonical replay
processes each admission as its own `.attestation` group right after the own tick's group, in
the same engine event, so the node processes the attestation at the tick's time.

* `admit_processAt`: an attestation admitted to `v`'s pool during a tick of `v` at `t` is
  processed by `v` at a cut of time `t`. -/

namespace Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

open Blocks Shape Node

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
variable {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
variable {F : ChainShapeFamily O I} {p : Params} {hN : p.n = Fintype.card V}
variable {hn : 1 ≤ Fintype.card V}
variable {A : NodeAC (paramsAtCount p (Fintype.card V) hN hn)}
variable (e : Encoding F E p hN hn A) (rho : Model.Run (compiled F) E)

/-- **A node processes its own admissions at their time.** An attestation the engine admits to
`v`'s pool during a tick of `v` at `t` is processed by `v` at a cut of time `t`: its
`.attestation` group follows the tick's own group in the tick's event. -/
theorem admit_processAt {j : Nat} {v : V} {t : Time} (he : rho.events[j]? = some (.tick v t))
    {a : FG.Att (Fintype.card V)} (ha : a ∈ admitsAt e rho v j) :
    ∃ k, (simTrace e rho).AttCallAt (rho.ownKey v) k a ∧ (simTrace e rho).time k = t := by
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem ha
  obtain ⟨-, hget⟩ := admitRecs_getElem? (runProposer rho hn) (digestOf e rho) (rho.ownKey v) t j
    (admitsAt e rho v j) (postTick e rho e.adapter.sign v j t) 1
  have hrec := hget m hm
  have h0 := groupRecs_attestation_length (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
    (((admitsAt e rho v j).take m).foldl (fun n a => (exec (runProposer rho hn) (digestOf e rho)
      (rho.ownKey v) n t (.attestation a)).1) (postTick e rho e.adapter.sign v j t)) t
    (Nat.pair j (1 + m)) (admitsAt e rho v j)[m]
  obtain ⟨r, hr0⟩ : ∃ r, (groupRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
      (((admitsAt e rho v j).take m).foldl (fun n a => (exec (runProposer rho hn)
        (digestOf e rho) (rho.ownKey v) n t (.attestation a)).1)
        (postTick e rho e.adapter.sign v j t)) t
      (Nat.pair j (1 + m)) (.attestation (admitsAt e rho v j)[m]))[0]? = some r := by
    rw [List.getElem?_eq_getElem (by rw [h0]; exact Nat.one_pos)]
    exact ⟨_, rfl⟩
  obtain ⟨hlab, htime, hnode, -⟩ := mem_groupRecs_fields _ _ _ _ _ _ _ (List.mem_of_getElem? hr0)
  have hlab' : r.label = .fg (.attestation (admitsAt e rho v j)[m]) := by
    simpa [exec, onAttestation] using hlab
  have hmem : r ∈ eventCuts e rho j := by
    rw [eventCuts_tick e rho j v t he]
    exact List.mem_append_right _ (List.mem_of_getElem? (hrec.trans hr0))
  obtain ⟨k, hk', hkeq⟩ := List.getElem_of_mem hmem
  have hk := allCuts_getElem?_add e rho j k (List.getElem?_eq_some_iff.mp he).1 hk'
  rw [List.getElem?_eq_getElem hk', hkeq] at hk
  refine ⟨cutMap e rho j + k, ⟨?_, ?_⟩, ?_⟩
  · rw [simTrace_node, hk, Option.elim_some, hnode]
  · rw [simTrace_label, hk, Option.map_some, hlab']
  · rw [simTrace_time, hk, Option.elim_some, htime]

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation
open Shape Blocks

section Events

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **A node processes its own admissions at their time.** An attestation the engine admits to
`v`'s pool during a tick of `v` at `t` (`admitsAt`) is processed by `rho.ownKey v` at a cut of
time `t`. -/
theorem admit_processAt {j : Nat} {v : V} {t : Time} (he : rho.events[j]? = some (.tick v t))
    {a : FG.Att (Fintype.card V)} (ha : a ∈ admitsAt S rho hn v j) :
    ∃ k, (simTrace S rho hn).ProcessAttAt (rho.ownKey v) k a ∧
      (simTrace S rho hn).time k = t := by
  have hstate : ∀ i, (stateAt S rho hn v i).node =
      (traceEncoding S hn).adapter.node
        (NodeAsChainShape.CanonicalTrace.stateAt (traceEncoding S hn) rho v i) := fun i => by
    rw [stateAt_eq]
    exact traceEncoding_induction S hn (fun e _ _ =>
      ((rho.stateBefore i v).st.1 hn).node =
        e.adapter.node (NodeAsChainShape.CanonicalTrace.stateAt e rho v i)) fun _ => by
      rw (config := { transparency := .default })
        [NodeAsChainShape.CanonicalTrace.stateAt_eq, cast_eq]
      rfl
  rw [admitsAt_eq, hstate, hstate, ← NodeAsChainShape.CanonicalTrace.admitsAt_eq] at ha
  rw [(simTrace_encoding S rho hn).1]
  obtain ⟨k, hcall, htime⟩ :=
    NodeAsChainShape.CanonicalTrace.admit_processAt (traceEncoding S hn) rho he ha
  exact ⟨k, Or.inl hcall, htime⟩

end Events

end Consensus.Goldilocks.Obligations

end
