module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunBlocks
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.GoldilocksStateAgreement

public section

/-! # Engine events as trace groups, given the node state

The engine/trace correspondence steps shared by the constant-fault rows of
`Simulation/RunSimulates` and the growing-fault rows of
`Growing/Simulation/{State,Events,PublishedBlocks}`. State agreement uses the same encoded replay
for both, and the group and release lemmas consume agreement or release facts at the actual event.

* `simTrace_state_of`: the engine node's state is the trace's state at every mapped cut;
* `restart_group_of_state`, `deliver_seq_of_state`: a restart of `v` is one group of the trace
  at the event's first cut, and a delivery is the
  groups of the canonical objects it delivers;
* `own_block_released_of`: an own block of the trace is released by its engine node at the
  cut's time. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

set_option linter.unusedVariables false in
/-- **The engine node's state is the trace's state at every mapped cut.** The concrete interface
retains the event-local premises; the encoded-node replay now derives agreement from validity. -/
theorem simTrace_state_of (hv : rho.ExecutionValid) {v : V}
    (hv0 : ∀ {i : Nat} {ev}, rho.events[i]? = some ev → ev.node = v → v ∉ rho.faultyAt 0) :
    ∀ i ≤ rho.events.length, (stateAt S rho hn v i).node =
        (simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i) := by
  intro i hi
  obtain ⟨htrace, hcut⟩ := simTrace_encoding S rho hn
  rw [htrace, hcut, stateAt_eq]
  refine (traceEncoding_induction S hn (fun e due _ => e.Lawful due →
    ((rho.stateBefore i v).st.1 hn).node =
      (NodeAsChainShape.CanonicalTrace.simTrace e rho).state (rho.ownKey v)
        (NodeAsChainShape.CanonicalTrace.cutMap e rho i)) ?_) (traceEncoding_lawful S hn)
  intro _ _ laws
  have h := NodeAsChainShape.CanonicalTrace.stateAgreement_all laws hv v i hi
  rw [NodeAsChainShape.CanonicalTrace.stateAt_eq] at h
  exact h

/-- **An engine delivery is the groups of the canonical objects it delivers**, given that the
engine node's state before the delivery is the trace's state there (`hstate`). -/
theorem deliver_seq_of_state {v : V} {i : Nat} {o} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t))
    (hstate : (stateAt S rho hn v i).node =
      (simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)) :
    DeliverSeq (runProposer S rho hn) (simTrace S rho hn) (digestOf S rho)
      (rho.voteIO v) (Model.digests rho.hash o) (rho.ownKey v) t
      (delivered (rho.voteIO v) (Model.digests rho.hash o) (stateAt S rho hn v i) o)
        (cutMap S rho hn i) (cutMap S rho hn (i + 1)) := by
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  rw [cutMap_succ, eventCuts_deliver S rho hn i v o t he]
  refine deliverSeq_of_recs S rho hn (runProposer S rho hn) (digestOf S rho)
    (rho.voteIO v) _ _ _ 0 _ (fun k hk => ?_) hstate.symm (fun k s hk _ => ?_)
  · rw [← eventCuts_deliver S rho hn i v o t he] at hk ⊢
    exact allCuts_getElem?_add S rho hn i k hi hk
  · have := range_of_event S rho hn hi hk
    rwa [cutMap_succ, eventCuts_deliver S rho hn i v o t he] at this

/-- **An engine restart is the node's restart group** at the event's first cut, given that the
engine node's state before the restart is the trace's state there (`hstate`). -/
theorem restart_group_of_state {v : V} {i : Nat} {t : Time}
    (he : rho.events[i]? = some (.restart v t))
    (hstate : (stateAt S rho hn v i).node =
      (simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)) :
    (simTrace S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (cutMap S rho hn i) t .restart ∧
      cutMap S rho hn (i + 1) = cutMap S rho hn i +
        (Node.exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        ((simTrace S rho hn).state (rho.ownKey v) (cutMap S rho hn i)) t .restart).2.length := by
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  rw [cutMap_succ, eventCuts_restart S rho hn i v t he]
  have h0 := hstate.symm
  have hne := exec_restart_ne_nil (runProposer S rho hn) (digestOf S rho)
    (rho.ownKey v) (stateAt S rho hn v i).node t
  have hcut : ∀ k < (groupRecs (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (stateAt S rho hn v i).node t
      (Nat.pair i 0) .restart).length,
      (allCuts S rho hn)[cutMap S rho hn i + k]? =
        (groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t (Nat.pair i 0) .restart)[k]? := fun k hk => by
    rw [← eventCuts_restart S rho hn i v t he] at hk ⊢
    exact allCuts_getElem?_add S rho hn i k hi hk
  have huniq : ∀ k, (simTrace S rho hn).event k = Nat.pair i 0 → cutMap S rho hn i ≤ k ∧
      k < cutMap S rho hn i + (groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t (Nat.pair i 0) .restart).length := fun k hk => by
    have := range_of_event S rho hn hi hk
    rwa [cutMap_succ, eventCuts_restart S rho hn i v t he] at this
  obtain ⟨hG, hlen⟩ :=
    groupAt_of_group S rho hn (runProposer S rho hn) (digestOf S rho) hcut h0 hne huniq
  exact ⟨hG, congrArg (cutMap S rho hn i + ·) hlen⟩

/-- **An own block is released at its cut's time** by its engine node: an own block is called
at a positive position, so by a public tick, whose releases `hrel` supplies; a delivery or a
restart calls blocks at position zero only. -/
theorem own_block_released_of (hrel : ∀ {i : Nat} {v : V} {t : Time},
      rho.events[i]? = some (.tick v t) → (S.params (pubOf E) hn).toParams.IsPublic t →
      ∀ r ∈ eventCuts S rho hn i, ∀ B acc, r.label = .fg (.block B acc) → r.pos ≠ 0 →
        blockObj (S.params (pubOf E) hn) B ∈ rho.releasesAt i)
    {y : Fin (Fintype.card V)} {k : Nat} {B : Blk (S.params (pubOf E) hn)}
    (hB : (simTrace S rho hn).OwnBlockAt y k B) :
    rho.releases (rho.key y) (blockObj (S.params (pubOf E) hn) B)
      ((simTrace S rho hn).time k) := by
  obtain ⟨⟨acc, hnode, hlab⟩, hpos⟩ := hB
  have hl : (simTrace S rho hn).label k ≠ none := by rw [hlab]; simp
  obtain ⟨r, i, ev, -, he, -, -, hidx, hn', ht, hp', hlab'⟩ :=
    simTrace_cut_origin S rho hn hl
  have hrl : r.label = .fg (.block B acc) := Option.some.inj (hlab'.symm.trans hlab)
  have hpos' : r.pos ≠ 0 := hp' ▸ hpos
  have hmem := List.mem_of_getElem? hidx
  have hkey : ev.node = rho.key y := key_of_ownKey S rho (hn'.symm.trans hnode)
  rw [ht, ← hkey]
  cases ev with
  | tick v t =>
    have hp : (S.params (pubOf E) hn).toParams.IsPublic t := by
      by_contra hp
      rw [eventCuts_tick_other S rho hn i v t he hp] at hmem
      obtain ⟨a, _, st, s, _, hg⟩ := mem_tickTail S rho hn v i t hmem
      obtain ⟨k', hk', rfl⟩ := List.getElem_of_mem hg
      have h := (getElem_groupRecs _ _ _ st t _ _ k' hk').2.2.2.2
      rw [hrl] at h
      simp [exec, onAttestation] at h
    exact ⟨i, Or.inl he, hrel he hp r hmem B acc hrl hpos'⟩
  | deliver v o t =>
    exfalso
    rw [eventCuts_deliver S rho hn i v o t he] at hmem
    obtain ⟨o', e, st', _, hce, kk, hk, hlabk, hposk⟩ :=
      mem_deliverRecs_exec _ _ _ _ _ _ _ _ _ _ hmem
    exact hpos' (hposk.trans
      (pos_of_block_cut _ _ _ _ _ (canonEvent_ne_tick hce) hk (hlabk.symm.trans hrl)))
  | restart v t =>
    exfalso
    rw [eventCuts_restart S rho hn i v t he] at hmem
    obtain ⟨kk, hk, rfl⟩ := List.getElem_of_mem hmem
    obtain ⟨-, -, -, hposk, hlabk⟩ := getElem_groupRecs _ _ _ _ _ _ _ kk hk
    have hk' := lt_of_lt_of_eq hk (length_groupRecs _ _ _ _ _ _ _)
    exact hpos' (hposk.trans (pos_of_block_cut _ _ _ _ _ (e := .restart)
      (fun _ _ h => by cases h) hk' (hlabk.symm.trans hrl)))

end Consensus.Goldilocks.Simulation

end
