module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.State
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Schedule
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EventGroups
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.GoldilocksStateAgreement
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeRunSchedule

public section

/-! # Canonical event groups under growing faults

All actual events correspond unconditionally: engine validity already requires the event
node to be honest at its own time. No terminal honest set is substituted for that condition.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- A public engine tick is exactly one canonical trace group. -/
theorem simTraceAt_tick_public_group (hv : rho.ExecutionValid)
    {v : V} {i : Nat} {t : Time} (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t) :
    (simTraceAt S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho)
        (rho.ownKey v) (cutMap S rho hn i) t
        (.tick (encodeTxs (Model.mempool rho.inbox v t)) (S.sign (pubOf E) (rho.ownKey v) t)) ∧
      cutMap S rho hn (i + 1) = cutMap S rho hn i +
        (Node.exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        ((simTraceAt S rho hn).state (rho.ownKey v) (cutMap S rho hn i)) t
        (.tick (encodeTxs (Model.mempool rho.inbox v t))
          (S.sign (pubOf E) (rho.ownKey v) t))).2.length := by
  obtain ⟨htrace, hcut⟩ := simTrace_encoding S rho hn
  obtain ⟨hpr, hdg⟩ := runProposer_digestOf S rho hn
  rw [simTraceAt_eq, htrace, hcut, hpr, hdg]
  simpa only [traceEncoding_adapter_sign] using
    NodeAsChainShape.CanonicalTrace.tick_public_group (traceEncoding S hn) rho
      (traceEncoding_lawful S hn) hv he hp

/-- A node honest and awake at a public time ticks there. -/
theorem simTraceAt_tick_of_awake (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} {t : Time} (hy : y ∈ honestKeysAt S rho t)
    (ht0 : 0 ≤ t) (hp : (S.params (pubOf E) hn).toParams.IsPublic t)
    (hw : (simTraceAt S rho hn).awake y t) :
    ∃ j, (simTraceAt S rho hn).TickAt (runProposer S rho hn) (digestOf S rho) y j t := by
  obtain ⟨hpr, hdg⟩ := runProposer_digestOf S rho hn
  simp only [simTraceAt_eq, (simTrace_encoding S rho hn).1, hpr, hdg] at hw ⊢
  rw [mem_honestKeysAt_iff, ← NodeAsChainShape.CanonicalTrace.mem_honestKeysAt_iff] at hy
  exact NodeAsChainShape.CanonicalTrace.tick_of_awake (traceEncoding S hn) rho
    (traceEncoding_lawful S hn) hv hy ht0 hp hw

/-- A delivery expands to precisely the groups of its canonical objects. -/
theorem simTraceAt_deliver (hv : rho.ExecutionValid)
    {v : V} {i : Nat} {o} {t : Time} (he : rho.events[i]? = some (.deliver v o t)) :
    DeliverSeq (runProposer S rho hn) (simTraceAt S rho hn) (digestOf S rho)
      (rho.voteIO v) (Model.digests rho.hash o) (rho.ownKey v) t
      (delivered (rho.voteIO v) (Model.digests rho.hash o) (stateAt S rho hn v i) o)
        (cutMap S rho hn i) (cutMap S rho hn (i + 1)) := by
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  have h0 := simTraceAt_state_all S rho hn hv v i hi.le
  rw [simTraceAt_eq] at h0 ⊢
  exact deliver_seq_of_state S rho hn he h0

/-- An engine restart is exactly one canonical restart group. -/
theorem simTraceAt_restart (hv : rho.ExecutionValid)
    {v : V} {i : Nat} {t : Time} (he : rho.events[i]? = some (.restart v t)) :
    (simTraceAt S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (cutMap S rho hn i) t .restart ∧
      cutMap S rho hn (i + 1) = cutMap S rho hn i +
        (Node.exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        ((simTraceAt S rho hn).state (rho.ownKey v) (cutMap S rho hn i)) t .restart).2.length := by
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  have h0 := simTraceAt_state_all S rho hn hv v i hi.le
  rw [simTraceAt_eq] at h0 ⊢
  exact restart_group_of_state S rho hn he h0

end Consensus.Goldilocks.Simulation
