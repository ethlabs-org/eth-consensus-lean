module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.State
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Schedule
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.EventGroups

public section

/-! # Canonical event groups under growing faults

All actual events correspond unconditionally: engine validity already requires the event
node to be honest at its own time. No terminal honest set is substituted for that condition.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- A public engine tick is exactly one canonical trace group. -/
theorem simTraceAt_tick_public_group (hv : rho.ExecutionValid)
    {v : V} {i : Nat} {t : Time} (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t) :
    (simTraceAt S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho)
        (rho.ownKey v) (cutMap S rho hn i) t
        (.tick (encodeTxs (Model.mempool rho.inbox v t))) ∧
      cutMap S rho hn (i + 1) = cutMap S rho hn i +
        (Node.exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        ((simTraceAt S rho hn).state (rho.ownKey v) (cutMap S rho hn i)) t
        (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2.length := by
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  have h0 := simTraceAt_state_all S rho hn hv v i hi.le
  rw [simTraceAt_eq] at h0 ⊢
  exact tick_public_group_of_state S rho hn he hp h0

/-- A node honest and awake at a public time ticks there. -/
theorem simTraceAt_tick_of_awake (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} {t : Time} (hy : y ∈ honestKeysAt S rho t)
    (ht0 : 0 ≤ t) (hp : (S.params (pubOf E) hn).toParams.IsPublic t)
    (hw : (simTraceAt S rho hn).awake y t) :
    ∃ j, (simTraceAt S rho hn).TickAt (runProposer S rho hn) (digestOf S rho) y j t := by
  obtain ⟨hwE, _, hth⟩ := (simTraceAt_awake_bounds S rho hn y t).mp hw
  have hh : rho.key y ∉ rho.faultyAt t := by
    rwa [mem_honestKeysAt_iff, min_eq_left hth] at hy
  obtain ⟨i, he⟩ := List.mem_iff_getElem?.mp (hv.tick_total _ t ht0 hth hh hwE)
  obtain ⟨hg, _⟩ := simTraceAt_tick_public_group S rho hn hv he hp
  rw [ownKey_key] at hg
  exact ⟨_, _, hg⟩

/-- A delivery expands to precisely the groups of its canonical objects. -/
theorem simTraceAt_deliver (hv : rho.ExecutionValid)
    {v : V} {i : Nat} {o} {t : Time} (he : rho.events[i]? = some (.deliver v o t)) :
    DeliverSeq (runProposer S rho hn) (simTraceAt S rho hn) (digestOf S rho)
      (Model.digests rho.hash o) (rho.ownKey v) t
      (delivered (S.params (pubOf E) hn) o) (cutMap S rho hn i) (cutMap S rho hn (i + 1)) := by
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
