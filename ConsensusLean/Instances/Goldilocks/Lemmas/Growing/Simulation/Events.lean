module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.State
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Schedule

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
        (.tick (encodeTxs (Model.mempool rho.inbox v t))) ∧
      cutMap S rho hn (i + 1) = cutMap S rho hn i +
        (Node.exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        ((simTraceAt S rho hn).state (rho.ownKey v) (cutMap S rho hn i)) t
        (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2.length := by
  rw [simTraceAt_eq]
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  rw [cutMap_succ, eventCuts_tick_public S rho hn i v t he hp]
  have h0 := (simTraceAt_state_all S rho hn hv v i hi.le).symm
  rw [simTraceAt_eq] at h0
  have hne := exec_tick_ne_nil (runProposer S rho hn) (digestOf S rho)
    (rho.ownKey v) (stateAt S rho hn v i).node t
    (encodeTxs (Model.mempool rho.inbox v t))
  have hcut : ∀ k < (groupRecs (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (stateAt S rho hn v i).node t
      (Nat.pair i 0) (.tick (encodeTxs (Model.mempool rho.inbox v t)))).length,
      (allCuts S rho hn)[cutMap S rho hn i + k]? =
        (groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t (Nat.pair i 0)
        (.tick (encodeTxs (Model.mempool rho.inbox v t))))[k]? := fun k hk => by
    rw [← eventCuts_tick_public S rho hn i v t he hp] at hk ⊢
    exact allCuts_getElem?_add S rho hn i k hi hk
  have huniq : ∀ k, (simTrace S rho hn).event k = Nat.pair i 0 → cutMap S rho hn i ≤ k ∧
      k < cutMap S rho hn i + (groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t (Nat.pair i 0)
        (.tick (encodeTxs (Model.mempool rho.inbox v t)))).length := fun k hk => by
    have := range_of_event S rho hn hi hk
    rwa [cutMap_succ, eventCuts_tick_public S rho hn i v t he hp] at this
  obtain ⟨hG, hlen⟩ :=
    groupAt_of_group S rho hn (runProposer S rho hn) (digestOf S rho) hcut h0 hne huniq
  exact ⟨hG, congrArg (cutMap S rho hn i + ·) hlen⟩

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
  rw [simTraceAt_eq]
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  have h0 := (simTraceAt_state_all S rho hn hv v i hi.le).symm
  rw [simTraceAt_eq] at h0
  rw [cutMap_succ, eventCuts_deliver S rho hn i v o t he]
  refine deliverSeq_of_recs S rho hn (runProposer S rho hn) (digestOf S rho)
    _ _ _ 0 _ (fun k hk => ?_) h0 (fun k s hk _ => ?_)
  · rw [← eventCuts_deliver S rho hn i v o t he] at hk ⊢
    exact allCuts_getElem?_add S rho hn i k hi hk
  · have := range_of_event S rho hn hi hk
    rwa [cutMap_succ, eventCuts_deliver S rho hn i v o t he] at this

/-- An engine restart is exactly one canonical restart group. -/
theorem simTraceAt_restart (hv : rho.ExecutionValid)
    {v : V} {i : Nat} {t : Time} (he : rho.events[i]? = some (.restart v t)) :
    (simTraceAt S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (cutMap S rho hn i) t .restart ∧
      cutMap S rho hn (i + 1) = cutMap S rho hn i +
        (Node.exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        ((simTraceAt S rho hn).state (rho.ownKey v) (cutMap S rho hn i)) t .restart).2.length := by
  rw [simTraceAt_eq]
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  rw [cutMap_succ, eventCuts_restart S rho hn i v t he]
  have h0 := (simTraceAt_state_all S rho hn hv v i hi.le).symm
  rw [simTraceAt_eq] at h0
  have hne := exec_restart_ne_nil (runProposer S rho hn) (digestOf S rho)
    (rho.ownKey v) (stateAt S rho hn v i).node t
  have hcut : ∀ k < (groupRecs (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (stateAt S rho hn v i).node t (Nat.pair i 0) .restart).length,
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

end Consensus.Goldilocks.Simulation
