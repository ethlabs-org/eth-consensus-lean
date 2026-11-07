module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunSimulates

public section

/-! # Engine states agree with the canonical growing trace

Validity makes every actual event an honest event, so each event realizes its node handler.
The canonical state correspondence is consequently unconditional in the observed node;
the consumer-facing interface retains its time-local honesty premise.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- Every bounded engine state matches the canonical event expansion. -/
theorem simTraceAt_state_all (hv : rho.ExecutionValid) (v : V) :
    ∀ i ≤ rho.events.length, (stateAt S rho hn v i).node =
      (simTraceAt S rho hn).state (rho.ownKey v) (cutMap S rho hn i) := by
  rw [simTraceAt_eq]
  intro i
  induction i with
  | zero =>
    intro _
    rw [cutMap_zero]
    exact (congrArg (·.node) (stateAt_zero S rho hn v)).trans
      (simTrace_init_eq S rho hn (rho.ownKey v)).symm
  | succ i ih =>
    intro hi
    have hi' : i < rho.events.length := by omega
    have ih := ih (by omega)
    have he : rho.events[i]? = some rho.events[i] := List.getElem?_eq_getElem hi'
    rw [cutMap_succ]
    by_cases hne : rho.events[i].node ≠ v
    · rw [state_of_other S rho hn v i _ he hne]
      refine ih.trans (state_of_block_ne S rho hn _ (fun k hk r hr => ?_)).symm
      rw [allCuts_getElem?_add S rho hn i k hi' hk] at hr
      obtain ⟨hnode, _, _⟩ := mem_eventCuts S rho hn he (List.mem_of_getElem? hr)
      rw [hnode]
      exact fun h => hne (rho.key.symm.injective h)
    rw [not_not] at hne
    have hcut : ∀ k < (eventCuts S rho hn i).length,
        (allCuts S rho hn)[cutMap S rho hn i + k]? = (eventCuts S rho hn i)[k]? :=
      fun k hk => allCuts_getElem?_add S rho hn i k hi' hk
    cases hev : rho.events[i] with
    | tick w t =>
      rw [hev] at he hne
      simp only [Model.Event.node] at hne
      subst hne
      by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
      · rw [eventCuts_tick_public S rho hn i w t he hp] at hcut ⊢
        rw [node_of_tick_public_at S rho hn hv w i t he hp]
        exact (state_of_group S rho hn _ _ hcut ih.symm).symm
      · rw [eventCuts_tick_other S rho hn i w t he hp, List.length_nil, Nat.add_zero,
          node_of_tick_other_at S rho hn hv w i t he hp]
        exact ih
    | deliver w o t =>
      rw [hev] at he hne
      simp only [Model.Event.node] at hne
      subst hne
      rw [eventCuts_deliver S rho hn i w o t he] at hcut ⊢
      rw [node_of_deliver_at S rho hn hv w i o t he]
      exact (state_of_deliverRecs S rho hn _ _ _ _ _ _ _ hcut ih.symm).symm
    | restart w t =>
      rw [hev] at he hne
      simp only [Model.Event.node] at hne
      subst hne
      rw [eventCuts_restart S rho hn i w t he] at hcut ⊢
      rw [node_of_restart_at S rho hn hv w i t he]
      exact (state_of_group S rho hn _ _ hcut ih.symm).symm

/-- Time-local state interface: the trace state at the mapped cut is the engine node
state observed while that node is honest. -/
theorem simTraceAt_state (hv : rho.ExecutionValid) {v : V} {i : Nat}
    (_hh : v ∉ rho.faultyAt (rho.cutTime i)) (hi : i ≤ rho.events.length) :
    (simTraceAt S rho hn).state (rho.ownKey v) (cutMap S rho hn i) =
      (stateAt S rho hn v i).node :=
  (simTraceAt_state_all S rho hn hv v i hi).symm

end Consensus.Goldilocks.Simulation
