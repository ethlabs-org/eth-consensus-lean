module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Interface
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.Const
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Constant-fault reduction of growing simulation

The event fields stay unguarded for growing consumers. Their static reduction needs only
the engine's `honest_only` schedule law, not the remaining execution-validity conditions.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- Constant-fault simulation agrees with static simulation when every engine event's node
is honest at its event time (`ExecutionValid.honest_only`). This premise is needed because
the growing event fields are unguarded, whereas static simulation constrains only honest
nodes: constant faults alone would still permit invalid runs with faulty-node events. -/
theorem simulatesAt_iff (hc : rho.point.ConstantFaults)
    (honest_only : ∀ e ∈ rho.events, e.node ∉ rho.faultyAt e.time)
    (tr : GoldilocksTrace (S.params (pubOf E) hn) (S.ro _)) (ι : Nat → Nat) :
    SimulatesAt S rho hn tr ι ↔ Simulates S rho hn tr ι := by
  have hkeys : honestKeysAt S rho = fun _ => honestKeys S rho :=
    funext (honestKeysAt_of_constant S rho hc)
  have hrun : Growing.GoldilocksRun (runProposer S rho hn) (digestOf S rho)
      (honestKeysAt S rho) tr ↔
      GoldilocksRun (runProposer S rho hn) (digestOf S rho) (honestKeys S rho) tr := by
    rw [hkeys, Growing.GoldilocksRun.const_iff]
  constructor
  · intro h
    exact
      { run := hrun.mp h.run
        ι_zero := h.ι_zero
        ι_mono := h.ι_mono
        covered := h.covered
        state := fun v hv i hi => h.state v i hi (by rwa [rho.faultyAt_eq_zero hc])
        now := h.now
        tick_public := fun v _ => h.tick_public v
        tick_other := fun v _ => h.tick_other v
        deliver := fun v _ => h.deliver v
        restart := fun v _ => h.restart v
        awake_of := fun y hy t => h.awake_of y t (by simpa only [hkeys] using hy)
        awake_to := fun y hy t => h.awake_to y t (by simpa only [hkeys] using hy)
        block_released := fun y hy k B =>
          h.block_released y k B (by simpa only [hkeys] using hy)
        vote_released := fun y hy k m =>
          h.vote_released y k m (by simpa only [hkeys] using hy)
        att_released := fun y hy k a =>
          h.att_released y k a (by simpa only [hkeys] using hy)
        block_relayed := fun y hy k B =>
          h.block_relayed y k B (by simpa only [hkeys] using hy)
        vote_forwarded := fun y hy k m =>
          h.vote_forwarded y k m (by simpa only [hkeys] using hy)
        att_relayed := fun y hy k a =>
          h.att_relayed y k a (by simpa only [hkeys] using hy) }
  · intro h
    have hevent {i : Nat} {e : Model.Event V (Model.protoOf (compiled (goldilocks S)) E).Object}
        (he : rho.events[i]? = some e) : e.node ∉ rho.faultyAt 0 := by
      simpa only [rho.faultyAt_eq_zero hc] using
        honest_only e (List.mem_of_getElem? he)
    exact
      { run := hrun.mpr h.run
        ι_zero := h.ι_zero
        ι_mono := h.ι_mono
        covered := h.covered
        state := fun v i hi hv =>
          h.state v (by rwa [← rho.faultyAt_eq_zero hc (rho.cutTime i)]) i hi
        now := h.now
        tick_public := fun v i t he => h.tick_public v (hevent he) i t he
        tick_other := fun v i t he => h.tick_other v (hevent he) i t he
        deliver := fun v i o t he => h.deliver v (hevent he) i o t he
        restart := fun v i t he => h.restart v (hevent he) i t he
        awake_of := fun y t hy => h.awake_of y (by simpa only [hkeys] using hy) t
        awake_to := fun y t hy => h.awake_to y (by simpa only [hkeys] using hy) t
        block_released := fun y k B hy =>
          h.block_released y (by simpa only [hkeys] using hy) k B
        vote_released := fun y k m hy =>
          h.vote_released y (by simpa only [hkeys] using hy) k m
        att_released := fun y k a hy =>
          h.att_released y (by simpa only [hkeys] using hy) k a
        block_relayed := fun y k B hy =>
          h.block_relayed y (by simpa only [hkeys] using hy) k B
        vote_forwarded := fun y k m hy =>
          h.vote_forwarded y (by simpa only [hkeys] using hy) k m
        att_relayed := fun y k a hy =>
          h.att_relayed y (by simpa only [hkeys] using hy) k a }

/-- Growing engine simulation implies its constant-fault counterpart. -/
theorem engineSimulatesNode_of_at (h : EngineSimulatesNodeAt V S) : EngineSimulatesNode V S := by
  apply (engineSimulatesNode_iff V S).mpr
  intro E rho hn hc hv
  obtain ⟨tr, ι, hs⟩ := (engineSimulatesNodeAt_iff V S).mp h E rho hn hv
  exact ⟨tr, ι, (simulatesAt_iff S rho hn hc hv.honest_only tr ι).mp hs⟩

/-- Growing collision transport implies its constant-fault counterpart. -/
theorem noCollTransport_of_at (h : NoCollTransportAt V S) : NoCollTransport V S := by
  apply (noCollTransport_iff V S).mpr
  intro E rho hn _ hv hnc
  rw [← simTraceAt_eq]
  exact (noCollTransportAt_iff V S).mp h E rho hn hv hnc

end Consensus.Goldilocks.Simulation
