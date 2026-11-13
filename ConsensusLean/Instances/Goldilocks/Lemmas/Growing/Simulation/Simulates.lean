module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.PublishedAttestations
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.VoteForward

public section

/-! # Engine-to-trace simulation under growing faults -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- The canonical trace simulates every valid growing-fault engine execution, from the engine's
own starts. -/
theorem simTraceAt_simulates (hv : rho.ExecutionValid)
    [Fact (S.vote.participationKind = none)] : -- TEMP(C2)
    SimulatesAt S rho hn (simTraceAt S rho hn) (cutMap S rho hn) (simIni S rho hn) where
  run := simTraceAt_goldilocksRun S rho hn hv
  ι_zero := cutMap_zero S rho hn
  ι_mono := cutMap_mono S rho hn
  covered := by rw [simTraceAt_eq]; exact simTrace_covered S rho hn
  state := fun v i hi _ => simTraceAt_state_all S rho hn hv v i hi
  now := now_eq_lastClock S rho hn hv
  tick_public := fun _ _ _ he hp => simTraceAt_tick_public_group S rho hn hv he hp
  tick_other := by
    intro v i t he hp
    rw [cutMap_succ, eventCuts_tick_other S rho hn i v t he hp,
      List.length_nil, Nat.add_zero]
  deliver := fun _ _ _ _ he => simTraceAt_deliver S rho hn hv he
  restart := fun _ _ _ he => simTraceAt_restart S rho hn hv he
  awake_of := fun y t _ hw => (simTraceAt_awake_bounds S rho hn y t).mp hw
  awake_to := fun _ _ _ hw ht hh => simTraceAt_awake_to S rho hn hv hw ht hh
  block_released := simTraceAt_block_released S rho hn hv
  vote_released := simTraceAt_vote_released S rho hn hv
  att_released := simTraceAt_att_released S rho hn hv
  block_relayed := simTraceAt_block_relayed S rho hn hv
  vote_forwarded := simTraceAt_vote_forwarded S rho hn hv
  att_relayed := simTraceAt_att_relayed S rho hn hv

end Consensus.Goldilocks.Simulation
