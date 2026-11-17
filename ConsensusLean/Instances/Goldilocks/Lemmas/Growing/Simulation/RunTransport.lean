module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunCommittee
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunMap
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.GoldilocksBridge
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Members
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.NoColl

public section

/-! # The engine's run at its selected-committee start

The canonical trace's starts `simIni` are the canonical committee start of the run committee read
at each slot's start (`simIni_eq_runStart`): `voteK` binds the run's selection
(`voteK_bindsSel`), so `simIni_eq_committeeStart` applies, and the run committee read at slot
starts is `voteK` (`dictOfTime_runCommittee`). So the canonical trace is a run of the shared
Goldilocks run interface at the run committee (`goldilocksRunMap_transport`): a Goldilocks run from
those starts (`simTraceAt_goldilocksRun`, read through `goldilocksRunInterface_run_iff`), and
collision-free when the engine run is (`noCollRun_simTraceAt`). -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks
open Obligations.Growing (voteK voteK_bindsSel)
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] (S : Setup) {E : Env V}
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **The engine's starts are the run's selected-committee start.** -/
theorem simIni_eq_runStart (hv : rho.ExecutionValid) :
    simIni S rho hn = SA.committeeStart (S.params (pubOf E) hn).genesisRoot
      (Generic.dictOfTime (S.params (pubOf E) hn) (runCommittee S rho hn)) := by
  rw [dictOfTime_runCommittee]
  exact simIni_eq_committeeStart S rho hn hv (voteK_bindsSel S rho)

/-- **The committee facts of the canonical trace at the run committee** (`voteK_facts`). -/
theorem runCommittee_facts (hv : rho.ExecutionValid)
    (hnc : Compose.NoCollRun (digestOf S rho) (simTraceAt S rho hn)) :
    Compose.Growing.CommitteeFacts (simTraceAt S rho hn) (honestKeysAt S rho)
      (Generic.dictOfTime (S.params (pubOf E) hn) (runCommittee S rho hn)) := by
  rw [dictOfTime_runCommittee]
  exact Obligations.Growing.voteK_facts S rho hn hv hnc (simTraceAt_goldilocksRun S rho hn hv)

/-- **The canonical trace is a run of the shared run interface** at the run committee, from
`ExecutionValid` alone: the run's committee start, positive slot committees of `committeeSize`
members, and their facts under collision freedom. -/
theorem goldilocksRunInterface_run_at (hv : rho.ExecutionValid) :
    (Generic.goldilocksRunInterface (S.params (pubOf E) hn) (S.ro _)).Run (runCommittee S rho hn)
      (runProposer S rho hn) (digestOf S rho) (honestKeysAt S rho) (simTraceAt S rho hn) := by
  apply (Generic.goldilocksRunInterface_run_iff _).2
  refine ⟨simIni_eq_runStart S rho hn hv ▸ simTraceAt_goldilocksRun S rho hn hv,
    S.committeeSize_pos (pubOf E) hn, ?_, ?_⟩
  · rw [dictOfTime_runCommittee]
    exact Obligations.Growing.voteK_ncard S rho hn hv
  · exact runCommittee_facts S rho hn hv

/-- **The run map transports the engine run to the shared run interface**: its trace is a run of
`goldilocksRunInterface`, read at the run map's signer (`goldilocksRunMap_signer`), at its
committee, from `ExecutionValid` alone (`goldilocksRunInterface_run_at`), and collision-free when
the engine run has no hash collision. -/
theorem goldilocksRunMap_transport (hv : rho.ExecutionValid) :
    Generic.GrowingRunTransport (goldilocksRunMap S rho hn hv)
      ((goldilocksRunMap_signer S rho hn hv).symm ▸
        Generic.goldilocksRunInterface (S.params (pubOf E) hn) (S.ro _)) where
  run hv' := by
    rw [Generic.ACRun.cast_run, goldilocksRunMap_committee, goldilocksRunMap_proposer,
      goldilocksRunMap_digest, goldilocksRunMap_honest, goldilocksRunMap_trace]
    exact goldilocksRunInterface_run_at S rho hn hv'
  no_collision hv' hc := by
    rw [goldilocksRunMap_digest, goldilocksRunMap_trace]
    exact noCollRun_simTraceAt S rho hn hv' hc

end Consensus.Goldilocks.Simulation

end
