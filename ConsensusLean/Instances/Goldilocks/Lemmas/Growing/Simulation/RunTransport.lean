module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunCommittee
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Run

public section

/-! # The engine's run at its selected-committee start

The canonical trace's starts `simIni` are the canonical committee start of the run committee read
at each slot's start (`simIni_eq_runStart`): `voteK` binds the run's selection
(`voteK_bindsSel`), so `simIni_eq_committeeStart` applies, and the run committee read at slot
starts is `voteK` (`dictOfTime_runCommittee`). -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks
open Obligations.Growing (voteK voteK_bindsSel)
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] (S : BoundSetup) {E : Env V}
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-- **The engine's starts are the run's selected-committee start.** -/
theorem simIni_eq_runStart (hv : rho.ExecutionValid) :
    simIni S rho hn = SA.committeeStart (S.params (pubOf E) hn).genesisRoot
      (Generic.dictOfTime (S.params (pubOf E) hn) (runCommittee S rho hn)) := by
  rw [dictOfTime_runCommittee]
  exact simIni_eq_committeeStart S rho hn hv (voteK_bindsSel S rho)

end Consensus.Goldilocks.Simulation

end
