module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Regimes.BlockFinality
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Always
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts

public section

/-! # Goldilocks suppliers for block-level finality accountability -/

namespace Consensus.Goldilocks.BlockFinality

private theorem requirements (sp : SA.SAParams)
    (ro : SA.ReplayOrder sp (List (FG.Att sp.n))) : (goldilocksNode sp ro).Requirements := by
  have h := SA.interface_requirements sp (List (FG.Att sp.n)) ro
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, SA.proposal_payload_valid sp _ ro⟩

/-- The original accountability row, discharged by the generic block theorem. -/
theorem goldilocks_final_accountable : Regimes.FinalAccountable := by
  intro sp ro dg H tr proposer hrun hnc
  exact final_accountable sp.toParams _ dg H _ tr proposer (requirements sp ro)
    hrun.genesis_root_ok hrun.toLocalRun hnc

/-- The original non-framing row needs only the local-run part of GoldilocksRun. -/
theorem goldilocks_non_framing : Regimes.NonFraming := by
  intro sp ro dg H tr proposer hrun
  exact non_framing sp.toParams _ dg H _ tr proposer hrun.toLocalRun

/-- The original finalized-safety row with its unchanged strict fault bound. -/
theorem goldilocks_finalized_safe : Regimes.FinalizedSafe := by
  intro sp ro dg H tr proposer hrun hnc
  exact finalized_safe sp.toParams _ dg H _ tr proposer (requirements sp ro)
    hrun.genesis_root_ok hrun.toLocalRun hnc

end Consensus.Goldilocks.BlockFinality

end
