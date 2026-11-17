module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Boundaries
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.Row
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.RowService
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.CorrectnessEdges
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Truncation
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.GoldilocksBridge
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC

public section

/-! # The shared Goldilocks run interface

The shared run interface (`goldilocksRunInterface`) starts each node with its committee
permission: it supplies the canonical committee start and the Goldilocks run and start equations
(`goldilocksRunInterface_run_iff`, `goldilocksRunInterface_data`). The run transport and the
concrete sleepy adapters read it from here.
-/

namespace Consensus.Goldilocks.Generic

open SA (SAParams ReplayOrder Payload gbar)
open Healing Healing.Growing

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The shared Goldilocks run interface, starting each node with its committee permission. -/
noncomputable def goldilocksRunInterface (sp : SAParams)
    (ro : ReplayOrder sp (List (FG.Att sp.n))) :
    ACRun (goldilocksNode sp ro) (fun v => v.val) where
  Run cm proposer dg H tr := Growing.GoldilocksRun proposer dg H tr
    (SA.committeeStart sp.genesisRoot (dictOfTime sp cm)) ∧
    0 < sp.committeeSize ∧
    (∀ s, ((dictOfTime sp cm).committee s).ncard = sp.committeeSize) ∧
    (Compose.NoCollRun dg tr → Compose.Growing.CommitteeFacts tr H (dictOfTime sp cm))
  start cm := SA.committeeStart sp.genesisRoot (dictOfTime sp cm)
  run_local h := h.1.toLocalRun
  run_requirements h y := Compose.requirements_from sp ro (h.1.vstart y)
  run_root h := h.1.genesis_root_ok
  run_truncH h b := ⟨KernelProof.goldilocksRun_truncH h.1 b, h.2.1, h.2.2.1,
    fun hnc => (h.2.2.2 hnc).truncH b⟩

/-- The run projection uses the committee-indexed initial AC states. -/
theorem goldilocksRunInterface_run_iff (cm : Time → Finset (Fin sp.n)) :
    (goldilocksRunInterface sp ro).Run cm proposer dg H tr ↔
      Growing.GoldilocksRun proposer dg H tr
        (SA.committeeStart sp.genesisRoot (dictOfTime sp cm)) ∧
      0 < sp.committeeSize ∧
      (∀ s, ((dictOfTime sp cm).committee s).ncard = sp.committeeSize) ∧
      (Compose.NoCollRun dg tr → Compose.Growing.CommitteeFacts tr H (dictOfTime sp cm)) := by rfl

/-- The shared run interface has the exact Goldilocks run and start equations. -/
theorem goldilocksRunInterface_data :
    GoldilocksRunData sp ro (goldilocksRunInterface sp ro) := by
  exact ⟨rfl, rfl⟩

end Consensus.Goldilocks.Generic
