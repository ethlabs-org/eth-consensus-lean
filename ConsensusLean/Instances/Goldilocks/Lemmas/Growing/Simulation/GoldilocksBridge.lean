module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.Boundaries
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Report.Row
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.RowService
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.CorrectnessEdges
public import ConsensusLean.Instances.Goldilocks.Statements.Obligations
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Truncation
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.GoldilocksBridge
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves

public section

/-! # The shared Goldilocks run interface

The shared run interface (`goldilocksRunInterface`) starts each node with its committee
permission: it supplies the canonical committee start and the Goldilocks run and start equations
(`goldilocksRunInterface_run_iff`, `goldilocksRunInterface_data`). The run transport and the
concrete sleepy adapters read it from here.
-/

namespace Consensus.Goldilocks.Generic

open AC (ACParams Payload gbar)
open Healing Healing.Growing

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp}

/-- The local run laws transfer by `LocalRun.truncH`; the Goldilocks-specific laws preserve the
same starts and the genesis root. -/
private theorem goldilocksRun_truncH {ini : Fin sp.n → (goldilocksNode sp).State}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr ini) (b : Time) :
    Consensus.Goldilocks.Growing.GoldilocksRun proposer dg (Generic.truncH H b) tr ini where
  toLocalRun := hrun.toLocalRun.truncH b
  vstart := hrun.vstart
  genesis_root_ok := hrun.genesis_root_ok

/-- Committee facts survive truncating honesty after `b`: the sizes do not read honesty, and P
and the gate read it only in hypotheses, where the truncation is a subset of `H`. -/
theorem _root_.Consensus.Goldilocks.Compose.Growing.CommitteeFacts.truncH
    {K : AC.CommitteeDict sp.n} (hK : Compose.Growing.CommitteeFacts tr H K) (b : Time) :
    Compose.Growing.CommitteeFacts tr (Generic.truncH H b) K where
  hsize := hK.hsize
  hP := ⟨fun t y hy i hi s v hv => hK.hP.1 t y hy.1 i hi s v hv,
    fun y i ℓ A hy hO s v hv => hK.hP.2 y i ℓ A hy.1 hO s v hv⟩
  hGate t ht x hx := hK.hGate t ht x hx.1

/-- The shared Goldilocks run interface, starting each node with its committee permission. -/
noncomputable def goldilocksRunInterface (sp : ACParams)
    (sign : Fin sp.n → Time → Bool := fun _ _ => true) (G : Nat := 0) :
    ACRun (goldilocksNode sp) (fun v => v.val) where
  Run cm proposer dg H tr := Growing.GoldilocksRun proposer dg H tr
    (AC.committeeStart sp.genesisRoot (dictOfTime sp cm)) ∧
    0 < sp.committeeSize ∧
    (∀ s, ((dictOfTime sp cm).committee s).ncard = sp.committeeSize) ∧
    (Compose.NoCollRun dg tr → Compose.Growing.CommitteeFacts tr H (dictOfTime sp cm)) ∧
    tr.SignCalendarAt proposer dg H sign ∧ SignGapAt sp.toParams sign G 0
  start cm := AC.committeeStart sp.genesisRoot (dictOfTime sp cm)
  run_local h := h.1.toLocalRun
  run_requirements h y := Compose.requirements_from sp (h.1.vstart y)
  run_root h := h.1.genesis_root_ok
  run_truncH h b := ⟨goldilocksRun_truncH h.1 b, h.2.1, h.2.2.1,
    (fun hnc => (h.2.2.2.1 hnc).truncH b),
    (fun y j t x fgDue hy hg => h.2.2.2.2.1 y j t x fgDue hy.1 hg), h.2.2.2.2.2⟩

/-- The run projection uses the committee-indexed initial AC states. -/
theorem goldilocksRunInterface_run_iff (cm : Time → Finset (Fin sp.n))
    {sign : Fin sp.n → Time → Bool} {G : Nat} :
    (goldilocksRunInterface sp sign G).Run cm proposer dg H tr ↔
      Growing.GoldilocksRun proposer dg H tr
        (AC.committeeStart sp.genesisRoot (dictOfTime sp cm)) ∧
      0 < sp.committeeSize ∧
      (∀ s, ((dictOfTime sp cm).committee s).ncard = sp.committeeSize) ∧
      (Compose.NoCollRun dg tr → Compose.Growing.CommitteeFacts tr H (dictOfTime sp cm)) ∧
      tr.SignCalendarAt proposer dg H sign ∧ SignGapAt sp.toParams sign G 0 := by rfl

/-- The shared run interface has the exact Goldilocks run and start equations. -/
theorem goldilocksRunInterface_data {sign : Fin sp.n → Time → Bool} {G : Nat} :
    GoldilocksRunData sp (goldilocksRunInterface sp sign G) sign G := by
  exact ⟨rfl, rfl⟩

end Consensus.Goldilocks.Generic
