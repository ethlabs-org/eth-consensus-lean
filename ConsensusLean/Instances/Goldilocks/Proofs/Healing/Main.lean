module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Standalone
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Bridge
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Assembly
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Service
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Recovery
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Assembly
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Coverage
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Recovery.Reports
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.ResetInv

public section

/-! # Goldilocks milestone Healing

`HealingACStatements` (H.1, its corollary, H.2) and `HealingRunStatements` (HR.1–HR.4, H.2 (run),
H.3, H.4, `healing_run_statements`) from `Lemmas/Healing/`; H.3's `Inv` half after the reset is
`Lemmas/Healing/ResetInv` (`non_interference`, `T_b = max((8k + 20)Δ, 8Δ)`).

`PhaseServiceStatements` (HS.1–HS.4) is proved too (`phase_service_statements`; HS.3 is the
claims' after-`r` part, `frozen_tree_agreement`). The partial assemblies, without `sorry`:

* `healing_run_proved`: the run bundle without H.3 (HR.1–HR.4, H.2 (run), H.4);
  `non_interference_of_reset_inv` gives H.3 from its `Inv` half alone (H.3 (a) is HR.3, (b) is HR.4,
  the `Geo` half of (c) is `settled_geo`, combined at `max(T_b, 8Δ)` by `Inv.mono`); and
  `healing_run_statements_of_reset_inv` is the bundle from that half
  (`healing_run_statements_of_nonInterference` from H.3 as stated).
* `phase_service_proved`: HS.1, HS.2 and HS.4; `phase_service_statements` is the bundle with
  HS.3.

`RecoveryStatements` (HR.5, O.1 and C1.3) is `recovery_statements`: the actual-report and outcome
suppliers close the bounded high-coverage construction, then the recovery adapter discharges
all three unchanged public statements. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-- **Healing, the AC statements**: H.1, its corollary and H.2. -/
theorem healing_ac_statements : SA.HealingACStatements where
  standalone := SA.ac_healing_standalone
  corollary := SA.ac_healing_standalone_corollary
  inclusion := SA.ac_inclusion

/-! ## The run bundle -/

/-- **The proved run statements**: HR.1–HR.4, H.2 (run) and H.4 (conditional on the bridge, as
stated), i.e. `HealingRunStatements` without H.3 (`nonInterference`). -/
theorem healing_run_proved :
    CutAndReset ∧ (∀ (P : Params) (ACP : Type), PhaseCount P ACP) ∧ ResetExistence ∧
      HeightScopedRetention ∧ RunInclusion ∧ AvailableHealing :=
  ⟨cut_and_reset, phase_count, reset_existence, height_scoped_retention, run_inclusion,
    available_healing⟩

/-- **H.3 from its `Inv` half.** If the AC projection satisfies `Inv(a_z + T_b)` after the reset,
for a `T_b ≥ 0` that is a function of the parameters only, then H.3 holds: (a) is HR.3, (b) is
HR.4, and the bridge (c) takes `max(T_b, 8Δ)`, with `Inv` by monotonicity (`Inv.mono`) and `Geo`
from the settled phase (`settled_geo`). The premise is the open part of H.3. -/
theorem non_interference_of_reset_inv
    (hinv : ∃ Tb : Nat → Time → Time → Nat → Nat → Time, (∀ n Δ ΔF k δt, 0 ≤ Tb n Δ ΔF k δt) ∧
      ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
        (proposer : Nat → Fin sp.n)
        (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
        (tr : GoldilocksTrace sp ro) (g ΔF Gp : Time),
        GoldilocksRun proposer dg H tr → HSShared tr H dg g ΔF → CatchRun tr H g (2 * sp.Δ) →
        PropPlus tr H proposer g Gp → ∀ a, IsReset tr H g a →
          SA.Inv proposer tr.projAC H (tr.HonestBlocks H)
            (a + Tb sp.n sp.Δ ΔF sp.k sp.toParams.δt)) :
    NonInterference := by
  obtain ⟨Tb, hTb, hinv⟩ := hinv
  refine ⟨fun n Δ ΔF k δt => max (Tb n Δ ΔF k δt) (8 * Δ), fun n Δ ΔF k δt =>
    (hTb n Δ ΔF k δt).trans (le_max_left _ _),
    fun sp ro proposer dg H tr g ΔF Gp hrun hs hc hp => ?_⟩
  have hr := reset_existence sp ro proposer dg H tr g ΔF Gp hrun hs hc hp
  obtain ⟨a, ha⟩ := hr.2.2.1
  exact ⟨a, ha, (hr.2.2.2.1 a ha).trans hr.2.2.2.2.1,
    height_scoped_retention sp ro proposer dg H tr g ΔF hrun hs.healthy hs.noColl a ha,
    (hinv sp ro proposer dg H tr g ΔF Gp hrun hs hc hp a ha).mono
      (add_le_add_right (le_max_left _ _) a),
    fun p P hP htp hph => settled_geo hrun hs hc hp ha (le_max_right _ _) p P hP htp hph⟩

/-- **The run bundle from H.3's `Inv` half** (`non_interference_of_reset_inv` and
`healing_run_proved`). -/
theorem healing_run_statements_of_reset_inv
    (hinv : ∃ Tb : Nat → Time → Time → Nat → Nat → Time, (∀ n Δ ΔF k δt, 0 ≤ Tb n Δ ΔF k δt) ∧
      ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
        (proposer : Nat → Fin sp.n)
        (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
        (tr : GoldilocksTrace sp ro) (g ΔF Gp : Time),
        GoldilocksRun proposer dg H tr → HSShared tr H dg g ΔF → CatchRun tr H g (2 * sp.Δ) →
        PropPlus tr H proposer g Gp → ∀ a, IsReset tr H g a →
          SA.Inv proposer tr.projAC H (tr.HonestBlocks H)
            (a + Tb sp.n sp.Δ ΔF sp.k sp.toParams.δt)) :
    HealingRunStatements where
  cutAndReset := cut_and_reset
  phaseCount := phase_count
  resetExistence := reset_existence
  heightScopedRetention := height_scoped_retention
  runInclusion := run_inclusion
  nonInterference := non_interference_of_reset_inv hinv
  availableHealing := available_healing

/-- **The run bundle from H.3** as stated (the other fields are `healing_run_proved`). -/
theorem healing_run_statements_of_nonInterference (h3 : NonInterference) :
    HealingRunStatements where
  cutAndReset := cut_and_reset
  phaseCount := phase_count
  resetExistence := reset_existence
  heightScopedRetention := height_scoped_retention
  runInclusion := run_inclusion
  nonInterference := h3
  availableHealing := available_healing

/-- **Healing, the run statements**: HR.1–HR.4, H.2 on the run, H.3 (`non_interference`) and H.4. -/
theorem healing_run_statements : HealingRunStatements :=
  healing_run_statements_of_nonInterference non_interference

/-! ## The phase-service bundle -/

/-- **The proved phase-service statements**: HS.1, HS.2 and HS.4, i.e. `PhaseServiceStatements`
without HS.3 (`frozenTreeAgreement`, proved as `frozen_tree_agreement`). -/
theorem phase_service_proved :
    ViableWitnessRetention ∧ CleanLockDrain ∧ CommonPathAcquisition :=
  ⟨viable_witness_retention, clean_lock_drain, common_path_acquisition⟩

/-- **The phase-service statements** HS.1–HS.4. -/
theorem phase_service_statements : PhaseServiceStatements where
  viableWitnessRetention := viable_witness_retention
  cleanLockDrain := clean_lock_drain
  frozenTreeAgreement := frozen_tree_agreement
  commonPathAcquisition := common_path_acquisition

/-- **Healing Recovery**: HR.5 cache acceptance, O.1 pattern recovery and C1.3 finalizing
coverage, with the actual-report and outcome suppliers discharged. -/
theorem recovery_statements : RecoveryStatements := by
  apply Recovery.recovery_statements_of_coverage
  intro sp ro proposer dg H tr g ΔF Gp W M cF kF
  exact Recovery.pattern_coverage_supply Recovery.outcome_service
    (fun _ => Recovery.ready_proposal_report_supply)

end Consensus.Goldilocks.Healing

end
