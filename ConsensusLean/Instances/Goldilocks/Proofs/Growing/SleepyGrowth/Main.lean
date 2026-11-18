module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Growth
public import ConsensusLean.Instances.Goldilocks.Results.Statements.SleepyGrowth
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Engine.Transport
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Outage.Engine.Members
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.NoColl
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Growing Sleepy strict growth (R.2): the committee rows and the engine form

* `Regimes.Growing.include_sleepy`, `Regimes.Growing.grow_sleepy`: the committee rows
  `IncludeSleepy` and `GrowSleepy` (`Results/Statements/SleepyGrowth`) from the finite rows
  `include_sleepy_at` and `grow_sleepy_at` through `b = t` and `b = t + D`, with their finite
  inputs derived from the rows' premises (`Lemmas/Growing/Sleepy/Service/Growth`).
* `Obligations.Growing.sleepy_grow_finite_at : SleepyGrowFinite`: the finite growth row on the
  canonical growing trace at every vote binding, at the run's committees `voteK`, through a bound
  `b` with `t + (4k + 6)Δ ≤ b ≤ horizon`. Its inputs are derived from engine premises through `b`:
  the finite service from synchrony (`sleepyServiceBefore_of_syncUntil_at`), the population count
  shapes from the sleepy budget (`sleepy_bounds_at`), the committee facts (`voteK_facts`) and the
  committee count shapes from committee sleepy participation of the run's selection
  (`committee_bounds_at`). Nothing is asserted beyond the horizon: no whole-run `SleepyRunAt` or
  `CommitteeSleepy` is inferred from the finite engine run. -/

namespace Consensus.Goldilocks.Regimes.Growing

open SA (SAParams ReplayOrder Payload)

/-- **R.2, `includeSleepy`, at a committee**, from `include_sleepy_at` through `b = t`. -/
theorem include_sleepy : IncludeSleepy := by
  intro sp ro dg H tr proposer ΔF K hrun hnc hKB hsl hCS τ P hP y t j ht hy hj
  have hb0 : 0 ≤ t := by
    obtain ⟨_, kP, -, -, -, hkP⟩ := hP
    have := hrun.time_nonneg kP
    linarith [sp.toParams.hΔ]
  exact include_sleepy_at hrun hnc hb0 (sleepyServiceBefore_of_syncOnAt hrun hsl.1 t)
    (sleepyBoundsFrom_of_sleepyRunAt hrun.antitone hsl t) hP ht le_rfl hy hj hKB
    (hCS.boundsFrom t)

/-- **R.2, `growSleepy`, at a committee**, from `grow_sleepy_at` through `b = t + D`. -/
theorem grow_sleepy : GrowSleepy := by
  intro sp ro dg H tr proposer ΔF k K hrun hnc hKB hsl hCS hk D t ht hrec
  have hb0 : 0 ≤ t + D := by
    have := sp.toParams.hΔ
    positivity
  exact grow_sleepy_at hrun hnc hb0 (sleepyServiceBefore_of_syncOnAt hrun hsl.1 (t + D))
    (sleepyBoundsFrom_of_sleepyRunAt hrun.antitone hsl (t + D)) hk ht le_rfl hrec hKB
    (hCS.boundsFrom (t + D))

end Consensus.Goldilocks.Regimes.Growing

namespace Consensus.Goldilocks.Obligations.Growing

open AsChainShape Simulation
open Shape
open Consensus.Model (pubOf)

/-- **R.2, growth, of the engine through a finite horizon** (`SleepyGrowFinite`): the finite growth
row `grow_sleepy_at` on the canonical growing trace at the run's committees `voteK`, with its
inputs from the engine premises through `b`. -/
theorem sleepy_grow_finite_at : SleepyGrowFinite := by
  intro S V _ _ E rho hn hv hc t b k ht hk htb hbh hnet hhalf θ η c W hθ hcu hW hcs hrec
  have hΔ := (S.params (pubOf E) hn).toParams.hΔ
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  have hnc := noCollRun_simTraceAt S rho hn hv hc
  have hb0 : 0 ≤ b := le_trans (by positivity) htb
  have hσ : (0 : Time) ≤ (S.params (pubOf E) hn).ts 0 + (S.params (pubOf E) hn).Δ :=
    add_nonneg (Compose.Growing.ts_natCast_nonneg 0) hΔ.le
  exact Regimes.Growing.grow_sleepy_at hrun hnc hb0
    (sleepyServiceBefore_of_syncUntil_at S rho hn hv hnc hbh hnet)
    (sleepy_bounds_at S rho hn hv hbh hhalf hσ (le_max_right _ _)) hk ht htb hrec
    (voteK_facts S rho hn hv hnc hrun)
    (committee_bounds_at S rho hn hv hrun (fun _ ht' _ => mem_voteK_iff_selected S rho hn hv ht')
      (voteK_nonempty S rho hn hv) hθ hcu hW hbh hcs hσ (le_max_right _ _))

end Consensus.Goldilocks.Obligations.Growing

end
