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
* `Obligations.Growing.sleepy_grow_finite_at`: the finite growth row on the canonical growing
  trace at every vote binding, at the run's committees `voteK`, through a bound `b` with
  `t + (4k + 6)Δ ≤ b ≤ horizon`. Its inputs are derived from engine premises through `b`: the
  finite service from synchrony (`sleepyServiceBefore_of_syncUntil_at`), the population count
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

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **Finite growth of the engine under growing faults.** For `t ≥ 0`, `k ≥ 1` and
`t + (4k + 6)Δ ≤ b ≤ horizon`, a valid engine run with no observed hash collision, synchrony
through `b`, the sleepy budget (threshold `1/2`, catch-up `catchUp`, look-ahead `5Δ`) on `[0, b]`,
committee sleepy participation of the run's selection on `[0, b]` (threshold `θ ≥ 1/2`, a
catch-up `c` that covers joining, look-ahead `W ≥ 5Δ`), and one proposer ready at its slot start
and honest through its hold in every window of `k` slots up to `t + (4k + 6)Δ`: some proposal
released at `τ > t` by a proposer ready at `τ` and honest through its hold is in every ready read at
`t + (4k + 6)Δ`, in no ready read at `t`, and each ready read at `t` is an ancestor of each ready
read at `t + (4k + 6)Δ`. -/
theorem sleepy_grow_finite_at (hv : rho.ExecutionValid) (hc : ¬ rho.HashCollision)
    {t b : Time} {k : Nat} (ht : 0 ≤ t) (hk : 1 ≤ k)
    (htb : t + (4 * k + 6) * (S.params (pubOf E) hn).Δ ≤ b) (hbh : b ≤ rho.horizon)
    (hnet : rho.log.SyncUntil rho.point b)
    (hhalf : rho.point.SleepyOn (1 / 2) (Regimes.catchUp (S.params (pubOf E) hn))
      (5 * (S.params (pubOf E) hn).Δ) 0 b)
    {θ : ℚ} {η c W : Time} (hθ : 1 / 2 ≤ θ) (hcu : 8 * (S.params (pubOf E) hn).Δ ≤ c + 1)
    (hW : 5 * (S.params (pubOf E) hn).Δ ≤ W)
    (hcs : rho.point.CommitteeSleepyOn
      ((shapeProgress (goldilocks S) V).toExternal.selected rho.point.env
        ((shapeProgress (goldilocks S) V).toExternal.ext ⟨E, rho⟩))
      θ η c W 0 b)
    (hrec : Regimes.Growing.ProposerRecurrence (simTraceAt S rho hn) (honestKeysAt S rho)
      (runProposer S rho hn) (Regimes.catchUp (S.params (pubOf E) hn)) k
      (Regimes.Growing.hold (S.params (pubOf E) hn)) 0
      (t + (4 * k + 6) * (S.params (pubOf E) hn).Δ)) :
    ∃ τ P, t < τ ∧
      Regimes.Growing.ReadyProposalAt (simTraceAt S rho hn) (honestKeysAt S rho)
        (Regimes.catchUp (S.params (pubOf E) hn)) τ
        (Regimes.Growing.hold (S.params (pubOf E) hn)) P ∧
      (∀ y j, Regimes.Growing.ReadyAt (simTraceAt S rho hn) (honestKeysAt S rho)
          (Regimes.catchUp (S.params (pubOf E) hn)) y
          (t + (4 * k + 6) * (S.params (pubOf E) hn).Δ) →
        Regimes.CutAfter (simTraceAt S rho hn) j (t + (4 * k + 6) * (S.params (pubOf E) hn).Δ) →
        Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho)) P
          (Regimes.readAfter (simTraceAt S rho hn) y j
            (t + (4 * k + 6) * (S.params (pubOf E) hn).Δ))) ∧
      (∀ x jx, Regimes.Growing.ReadyAt (simTraceAt S rho hn) (honestKeysAt S rho)
          (Regimes.catchUp (S.params (pubOf E) hn)) x t →
        Regimes.CutAfter (simTraceAt S rho hn) jx t →
        ¬ Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho)) P
          (Regimes.readAfter (simTraceAt S rho hn) x jx t)) ∧
      ∀ x jx y j, Regimes.Growing.ReadyAt (simTraceAt S rho hn) (honestKeysAt S rho)
          (Regimes.catchUp (S.params (pubOf E) hn)) x t →
        Regimes.CutAfter (simTraceAt S rho hn) jx t →
        Regimes.Growing.ReadyAt (simTraceAt S rho hn) (honestKeysAt S rho)
          (Regimes.catchUp (S.params (pubOf E) hn)) y
          (t + (4 * k + 6) * (S.params (pubOf E) hn).Δ) →
        Regimes.CutAfter (simTraceAt S rho hn) j (t + (4 * k + 6) * (S.params (pubOf E) hn).Δ) →
        Anc ((simTraceAt S rho hn).HonestBlocksAt (honestKeysAt S rho))
          (Regimes.readAfter (simTraceAt S rho hn) x jx t)
          (Regimes.readAfter (simTraceAt S rho hn) y j
            (t + (4 * k + 6) * (S.params (pubOf E) hn).Δ)) := by
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
