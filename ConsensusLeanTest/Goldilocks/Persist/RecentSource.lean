module
public import ConsensusLeanTest.Goldilocks.Persist.Premises
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Persist.Induction
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
@[expose] public section

/-! # C1.1's corollary, recent source, next vote: the premises at slot `m = 1`

Kind (a), joint satisfiability (CONTRIBUTING "Statements"), of `Compose.RecentSourceNextVote` on
the one-validator tick run of `Goldilocks/Runs/OneValidator/Premises` (`n = 1`, `Δ = 1`, `t_s = 4s`,
a tick at every time, no restart). `Goldilocks/Persist/Premises` meets `PersistPremises` for the
optimistic fast lock of slot `j = 1` on `blk 1` (cut `35`) up to slot `2 = m + 1`; this file adds
the premise that was never instantiated, the source:

* `toFGAt_blk1`: `ac_to_fg` at cut `36` (the tick of `t_1 = 4`, slot `m = 1`) returns `blk 1`.
  It is read off the next cut, the run's `fg_attest(blk 1)`, through `Compose.attest_source`.
* `recentSource_premises_tickRun` bundles every premise with `j = m = 1` (`j ≤ m ≤ j + 2`);
  `recentSource_tickRun` applies the proved statement, and `recentSource_conclusion_nonempty`
  shows that its conclusion is not vacuous: an honest vote of slot `2` exists.

With `n = 1` and `f = 0` this shows the premises consistent, not met with faults. -/

namespace Consensus.Goldilocks.Witness.One

open SA

/-- `ac_to_fg` at cut `36`, the tick of `t_1 = 4`, returns the validator's own block `blk 1`:
the next cut signs `fg_attest(blk 1)`, and an honest signing is the FG update of the source the
`ac_to_fg` cut before it returned. -/
theorem toFGAt_blk1 : ∃ ℓ, SA.ToFGAt (tickRun N1 dg1).projAC v0 36 ℓ (blk 1) := by
  obtain ⟨_, _, -, -, hc, -⟩ := tickCuts_A 0
  have hatt : (tickRun N1 dg1).CallAt v0 37 (.fg (.attest (blk 1) (some (att 1)))) := by
    refine ⟨rfl, ?_⟩
    rw [tickRun_label, show 37 / 8 = 4 * (0 + 1) by omega, hc]
    rfl
  obtain ⟨j', hj', ℓ, hcall, hcl, -, hC, -⟩ :=
    Compose.attest_source tickRun_goldilocksRun.toLocalRun (Set.mem_univ v0) hatt
  obtain rfl : j' = 36 := by omega
  refine ⟨ℓ, Compose.projAC_callAt.2 hcall, hcl, ?_⟩
  rw [projAC_state']
  exact hC

/-- (a) **The premises of `RecentSourceNextVote` are jointly satisfiable**: a Goldilocks run;
`PersistPremises` for the fast lock of slot `j = 1` on `blk 1` (cut `35`, counting `{cv 1}`) up
to slot `m + 1 = 2`; `ac_to_fg` returning `blk 1` at cut `36`, in slot `m = 1`; and
`j ≤ m ≤ j + 2`. -/
theorem recentSource_premises_tickRun :
    GoldilocksRun (sp := sp1) (ro := ro1) (fun _ => v0) dg1 Set.univ (tickRun N1 dg1) ∧
      Compose.PersistPremises (tickRun N1 dg1) Set.univ dg1 1 v0 35 1 (1 + 1) (blk 1) {cv 1} ∧
      (∃ ℓ, SA.ToFGAt (tickRun N1 dg1).projAC v0 36 ℓ (blk 1)) ∧
      sp1.slot ((tickRun N1 dg1).time 36) = 1 ∧ 1 ≤ 1 ∧ 1 ≤ 1 + 2 :=
  ⟨tickRun_goldilocksRun, persistPremises_tickRun, toFGAt_blk1,
    by rw [time_run, slot_nat], le_rfl, by omega⟩

/-- **`RecentSourceNextVote` on the witness**: every honest vote of slot `2` extends `blk 1`. -/
theorem recentSource_tickRun : ∀ y ∈ (Set.univ : Set (Fin sp1.n)), ∀ k e,
    SA.VoteAt (tickRun N1 dg1).projAC y k e → e.msg.slot = 1 + 1 →
      SA.VoteExtends ((tickRun N1 dg1).HonestBlocks Set.univ) e.msg (blk 1) := by
  obtain ⟨hrun, hp, ⟨ℓ, hto⟩, hsl, hjm, hmj⟩ := recentSource_premises_tickRun
  exact Compose.recent_source_next_vote sp1 ro1 dg1 Set.univ (tickRun N1 dg1) 1 v0 35 36 1 1 ℓ
    (blk 1) {cv 1} (fun _ => v0) hrun hp hto hsl hjm hmj

/-- The conclusion is not vacuous: the validator votes in slot `2` (cut `8·t_2 + 3`). -/
theorem recentSource_conclusion_nonempty :
    ∃ k e, SA.VoteAt (tickRun N1 dg1).projAC v0 k e ∧ e.msg.slot = 1 + 1 := by
  obtain ⟨_, e, hl, -, hm, -⟩ := vote_label 1
  exact ⟨_, e, ⟨_, Compose.projAC_callAt.2 ⟨rfl, hl⟩, List.mem_singleton_self _⟩, by rw [hm]; rfl⟩

end Consensus.Goldilocks.Witness.One

end
