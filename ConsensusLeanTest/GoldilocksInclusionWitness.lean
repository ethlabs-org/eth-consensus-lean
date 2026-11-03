module
public import ConsensusLeanTest.GoldilocksPersistWitness
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.Inclusion
@[expose] public section

/-! # A1.7 inclusion: the premises at slot `1`, at the boundary `t_1 + 6Δ`

Kind (a), joint satisfiability (CONTRIBUTING "Statements"), of `Compose.Inclusion` (A1.7) on the
one-validator tick run of `GoldilocksWitness` (`n = 1`, `Δ = 1`, `t_s = 4s`, a tick at every time,
no restart), for an update instance of slot `s = 1` (the earlier Service witness,
`servedAt_tickRun`, only reaches the update of slot `0`):

* the proposal: `P = blk 1`, processed as the validator's own block at cut `34` (`t_1 = 4`), with
  the proposer joined there;
* the cut: `i = 81`, the `ac_to_fg` at time `10 = t_1 + 6Δ`, right after the tick of cut `80`
  that runs the update of slot `1` (`UpdatedNoRestart` with `k = 80`). This is the boundary that
  the update clause (consensus-lean#77) is about: `inclusion_update_boundary` shows the clause
  fails at cut `80` itself, the first cut at `t_1 + 6Δ`, so `81` is the earliest cut where every
  premise holds;
* the genesis root is its digest (`dg1_genesis`), the run is a `GoldilocksRun` with `NoColl` and
  `Sleepy` (`tickRun_service_premises`).

`inclusion_premises_tickRun` bundles every premise; `inclusion_tickRun` applies the proved
statement to them. The witness reads no lock or confirmation rule: the conclusion comes from
`inclusion_sleepy`, not from evaluating `ac_confirmed`.

Not covered here: rejections of the update clause (#77) and of the genesis-root premise (#73).
On this run the #77 rejection is unavailable (with `n = 1` the optimistic confirmation already
moves the record to `blk 1` at `t_1`); it needs a fixture whose proposal is not optimistically
confirmed before the update. With `n = 1` and `f = 0` this shows the premises consistent, not
met with faults. -/

namespace Consensus.Goldilocks.Witness.One

open SA Node

/-- The first cut of the tick of time `t` (cut `8t`) is its `ac_on_tick`. -/
theorem tickRun_label_tick (t : Nat) : (tickRun N1 dg1).label (8 * t) =
    some (acCall v0 (tickState N1 dg1 t) (t : Int) .tick).2 := by
  rw [tickRun_label, show 8 * t / 8 = t by omega, show 8 * t % 8 = 0 by omega]
  exact tickCuts_head N1 dg1 t

/-- The validator processes its own proposal `blk 1` at cut `34`, at `t_1 = 4`. -/
theorem proposesAt_blk1 : (tickRun N1 dg1).ProposesAt v0 34 (blk 1) := by
  obtain ⟨fg', e, -, -, hc, -⟩ := tickCuts_A 0
  refine ⟨⟨⟨true, rfl, ?_⟩, by decide⟩, eq_v0 rfl _, ?_⟩
  · rw [tickRun_label, show 34 / 8 = 4 * (0 + 1) by omega, hc]; rfl
  · rw [blk_slot]; rfl

/-- Cut `81` is the `ac_to_fg` of the tick of time `10`. -/
theorem tickRun_isCall_81 : (tickRun N1 dg1).IsCall v0 81 := by
  refine ⟨.ac ⟨.toFG, Node.frame (tickState N1 dg1 10), []⟩, rfl, ?_⟩
  rw [tickRun_label, show 81 / 8 = 10 by omega, tickCuts_other (by omega) (by omega)]; rfl

/-- The update of slot `1` runs at the tick of time `10 = t_1 + 6Δ` (cut `80`), and the
validator has run it with no restart since before cut `81`. -/
theorem updatedNoRestart_81 : Compose.UpdatedNoRestart (tickRun N1 dg1) v0 81 1 := by
  refine ⟨80, by decide, _, ⟨Compose.projAC_callAt.2 ⟨rfl, tickRun_label_tick 10⟩, rfl, ?_, ?_⟩,
    fun k' _ _ => tickRun_no_restart _ k'⟩
  · rw [time_eq, ts_nat]; rfl
  · rw [projAC_state']
    exact joined_of_bot (tickRun_restartTime 80) _

/-- (a) The update clause is tight at the boundary: before cut `80`, the first cut at
`t_1 + 6Δ = 10`, no cut has run the update of slot `1`, though cut `80` meets every other premise
of A1.7 (it is a call at time `10`, awake and joined, with no restart). -/
theorem inclusion_update_boundary :
    (tickRun N1 dg1).IsCall v0 80 ∧ (tickRun N1 dg1).time 80 = sp1.ts (1 : Nat) + 6 * sp1.Δ ∧
      ¬ Compose.UpdatedNoRestart (tickRun N1 dg1) v0 80 1 := by
  refine ⟨⟨_, rfl, tickRun_label_tick 10⟩, by rw [ts_nat]; rfl, ?_⟩
  rintro ⟨k, hk, ℓ, ⟨-, -, ht, -⟩, -⟩
  rw [time_eq, ts_nat] at ht
  change ((k / 8 : Nat) : Int) = 4 * ((1 : Nat) : Int) + 6 * 1 at ht
  omega

/-- (a) **The premises of A1.7 are jointly satisfiable at slot `1`**: a Goldilocks run with
`NoColl`, `Sleepy` and a genesis whose root is its digest; the honest proposal `blk 1` of slot
`1` at cut `34` by a joined proposer; and the cut `81` at `t_1 + 6Δ`, where the validator is
awake and joined (also at `t_1 + 6Δ`), has not restarted, and has run the update of slot `1`. -/
theorem inclusion_premises_tickRun :
    GoldilocksRun (sp := sp1) (ro := ro1) (fun _ => v0) dg1 Set.univ (tickRun N1 dg1) ∧
      Compose.NoCollRun dg1 (tickRun N1 dg1) ∧ (tickRun N1 dg1).SleepyRun Set.univ 1 ∧
      (sp1.toParams.genesisBlock (goldilocksNode sp1 ro1).genesisPayload).RootOk dg1 ∧
      (tickRun N1 dg1).ProposesAt v0 34 (blk 1) ∧ (blk 1).slot = 1 ∧
      joined sp1 ((tickRun N1 dg1).state v0 34).ac ((tickRun N1 dg1).time 34) ∧
      (tickRun N1 dg1).IsCall v0 81 ∧ sp1.ts (1 : Nat) + 6 * sp1.Δ ≤ (tickRun N1 dg1).time 81 ∧
      (tickRun N1 dg1).awake v0 ((tickRun N1 dg1).time 81) ∧
      (tickRun N1 dg1).JoinedAt v0 ((tickRun N1 dg1).time 81) ∧
      (tickRun N1 dg1).awake v0 (sp1.ts (1 : Nat) + 6 * sp1.Δ) ∧
      (tickRun N1 dg1).JoinedAt v0 (sp1.ts (1 : Nat) + 6 * sp1.Δ) ∧
      (∀ k', (tickRun N1 dg1).RestartAt v0 k' →
        sp1.ts (1 : Nat) + 6 * sp1.Δ < (tickRun N1 dg1).time k' →
        (tickRun N1 dg1).time k' ≤ (tickRun N1 dg1).time 81 → False) ∧
      Compose.UpdatedNoRestart (tickRun N1 dg1) v0 81 1 := by
  have hj : ∀ t, (tickRun N1 dg1).JoinedAt v0 t := fun _ k hk =>
    absurd hk (tickRun_no_restart _ k)
  refine ⟨tickRun_goldilocksRun, dg1_noColl _, tickRun_sleepy, dg1_genesis, proposesAt_blk1,
    blk_slot 1, joined_of_bot (tickRun_restartTime 34) _, tickRun_isCall_81, ?_, ?_, hj _, ?_, hj _,
    fun k' hk' => absurd hk' (tickRun_no_restart _ k'), updatedNoRestart_81⟩
  · rw [ts_nat]; change (4 * ((1 : Nat) : Int) + 6 * 1 : Int) ≤ ((81 / 8 : Nat) : Int); omega
  · change (0 : Int) ≤ ((81 / 8 : Nat) : Int); omega
  · rw [ts_nat]; change (0 : Int) ≤ 4 * ((1 : Nat) : Int) + 6 * 1; omega

/-- **A1.7 on the witness**: the honest proposal `blk 1` is in the confirmed tip of the validator
before cut `81`, as `inclusion_sleepy` gives from `inclusion_premises_tickRun`. -/
theorem inclusion_tickRun :
    Anc ((tickRun N1 dg1).HonestBlocks Set.univ) (blk 1) ((tickRun N1 dg1).confirmedAt v0 81) := by
  obtain ⟨hrun, hnc, hsl, hg, hP, hPs, hpj, hc, ht, hyw, hyj, hyw₀, hyj₀, hnr, hu⟩ :=
    inclusion_premises_tickRun
  exact Compose.inclusion_sleepy sp1 ro1 (fun _ => v0) dg1 Set.univ (tickRun N1 dg1) 1 hrun hnc
    hsl hg v0 (Set.mem_univ _) 34 (blk 1) 1 hP hPs hpj v0 (Set.mem_univ _) 81 hc ht hyw hyj hyw₀
    hyj₀ hnr hu

end Consensus.Goldilocks.Witness.One

end
