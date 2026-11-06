# Statement-to-scenario coverage

This is a reading map, not a count of independent tests or a claim of exhaustive model checking.
Paths below are relative to `ConsensusLeanTest/` unless explicitly prefixed with `ConsensusLean/`.
The statement families and their proof status are in [the roadmap](roadmap.md) and
[the claim mapping](goldilocks-mapping.md). Certification still requires a full-tier result for a
named commit; a scenario application does not certify all behaviours of a protocol.

## How to read and maintain the map

- **Premises (a):** hypotheses hold together. A universal conclusion may still be vacuous.
- **Reachability (b):** an actual execution reaches the named event or conclusion. Distinguish an
  independently computed observation from an application of the theorem being exercised.
- **Rejection (r):** a named premise or conclusion fails. A rejection is not a counterexample to a
  theorem whose hypotheses it does not meet.
- **Control:** restore the omitted premise, retain the other premises and apply the production theorem.
- **Arithmetic:** checks formulas or boundary values, not execution reachability.

The tables name representative entry points rather than every helper theorem. When adding a witness,
record the statement, run laws, discharged premises, nonempty event, branch and remaining limitations.
Do not replace a symbolic infinite run by a finite snapshot when its Healthy premise needs an infinite
horizon. Do not infer repository-wide absence from a limitation of one witness.

## Generic statements and model obligations

| Statement or contract | Premises / reachability | Rejection / control / arithmetic | Limits and reading entry point |
|---|---|---|---|
| `ObligationsSufficient`, `CorrectProtocol` | `Shape/Leaks.lean`: `recorder_live_testK`; `Shape/Controls.lean` supplies explicit positive numbers | `Shape/Leaks.lean`: do-nothing, fabricating and self-silencing shapes; `Shape/Vacuity.lean`: `noService_not_obligations`, admissibility, fit and tolerance rejections; `Problem/CorrectProtocol.lean`: vacuous systems and censoring progress | These test the generic contract, not Goldilocks node executions. |
| `RegimesRealizable` | `Shape/Realizable.lean`: active coverage, late GST and outage; `Problem/Regimes.lean`: regime premises; `Problem/CorrectProtocol.lean`: rotating sleepers | `allProposers_no_witness` in `Shape/Realizable.lean`; progress/threshold controls in `Shape/Controls.lean` and `Shape/Vacuity.lean` | Existential realizability does not establish progress against every adversary. |
| `LogFaithful`, `HeldIffServed`, model laws | `Model/Basic.lean`, `Model/Lift.lean`, `Problem/Network.lean`: events, views, rehashing, delivery and truncation | `Problem/Network.lean`: silent runs and strict waker deadlines; `Problem/Properties.lean`: property rejections, including `local_accountability_teeth` | Model semantics and property teeth, not a separate protocol liveness witness. |

## Goldilocks endpoint and component statements

| Statement family | Premises / reachability | Rejection / control / arithmetic | Limits and entry point |
|---|---|---|---|
| `MeetsObligations`, `GoldilocksCorrect` | `Goldilocks/Refinement/Obligations.lean`: `meets_obligations_nonvacuous`, `meetsObligations_realizable_small`, `goldilocksCorrect_realizable_small` | Same file: small/large setups, exact assumption range, timeout rejection, catch-up, healing, latency, outage and FG-gap formulas | The active five-validator witnesses come from generic realizability; they are not a concrete healthy finalizing Goldilocks execution. |
| Simulation and engine-to-node adapters | `Goldilocks/Refinement/Simulation.lean`; `Goldilocks/Refinement/{Sleepy,Final,NonfinalQuery}.lean` | `Goldilocks/Refinement/Obligations.lean` checks both FG-delay orderings arithmetically | Selection satisfiability and adapter applications must not be confused with a run traversing every network branch. The three whole-run network transport suppliers are stated but open, not endpoint premises. |
| FG safety, finality, accountability | `Goldilocks/FG/{Statements,Aggregation,Retention,RetentionThroughAppend,FaultyFinalization}.lean` | `FG/{Faulty,ConflictChains,FinalityGate,AccountableTightness}.lean` | Chain-level traces and threshold cases; an engine-run correctness claim needs the simulation and regime premises as well. |
| FG store, frame and replay service | `Goldilocks/FGStore/{Statements,Entry,TimeoutEntry,Coverage,Service,Crossing}.lean`; `Goldilocks/Frame/{Statements,Seq}.lean` | `FGStore/{QuorumFree,CrossingRejection}.lean`; `Frame/Rejection.lean` | Component steps include timeout and crossing branches but do not by themselves witness the full healthy run. |
| AC base, steps, inclusion and composition | `Goldilocks/AC/{Base,Optimistic,FastUpdate,Transfer,Inclusion}.lean`; `Goldilocks/Compose/Statements.lean`; `Goldilocks/Run/Statements.lean` | `AC/{JoinedRestart,InclusionUpdateRejection,GradedVeto,LockRule}.lean`; `Compose/{ThresholdRejections,ProjectionRejection,Restart}.lean`; `Run/{Faulty,Conflict,AttestationPremise}.lean` | Handler and premise tests include restarts and faults; this does not make the healthy outcome witness cover those branches. |
| Regime and service adapters | `Goldilocks/Regimes/Sleepy.lean`; `Goldilocks/Runs/Asleep/{Run,Sleepy}.lean`; `Goldilocks/Persist/Premises.lean`: `tickRun_service_premises` | `Goldilocks/Regimes/BudgetTightness.lean` | Distinguish sleepy sleep/wake cases from healthy post-GST rejoining and from C1.2. |

## Persistence: three distinct rejection/control pairs

All three families exercise `RecentSourceNextVote`, a corollary of C1.1, with five validators.
The local premise-bundle equivalences tie each omitted-field bundle to production `PersistPremises`.
They test necessity of individual assumptions, not failure of the proved statement.

| Omitted premise | Rejection | Restoring control | Non-vacuity and limits |
|---|---|---|---|
| `halfCommittee` | `Goldilocks/HalfCommittee/Premises.lean`: `halfCommittee_necessary`; honest `c` votes on `V`, not extending `B` | `HalfCommittee/Control.lean`: `d` wakes/restarts at `24`; voters `{a,b,d}` restore the bound; `control_persistPremises`, `control_next_votes_extend`, `control_c_votes_B` | Faults, restart and retained locks are exercised. No slot-9 vote, so not all later-carry positions have an actual voter. |
| Initial `carry` | `Goldilocks/InitialCarry/Reject.lean`, with the other fields in `InitialCarry/Premises.lean` | `InitialCarry/Control.lean`: deliver `Da, Db` to `c` at `23`, before the initial deadline `27`; full premises and `control_next_votes_extend` | Horizon `35`; the `s' = 8` later-Carry instance has no vote. This is not a substitute for the next pair. |
| `carryLater` | `Goldilocks/CarryLater/Reject.lean`, with the other fields in `CarryLater/Premises.lean` | `CarryLater/Control.lean`: deliver `Y` to the late-waking `c` at `25`; full premises, `control_next_votes_extend`, `control_c_votes_Y` | Horizon `39`; later-Carry at both `s' = 7, 8` is checked at actual slot-8 and slot-9 votes. |

Positive one-validator coverage is separate: `Goldilocks/Persist/Premises.lean` supplies
`persistPremises_tickRun`; `Persist/RecentSource.lean` applies `recent_source_tickRun` and proves
an actual next-slot vote in `recentSource_conclusion_nonempty`. Zero faults and permanent wakefulness
make this a useful baseline, not a replacement for the three rejection/control pairs.

## Healing: statements, applications and remaining branches

**The “Not provided” list in `Goldilocks/Healing/Statements.lean` is stale as a global work queue.**
That file's idle/periodic premise witnesses and closed-form checks remain useful, but later files
provide the following applications. Do not read the old list as evidence that they are missing.

| Statement | Premise / application evidence | Nonempty observation, arithmetic or rejection | Remaining limitation |
|---|---|---|---|
| HR.1 `CutAndReset`, HR.3 `ResetExistence`, HR.4 `HeightScopedRetention` | `Goldilocks/Healing/TickRun.lean`: `healing_premises`, `reset_bundle`, `tickRun_cutAndReset`, `tickRun_resetExistence`, `tickRun_retention` | Reset `a_z = 16`, initial height `H_z = 3`, reset bound `1056` | One honest validator, no faults, GST `0`, no restart. |
| HR.2 `PhaseCount` | `Goldilocks/Healing/Statements.lean`: idle phase; `Healing/PhaseCount.lean`: `phaseCount_premises`, `phaseCount_applies` | `phaseCount_b_witness`, `phaseCount_c_witness`: top-to-contest at fixed frontier `3`, nonempty counted set; `phaseCount_b_needs_fixed_frontier` rejects monotonicity across a frontier rise | FG-local trace, not a healthy node-run acquisition witness; `phaseCount_applies` takes the statement as a premise. |
| H.1 standalone AC healing and corollary; H.2(i) | `Goldilocks/Healing/SA.lean`: `concreteRunFacts` discharges the abstract run-fact bundle; `healing_live_witness` combines premises, `Geo`, `Inv`, a vote and a confirmation | `confirmed_tick38` observes slot-8 confirmation at the exact deadline; `common_confirmed_from42`; H.2(i) has an actual vote | Driven SA run with one honest validator, not a multi-validator node-run settled phase. |
| H.2 run projection and part (ii); H.4 available healing | `Goldilocks/Healing/TickRun.lean`: `projection_bundle`, `tickRun_runInclusion`, `tickRun_availableHealing` | `blk272_confirmed` at cut `8752`, time `1094`; `T_heal = 1088`; `Healing/Statements.lean` also checks closed forms for every parameter | `Geo` in the bridge is vacuous: accepting the own block raises the frontier between proposal and vote. Unanimity is read directly from the run. |
| H.3 bridge and HS.4 `CommonPathAcquisition` | `Goldilocks/Runs/OneValidator/Run.lean`: `tickRun_bridgeAt`; `Goldilocks/Healing/Settled.lean`: `settledIn_tickRun`, `acquisition_premises`, `acquisition_applies` | `acquisition_phase_changes`: the phase changes by the deadline `w + D_HS = 92` | HS.4's acquisition disjunct and client step are not exercised on this run. The bridge alone is not a non-vacuous test of all H.3 clauses or HS.1–HS.3. |
| HR.5 cache acceptance | `Goldilocks/Healing/Recovery.lean`: `blk6_cache_premise`, `tickRun_cacheAcceptance` | Actual acceptance of `blk 6` at cut `194`, time `24`; `finalized_after_blk6` bounds the cache to `blk 4` or `blk 5` | No independent exact cache computation; held-block height bound is met with equality. |
| O.1 `PatternRecovery`, C1.3 `FinalizingCoverage` | `Goldilocks/Healing/Recovery.lean`: `recovery_premises`; `tickRun_recovery` closes the statement parameters of `tickRun_patternRecovery` and `tickRun_finalizingCoverage` | `M* = 24`, `R* = 1092`, `T_rec = 1209`; a proposal in slots `273`–`299` is below later finality | `Rec`'s clean/records fields are not specialised to concrete cuts; the later cache is obtained by the theorem, not independently computed. |
| C1.2 `OutcomeService` | `Goldilocks/Runs/TwoValidator/GoodWindow.lean`: `twoRun_goodWindow`, `twoRun_outcome`, run laws and Healthy discharged | Entry `E₃ = blk 21`; literal window `{32}`; carrier accepted by both nodes; target quorum has two rows | See the explicit branch inventory below. The symbolic infinite execution is not a finite `decide` fixture. |

### C1.2 GoodWindow branch inventory

`Runs/TwoValidator/GoodWindow.lean` establishes a real good window, not just satisfiable premises.
Its stated limitations are:

| Axis | Exercised | Not exercised by this witness |
|---|---|---|
| Previous-height bound | `bound = true` | Non-vacuous `bound = false`; its conjunct is vacuous here |
| Outcome | Literal good window and application of the outcome disjunction | A separate concrete early-outcome execution |
| Population | Two honest validators, zero faults | Nonzero faults under the same outcome premises |
| Joining | Always awake, joined, no restart | Wake/rejoin delivery and ready-proposal joinedness |
| Target rows | Already on the parent chain; fresh row `(v0, 4)` is included by the carrier | Target quorum depending on off-chain emitted/pooled rows |
| Catch-up | GST `0`, so no pre-GST acceptance | Non-vacuous pre-GST `Catch(2Δ)` |
| Window width | `k_F = 0`, one slot | Positive-width window with more than one candidate slot |

These are gaps in this execution's branch coverage, not assertions of absence throughout the repository.
For example, restart, faults and late delivery already occur in persistence and component tests above,
but those tests do not discharge C1.2's joint premises.

## Candidate next scenarios

These are candidates for prioritisation, not promised tests or a selected implementation:

1. A C1.2 entry with `bound = false`, an actual entry/vote and every joint premise discharged.
2. A long-lived settled phase exercising HS.4's acquisition/client branch and non-vacuous node-run `Geo`,
   rather than only the phase-change alternative.
3. A healthy outcome run with a genuine wake/rejoin or pre-GST acceptance, so delivery/catch-up deadlines
   constrain an observed event. Existing sleepy and persistence wake cases should be reused where appropriate,
   not counted as this joint healthy scenario already.
4. A C1.2 window whose target quorum needs off-chain rows, or a positive-width window, with an independently
   observed carrier/early outcome. These are separate axes; combining all of them is not required.

Choose the mathematical branch first, then confirm that no existing fixture already discharges its full
premises before constructing another run. This document adds no scenario or theorem.
