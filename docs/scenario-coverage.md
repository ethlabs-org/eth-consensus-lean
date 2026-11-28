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
| `MeetsObligations`, `GoldilocksCorrect` | `Goldilocks/Refinement/Obligations.lean`: `meetsObligations_realizable_small`, `goldilocksCorrect_realizable_small` | Same file: small/large setups, exact assumption range, timeout rejection, catch-up, healing, latency, outage and FG-gap formulas | The active five-validator witnesses come from generic realizability; they are not a concrete healthy finalizing Goldilocks execution. |
| Simulation and engine-to-node adapters | `Goldilocks/Refinement/Simulation.lean`; `Goldilocks/Refinement/{Sleepy,Final,NonfinalQuery}.lean` | `Goldilocks/Refinement/Obligations.lean` checks both FG-delay orderings arithmetically | Selection satisfiability and adapter applications must not be confused with a run traversing every network branch. The endpoint reads the per-service network suppliers directly; the whole-run network transports were retired unproved. |
| FG safety, finality, accountability | `Goldilocks/FG/{Statements,Aggregation,Retention,RetentionThroughAppend,FaultyFinalization}.lean` | `FG/{Faulty,ConflictChains,FinalityGate,AccountableTightness}.lean` | Chain-level traces and threshold cases; an engine-run correctness claim needs the simulation and regime premises as well. |
| FG store, frame and replay service | `Goldilocks/FGStore/{Statements,Entry,TimeoutEntry,Coverage,Service,Crossing}.lean`; `Goldilocks/Frame/{Statements,Seq}.lean` | `FGStore/{QuorumFree,CrossingRejection}.lean`; `Frame/Rejection.lean` | Component steps include timeout and crossing branches but do not by themselves witness the full healthy run. |
| AC base, steps, inclusion and composition | `Goldilocks/AC/{Base,Optimistic,FastUpdate,Transfer}.lean`; `Goldilocks/Compose/Statements.lean`; `Goldilocks/Run/Statements.lean` | `AC/{JoinedRestart,GradedVeto,LockRule}.lean`; `Compose/{ThresholdRejections,ProjectionRejection,Restart}.lean`; `Run/{Faulty,Conflict,AttestationPremise}.lean` | Handler and premise tests include restarts and faults; this does not make the healthy outcome witness cover those branches. |
| Regime adapters | `Goldilocks/Regimes/Sleepy.lean` | `Goldilocks/Regimes/BudgetTightness.lean` | Distinguish sleepy sleep/wake cases from healthy post-GST rejoining and from C1.2. |

## Persistence

C1.1 and its corollary are no longer milestone statements, and their premise bundle is not stated.

## Healing: statements, applications and remaining branches

**The “Not provided” list in `Goldilocks/Healing/Statements.lean` is stale as a global work queue.**
That file's idle/periodic premise witnesses and closed-form checks remain useful, but later files
provide the following applications. Do not read the old list as evidence that they are missing.

| Statement | Premise / application evidence | Nonempty observation, arithmetic or rejection | Remaining limitation |
|---|---|---|---|
| HR.1 `CutAndReset` | `Goldilocks/Healing/TickRun.lean`: `healing_premises`, `tickRun_cutAndReset` | Reset `a_z = 16`, initial height `H_z = 3` | One honest validator, no faults, GST `0`, no restart. |
| The premises of HS.4 (retired) | `Goldilocks/Healing/Settled.lean`: `settledIn_tickRun`, `acquisition_premises` | `acquisition_phase_changes`: the phase changes by the deadline `w + D_HS = 92` | The run directly witnesses phase change, not acquisition or client progress; it does not apply a phase-service theorem. |

## Candidate next scenarios

These are candidates for prioritisation, not promised tests or a selected implementation:

1. A C1.2 entry with `bound = false`, an actual entry/vote and every joint premise discharged.
2. A long-lived settled phase exercising HS.4's acquisition/client branch and non-vacuous node-run `Geo`,
   rather than only the phase-change alternative (paper-claim scenario, not an application of a retained Lean
   theorem).
3. A healthy outcome run with a genuine wake/rejoin or pre-GST acceptance, so delivery/catch-up deadlines
   constrain an observed event. Existing sleepy and persistence wake cases should be reused where appropriate,
   not counted as this joint healthy scenario already.
4. A C1.2 window whose target quorum needs off-chain rows, or a positive-width window, with an independently
   observed carrier/early outcome. These are separate axes; combining all of them is not required.

Choose the mathematical branch first, then confirm that no existing fixture already discharges its full
premises before constructing another run. This document adds no scenario or theorem.
