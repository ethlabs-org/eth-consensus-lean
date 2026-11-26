# Roadmap

Milestones, their statements, the Lean names and their status: this file says what exists. Every Lean name
here is fully qualified (namespace `Consensus`) and must be listed in `ConsensusLeanTest/Index.lean`, whose build checks that it exists (check.sh step 12), so a
rename or removal fails until this file is updated.

Status: **proved in Solution** (proved; in the closure of `Solution`, so axiom-audited on every checked head and replayed
nightly: leanchecker on every leaf module, the comparator on `Solution`), **proved**, **stated** (statement written,
proof open), **planned**. **Certified** is reserved for a full-tier certification: `check.sh --full` passed on a
named main commit, that is, a passing `full` workflow run of that commit.

## Generic contract

The review statements (`ConsensusLean/Statements/Review.lean`, trusted surface) and the milestones that prove
them. `Solution.lean` proves each statement by the milestone theorem whose type it is.

| Milestone (`ConsensusLean/Proofs/`) | Statement | Milestone theorem | Solution | Status |
|---|---|---|---|---|
| `Behaviour` (L2 ⇒ L0: shape claims give the behaviour; composed in `ConsensusLean/Main.lean`) | `Consensus.Review.ObligationsSufficient` | `Consensus.Shape.ShapeObligations.correct` (from `Consensus.Shape.refinement`) | `Consensus.Review.obligationsSufficient` | proved in Solution |
| `Behaviour` on a class of runs, with unrestricted adequacy and realizability | `Consensus.Review.ObligationsSufficientOn` | `Consensus.Shape.ShapeObligationsOn.correct` | `Consensus.Review.obligationsSufficientOn` | proved in Solution |
| `RegimesRealizable` (active witnesses for admissible, tolerant contracts) | `Consensus.Review.RegimesRealizable` | `Consensus.Shape.regimes_realizable` | `Consensus.Review.regimesRealizable` | proved in Solution |
| `Faithful` (L1: the log is the engine's communication) | `Consensus.Review.LogFaithful` | `Consensus.Model.sysOf_log_faithful` | `Consensus.Review.logFaithful` | proved in Solution |
| `Faithful` (L1: holding is being served) | `Consensus.Review.HeldIffServed` | `Consensus.Model.Run.held_iff_served` | `Consensus.Review.heldIffServed` | proved in Solution |

Corollary outside the trusted surface: `Consensus.Shape.ShapeObligations.activeService` (proved).

## Goldilocks

Mapping from the Goldilocks references to the Lean names: `docs/goldilocks-mapping.md`.

**Growing faults.** The generic roots and the Goldilocks roots cover nondecreasing compromised sets.
The Goldilocks roots are `Consensus.Goldilocks.MeetsObligations`, proved by
`Consensus.Goldilocks.Growing.meets_obligations` and exported as `Consensus.Goldilocks.meetsObligations`, and
`Consensus.Goldilocks.GoldilocksCorrect`, proved as `Consensus.Goldilocks.goldilocksCorrect`.

The compiled Goldilocks counterexample to proposer `hold = 0` is the rejection test
`ConsensusLeanTest/Goldilocks/Regimes/ProposerHold.lean`. The hold is a parameter of the L2
progress contract. The test refutes the `sleepyLive` field of `ShapeClaimsAt` at hold `0`, and
makes no claim that `GoldilocksCorrect` fails at hold `0`. The refuting run has growing faults;
key `2`'s read on it is computed on the run's retained constant-fault run (`Model.Run.retain`),
so the test does not wait for the dynamic sleepy invariant.
The constant-fault controls reject a proposer compromised within its hold window and reduce
arbitrary holds to the original recurrence on constant faults. That `hold = 1` suffices is part of
the certified endpoint `Consensus.Goldilocks.MeetsObligations`.

| Step | Lean names | Status |
|---|---|---|
| Proposer hold-zero counterexample (`ProposerHold.lean`), the prerequisite of the swap | `Consensus.Goldilocks.Test.ProposerHold.sleepyLive_hold_zero_false`, `Consensus.Goldilocks.Test.ProposerHold.claims_hold_zero_false`, `Consensus.Goldilocks.Test.ProposerHold.obligations_hold_zero_false` | done: the three theorems refute the `sleepyLive` field of `ShapeClaimsAt` at hold `0` (no claim that `GoldilocksCorrect` fails at hold `0`), on a growing-fault run, with the read computed on its retained constant-fault run; the control `run_not_prog_hold_one` shows the run fails the hold-`1` recurrence |
| Dynamic certification swap: the growing-fault endpoint and headline are the Challenge roots | `Consensus.Goldilocks.meetsObligations`, `Consensus.Goldilocks.goldilocksCorrect` | done; certified (full tier PASSED on main 921ff811a4a475ff614e14adace3907540d6e981); commits after it are not covered |
| Pre-foundation baseline: pinned numbers and the properties sheet | — | archived ([`archive/consensus-lean-baseline`](https://github.com/ethlabs-org/verified-consensus/tree/79cdddc8e8e4c981211076da0ab1e7ee0bac1a25/archive/consensus-lean-baseline) at `79cdddc8`); no live statement depends on it |
| First slice: Goldilocks Spec, `AsChainShape.lean`, `Statements/<M₁>`, witnesses, finite model; then a proof pilot | — | done: the Spec, `AsChainShape.lean`, the milestone statements and their witnesses exist, and the milestones are proved (the obligations endpoint in Solution, the others as lemmas: `docs/decisions.md` §"Trusted surface and Challenge scope") |
| Certification: `Challenge`/`Solution` entries (`milestone_statements_modules` in `scripts/boundaries.toml`), kernel replay and comparator; at that record Challenge certified the four review statements, the obligations endpoint and the headline `GoldilocksCorrect` only (the current scope is below), and the other milestones are proved lemmas (`proved_milestone_modules`, `docs/decisions.md` §"Trusted surface and Challenge scope") | — | certified (full tier PASSED on main b75cd7c586bcdb708d0c94e125307cf32edf051d, 1351 s, zero skips: cold build, every-leaf kernel replay, `lake check`, `lake comparator --paranoid` and the rebuild canary, each with its controls); commits after it are not covered |
| Constant-fault obligations endpoint and headline: the stock Goldilocks family on the runs whose faults do not grow, at `goldilocksContract` and `contract_coefficients` | — | removed: no longer a Challenge root after the swap, then an untrusted corollary of the growing-fault pair that nothing used. Earlier static endpoint certified on main 2a9b34a11bb9f754a5526593fab6d72366c325a7 and re-certified on ebb2f2ec2783911997e7f4945684f54382690ea6, c361faa46d43bdbdbd6cca76f301e374bb8236ef and b75cd7c586bcdb708d0c94e125307cf32edf051d; these records do not certify the growing-fault migration |
| Healing, the run bundle (`Milestones/Statements/Healing/Run`): HR.1–HR.4, H.2 on the run, H.3 FG non-interference and H.4 | — | retired: the bundle and its pins, H.3 (`NonInterference`, with its proof `Lemmas/Healing/ResetInv`) and H.4 (`AvailableHealing`) are removed; H.2 on the run is removed with H.1 and H.2 (row below); the HR.1–HR.4 statements stay as the types of the lemmas the recovery proofs and the tick-run witnesses read |
| Healing, the phase service (`Milestones/Statements/Healing/Service`): HS.1–HS.4 and their bundle | `Consensus.Goldilocks.Healing.frozen_tree_agreement_clean` | retired: the bundle and its pins and HS.3 (`FrozenTreeAgreement`) are removed; HS.3's after-`r` part stays proved from HS.2 (`frozen_tree_agreement_clean`), and HS.1, HS.2 and HS.4 stay as the types of the lemmas the recovery proofs read |
| Healing, re-proved without HS.3 (a): HR.3 reset existence and HS.4 common-path acquisition. Their consumers read only HS.3 (b), which follows from HS.2; the earlier proofs are restored over it, with no `reset_inv` | `Consensus.Goldilocks.Healing.ResetExistence`, `Consensus.Goldilocks.Healing.reset_existence`, `Consensus.Goldilocks.Healing.CommonPathAcquisition`, `Consensus.Goldilocks.Healing.common_path_acquisition` | proved (standard axioms) |
| Healing, outcome service (`Milestones/Statements/Healing/Outcome`): C1.2 AC outcome service for honest entries, a literal good window or an accepted early justification by the end of the window | `Consensus.Goldilocks.Compose.OutcomeService`, `Consensus.Goldilocks.Healing.Recovery.outcome_service` | proved (`Lemmas/Healing/Recovery/Reports`, 10c3f956; standard axioms) |
| Healing, recovery (`Milestones/Statements/Healing/Recovery`): node O.1 pattern recovery and C1.3 recurring finalizing coverage at a slot dictionary `K` (from its committee start, with its committee facts and CS2 after the slot of `ḡ`); HR.5 cache acceptance after the reset (the committee start of `K` only). HR.5 is `Lemmas/Healing/Recovery/Cache` (c504ef66); C1.3 is the selected `UPat` stretch, acquisition, old-entry crossing and two-window finalization (`Lemmas/Healing/Recovery`), and O.1 is C1.3 at `R_*` with recovery from high finality (`Recovery/Assembly`) | `Consensus.Goldilocks.Healing.RecoveryStatements`, `Consensus.Goldilocks.Healing.recovery_statements`, `Consensus.Goldilocks.Healing.PatternRecovery`, `Consensus.Goldilocks.Healing.FinalizingCoverage`, `Consensus.Goldilocks.Healing.CacheAcceptanceAfterReset`, `Consensus.Goldilocks.Healing.cache_acceptance_after_reset` | proved: the retained recovery bundle is proved (standard axioms) |
| Common (`Lemmas/Common/Claims`, outside the trusted surface): F.2 tree mathematics, F.3 digests, slot arithmetic | `Consensus.Goldilocks.CommonStatements`, `Consensus.Goldilocks.common_statements` | proved (`Lemmas/Common/StatementsBundle`, 357c9f29; standard axioms): `Anc.antisymm`, `Anc.total`, `deepest_common_ancestor`, `digest_determines_block` (F.3, with valid roots and equal proposers) and `slotOf_spec`; not imported by `Solution` |
| Frame (`Lemmas/AC/FrameClaims`, outside the trusted surface): G0.3/G0.4 frame facts and sequence vocabulary | `Consensus.Goldilocks.FrameStatements`, `Consensus.Goldilocks.frame_statements` | proved (`Lemmas/AC/FrameStatements`, 60e5bf96; standard axioms); not imported by `Solution`; retention is also exercised on a witness (`ConsensusLeanTest/Goldilocks/Frame/Statements`) |
| Simulation interface (`Lemmas/Simulation/Interface`, outside the trusted surface and `Challenge`): simulation, reads, `NoColl` transport, `conflicts`, evidence, finalized accountability | — | retired: the stock bundle `simulation_statements`, its structure and the stock simulation, `NoColl` transport, evidence and finalized-accountability statements with their proofs are removed (none was in the closure of `Solution`); reads (`readIsOut`) and `conflicts` (`conflicts_iff`) stay, and the growing-fault forms are proved in `Lemmas/Growing/Simulation` (`Consensus.Goldilocks.Simulation.simTraceAt_simulates`, `Consensus.Goldilocks.Simulation.noCollRun_simTraceAt`, `Consensus.Goldilocks.Simulation.held_att_in_view_at`, `Consensus.Goldilocks.Simulation.final_accountable_at`) |
| Healing, AC level (`Milestones/Statements/Healing/AC`): H.1 standalone AC healing and its corollary (also at `t_p ≥ ḡ + (8k + 4)Δ`), H.2 AC inclusion and H.2 on the run, static and under growing faults | — | removed: standalone H.1/H.2 and H.2 (run) are not retained Lean Results; their vocabulary and support needed by retained results or downstream consumers remain. The statements, their closed forms, bundle, pins and witnesses, and their static proofs, are deleted; `Milestones/Statements/Healing/AC` keeps the healing vocabulary that other statements read, and the population-committee `…U` lemmas that the downstream consumer reads stay in `Lemmas/Healing/AC` |
| Late release of signed FG attestations: a per-validator release schedule, a queue of held attestations that never delays AC votes, and a release gap `R` in the contract charged in the final anchor spacing `⌈(6 + F + R + G)/4⌉` (`docs/decisions.md` §"The node as a chain shape") | — | covered by the certified endpoint `Consensus.Goldilocks.MeetsObligations`, whose contract assumptions carry the release gap (`releaseGap`, `release_liveness`); no separate statement |
| Continuation after healing under corruption growth (`Milestones/Statements/Continuation`, untrusted side property, not part of correctness): on a run healthy from GST up to a hand-over time `T` at or after the heal point and only sleepy afterwards, with fewer than `α·n` convicted by any two honest views, the available and stable outputs are ready-reader safe from the heal point and transaction-live with the healed latency, and the regime is realizable at every delay and GST with at least `β·n` corruption | `Consensus.Goldilocks.GoldilocksContinues`, `Consensus.Goldilocks.goldilocks_continues` | proved (standard axioms; lemma, not certified; pinned by `ConsensusLeanTest/MilestoneAxioms`) |

**Current Challenge scope.** `Challenge.lean` and `comparator.json` hold eight statements: the five review statements of
`Statements/Review` and the Goldilocks statements of `Statements/Obligations` (the obligations endpoint, the headline
`GoldilocksCorrect` and its explicit-excuse form `GoldilocksCorrectWithExcuses`). The endpoint includes the
outage and sleepy shape claims at every vote binding.

**Committee scope.** The Goldilocks family is stated at every vote binding (`docs/decisions.md` §"Committee
modelling"); the certified endpoint and headline forms cover every binding. The premise bundle
`Consensus.Goldilocks.AC.HealthyBaseU` carries `committeeSize = n` as a field: it is stated at
population-sized committees only, and no certified statement reaches it. The HS shared premises
`Consensus.Goldilocks.Healing.HSShared` are stated at a slot dictionary `K` (its committee facts and
CS2 after the slot of `ḡ`), and so are the healing statements over them (C1.2, HR.3, HS.1, HS.2, HS.4,
node O.1, C1.3); HR.4 takes the same two facts directly, and HR.5 takes only the committee start.

## Shape examples

`ConsensusLean/Examples/Shape/{Bft,Streamlet,Tendermint}.lean` (not instances, not on the trusted surface): contract values with admissibility, progress-fit and
tolerance proofs (`Consensus.Shape.bftContract_admissible`, `Consensus.Shape.streamletContract_progressTolerant`,
`Consensus.Shape.tendermintContract_progressTolerant`); no protocol proofs and no milestones yet.

## Deferred

leanblueprint and a dependency graph (trigger: a second instance with milestones, or outside contributors);
a Mathlib-free Spec package (trigger: reuse outside the project).
