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

**Growing-fault migration.** The generic roots cover nondecreasing compromised sets, including
constant intervals. The current Goldilocks roots are
`Consensus.Goldilocks.MeetsObligationsConstant`, proved by
`Consensus.Goldilocks.Obligations.meets_obligations_constant` and exported as
`Consensus.Goldilocks.meetsObligationsConstant`, and
`Consensus.Goldilocks.GoldilocksCorrectConstant`, proved as
`Consensus.Goldilocks.goldilocksCorrectConstant`. Only behaviour is restricted to constant faults;
adequacy and realizability include growing faults. The dynamic statements
`Consensus.Goldilocks.MeetsObligations` and `Consensus.Goldilocks.GoldilocksCorrect` are stated and open
in `Statements/Growing.lean`, outside the Solution closure. Certification records below describe
the earlier static endpoint, not certification of the dynamic statements.

The compiled Goldilocks counterexample to proposer `hold = 0` is the rejection test
`ConsensusLeanTest/Goldilocks/Regimes/ProposerHold.lean`. The hold is a parameter of the L2
progress contract. The test refutes the `sleepyLive` field of `ShapeClaimsAt` at hold `0`, and
makes no claim that `GoldilocksCorrect` fails at hold `0`. It reads the claim on a retained
constant-fault run (`Model.Run.retain`), so it does not wait for the dynamic sleepy invariant.
The constant-fault controls reject a proposer compromised within its hold window and reduce
arbitrary holds to the original recurrence on constant faults. That `hold = 1` suffices rests on
the window audit and these constant-fault reductions until the dynamic invariant is proved.

| Step | Lean names | Status |
|---|---|---|
| Dynamic certification swap: compiled proposer hold-zero counterexample (`ProposerHold.lean`) | — | done: `sleepyLive_hold_zero_false`, `claims_hold_zero_false` and `obligations_hold_zero_false` refute the `sleepyLive` field of `ShapeClaimsAt` at hold `0` (no claim that `GoldilocksCorrect` fails at hold `0`), on a retained constant-fault run; the control `run_not_prog_hold_one` shows the run fails the hold-`1` recurrence |
| Pre-foundation baseline: pinned numbers and the properties sheet | — | archived ([`archive/consensus-lean-baseline`](https://github.com/ethlabs-org/eth-consensus-lean/tree/79cdddc8e8e4c981211076da0ab1e7ee0bac1a25/archive/consensus-lean-baseline) at `79cdddc8`); no live statement depends on it |
| First slice: Goldilocks Spec, `AsChainShape.lean`, `Statements/<M₁>`, witnesses, finite model; then a proof pilot | — | done: the Spec, `AsChainShape.lean`, the milestone statements and their witnesses exist, and the milestones are proved (the obligations endpoint in Solution, the others as lemmas: `docs/decisions.md` §"Trusted surface and Challenge scope") |
| Certification: `Challenge`/`Solution` entries (`milestone_statements_modules` in `scripts/boundaries.toml`), kernel replay and comparator; Challenge certifies the four review statements, the obligations endpoint and the headline `GoldilocksCorrect` only, and the other milestones are proved lemmas (`proved_milestone_modules`, `docs/decisions.md` §"Trusted surface and Challenge scope") | — | certified (full tier PASSED on main b75cd7c586bcdb708d0c94e125307cf32edf051d, 1351 s, zero skips: cold build, every-leaf kernel replay, `lake check`, `lake comparator --paranoid` and the rebuild canary, each with its controls); commits after it are not covered |
| Constant-fault obligations endpoint: the Goldilocks family meets `ShapeObligationsOnAs .ebbAndFlow` at `goldilocksContract` and `contract_coefficients` | `Consensus.Goldilocks.MeetsObligationsConstant`, `Consensus.Goldilocks.Obligations.meets_obligations_constant`, `Consensus.Goldilocks.meetsObligationsConstant` | proved in Solution; awaiting full-tier certification. Earlier static endpoint certified on main 2a9b34a11bb9f754a5526593fab6d72366c325a7 and re-certified on ebb2f2ec2783911997e7f4945684f54382690ea6, c361faa46d43bdbdbd6cca76f301e374bb8236ef and b75cd7c586bcdb708d0c94e125307cf32edf051d; these records do not certify the growing-fault migration |
| Constant-fault headline (`Statements/Obligations`): for every setup, assumption set and finite validator type, `CorrectProtocolOn` constant faults, with unrestricted adequacy and realizability; composed by `ShapeObligationsOn.correct` | `Consensus.Goldilocks.GoldilocksCorrectConstant`, `Consensus.Goldilocks.goldilocksCorrectConstant` | proved in Solution; awaiting full-tier certification |
| Healing, the run bundle (`Milestones/Statements/Healing/Run`): HR.1–HR.4, H.2 on the run, H.3 FG non-interference and H.4 (with HR.2 as its closed form `PhaseCountAll`). H.3's `Inv(a_z + T_b)` half is proved after the reset with `T_b = max((8k + 20)Δ, 8Δ)` (`Lemmas/Healing/ResetInv`), so H.4's bridge premise is discharged by H.3; the statements are unchanged | `Consensus.Goldilocks.Healing.HealingRunStatements`, `Consensus.Goldilocks.Healing.healing_run_statements`, `Consensus.Goldilocks.Healing.NonInterference`, `Consensus.Goldilocks.Healing.non_interference` | proved (standard axioms; lemma, not certified; pinned by `ConsensusLeanTest/MilestoneAxioms`) |
| Healing, the phase service (`Milestones/Statements/Healing/Service`): HS.1–HS.4 and their bundle, with HS.3 stated as the claims' after-`r` part (`docs/decisions.md` §"Goldilocks model choices", HS.3) and proved from HS.2 | `Consensus.Goldilocks.Healing.PhaseServiceStatements`, `Consensus.Goldilocks.Healing.phase_service_statements`, `Consensus.Goldilocks.Healing.FrozenTreeAgreement`, `Consensus.Goldilocks.Healing.frozen_tree_agreement`, `Consensus.Goldilocks.Healing.frozen_tree_agreement_clean` | proved (standard axioms; lemma, not certified; pinned by `ConsensusLeanTest/MilestoneAxioms`) |
| Healing, re-proved without HS.3 (a): HR.3 reset existence, HS.4 common-path acquisition and H.4 available healing (conditional on the bridge, `BridgeAt`). Their consumers read only HS.3 (b), which follows from HS.2; the earlier proofs are restored over it, with no `reset_inv` | `Consensus.Goldilocks.Healing.ResetExistence`, `Consensus.Goldilocks.Healing.reset_existence`, `Consensus.Goldilocks.Healing.CommonPathAcquisition`, `Consensus.Goldilocks.Healing.common_path_acquisition`, `Consensus.Goldilocks.Healing.AvailableHealing`, `Consensus.Goldilocks.Healing.available_healing` | proved (standard axioms) |
| Healing, outcome service (`Milestones/Statements/Healing/Outcome`): C1.2 AC outcome service for honest entries, a literal good window or an accepted early justification by the end of the window | `Consensus.Goldilocks.Compose.OutcomeService`, `Consensus.Goldilocks.Healing.Recovery.outcome_service` | proved (`Lemmas/Healing/Recovery/Reports`, 10c3f956; standard axioms) |
| Healing, recovery (`Milestones/Statements/Healing/Recovery`): node O.1 pattern recovery, C1.3 recurring finalizing coverage, HR.5 cache acceptance after the reset. HR.5 is `Lemmas/Healing/Recovery/Cache` (c504ef66); C1.3 is the selected `UPat` stretch, acquisition, old-entry crossing and two-window finalization (`Lemmas/Healing/Recovery`), and O.1 is C1.3 at `R_*` with recovery from high finality (`Recovery/Assembly`) | `Consensus.Goldilocks.Healing.RecoveryStatements`, `Consensus.Goldilocks.Healing.recovery_statements`, `Consensus.Goldilocks.Healing.PatternRecovery`, `Consensus.Goldilocks.Healing.FinalizingCoverage`, `Consensus.Goldilocks.Healing.CacheAcceptanceAfterReset`, `Consensus.Goldilocks.Healing.cache_acceptance_after_reset` | proved (standard axioms): with it every Healing statements module (run, phase service, outcome, recovery, AC level) has a proved bundle |
| Common (`Lemmas/Common/Claims`, outside the trusted surface): F.2 tree mathematics, F.3 digests, slot arithmetic | `Consensus.Goldilocks.CommonStatements`, `Consensus.Goldilocks.common_statements` | proved (`Lemmas/Common/StatementsBundle`, 357c9f29; standard axioms): `Anc.antisymm`, `Anc.total`, `deepest_common_ancestor`, `digest_determines_block` (F.3, with valid roots and equal proposers) and `slotOf_spec`; not imported by `Solution` |
| Frame (`Lemmas/AC/FrameClaims`, outside the trusted surface): G0.3/G0.4 frame facts and sequence vocabulary | `Consensus.Goldilocks.FrameStatements`, `Consensus.Goldilocks.frame_statements` | proved (`Lemmas/AC/FrameStatements`, 60e5bf96; standard axioms); not imported by `Solution`; retention is also exercised on a witness (`ConsensusLeanTest/Goldilocks/Frame/Statements`) |
| Simulation interface (`Lemmas/Simulation/Interface`, outside the trusted surface and `Challenge`): simulation, reads, `NoColl` transport, `conflicts`, evidence, finalized accountability | `Consensus.Goldilocks.Simulation.SimulationStatements`, `Consensus.Goldilocks.Simulation.simulation_statements` | proved (standard axioms), the bundle assembled from its fields (`engineSimulatesNode`, `readIsOut`, `noCollTransport`, `conflicts_iff`, `evidenceInView`, `finalizedAccountable`; four of them in Accepted's proof closure) |
| Healing, AC level (`Milestones/Statements/Healing/AC`; closed forms `ACHealingStandaloneAll`, `ACHealingStandaloneCorollaryAll`, `ACInclusionAll`): H.1 standalone AC healing and H.2 AC inclusion over driven AC traces; H.1's corollary follows from H.1 | `Consensus.Goldilocks.SA.HealingACStatements`, `Consensus.Goldilocks.Healing.healing_ac_statements`, `Consensus.Goldilocks.SA.ac_healing_standalone_corollary` | proved (standard axioms; lemma, not certified; pinned by `ConsensusLeanTest/MilestoneAxioms`) |

## Shape examples

`ConsensusLean/Examples/Shape/{Bft,Streamlet,Tendermint}.lean` (not instances, not on the trusted surface): contract values with admissibility, progress-fit and
tolerance proofs (`Consensus.Shape.bftContract_admissible`, `Consensus.Shape.streamletContract_progressTolerant`,
`Consensus.Shape.tendermintContract_progressTolerant`); no protocol proofs and no milestones yet.

## Deferred

leanblueprint and a dependency graph (trigger: a second instance with milestones, or outside contributors);
a Mathlib-free Spec package (trigger: reuse outside the project).
