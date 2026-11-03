# Roadmap

Milestones, their statements, the Lean names and their status. Work is claimed and tracked in GitHub issues
(rules: issue #2); this file says what exists. Every Lean name here is fully qualified (namespace `Consensus`)
and must be listed in `ConsensusLeanTest/Index.lean`, whose build checks that it exists (check.sh step 12), so a
rename or removal fails until this file is updated.

Status: **proved in Solution** (proved; in the closure of `Solution`, so axiom-audited on every PR and replayed
nightly: leanchecker on every leaf module, the comparator on `Solution`), **proved**, **stated** (statement written,
proof open), **planned**. **Certified** is reserved for a full-tier certification: `check.sh --full` passed on a
named main commit, recorded on [#63](https://github.com/ethlabs-org/consensus-lean/issues/63).

## Generic contract

The review statements (`ConsensusLean/Statements/Review.lean`, trusted surface) and the milestones that prove
them. `Solution.lean` proves each statement by the milestone theorem whose type it is.

| Milestone (`ConsensusLean/Proofs/`) | Statement | Milestone theorem | Solution | Status |
|---|---|---|---|---|
| `Behaviour` (L2 ⇒ L0: shape claims give the behaviour; composed in `ConsensusLean/Main.lean`) | `Consensus.Review.AcceptedGood` | `Consensus.Shape.Accepted.good` (from `Consensus.Shape.refinement`) | `Consensus.Review.acceptedGood` | proved in Solution |
| `RegimesRealizable` (active witnesses for admissible, tolerant contracts) | `Consensus.Review.RegimesRealizable` | `Consensus.Shape.regimes_realizable` | `Consensus.Review.regimesRealizable` | proved in Solution |
| `Faithful` (L1: the log is the engine's communication) | `Consensus.Review.LogFaithful` | `Consensus.Model.sysOf_log_faithful` | `Consensus.Review.logFaithful` | proved in Solution |
| `Faithful` (L1: holding is being served) | `Consensus.Review.HeldIffServed` | `Consensus.Model.Run.held_iff_served` | `Consensus.Review.heldIffServed` | proved in Solution |

Corollary outside the trusted surface: `Consensus.Shape.Accepted.activeService` (proved).

## Goldilocks

Mapping from the Goldilocks references to the Lean names: `docs/goldilocks-mapping.md`.

| Step | Lean names | Status |
|---|---|---|
| Pre-foundation baseline: pinned numbers and the properties sheet (`ConsensusLean/Instances/Goldilocks/`) | `Consensus.Shape.goldilocksContract`, `Consensus.Shape.GoldilocksTarget` | stated; **not approved**, no proof targets it (issue #38) |
| First slice (foundation step 7, issue #10): Goldilocks Spec, `Refinement/Defs.lean`, `Statements/<M₁>`, witnesses, finite model; approval (the tag); then a two-agent proof pilot | — | planned (after the statements are settled in fradamt-agent/goldilocks: #4, #5, #7, #12) |
| Certification (foundation step 8, issue #11): `Challenge`/`Solution` entries for the finished milestones (`milestone_statements_modules` in `scripts/boundaries.toml`), nightly replay and comparator | — | certified (full tier PASSED on main 2a9b34a11bb9f754a5526593fab6d72366c325a7, 1371 s, zero skips; [#63](https://github.com/ethlabs-org/consensus-lean/issues/63) row 11-03 02:28); re-certified on main ebb2f2ec2783911997e7f4945684f54382690ea6 (full tier PASSED, exit 0, 1381 s, zero skips; [#63](https://github.com/ethlabs-org/consensus-lean/issues/63) row 11-03 04:45: cold build 243 s, every-leaf kernel replay 235 s with controls, the default-target lake check 561 s with the standard three axioms and the good/bad fixtures, `lake comparator --paranoid` 174 s over 25,065 declarations with controls, rebuild canary 16 s with both controls, 0 lexical sorry/admit), which covers the strengthened `Realizable` of a90299c1 and the trusted-layer review documentation batch: certified as of ebb2f2ec |
| Accepted: the concrete acceptance endpoint of the Goldilocks family (`Statements/Refinement/Accepted`; for every setup and assumption set the family is accepted at `acceptanceContract` with the fixed coefficients `accepted_coefficients`) | `Consensus.Goldilocks.Refinement.AcceptedEndpoint`, `Consensus.Goldilocks.Refinement.accepted_endpoint`, `Consensus.Goldilocks.Refinement.acceptedEndpoint` | certified (full tier PASSED on main 2a9b34a11bb9f754a5526593fab6d72366c325a7, 1371 s, zero skips; [#63](https://github.com/ethlabs-org/consensus-lean/issues/63) row 11-03 02:28); re-certified on main ebb2f2ec2783911997e7f4945684f54382690ea6 (full tier PASSED, exit 0, 1381 s, zero skips; [#63](https://github.com/ethlabs-org/consensus-lean/issues/63) row 11-03 04:45: cold build 243 s, every-leaf kernel replay 235 s with controls, the default-target lake check 561 s with the standard three axioms and the good/bad fixtures, `lake comparator --paranoid` 174 s over 25,065 declarations with controls, rebuild canary 16 s with both controls, 0 lexical sorry/admit), which covers the strengthened `Realizable` of a90299c1 and the trusted-layer review documentation batch: certified as of ebb2f2ec |
| Healing, the whole-run statements (`Statements/Healing/Run`, `Statements/Healing/Service`): HR.3 reset existence, H.3 non-interference, H.4 available healing, HS.3 frozen-tree agreement, HS.4 common-path acquisition and their two bundles. Their whole-run proofs depended on `sorry` and were removed (#136, sorry group D); the statements are unchanged | `Consensus.Goldilocks.Healing.HealingRunStatements`, `Consensus.Goldilocks.Healing.PhaseServiceStatements`, `Consensus.Goldilocks.Healing.ResetExistence`, `Consensus.Goldilocks.Healing.NonInterference`, `Consensus.Goldilocks.Healing.AvailableHealing`, `Consensus.Goldilocks.Healing.FrozenTreeAgreement`, `Consensus.Goldilocks.Healing.CommonPathAcquisition` | stated; proof open (no inhabitant) |

## Other instances

`ConsensusLean/Instances/{Bft,Streamlet,Tendermint}/`: contract values with admissibility, progress-fit and
tolerance proofs (`Consensus.Shape.bftContract_admissible`, `Consensus.Shape.streamletContract_progressTolerant`,
`Consensus.Shape.tendermintContract_progressTolerant`); no protocol proofs and no milestones yet.

## Deferred (foundation plan §10)

leanblueprint and a dependency graph (trigger: a second instance with milestones, or outside contributors);
a Mathlib-free Spec package (trigger: reuse outside the project).
