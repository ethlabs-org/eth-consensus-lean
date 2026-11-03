# Roadmap

Milestones, their statements, the Lean names and their status. Work is claimed and tracked in GitHub issues
(rules: issue #2); this file says what exists. Every Lean name here is fully qualified (namespace `Consensus`)
and must be listed in `ConsensusLeanTest/Index.lean`, whose build checks that it exists (check.sh step 12), so a
rename or removal fails until this file is updated.

Status: **proved in Solution** (proved; in the closure of `Solution`, so axiom-audited on every checked head and replayed
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
| Pre-foundation baseline: pinned numbers and the properties sheet | — | archived (`archive/consensus-lean-baseline`, Francesco); never approved, no live statement depends on it |
| First slice (foundation step 7, issue #10): Goldilocks Spec, `Refinement/Defs.lean`, `Statements/<M₁>`, witnesses, finite model; approval (the tag); then a two-agent proof pilot | — | planned (after the statements are settled in fradamt-agent/goldilocks: #4, #5, #7, #12) |
| Certification (foundation step 8, issue #11): `Challenge`/`Solution` entries for the finished milestones (`milestone_statements_modules` in `scripts/boundaries.toml`), nightly replay and comparator | — | certified (full tier PASSED on main 2a9b34a11bb9f754a5526593fab6d72366c325a7, 1371 s, zero skips; [#63](https://github.com/ethlabs-org/consensus-lean/issues/63) row 11-03 02:28); re-certified on main ebb2f2ec2783911997e7f4945684f54382690ea6 (full tier PASSED, exit 0, 1381 s, zero skips; [#63](https://github.com/ethlabs-org/consensus-lean/issues/63) row 11-03 04:45: cold build 243 s, every-leaf kernel replay 235 s with controls, the default-target lake check 561 s with the standard three axioms and the good/bad fixtures, `lake comparator --paranoid` 174 s over 25,065 declarations with controls, rebuild canary 16 s with both controls, 0 lexical sorry/admit), which covers the strengthened `Realizable` of a90299c1 and the trusted-layer review documentation batch; re-certified on main c361faa46d43bdbdbd6cca76f301e374bb8236ef (full tier PASSED, 1381 s, zero skips; [#63](https://github.com/ethlabs-org/consensus-lean/issues/63) row 11-03 09:04, combined phase 2 and head-drop certification: every-leaf kernel replay with controls 227 s, the default-target lake check with the good/bad fixtures 578 s with only the standard three axioms, `lake comparator --paranoid` 175 s over 25,043 declarations, rebuild canary 15 s with the proof hash unchanged, 0 lexical sorry/admit), which covers the half-open L0 delivery, the flat catch-up, the retired `SleepySafePrefix` row and the Goldilocks head-drop: certified as of c361faa4; commits after it are not covered by a full tier yet |
| Accepted: the concrete acceptance endpoint of the Goldilocks family (`Statements/Refinement/Accepted`; for every setup and assumption set the family is accepted at `acceptanceContract` with the fixed coefficients `accepted_coefficients`) | `Consensus.Goldilocks.Refinement.AcceptedEndpoint`, `Consensus.Goldilocks.Refinement.accepted_endpoint`, `Consensus.Goldilocks.Refinement.acceptedEndpoint` | certified (full tier PASSED on main 2a9b34a11bb9f754a5526593fab6d72366c325a7, 1371 s, zero skips; [#63](https://github.com/ethlabs-org/consensus-lean/issues/63) row 11-03 02:28); re-certified on main ebb2f2ec2783911997e7f4945684f54382690ea6 (full tier PASSED, exit 0, 1381 s, zero skips; [#63](https://github.com/ethlabs-org/consensus-lean/issues/63) row 11-03 04:45: cold build 243 s, every-leaf kernel replay 235 s with controls, the default-target lake check 561 s with the standard three axioms and the good/bad fixtures, `lake comparator --paranoid` 174 s over 25,065 declarations with controls, rebuild canary 16 s with both controls, 0 lexical sorry/admit), which covers the strengthened `Realizable` of a90299c1 and the trusted-layer review documentation batch; re-certified on main c361faa46d43bdbdbd6cca76f301e374bb8236ef (full tier PASSED, 1381 s, zero skips; [#63](https://github.com/ethlabs-org/consensus-lean/issues/63) row 11-03 09:04, combined phase 2 and head-drop certification: every-leaf kernel replay with controls 227 s, the default-target lake check with the good/bad fixtures 578 s with only the standard three axioms, `lake comparator --paranoid` 175 s over 25,043 declarations, rebuild canary 15 s with the proof hash unchanged, 0 lexical sorry/admit), which covers the half-open L0 delivery, the flat catch-up, the retired `SleepySafePrefix` row and the Goldilocks head-drop: certified as of c361faa4; commits after it are not covered by a full tier yet |
| Healing, the whole-run statements without an inhabitant (`Statements/Healing/Run`, `Statements/Healing/Service`): H.3 non-interference, HS.3 frozen-tree agreement and their two bundles. Their whole-run proofs depended on `sorry` and were removed (#136, sorry group D); the statements are unchanged. HS.3 (b) alone is proved (`Consensus.Goldilocks.Healing.frozen_tree_agreement_clean`, from HS.2); HS.3 (a) and H.3 (through the bridge) stay open | `Consensus.Goldilocks.Healing.HealingRunStatements`, `Consensus.Goldilocks.Healing.PhaseServiceStatements`, `Consensus.Goldilocks.Healing.NonInterference`, `Consensus.Goldilocks.Healing.FrozenTreeAgreement` | stated; proof open (no inhabitant) |
| Healing, re-proved without HS.3 (a): HR.3 reset existence, HS.4 common-path acquisition and H.4 available healing (conditional on the bridge, `BridgeAt`). Their consumers read only HS.3 (b), which follows from HS.2; the proofs removed at #136 are restored over it, with no `reset_inv` | `Consensus.Goldilocks.Healing.ResetExistence`, `Consensus.Goldilocks.Healing.reset_existence`, `Consensus.Goldilocks.Healing.CommonPathAcquisition`, `Consensus.Goldilocks.Healing.common_path_acquisition`, `Consensus.Goldilocks.Healing.AvailableHealing`, `Consensus.Goldilocks.Healing.available_healing` | proved (standard axioms) |

## Other instances

`ConsensusLean/Instances/{Bft,Streamlet,Tendermint}/`: contract values with admissibility, progress-fit and
tolerance proofs (`Consensus.Shape.bftContract_admissible`, `Consensus.Shape.streamletContract_progressTolerant`,
`Consensus.Shape.tendermintContract_progressTolerant`); no protocol proofs and no milestones yet.

## Deferred (foundation plan §10)

leanblueprint and a dependency graph (trigger: a second instance with milestones, or outside contributors);
a Mathlib-free Spec package (trigger: reuse outside the project).
