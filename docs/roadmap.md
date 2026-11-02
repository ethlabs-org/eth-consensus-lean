# Roadmap

Milestones, their statements, the Lean names and their status. Work is claimed and tracked in GitHub issues
(rules: issue #2); this file says what exists. Every Lean name here is fully qualified (namespace `Consensus`)
and must be listed in `ConsensusLeanTest/Index.lean`, whose build checks that it exists (check.sh step 12), so a
rename or removal fails until this file is updated.

Status: **certified** (proved; in the closure of `Solution`, so axiom-audited on every PR and replayed nightly:
leanchecker on every leaf module, the comparator on `Solution`), **proved**, **stated** (statement written, proof
open), **planned**.

## Generic contract

The review statements (`ConsensusLean/Statements/Review.lean`, trusted surface) and the milestones that prove
them. `Solution.lean` proves each statement by the milestone theorem whose type it is.

| Milestone (`ConsensusLean/Proofs/`) | Statement | Milestone theorem | Solution | Status |
|---|---|---|---|---|
| `Behaviour` (L2 ⇒ L0: shape claims give the behaviour; composed in `ConsensusLean/Main.lean`) | `Consensus.Review.AcceptedGood` | `Consensus.Shape.Accepted.good` (from `Consensus.Shape.refinement`) | `Consensus.Review.acceptedGood` | certified |
| `RegimesRealizable` (active witnesses for admissible, tolerant contracts) | `Consensus.Review.RegimesRealizable` | `Consensus.Shape.regimes_realizable` | `Consensus.Review.regimesRealizable` | certified |
| `Faithful` (L1: the log is the engine's communication) | `Consensus.Review.LogFaithful` | `Consensus.Model.sysOf_log_faithful` | `Consensus.Review.logFaithful` | certified |
| `Faithful` (L1: holding is being served) | `Consensus.Review.HeldIffServed` | `Consensus.Model.Run.held_iff_served` | `Consensus.Review.heldIffServed` | certified |

Corollary outside the trusted surface: `Consensus.Shape.Accepted.activeService` (proved).

## Goldilocks

Mapping from the Goldilocks references to the Lean names: `docs/goldilocks-mapping.md`.

| Step | Lean names | Status |
|---|---|---|
| Pre-foundation baseline: pinned numbers and the properties sheet (`ConsensusLean/Instances/Goldilocks/`) | `Consensus.Shape.goldilocksContract`, `Consensus.Shape.GoldilocksTarget` | stated; **not approved**, no proof targets it (issue #38) |
| First slice (foundation step 7, issue #10): Goldilocks Spec, `Refinement/Defs.lean`, `Statements/<M₁>`, witnesses, finite model; approval (the tag); then a two-agent proof pilot | — | planned (after the statements are settled in fradamt-agent/goldilocks: #4, #5, #7, #12) |
| Certification (foundation step 8, issue #11): `Challenge`/`Solution` entries for the finished milestones (`milestone_statements_modules` in `scripts/boundaries.toml`), nightly replay and comparator | — | done; full tier pending |
| Accepted: the concrete acceptance endpoint of the Goldilocks family (`Statements/Refinement/Accepted`; for every setup and assumption set the family is accepted at `acceptanceContract` with the fixed coefficients `accepted_coefficients`) | `Consensus.Goldilocks.Refinement.AcceptedEndpoint`, `Consensus.Goldilocks.Refinement.accepted_endpoint`, `Consensus.Goldilocks.Refinement.acceptedEndpoint` | done; full tier pending |

## Other instances

`ConsensusLean/Instances/{Bft,Streamlet,Tendermint}/`: contract values with admissibility, progress-fit and
tolerance proofs (`Consensus.Shape.bftContract_admissible`, `Consensus.Shape.streamletContract_progressTolerant`,
`Consensus.Shape.tendermintContract_progressTolerant`); no protocol proofs and no milestones yet.

## Deferred (foundation plan §10)

leanblueprint and a dependency graph (trigger: a second instance with milestones, or outside contributors);
a Mathlib-free Spec package (trigger: reuse outside the project).
