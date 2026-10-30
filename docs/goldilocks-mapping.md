# Goldilocks mapping (skeleton)

From the Goldilocks references to the Lean definitions, milestones and names (foundation plan §4: one mapping
file per instance). Every Lean name here is fully qualified (namespace `Consensus`) and must be listed in
`ConsensusLeanTest/Index.lean`, whose build checks that it exists (check.sh step 12).

**Status: skeleton.** The only Goldilocks Lean today is the pre-foundation baseline
(`ConsensusLean/Instances/Goldilocks/{Spec,Statements}/Baseline.lean`): the round-model FG-SA numbers and the properties
sheet. It is **not approved** and no proof targets it (issue #38). The first slice (issue #10) re-derives the
statements from the current spec and fills the "First slice" table; each row then gets a read-back by an agent
that did not write it (`CONTRIBUTING.md` "Statements").

## References

All in fradamt-agent/goldilocks, `spec/`:

| Id | Document | Role |
|---|---|---|
| FGSA | `fgsa-protocol.tex` | FG-SA in the round model: the source of the baseline's numbers |
| SPEC | `fgsa-spec.tex` | the current Goldilocks spec (with loose BJ, goldilocks#14, and weakened E1, goldilocks#15) |
| CLAIMS | `goldilocks-claims.tex` (draft, goldilocks#12) | the claims and proof DAG that the instance statements will transcribe |

## Baseline (pre-foundation, not approved)

| Reference | Definition | Milestone | Lean name |
|---|---|---|---|
| FGSA: outputs confirmed (available and stable) and finalized (final) | output schema | — | `Consensus.Shape.goldilocksSchema` |
| FGSA: slots of `4Δ` | time grid | — | `Consensus.Shape.goldilocksGrid` |
| FGSA: one proposer per slot; committee kinds are placeholders | skeleton | — | `Consensus.Shape.goldilocksSkeleton` |
| FGSA: round length `R`, lock lifetime `lockK`, look-back `eta` | parameters | — | `Consensus.Shape.FGSAParams` |
| FGSA: catch-up, heal, latency, outage budget, progress | contract (pinned numbers) | — | `Consensus.Shape.goldilocksContract`, `Consensus.Shape.goldilocks_admissible`, `Consensus.Shape.reference_bounds` |
| intended properties (pre-foundation lists) | reviewed target: bindings, acceptance, extras | — | `Consensus.Shape.GoldilocksTarget`, `Consensus.Shape.GoldilocksBindings`, `Consensus.Shape.GoldilocksExtraAt` |

## First slice (issue #10; to be filled)

| Reference | Definition | Milestone | Lean name |
|---|---|---|---|
| SPEC: protocol semantics | `Instances/Goldilocks/Spec/` | — | |
| SPEC → generic contract | abstraction map, `Instances/Goldilocks/Refinement/Defs.lean` | refinement | |
| CLAIMS: the first milestone's claims | `Instances/Goldilocks/Statements/<M₁>.lean` | `M₁` | |

## Exclusions

What the model leaves out, and why. Generic exclusions (static adversary, equal weights, one `Δ`, no
responsiveness claim, no transaction validity, …) are in README "Scope". For the baseline, the sheet's module
docstring (`ConsensusLean/Instances/Goldilocks/Statements/Baseline.lean`) lists the intended properties not yet stated
(§3), those stated weaker than intended, and the migration obligations. Known differences between the baseline
and SPEC (issue #38): lock lifetime and outage budget, FG attestations after every tick instead of once per
round, and the loose-BJ bounds (`K_W = 2`, general `Δ_F`). The first slice replaces this paragraph with one row
per exclusion: what is left out, why, and which claim it affects.
