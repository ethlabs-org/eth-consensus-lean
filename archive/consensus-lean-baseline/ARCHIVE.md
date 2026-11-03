# Goldilocks Baseline sheet (archived, reference only)

The pre-foundation Goldilocks baseline of this repository, archived by Francesco's decision (2026-11-03,
rule-cost sweep): the round-model pinned numbers (`ConsensusLean/Instances/Goldilocks/Spec/Baseline.lean`:
`goldilocksSchema`, `goldilocksSkeleton`, `FGSAParams`, `goldilocksContract`) and the properties sheet
(`ConsensusLean/Instances/Goldilocks/Statements/Baseline.lean`: `GoldilocksBindings`, `GoldilocksExtraAt`,
`GoldilocksTarget` and its §1 theorems), with their tests (`ConsensusLeanTest/Goldilocks.lean`). The files are
copied unchanged from `main` at the archiving commit's parent; their history is in Git.

- **Never approved.** It was a pre-foundation target; no proof targeted it, and nothing in the closure of
  `Challenge`, `Solution` or `Refinement.Accepted` imported it.
- **Not built.** These files are outside the source directories of the lakefile, so `ConsensusLean` and
  `ConsensusLeanTest` do not contain or import them; they are in no root, no layer of
  `scripts/boundaries.toml`, no snapshot and no name index. They target the toolchain of the archiving commit.
- **Not checked, not edited.** No step of `scripts/check.sh` reads them.
