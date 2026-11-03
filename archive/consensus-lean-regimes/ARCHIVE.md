# Goldilocks node-level regime rows R.3–R.6 (archived, reference only)

The node-level Goldilocks regime statements R.3 (healed), R.4 (final), R.5 (outage) and R.6 (weak), retired by
Francesco's decision (2026-11-03; plan: workbench `cards/regimes_retire_budget.md`):
`ConsensusLean/Instances/Goldilocks/Statements/Regimes/{Healed,Final,Outage,Weak}.lean` (28 declarations, none
proved). The files are copied unchanged from `main` at the archiving commit's parent; their history is in Git.
R.3–R.5 correspond to the generic rows of the Accepted endpoint `healedSafe`, `healthyLive` (through
`Accepted.good`) and `persists`; R.6 (weak continuation) has no generic row and is dropped. R.1, R.2, R.7 and R.8 (`Statements/Regimes/{Sleepy,Always}`) are not archived.

- **Never proved.** None of them was in `Challenge`, `comparator.json`, `Solution` or the declaration closure of
  the Accepted endpoint.
- **Not built.** These files are outside the source directories of the lakefile, so `ConsensusLean` and
  `ConsensusLeanTest` do not contain or import them; they are in no root, no layer of
  `scripts/boundaries.toml`, no snapshot and no name index. They target the toolchain of the archiving commit.
- **Not checked, not edited.** No step of `scripts/check.sh` reads them.
