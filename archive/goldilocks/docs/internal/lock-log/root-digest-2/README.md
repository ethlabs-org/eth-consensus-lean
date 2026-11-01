# ROOT-DIGEST-2 landing record

Date: 2026-10-05. Source base: `c24711d`. Integration base: `f106ff8`.
Input: `54e6aa4` on `lf-rd2w3`. The result is an uncommitted working tree.
The owner makes the commit. The cause is ROOT-DIGEST-2 option 3.

## Catalog

The measured catalog set is empty: 0 CHANGED, 0 REMOVED, and 0 ADDED.
All 252 lock lines keep their old hashes. The lock bytes equal the `c24711d` bytes.
`catalog-reconciliation.json` records the SHA-256 and the measured counts.
No catalog write is needed. The final check must report no delta.

The old dependency prediction listed 77 roots. Each of those roots reaches at least
one of 78 distinct internal constants that the old declaration snapshot omitted.
The snapshot skipped `n.isInternal` names except names with the `_private.` prefix.
The prediction treated every absent old name as a changed declaration.
All 78 causes have internal names and no source declaration range. None has an old
fingerprint in that snapshot. Thus the prediction compared an incomplete name set;
it did not find 77 changed lock hashes. The catalog tool includes generated
constants in each closure and measures no change.

The exact 77-root set is in `catalog-predicted-names.txt`. The 78 causes are in
`catalog-omitted-internal-names.txt`. `catalog-prediction-causes.json` gives the exact
root and cause mapping. `catalog-measured-diff.txt` gives the cleared measured set.
No predicted cause remains unexplained.

## Frozen interfaces and costs

`frozen-classification.json.gz` records every changed or added FG-SA and Gen entry
with its kind, old hash, new hash, and exact cause. There are no removals.
FG-SA has 919 CHANGED and 46 ADDED entries. Gen has 125 CHANGED and 37 ADDED entries.
The Gen changes include the 64-entry mode extension, 61 dependency entries, and
37 added root companions. The v2 manifest has no delta from `c24711d`.
`frozen-summary.json` groups the exact causes and counts. The frozen FG-SA file
and its SHA remain unchanged. The existing GUP, LIVE-DC, TF-SEED, ROOT-DIGEST, and
r2.1–r2.3 exceptions remain in the classifications.

The full type records are in `full-frozen-diff.json`, held for owner transfer to
`TS/codex/reports/rdigest2/w3c/`. The large build, gate, and audit logs are also held
for that transfer. They are excluded from this compact record.
`nv-cost-summary.json` retains the W3b paired costs against `c24711d`.
No NV metric exceeds +10%. The accepted three fixture costs remain accepted.
The 304, 404, and 405 endpoint checks remain part of the full build.

## Landing checks

`checks.json` records the final commands and their real exit codes.
`proof-equations.json.gz` maps each original key to its hiding method.
`type-comparison.json` records the public-type comparison for all eight modules.
`axiom-audit.json.gz` records the refreshed declaration names and axiom sets.
`unused-imports.json` records each removed redundant import.
The check-build self-test archives committed HEAD. Any failure that needs the
owner's commit is recorded separately; it is not reported as a passed check.

## Final acceptance status

Every check in the final W3d table exits 0. All check-build sections (a)–(j) exit 0.
The final report and command records are at
`TS/codex/reports/rdigest2/w3d/rd2w3d-final.md` and
`TS/codex/reports/rdigest2/w3d/rd2w3d/final-checks.json`.

The W3c lease patch and W3d fixture arguments are applied. The negative lease
fixtures pass the required `.block` arguments. B3a generates `namedParentHeld.eq_1`
in Model.Store through a private theorem. Run.Proofs.Hooks no longer exports it.
CheckProofEqns, with the existing baseline, checks 651 proof modules and reports
0 unaccepted exports and 0 Gen exports. All 31 original equation keys are hidden.
The eight E1 modules keep all 133 public declaration types. The axiom audit has
1,147 current names and only standard axioms. The Claims compiled EXPECTED/coverage
audit and source ORDER checks pass. The Claims shake scan has 0 NEW findings.

Both landing reviews report LAND:
`TS/codex/reports/reviews/rd2land-sol61.md` and
`TS/codex/reports/reviews/rd2land-astra.md`.
The FULL-tier NUC gate reports PASS. ROOT-DIGEST-2 landed at `be214b3`.
