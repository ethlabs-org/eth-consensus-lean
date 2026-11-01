# Precheck policy inputs

Current policy (2026-10-09): compiled APIs, dependencies, catalog roots, and public
name inventories use committed current snapshots. An explicit `--write` command
updates generated data. Review additions, removals, ORDER moves, statements, and
changed dependency paths. There are no API freeze copies or per-root exceptions.
The guard merger still copies literal target data into trusted checker code.
The source check requires coverage; the compiled scan requires exact inventory
equality. F-7/F-10 are retired; the legacy API snapshot records those changes.
No checker reads historical port ledgers, census, or ownership records.

Commands:

- `python3 -B scripts/write-api-snapshots.py --write` updates API products.
- `python3 -B scripts/write-api-snapshots.py --check` checks those products.
- `python3 -B scripts/write-check-inventories.py --write` updates audit names.
- `python3 -B scripts/write-check-inventories.py --check` checks audit names.
- `lake env lean --run scripts/CatalogLock.lean --write` updates the catalog.
- `python3 -B scripts/api-diff.py --base <commit> --target <commit>
  --snapshots <paths> --output <report.json>` produces the review report.
- `python3 -B scripts/fgsa-deep.py --attribute --baseline <base.json>
  --snapshot <target.json> --roots <names.txt|roots.tsv|roots.json>` attributes
  deep changes through named roots and shared dependencies on both graph sides.
  Missing planned names are unresolved diagnostics, not fabricated graph nodes.


The default `precheck.sh <worktree>` copies checker code from its own checkout.
Target source files and approved data removals still pass the main policy checks.
A local `.lake/gate-last-full` file is only a tier-selection hint. It is not proof
of a FULL pass and cannot skip the policy copy.

Use `--brief FILE --base REF` to check the complete change scope. The base must
be an ancestor of target HEAD. The check includes committed changes, staged and
unstaged changes, untracked files, deletions, and both paths of a rename.
The brief must contain exactly one section with this format:

````text
ALLOWED_PATHS:
```text
scripts/check-layers.py
AvailableChainFGSAProofs/Proofs/Shared/
```
````

Each entry is an exact relative file path or a directory path that ends in `/`.
Globs, absolute paths, `..`, `.git`, and `.lake` are refused. If `--base` is absent,
the scope check uses main HEAD. Without `--brief`, the default policy is unchanged.

## Exact-head FULL receipts

`precheck.sh --full-pass RECEIPT <worktree>` can skip the main policy copy only
when all these checks pass:

- The receipt has a valid OpenSSH signature in namespace `lean-framework-full-v1`.
- The signer has identity `full-gate` in main's committed `scripts/full-pass-signers`.
- The receipt says FULL PASS, and names the exact target HEAD and current main HEAD.
- The target has no tracked changes or untracked files before and after verification.

The default signer file trusts no key. A lead must add an operator public key in a
policy-only change before this mode can accept a receipt. A target cannot add its
own key, and a local edit to main's signer file has no effect. There is no fallback
from a refused receipt to the bypass path. The normal precheck remains available.

A trusted gate operator can run:

```bash
bash scripts/gate.sh --tier full --base <main-head> --attest-key <private-key>
```

The gate requires a clean target at the start and end. It signs only after every
FULL step returns zero, including proof audit coverage. The JSON receipt and its
`.sig` file stay in the gate log directory. The receipt is bound to both commits;
a new target commit or a new main policy commit requires a new FULL run.
The gate refuses an inherited nonzero `SOURCE_ONLY`. The signer requires exactly
the FULL step set: empty, partial, extra, malformed, and failed results are refused.
Both tiers select `NEG=1` if `BASE..HEAD` matches `scripts/checker-paths.txt` or is
empty (BASE = HEAD, as on main after a landing).
`--neg` or `NEG=1` forces controls. An absent base defaults to the merge base with main.
The receipt records the decision and matched paths. Its `checker-self-tests` step is
required with controls and absent without them. Signing and verification recompute
the diff; a FULL receipt without controls is valid only if no checker path changed.

The private key is the trust boundary. Keep it under the trusted gate operator's
control and supply it only to reviewed gate code in a trusted execution environment.
A signer with this key can issue trusted receipts. This feature does not claim to
protect the key from hostile code that runs with the signer's filesystem access.
No key is created or installed by the gate, and no receipt is signed by default.

## Shared data

`import-policy.json` is the source of the import sets. Run
`python3 scripts/generate-import-policy.py` after an approved data change.
`gate_precheck` uses `--check` and refuses generated-file drift. Layer rules retain
separate named sets where the older checks had different scopes.

`fg-expected.txt` and `fgsa-claims-expected.txt` contain literal tuples. Readers
parse them as data. Main's guard-list merger also accepts the older inline tuples.
It checks removals before it copies target inventory values into main's code.
All readers reject duplicate raw entries. JSON and coverage readers also reject
duplicate object keys before a parser can discard them.

`proof-audit-coverage.txt` pins all active audit names in the six FULL audit files.
Run `python3 scripts/check-proof-coverage.py --write` to generate it with the Lean
parser and compiled owner data, then review the diff. Normal checks never write it.
The complete check accepts namespace-local names and imported declarations, checks
each owner, and refuses missing audit lines and missing inventory entries.

`claims-model-scope.txt` contains exact owner/name pairs. It includes the two
existing Model definitions and their future `_def` names. It does not require
absent lemmas or permit a whole Model namespace. Required existing definitions
also enter the compiled EXPECTED check.
