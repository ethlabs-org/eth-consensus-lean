# Sleep development package maps

Run `bash scripts/dev-check.sh --package WP` for `scripts/dev-pkg/WP.txt`.
The fixed S1 scope is in `scripts/dev-scope-s1.txt`.

Each map has three sections:

```text
┌─────────────────┬──────────────────────────────────────────────────┐
│ Section         │ Entry                                            │
├─────────────────┼──────────────────────────────────────────────────┤
│ [TARGETS]       │ Module.Name                                      │
│ [GREEN]         │ Module.Name                                      │
│ [EXPECTED-FAIL] │ Module.Name RepairPackage                        │
└─────────────────┴──────────────────────────────────────────────────┘
```

TARGETS lists every existing module that the package changes, every new module,
every test module and every audit root. Targets outside S1 are allowed. Keep this
list independent of the compile classification. GREEN and EXPECTED-FAIL must cover
S1 REQUIRED union TARGETS exactly. Each EXPECTED-FAIL entry needs a repair owner.
The same target can occur in TARGETS and GREEN, or in TARGETS and EXPECTED-FAIL.
Other duplicate entries, unknown modules and entries outside the domain fail.

The package check builds each GREEN module with `--wfail`. It runs a strict audit
on each GREEN source that has `#print axioms` commands. Move a broken audit root to
EXPECTED-FAIL with its repair owner; keep the module REQUIRED in the fixed S1 scope.
At S1, all REQUIRED modules must compile. EXPECTED-FAIL is not an S1 section.
New modules under the S1 prefixes must be added to the fixed scope; a missing entry
fails before build. DEFERRED entries have owners and come from import closure, not
from build failures. REQUIRED modules and S1 audits cannot reach DEFERRED modules.

Use `--stage s1` for the eight strict audits, six scoped coverage keys and the
FGCompose source-name comparison. Use `--all` at G-S2 for the default build,
claims check, full proof coverage, Compose check and all strict audit roots.
Neither development level checks manifest or deep data. G-S3 uses the full gate.
Successful development checks report `DCK PASS (level)`.

Each package updates its own map, ledger rows and matching audit inventory in the
same commit as its declarations. Use `check-proof-coverage.py --audits Key...` to
check selected sections. Add `--write` to regenerate those sections. This imports
only the selected audit roots and keeps other sections byte-identical. The full
unscoped check reconciles every audit at G-S2. Unknown keys fail before Lean runs.
EngineV2 and KitV2 keep strict audits but have no proof-coverage keys. Full data
inventories and the final SLEEP-1 freeze remain P-Da work.

Controls run by default (`NEG=1`) under DCK and under the full gate's build checks.
They use private `.lake` fixtures. `NEG=0` skips controls, not positive checks.
