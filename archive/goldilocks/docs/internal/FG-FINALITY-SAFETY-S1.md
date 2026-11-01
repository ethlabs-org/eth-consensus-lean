# FG finality safety: S1

All contracts are PROVISIONAL. There are no generic safety proof modules.
The six planned theorem types are checked as propositions in Tests/SafetyReads.
No theorem is assumed. The owner equations use rfl.

New Statements modules: SafetyReads, SafetyStore, SafetyClient, SafetyClaims.
They contain FGSafetyReads, wire/store/order/scope/client/unit laws,
the run and observation predicates, and their exact owner equations.
There are 76 new public declarations and projections. Tests/SafetyAxioms
checks each one. Both source and compiled coverage use the existing driver.

Exact new guard pairs in check-layers.py and CheckFGAxioms.lean:

```text
Statements.SafetyReads → AvailableChainKitFG.ClientOnce
Statements.SafetyReads → AvailableChainSimplexFG.Evidence
Statements.SafetyReads → AvailableChainKitFG.CertificateCoreDef
Statements.SafetyReads → AvailableChainGeneric.Statements.V2.Duty.Slashing
Statements.SafetyStore → AvailableChainKitFG.StoreSafetyDef
Statements.SafetyClient → AvailableChainGeneric.Statements.Pure.Quorum
```

The importer prefix in that list is AvailableChainFGCompose.
The facade permits the four named new Statements imports.
The original Shared.FGCompose allowance still covers only the three original
modules. No adapter-to-Compose edge is added in S1.
The own Statements imports use the existing own-Statements rule.
SafetyClaims also imports EngineV2.Conditions.Duty.Committees and
Generic.Statements.V2.Duty.Counts. Both use existing step-1 type allowances.
The Statements boundary still rejects Proofs imports.

import-policy.json and check-fgsa-claims.sh: zero diff in S1.
check-gly-rules.py and all F-3/F-13/GEN-FIRST allow data: zero diff.
Data changes: fg-compose-expected.txt adds the 76 names;
proof-audit-coverage.txt adds their exact owning modules and audit.
The new FGSafety-axioms gate step is required by full-pass.py.
The existing policy controls test every required step, including this step.
Layer fixtures check the exact external edges and adjacent module names.
Safety source/compiled controls check missing source, olean, names, and
forbidden axioms for each new Statements module. The existing proof audit
controls check missing lines and wrong owning modules.

safetyHolder and its equation take no Env or DecidableEq argument.
safetyFinalizedAt uses only the finality view. The order record does not
use Good or an invariant. The client record retains restart preservation.
The run scope includes raw rejected proposals. It does not use proposalFG.

Validation passed before the S0/S1 commit. The touched modules and full
repository build used --wfail. The full build completed 4,356 jobs.
check-build.sh passed, including check-gly-rules and CheckProofEqns.
The latter checked 739 proof modules and 1,033 existing exports, with zero
unaccepted exports. The layer check and precheck.sh passed.
Compiled coverage checked 4,725 declarations in 11 audit modules.
The Compose closure checked 256 constants in 13 source modules.
The explicit safety controls passed. Archive pins, FG-SA model/run/claims,
CatalogLock, and V2/Generic/FG-SA manifest checks passed. Claims used NEG=0.
All 122 frozen files are byte-identical. All new axioms are standard only.
An initial audit lacked the existing LegacyMode olean. It was built; the
complete list was rerun. No missing-module audit was skipped.
The exact guard and inventory diff is in FG-FINALITY-SAFETY-S1-guards.patch.
