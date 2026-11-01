Archival since 2026-10-09 (user decision); the S0 freeze is retired.

# FG finality safety: S0, S1, S1P

S0/S1 commit: `2ebd6523` (rebased from `78b736b`). All contracts are PROVISIONAL.
Earlier S1P: `fcbf0266` (rebased from `aea1639`). S1P is now complete.
S2 has not started. No push, review, or agent process was started.

S0 records the fixed 2d5b47a input, step-1 API, source and guard hashes,
and the lead acceptance of Opus finding 10. HEAD 88c616d had the same tree.
All frozen FG-SA Statements/Claims, PC-SA claim sources, manifest policy,
pins, allow files, and frozen audits keep their bytes.

S1 adds SafetyReads, SafetyStore, SafetyClient, and SafetyClaims in Compose.
It adds FGSafetyReads, FGSafetyWireLaws, FGSafetyStoreLaws,
FGSafetyOrderLaws, FGSafetyScopeLaws, FGSafetyClientLaws, and
FGSafetyUnitLaws. It adds fourteen read/predicate definitions and their
proved owner equations. There are 76 new public names and
projections. The six planned theorem types check as propositions.
There are no unproved theorems or generic safety proof modules.
The exact S1 guard/inventory diff is in FG-FINALITY-SAFETY-S1-guards.patch.
S1 changes no import-policy.json, check-gly-rules.py, or allow-list line.

For both `.on` and `.idle`, S1P proves:

- All five FGSafetyWireLaws fields. Encoding is injective. Decode/encode,
  authentication, visibility, and exact proposal carriage agree.
- Initial, clock, process, restart, and own-record equations.
- initial_tf and restart_tf, without a Reachable premise.
- process_F and all three fields of the complete FGSafetyOrderLaws record.
  Erasure prefix and output equality remain its two other fields.
- Source membership and own-core equality for the mode-general core read.

The `.on` core read equals the old pcsaCoreReads by a proved owner bridge.
Both seat equivalences are Equiv.refl. Producer signature checks cover
FG-SA and both PC modes. No new premise or cast is needed.
The PC finality view equals FG-SA's window view. The PC certificate record
uses FGSA.fgCertificateLaws, a shared model fact. It uses no FG-SA run claim.
The local lease-deletion fact preserves fg, proposals, and rowPool.

Exact theorem and definition axiom sets are in S1P-axioms.json, under the
full file name FG-FINALITY-SAFETY-S1P-axioms.json. Every set is a subset of
`propext`, `Classical.choice`, and `Quot.sound`. General mode proofs and
explicit `.on`/`.idle` instantiations use the same axiom sets.

The invariant and process_new drafts are in FG-FINALITY-SAFETY-PC-DRAFTS.md.
They start from Reachable and a local ViewRootInj induction. They list the
accepted packed-body/row correspondence and exact named-body obligations.
The named scope uses full PC payloads, including attachments. Emitted tips
need a stored named parent; the emitted-only tip is not placed in Q.
The order citation is pcsa_admitBlock_fg_cases in Shared/FGStore.lean. It moved unchanged from AcFrame/Store.lean:69–85.
Acceptance tests use the original state. Lease deletion precedes the FG
window update. Reconciliation and collection do not write FG.

P2 resolves the lane STOP through lower-helper extraction. Shared.FGStore
owns pcsa_normalizeS_fg, pcsa_reconcile_fg, pcsa_fold_admitRow_fg,
pcsa_fold_poolAckRaw_fg, and pcsa_admitBlock_fg_cases. Their declaration
bytes are unchanged. AcFrame.Store keeps its lane-specific proofs and
publicly imports Shared.FGStore, so its existing imports retain the names.
The move commit changes only the module layout, imports, and audit owners.

The later proof commit adds pcsa_process_F_mono for every PC store and wire.
HEAD, row, ACK, PC, and failed-decode cases preserve FG. A proposal either
preserves FG or calls the window handler on the original FG state.
FGSA.Window.window_on_block_F_mono proves growth in the latter case.
This is a shared window-model fact. It is not an FG-SA run safety theorem.
The new proof uses change bridges and named frame facts. It adds no model
read, owner equation, premise, foreign equation export, or layer exception.

pcsa_safety_process_F lifts that fact through pcsaCoreReadsWith_def.
pcsaSafetyOrderLaws combines it with erase_prefix and output_eq.
The audit checks explicit .on and .idle record instances. Both modes use
the same general proofs and axiom sets. All 42 saved S1P axiom sets are
subsets of propext, Classical.choice, and Quot.sound.

Full PC invariant, insertion metadata, named/emitted-parent scope,
core metadata growth, and client tick_rows remain later work. The prose
drafts stay in FG-FINALITY-SAFETY-PC-DRAFTS.md. There is no open S1P STOP.
FG-SA stays on its existing claim path. S2 has not started.

S1P guard changes are exact. The only new Compose adapter pairs are:

```text
AvailableChainFGSAProofs.Proofs.Shared.FGSafetyClient
  → AvailableChainFGCompose.Statements.SafetyClient
  → AvailableChainFGCompose.Statements.SafetyStore
AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyClient
  → AvailableChainFGCompose.Statements.SafetyClient
  → AvailableChainFGCompose.Statements.SafetyStore
```

import-policy.json laneUpstream adds only those two named Statements paths.
The claims direct-import guard uses the same COMPOSE_EDGES exact-pair table.
It adds no broad prefix allowance.
The new PC adapters permit direct FG-SA imports only of Proofs.Carrier and
Proofs.StoreLaws. FG-SA run imports and their neighboring paths are rejected.
The AcFrame lane remains rejected. Existing Claims and Run edges stay fixed.
There is no check-gly-rules or F-3/F-13/GEN-FIRST allow-list change.
Checker code in S1P, with reasons:

- scripts/check-layers.py adds the four exact adapter-to-Statements pairs
  listed above. It also restricts the two new PC adapters to the named
  FG-SA Carrier and StoreLaws producers. This prevents FG-SA run dependencies.
- scripts/import-policy.json adds SafetyClient and SafetyStore to
  laneUpstream. check-layers.py still requires the exact importer pairs.
- scripts/check-fgsa-claims.sh consults the existing shared COMPOSE_EDGES
  table. The FG-SA adapter needs those exact imports for its signatures.
  The former check rejected them before the audit-pool self-test could run.
- scripts/gate.sh adds FGSASafety-axioms and PCSASafety-axioms. The two
  new adapter audit modules must run in the gate.
- scripts/full-pass.py requires both new audit steps in a FULL receipt.
  An omitted or failed adapter audit must prevent a FULL result.
- scripts/check-proof-coverage.py adds both adapter audits to AUDITS.
  scripts/proof-audit-coverage.txt records each new name and its owner.
- scripts/check-layers-selftest.sh rejects adjacent .Extra imports,
  PC adapter imports of FG-SA run proofs, and the AcFrame lane edge.
  These controls test the new exact boundaries and preserve the lane boundary.

There is no S1P change to scripts/CheckFGAxioms.lean or check-gly-rules.
The exact S1P checker and inventory diff is in
FG-FINALITY-SAFETY-S1P-guards.patch.

S0/S1 validation passed before commit. Its complete results are in the S1
notes. The earlier S1P pre-commit list passed. The affected modules and full
build pass with --wfail. check-build.sh, the layer check, check-gly-rules,
and precheck.sh . pass. CheckProofEqns checks 742 proof modules and 1,033
existing exports, with zero unaccepted. Coverage checks 4,764 declarations
in 13 audits. The Compose closure checks 256 constants in 13 source modules.
Archive pins, FG-SA model/Run/Claims, FG-SA/V2/Generic manifests, and
CatalogLock pass. Claims checks use NEG=0. No required audit is skipped.
All 122 frozen hashes match. The explicit S1P axiom audits match all 39
saved declaration sets exactly. All sets use standard axioms only.
Validation log: /private/tmp/fg-fin-resume-full.log. The first resumed claims
check also passes: /private/tmp/fg-fin-resume-claims-before.log.

Resume fix: the previous claims/build run ended at unused-imports, rc 1.
Shake reported four new removals in Shared/FGSafetyClient. The adapter
now imports Run.Statements.Client for decodeRowObject. It uses supported
shake keep comments on the three imports needed by anonymous producer
signature checks. No shake baseline or checker rule was changed for this fix.
The S1 guard patch keeps its original bytes; its reformat was removed.

Frozen read-owner decision: keep the new reads and their _def theorems
in AvailableChainFGSARun/Model/Protocol.lean and
AvailableChainPCSARun/Model/Protocol.lean. Neither file is in the 122-file
frozen set. All frozen file hashes match. The five step-1 Lean API modules
keep their bytes. The FG-SA manifest/API check reports 1,174 entries in
50 modules, complete, with matching hashes. No frozen check objects.

The affected-module build passes with --wfail. The focused Shake command
then found stale downstream build files. The full repository build
rebuilds those files before the required Shake and claims checks.

Review-fix commits: P1 `fbe5db6e`; helper move `ea23a148`;
order completion `fa7bb693`. Each has the required Claude-Session trailer.
No push.
The current rebase target is main `861ca1f`. The fixed S0 input remains `2d5b47a`.
The integration delta against the earlier main base is the PC relay model,
its affected proofs and regression, and audit-pool-selftest.py. The 122
frozen hashes and five step-1 Lean API hashes match after each fix commit.
P1 selects Or.inl before change and uses only the left carriesS branch.
The PC-object branch is not used by that proof.

Each S1 checker change, with its reason:

- scripts/check-layers.py adds the six exact safety Statements edges and
  four facade imports. This permits only the reviewed S1 dependencies.
- scripts/CheckFGAxioms.lean uses the same exact edges and facade imports
  in the compiled Compose closure check.
- scripts/check-layers-selftest.sh tests those edges and their neighbors.
- scripts/check-fg-compose-controls.py tests missing source, olean, name,
  and forbidden-axiom cases for the four safety Statements modules.
- scripts/fg-compose-expected.txt adds the 76 required safety names.
- scripts/check-proof-coverage.py adds the SafetyAxioms audit.
- scripts/proof-audit-coverage.txt maps those 76 names to their owners.
- scripts/gate.sh adds the required FGSafety-axioms step.
- scripts/full-pass.py requires that step in a FULL receipt.

The earlier S1P checker changes and reasons are listed above. The review
fixes change no checker code. Their only checker-data change is in
scripts/proof-audit-coverage.txt: remap five moved owners, then add the
three new theorem audits. Tests/FGSafety.lean adds their three #print
axioms lines and complete order-record checks for both modes.
The exact review-fix inventory diff is FG-FINALITY-SAFETY-REVIEW-guards.patch.
That patch records the owner remap and three theorem audit additions.
It is a document, not a pending request for a guard exception.
No import-policy, check-layers, allow-list, or equation-baseline line changes.

The rebase also imports main's scripts/audit-pool-selftest.py change.
It separates success and timeout budgets. It checks exact exit codes,
passing twins, and published child PIDs before cleanup. These are main's
control changes, not a new exception in the review fixes.

Full pre-commit checks pass before each of the three review-fix commits.
They include touched builds with --wfail, check-build.sh, check-layers,
check-gly-rules, precheck.sh ., coverage, Compose, archive pins, FG-SA
model/Run/Claims, CatalogLock, manifests, and the new theorem axioms.
Claims use NEG=0. The final equation audit has 743 proof modules, 1,033
existing exports, and zero unaccepted. Coverage has 4,767 declarations
in 13 audits. All 42 S1P axiom sets match the saved JSON exactly.
Logs: /private/tmp/fg-fin-review-p1-full.log,
/private/tmp/fg-fin-review-move-full.log, and
/private/tmp/fg-fin-review-complete-full.log.

Cont3 validation of the staged order completion passes. It includes the
full pre-commit list and check-build.sh. Claims use NEG=0. All 42 saved
axiom sets match exactly. All 122 frozen hashes, five step-1 Lean hashes,
and moved helper and remaining AcFrame proof bytes match.
Log: /private/tmp/fg-fin-cont3-before-full.log.

Cont3 rebases all five FG finality commits onto main 861ca1f.
The order completion is fa7bb693, rebased from 91ff57f8. The helper move
is ea23a148, rebased from 13bb4eff. P1 is fbe5db6e, rebased from 20d26c2.
The rebase has no conflict. Its only source delta is main's root-form
PC-object carriesS branch and its PcRelayRegression tests. All local
proof bytes are unchanged. P1 still selects the left branch with Or.inl.
The guard patch remains a document. No guard code or exception is added.
The full post-rebase build and pre-commit list pass. All 13 independent
checker commands return zero. Claims then pass alone with NEG=0.
Both mode instances compile. All 42 saved axiom sets match exactly and
use only propext, Classical.choice, and Quot.sound. The 122 frozen files,
five step-1 Lean API files, and moved proof bytes keep their hashes.
CheckProofEqns has 743 proof modules, 1,033 exports, and zero unaccepted.
Coverage has 4,767 declarations in 13 audits. No source fix was needed.
Log: /private/tmp/fg-fin-cont3-after-full.log.
Checker logs: /private/tmp/fg-fin-cont3-after-checks/.
S1P is complete. P1 and P2 are fixed. S2 has not started. No push.
