# P-H2 Round 10 handoff

Branch: sleep-ph2k. Base: b123d7a3. Source/map commit: 22779dbd.
No H2 production obligation remains. Global integration still needs P-As.

## Caller ports and package maps

HealingPhaseSettle uses healing_phase_witness_receipts_recovery for the selected
frontier, top and contest witnesses. It uses healing_ready_read_cutoff for the
previous-slot GST cut and fgsa_rMonoAll for restart-safe settlement. The old
all-carrier service hypothesis is removed. Event and first-rise phase starts
use recoveryStart p E. HealingFrontierRead uses the same start in all six cases.
Saved-window transport guards stay at GST.

PromotionPhase, PromotionSource, HealingPhaseSettle and HealingSleepAxioms all
build with --wfail. They are registered in P-H2.txt. HealingFrontierRead is also
registered because this writer owns its test port. No module is deleted.
All 18 P-H2 expected failures in P-H1.txt are now GREEN.

- P-H2: 120 TARGETS, 590 GREEN, zero EXPECTED-FAIL.
- P-H1: 123 TARGETS, 590 GREEN, one EXPECTED-FAIL (the P-As proof facade).

No production interface changes in this round. Closed H1 theorem statements
are byte-identical. Public claims, budget sums and deadlines are unchanged.
docs/ARCHITECTURE.md needs no interface update. The named producer telescopes
and Foundation wiring in P-H2.round9-handoff.md remain current.

## Complete FG-SA inventory and P-As limits

The Mac inventory builds all 700 non-Assembly/non-NonVacuity Proofs and Tests
modules in the FG-SA libraries with --wfail. The build finds no source failure
outside the excluded P-As files. A separate --wfail build passes for the 695
roots whose import closure avoids the two broken Assembly modules.

Five remaining inventory roots depend on P-As ports:

- Tests.Axioms imports Assembly.Healing and Assembly.ResetArrival.
- Tests.FGCompose imports Assembly.ResetArrival.
- Tests.HealingHTime imports Assembly.ResetArrival.
- Tests.LiveDC imports Assembly.ResetArrival.
- Tests.WeakContinuationGrowthAssemblyAxioms imports Assembly.ResetArrival.

All five use the AvailableChainFGSAProofs prefix. Their own sources have no
reported compile error. Their dependency failures remain P-As work.

A --wfail build also covers all eight full FG-SA library/test-library targets.
It fails only in these P-As sources:

- Assembly/Healing.lean:68 passes a GST bound where recoveryStart is required.
- Assembly/ResetArrival.lean:106 begins the old mono/post-reset telescope calls.
  Use fgsa_rMonoAll and the named joint invariant/extension/input producers
  from the round-9 handoff. Later errors follow those old calls.
- NonVacuity/HealingPackages.lean:453, HealingFirst.lean:205 and
  HealingReset.lean:202 begin old restore calls. Restore takes the exact time.
  These fixtures also need the current sleep schedule and Base record fields.

This writer changed no Assembly, Root or NonVacuity source.

## Validation evidence

All cited evidence is in .lake/sleep-ph2k/.

- caller-build.log: both caller tests and the four missing entries PASS --wfail.
- inventory-build.log and InventoryTargets.txt: the complete 700-root probe.
- inventory-green-build.log and InventoryGreenTargets.txt: 695/695 PASS --wfail.
- inventory-classification.log and integration-failures.log: exact P-As owners.
- full-libraries-build.log: all eight libraries attempted; five P-As source failures.
- dck-h2.log: DCK PASS; 51 strict groups / 4,081 permitted results; 24 controls PASS.
- dck-h1.log: DCK PASS; 53 strict groups / 4,209 permitted results; 24 controls PASS.
- package-counts.log: exact target, classification, strict audit and control counts.
- exports.log: H2's 590 GREEN roots; 474 proof modules; 253 exports; zero unaccepted.
- exports-inventory.log: both package GREEN sets plus the independent inventory;
  972 roots, 644 proof modules, 253 exports, zero unaccepted. InventoryExportRoots.txt
  records the exact root set. No export baseline or allowance changes.
- manifest.log: FG-SA shallow/deep, legacy, V2, generic and Compose snapshots PASS.
  The claim API stage fails on missing Assembly/ResetArrival.olean. The full manifest
  and its later snapshot controls are not PASS. P-As owns the source port above.
- layers.log: 72 inherited findings, zero new. headers.log: PASS.
- sleep-scopes.log: PASS. source-audit.log: no admission, overlong Lean line,
  closed H1 proof change, public change, Assembly edit or NonVacuity edit.

Re-run the complete inventory, full library build and manifest after P-As lands.
No baseline, allowance, snapshot or checker change is needed for these test ports.
