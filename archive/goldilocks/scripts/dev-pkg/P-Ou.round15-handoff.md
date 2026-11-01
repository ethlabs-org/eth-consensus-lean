# P-Ou Round 15 handoff

Base: 8f796bb7, branch sleep-pou14. Statement commit: 2bf83b53. Proof commit: dc6ce63b.
Ruling: OUTAGE-CONT-REPAIRED (lead 2026-10-10).
Status: PREPARED. Both exporters are unconditional on the amended conclusion and GREEN.
Full manifest validation is blocked by inherited Assembly and Healing failures;
this package is not reported CLOSED.

## Public amendment

Statements/OutageContinuation.lean contains the exact recommended definitions from
codex/jobs/wseed-verify.md. Only continuation output reads take OutageRepairReady.
HEAD and F clauses, Join readers and FGSAClaims fields are unchanged.
This is an INTENTIONAL FG-SA sleep adaptation: conditional safety after a repairing
gate, not SAME as DC stableAsynchronyResilient. It has no fixed repair deadline.
Current manifest pins: docs/api/fgsa-outage-cont-repaired-pins.json.
Frozen baselines, protocol declarations and Healing modules are unchanged.

## Gate proof and inputs

All paths in this section are under AvailableChainFGSAProofs/Proofs/.
Outage/ScopedCatchUp.lean contains the full types and caller context:

- outage_conflicting_stable_no_lease_veto: a live obligation below conflicting old S,
  and compatible with B, is below B; it cannot veto a compatible result.
- outage_conflicting_stable_advance_iff and outage_gateStep_conflicting_stable_iff:
  for conflicting old S, repair holds exactly when the genuine result is not below S.
- outage_caught_up_gate_seed_iff: the exact equivalence at an actual post-handover gate.
- outage_repair_gate_seed: use the gate supplied by OutageRepairReady. Compatible
  old S uses outage_gateStep_stable_compatible; conflicting old S uses the exact iff.
- outage_continuation_public_reads: covered inclusion, finality inclusion, or the
  supplied repair seed plus outage_stable_compatible_suffix through the inclusive read.

The public reader existential does not select the repair gate. The repair witness
has its own enabled event, label bound and index before the inclusive read.
The suffix proof includes later ticks, deliveries and restarts. It needs no awake
or restart-free interval from the repair gate to the read.

Round 14's unused pre-cut, enabled-veto and retained-result helper lemmas are dropped.
Its used no-veto, advance iff, gate iff and actual-gate iff proofs are retained.
OutageWSeed and its home equation are removed. They are false under the old premises.

```text
┌──────────────────────┬───────────────┬────────────────────────────────────────┐
│ Explicit input       │ Status        │ Named producer or exact source         │
├──────────────────────┼───────────────┼────────────────────────────────────────┤
│ Sleep regime         │ Public premise│ OutageContinuationSleepPrem             │
│ Foundation           │ Named P-Fd    │ fgsa_fgFoundationClaim                  │
│ Source frame         │ Named P-Fd    │ fgsa_srcFrameAboveClaim                 │
│ Source discipline    │ Named P-Fd    │ fgsa_sourceDisciplineClaim              │
│ TSrc, named rows, QC │ Proved        │ SourceDisciplineAt projections          │
│ Finite Clean bundle  │ Proved        │ outage_clean_cut_supplier               │
│ Clean state/history  │ Proved        │ cleanState_of_hist; clean_invariant     │
│ Clean enabled output │ Proved        │ clean_gateOutput_body                   │
│ Clean HEAD transfer  │ Proved        │ cleanHistoryAt_body                     │
│ Clean saved row      │ Proved        │ clean_epoch_saved_row                   │
│ Arming, protected FG │ Proved        │ outage_scoped_arming; initial lift      │
│ Joined provenance    │ Proved        │ outage_joined_provenance                │
│ Results and F        │ Proved        │ outage_continuation_event_state         │
│ Live gate rows       │ Proved        │ outage_caught_up_gate_rows              │
│ Repair readiness    │ Per-read guard│ OutageRepairReady; model predicates     │
│ Post-gate S seed     │ Proved        │ outage_repair_gate_seed                 │
│ Inclusive suffix     │ Proved        │ outage_stable_compatible_suffix         │
└──────────────────────┴───────────────┴────────────────────────────────────────┘
```

The finite Clean supplier's complete type and proof are in
Assembly/OutagePublicInputs.lean, outage_clean_cut_supplier. It uses only the actual
HealthyPrefixSleep₂, derived FaultQ, foundation and source-frame facts. No new
all-node join, saved-row or future-cut premise is left. The regime and initial
read are the existing public antecedents. Repair readiness is a qualification of
each output read, not a claim that every reader repairs by a deadline.

## Exact P-As Root request

Owner P-As: replace Assembly/Root.lean:158-163's old exporter call with:

```lean
theorem fgsa_outageContinuationClaim (p : Params) : OutageContinuationClaim p :=
  outageContinuation_claim_of p
    (fgsa_fgFoundationClaim p) (fgsa_srcFrameAboveClaim p)
    (fgsa_sourceDisciplineClaim p) (assembly_outage_clean_cut_supplier p)
```

The exporter argument list is p, FGFoundationClaim, SrcFrameAboveClaim,
SourceDisciplineClaim, and the finite Clean supplier. There is no WSeed argument.
Add assembly_outage_clean_cut_supplier to Assembly/Outage.lean by copying the
full type and proof of outage_clean_cut_supplier from Assembly/OutagePublicInputs.lean.
Root already imports Assembly/Outage. Use its existing Clean.Export route for the
producer leaves. Keep Assembly siblings out of direct Assembly imports.
The exact copied proof and Root call compile in .lake/sleep-pou-r15/RootRequest.lean;
the final strict evidence is root-request-final.log and root-request-strict.log. No public premise is added.

Assembly/OutagePublicInputs.lean, outage_continuation_public_suppliers, independently
proves the full amended companion from the named producers. Its result has no
extra assumptions. Outage.Export and OutageContinuation.Export are the two lane
boundaries. The existing Shared/Claims.outageContinuation_of_body adapter uses
the amended conclusion through its existing OutageContinuationConcl result type.
P-As must also port the three inherited Assembly/Outage callers at 250, 264 and
278. The current functions still pass obsolete hstore and hnamed arguments.
Use outage_outageCompatClaim_of with the same four named producers and the copied
assembly_outage_clean_cut_supplier. Its true P1 projection supplies FastP1; its
false case supplies SlowP1. Round 13's compiled request contains these exact adapters.
The inherited failures are saved in snapshot-all-deps-build.log.

P-As also owns integration of P-Ou.audit-fragment.txt and P-Ou.coverage-fragment.txt
into the global proof audit. Keep the serial audit's production-only imports.

## Negative-run regression

The old claim and universal seed are false in codex/jobs/wseed-run/run.md.
The copied source checker passes in .lake/sleep-pou-r15/wseed-run.log.
The amended readiness check passes in repair-regression.log: 668 qualified
node/time outputs through 106 are compatible with B. Node 7 at 106 is excluded;
old S=A, result=g, F=g. In the simple awake extension, the label-26 gate at 110
returns Y and repairs S to Y; node 7 is then included.
The source replay and extension are regression evidence, not a Lean execution
certificate. The general qualified theorem is checked by the Lean kernel.
The regression script is .lake/sleep-pou-r15/wseed-run/repair_regression.py.

## Saved validation

All evidence paths are under .lake/sleep-pou-r15/.

- exporters-build-2.log: both lane exporters and actual public suppliers compile
  with --wfail. The direct repair predicate audit also builds (public-audit-build.log).
- exports-final.log and coverage-final.log: 375 proof modules, 253 exports,
  zero unaccepted; 372 local coverage rows, complete audit coverage; Gen zero.
- serial-final.log and serial-strict-final.log: 335 production-only commands,
  only propext, Classical.choice and Quot.sound.
- root-request-final.log and root-request-strict.log: the exact copied finite
  Clean supplier and Root call compile; two standard-axiom results.
- layers-final.log: 72 inherited findings, zero new.
- headers-final.log: PASS; 1,747 files; zero failures and zero items to review.
- scope-check.log: exact recommended definitions; unchanged Join, protocol,
  Healing, frozen baselines and FGSAClaims digest; added Lean lines at most 100.
- wseed-run.log and repair-regression.log: negative-run source replay and the
  amended qualification at 106/110 pass. This is not a Lean execution fixture.
- manifest-write.log: current shallow/deep manifests regenerated. The shallow
  pins cover two entries; deep pins also cover the dependent companion digest.

The full Claims snapshot writer needs all source modules, including modules outside
P-Ou's GREEN scope. snapshot-all-deps-build.log records these inherited failures:
Assembly/Outage, Healing/PhaseBoot, Promotion, PhaseSettle, FrontierSeed,
FrontierServiceGate, Repair, OpeningServiceGate and FrontierServiceSupport.
The first three Assembly failures are obsolete caller arguments. Healing has
existing recoveryStart bounds and support-scope ports. P-As owns the Assembly
ports above. P-H1/P-H2 own the Healing repairs; no Healing source was edited.
claims-snapshot-blocked.log saves the final writer failure. The full
check-fgsa-manifest.sh result is in manifest-check.log. Current public shallow/deep
products are updated; the auxiliary Claims snapshot could not be regenerated.
No checker, allowance or frozen baseline is changed to hide these failures.

Final DCK: dck-final.log PASS; 48 strict sources, 3,406 permitted axiom results,
all controls PASS. Map: 69 targets, 536 GREEN, two inherited S-Ap EXPECTED-FAIL entries.
The actual shallow/deep checks PASS in manifest-check.log: 1,358 entries, 59 modules;
1,358 deep roots and 3,818 dependency nodes. Legacy, V2, Gen and Compose snapshots
also PASS. The full script FAILS at the auxiliary Claims snapshot on missing
Healing/Promotion.olean. Its source build has an inherited recoveryStart-bound
caller error at Promotion:194 (snapshot-all-deps-build.log). The full script
stops before its snapshot controls. The standalone DCK controls do PASS.
After P-As/P-H integration, rerun the current Claims writer and the entire
check-fgsa-manifest.sh with its controls; report CLOSED only after that pass.
