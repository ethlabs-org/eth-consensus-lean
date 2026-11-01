# P-Ar Round 7 handoff — 2026-10-10

Base: sleep-int 102d8f5b. Branch: sleep-par7.
P-Ar CLOSED. The last closure item and final package validation pass.

## Producer and shared supplier

Import AvailableChainFGSAProofs.Proofs.Outage.ArmingKernel.

```lean
theorem arming_continuation_prefix_receipt [Fintype V] {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF) :
    OutagePrefixReceipt p c E rho fast T b₀
```

The producer calls arming_prefix_receipt_of_healthy_prefix with h.pre.
That supplier takes HealthyPrefix₂. It derives each local batch from
arming_batch_service_of_prefix, protected receiver membership, the label
window, and the per-label earlyTime q ≤ b₀ guard. Equality is allowed.
The lower service suppliers use the same healthy prefix, actual emissions
or source acceptances, compatible targets, and the receiver's own epoch.
The final prefix supplier has no assumed receipt-service callback.

Both arming_prefix_batch_receipt and arming_batch_service keep their exact
existing names and types. The other six existing service exports also
keep their types. All 28 existing theorem signatures in ArmingKernel are
unchanged. The outage export and continuation export use the same supplier.
No η budget, OutageE1, OutageLengthV, or OutageE is used by this prefix proof.
All required premises are present. There is no missing-field STOP.
Public Claims/Statements and non-arming Outage files are unchanged.

## Actual consumer check

The extracted check imports the real, unchanged RestoredBatch consumer.
It does not copy that consumer or assume its prefix input.
Saved source: .lake/sleep-par-r7/ContinuationConsumer.lean.
Saved output: .lake/sleep-par-r7/consumer-check.log.

```lean
import AvailableChainFGSAProofs.Proofs.Outage.ArmingKernel
import AvailableChainFGSAProofs.Proofs.Outage.RestoredBatch

namespace AvailableChain.FGSA.Run.Tests.OutageArming

theorem continuation_receipt_consumer {p : Params} {In V : Type}
    [DecidableEq V] [Fintype V] {c : AppCodec In} {E : Generic.Env V}
    {rho : V2.D.Run V (fgsa p c)} {fast : Bool} {T b₀ b₁ ΔF : Time}
    (h : OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF) :
    OutageContinuationReceipt p c E rho fast T b₀ b₁ := by
  exact outage_continuation_receipt_of_prefix h (arming_continuation_prefix_receipt h)

end AvailableChain.FGSA.Run.Tests.OutageArming

#print axioms AvailableChain.FGSA.Run.Tests.OutageArming.continuation_receipt_consumer
```

Run after building ArmingKernel and RestoredBatch:

```bash
lake env lean -Ewarning .lake/sleep-par-r7/ContinuationConsumer.lean
```

This application type-checks. Its strict audit uses only propext,
Classical.choice, and Quot.sound. RestoredBatch was built with --wfail.
The persistent production-prefix regression is continuation_prefix_consumer
in Tests/OutageArming.lean:1416, with its own strict command.

## Declarations and audits

All new production declarations are in ArmingKernel.lean:

```text
┌──────┬───────────────────────────────────────────────────┐
│ Line │ Declaration                                       │
├──────┼───────────────────────────────────────────────────┤
│ 262  │ arming_nonrow_delivery_of_prefix                   │
│ 310  │ arming_fresh_head_service_of_prefix                │
│ 374  │ arming_proposal_service_trigger_of_prefix          │
│ 572  │ arming_proposal_anchor_service_of_prefix           │
│ 662  │ arming_target_service_of_prefix                    │
│ 721  │ arming_head_not_excluded_of_prefix                 │
│ 831  │ arming_batch_service_of_prefix                    │
│ 892  │ arming_prefix_receipt_of_healthy_prefix            │
│ 901  │ arming_continuation_prefix_receipt                 │
└──────┴───────────────────────────────────────────────────┘
```

The production fragment has 216 strict commands and 216 matching owner rows.
It imports production modules only. The local audit has 271 commands and
complete checked coverage. All nine new production declarations have direct
strict commands in both the fragment and OutageArming. The test declaration
has a local command only. Use the existing Tests.Axioms coverage key during
serial integration; no shared audit or coverage file was edited here.

Evidence: .lake/sleep-par-r7/. No public STOP.

## Final validation and status

P-Ar CLOSED. All 22 owned targets remain GREEN. The map has 490 GREEN
modules. The two inherited EXPECTED-FAIL roots remain AvailableChainFGSARun
and AvailableChainFGSARun.Tests.Axioms, both owned by S-Ap.
No assigned target was removed or moved to EXPECTED-FAIL.

```text
┌──────────────────────────┬──────────────────────────────────────────────┐
│ Check                    │ Result                                       │
├──────────────────────────┼──────────────────────────────────────────────┤
│ DCK P-Ar                 │ PASS: 22 targets, 490 GREEN                   │
│ Package strict audits    │ PASS: 38 roots, 3,235 results                 │
│ DCK controls             │ All 24 PASS                                  │
│ Complete GREEN exports   │ 294 proof modules, 253 exports, 0 unaccepted  │
│ Local complete coverage  │ 271 commands, correct source owners          │
│ Local exports / control  │ 170 modules, 252 exports, 0 unaccepted; PASS  │
│ Production strict audit  │ 216 commands / results / matching owner rows │
│ Actual continuation call │ PASS; 1 strict result                        │
│ Layers                   │ 72 inherited findings, 0 new                 │
│ Module headers           │ No P-Ar failure; P-Ou GoodVotes:2 fails       │
│ Source checks            │ 28 old signatures unchanged; width <=100     │
└──────────────────────────┴──────────────────────────────────────────────┘
```

Only propext, Classical.choice, and Quot.sound occur in strict results.
No public claim, dependency, baseline, allowance, or shared inventory changed.
No new P-Ar closure input remains. P-Ou hRows was supplied in the merged base.
The old Round 6 hRows note is superseded. Other packages keep their own work.

Evidence: consumer-build.log, consumer-check.log, dck.log,
exports-green.log, coverage-write.log, coverage-check.log, coverage.txt,
fragment.log, layers.log, module-headers.log, and source-checks.log under
.lake/sleep-par-r7/.
