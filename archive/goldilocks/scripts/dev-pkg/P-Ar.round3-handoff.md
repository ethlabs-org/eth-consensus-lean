# P-Ar Round 3 handoff

Base: sleep-int d60ff01d. Branch: sleep-par3. P-Cl1 audit completion is CLOSED.
The public prefix receipt is CLOSED. Full sleep certificate assembly is OPEN.

## Prefix receipt

Import `AvailableChainFGSAProofs.Proofs.Outage.ArmingKernel`.

`arming_prefix_batch_receipt p : OutagePrefixReceiptDerivedClaim p` is proved
from `OutageSleep₂`. It has no extra service premise. P15-CUT is included.
`arming_batch_service h hx hq hCut` returns the concrete service record.

The proposal anchor is `voteTime q`; its deadline is `earlyTime q`. Proposal
history is durable. Checked delivery supplies dependencies. The public anchor
supplies the handler clock bound. Stored targets use `fgsa_block_accepted_origin`;
their original source acceptance remains the trigger across restart. Triggered
proposals pass the permanent invalidity test. Compatible finality supplies the
other non-exclusion clause. Honest HEAD uniqueness excludes cap conflicts.

`arming_proposal_service` retains its old type. The additive
`arming_proposal_service_trigger` accepts either emission or original acceptance.

## T25 and protected receivers

`arming_healthy_batch` retains its joined transfer and selected-voter guards.
`arming_healthy_batch_protected` derives its receipt services from the regime.
Its remaining inputs are the joined Clean transfer, the comparison result at
label l, `coverLabel b₀ = l + 1`, and the receiver's early-read F floor below D.
It returns the stored batch with strict vote and target stamps at an actual
awake receiver tick. It does not request transfer for an unjoined reader.

`arming_protected_origin_on` obtains an actual positive-label Clean origin from
the Clean state/history at the cut and the stable read. No global epoch is used.

`arming_slow_current_rows_on` returns current F above B, or all slow rows at the
cut with B <= Ca <= D. Its receiver is in the slow protected set. It starts the
row epoch at the row label's start, permits a restart exactly at that start,
and uses the slow lag to put the origin strictly before each row label.

## Returned P-Cl1 row

Pass `clean_epoch_saved_row h hq hf hsrc` as the `hSaved` input of
`arming_cut_saved_on` or `arming_slow_current_rows_on`. Pass the actual
`CleanState` at the cut as `hState`. The type is checked by
`Tests.OutageArming.current_row_consumer` with the actual P-Cl1 theorem.

The consumer keeps the finality alternative. On the row branch, `savedOnly`
puts Ca in the actual Clean result set, and the comparison maximum gives Ca <= D.
The row branch then fits `arming_pending_rows_on` exactly. Keep both receiver
epochs: inclusive cut to strict pending read, and strict read to the actual tick.

Clean proof modules cannot be imported into the Outage lane. Assembly must pass
these proven Clean inputs. No layer allowance or baseline was added.

## Lower GREEN exports for PersistenceStep

Import `AvailableChainFGSAProofs.Proofs.Outage.ArmingStep` for:

- `arming_write_row`
- `arming_writeKeys_stable`
- `arming_gateResult_tick hs hEnabled`

The last equation requires `enabledGateAt`. A raw result alone is insufficient.
`arming_enabled_of_result` in ArmingHistory obtains that guard from a nonempty
executed result. The six lease-write helpers and the gate equation moved from
ArmingGate to ArmingStep; their names are retained.

`arming_gate_write` now requires `joinedNow p P = true`.
`arming_gate_core_on` proves the pending S and lease-or-F result for protected
receivers, from the certificate and `coverLabel b₀ = l + 1`. It derives awake,
the enabled gate, and the equal-time receiver epoch from that protected scope.
It has no global NoRestart premise. The legacy `arming_gate_core` and
`pending_gate_lease_or_F` now require awake at the exact pending gate in their
receiver conclusions. Their tick witness is obtained with that exact fact.

## Remaining full certificate port

All 16 P-Ar targets compile. This does not close the full sleep certificate.
ArmingMain's `arming_cert`, `fast_arming` and `slow_arming` remain legacy
NoRestart producers. They use all-honest `ArmingBatchState`, the awake batch
denominator, all-honest `hcleanGate`, and the old saved-retention input.
Their legacy batch proof is separate from joined T25. They now also receive
`NamedReceiptRootCollisionFree`, as required by their receipt consumers.

Full closure must construct the protected receiver certificate from the Clean
origin, joined batch, current saved rows and local receiver epochs, then connect
it to pending input and the scoped gate producer. The finality branch must pass
through that construction. Do not supply NoRestart from OutageSleep₂.

No Claims/Statements, P-Ou proof, Shared proof, checker, baseline or allowance
changed. The P-Ou owner must apply its consumer ports in its own work tree.

## Validation

DCK P-Ar PASS. Package map: 17 targets, 485 GREEN, zero owned EXPECTED-FAIL.
The two inherited EXPECTED-FAIL modules remain with S-Ap.
Complete GREEN exports and 166-entry local coverage PASS: 288 proof modules,
253 exports, zero unaccepted, Gen zero exports. The coverage control passes.
Layers: 72 inherited findings, zero new. Evidence: `.lake/sleep-par-r3/`.
