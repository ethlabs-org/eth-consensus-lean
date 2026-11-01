# P-Cl1 Round 2 handoff

Base: d2b00d72, branch sleep-pcl1b. Shared proof files and Clean/Export are unchanged.

## P-Ar: current saved row

Import `AvailableChainFGSAProofs.Proofs.Clean.EpochSaved`.
Use `clean_epoch_saved_row h hq hf hsrc hx hcut hAw hEpoch hOrigin`.

- `hAw` is the receiver's `AwakeClosed` from `slotStartZ q` through `b₀`.
- `hEpoch` is its `RestartFreeTime` on that same interval. A restart at the
  start is allowed. `arming_receiver_window` supplies the protected interval;
  restrict its upper endpoint to the Clean cut before this call.
- `hOrigin` says B is genesis, or B is below a Clean result with label r < q.
  Use the arming origin and lag bound to prove that strict label inequality.
  Do not substitute an arbitrary same-label result: compatibility alone does
  not prove B is below that receiver's result.
- The conclusion is B below current F, or a saved row at q with B below C.
  The proof constructs the enabled receiver gate and its nonempty result,
  orders the earlier origin below C, and retains C in that receiver epoch.

The theorem does not assume a local gate result, a saved row, or cache retention.
It derives each of them. It imports the Clean core and no P-Cl2 wrapper.

## P-Cl2: history, gate and truncation

`cleanHistoryAt_body`, `cleanGateAt_body`, and `cleanTruncAt_body` now have the
approved D018–D021 body types. Their existing wrappers can use the same calls.
The source gate guard and receiving voter guard remain separate.

## P-Cl2: Safety transport

`cleanSafety_of_trunc_body` now takes only the core's two all-node state facts:

```lean
(hs : V2.D.ScheduleWellFormed E rho)
(ht : CompatOn (· ∈ rho.honest) (S_at p c E rho)
        (· ≤ timeIdx rho rho.horizon) ∧
      MonoOn (· ∈ rho.honest) (S_at p c E rho)
        (· ≤ timeIdx rho rho.horizon))
```

It returns the exact reader-scoped `CleanSafetyAt` body, including all integer
output reads. The discarded history/frame/gate conjuncts were unused by the
transport proof. The old internal input body no longer matched the approved
scoped truncation statement.

For a complete core call, use this compiled supplier:

```lean
-- h : CleanCutSet p c E rho rho.horizon ΔF
-- hq : Gen.Pure.FaultQ p.n (Gen.V2.Duty.faulty rho).card
-- hf : FGFoundation p c E rho
-- hsrc : SrcFrameAboveStmt p c E rho
exact cleanSafety_body p c E rho h hq hf hsrc
```

Repair `Clean/Export.cleanSafetyAt_of_trunc` at its current line 107. Its call
at line 111 cannot pass a scoped `CleanTruncAt` as the all-node input pair.
For the zero lane, use the first two all-node clauses of
`(cleanCut_zero_body h).2`. For the positive core lane, use
`clean_sCompatible` and `sExtends`, or call `cleanSafety_body` directly.

The generic `cleanSafety_of_cut` caller at line 161 must obtain the same
all-node suppliers from the assembled Clean core before the transport call.
Do not project the two scoped clauses of public `CleanTruncAt` as all-node
facts. If this generic adapter remains conditional, keep those suppliers as
explicit internal assembly inputs; do not add them to `CleanSafetyClaim`.
Public claim statements are unchanged. P-Cl1 has not edited Clean/Export.

## Audit integration

`scripts/dev-pkg/P-Cl1.audit-fragment.txt` lists the missing canonical imports
and commands under the existing FGSAProofs audit key.
`scripts/dev-pkg/P-Cl1.coverage-fragment.txt` lists their owner/name pairs.
The local `Tests/CleanEpochAxioms` root audits all P-Cl1 public proofs now.
Apply the canonical fragment in the lead serial integration window.
