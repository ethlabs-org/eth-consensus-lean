# P-Ou Round 5 handoff

Base: 81186a4b. Branch: sleep-pou4. P-Ou remains PREPARED, not CLOSED.
Proof groups: c4a39af7, 9ff21cea. Public claims and protocol declarations are unchanged.
This file replaces the pending-source and old-deadline entries in the round 4 handoff.
The other round 4 ownership and assembly boundaries still apply.

## Pending producers

ReceiverInputs:365, outage_arming_sources_from_prefix closes the full source seed:

```lean
(h : HealthyPrefixSleep₂ p c E rho b₀ ΔF)
(htsrc : TSrc p c E rho)
(hc : ArmingSleepCert p c E rho fast T b₀ B l D Dh)
(htransfer : ∀ y z s C H, y ∈ rho.honest → z ∈ rho.honest →
  joinedAt p E rho z (s + 1) (SA.voteTime p.toParams (s + 1)) →
  SA.gateTime p.toParams s ≤ b₀ → gateResult p c E rho y s = some (some C) →
  vHead p c E rho z s = some H → Block.Preceq C H) :
OutageSourceHistory p c E rho B
  (afterTicksIdx rho (SA.gateTime p.toParams (l + 1)))
```

ReceiverInputs:344 proves the exact hPending of PersistenceSleep:266 for all honest actions,
including W. It uses the actual source's passed gate and the joined Clean batch.
It does not restrict the global source seed to covered nodes.

GoodVotes:136 proves hTargets at label l+1 from the scoped certificate and htransfer.
It applies at every actual enabled pending receiver, including W.
PersistenceSleep:249 extends the strict-cut F bound to that actual tick.
The epoch and environment join producers are PersistenceSleep:192/209/218.

ReceiverInputs:18/83/166 supply prefix HEAD, retained proposal and batch services.
ReceiverInputs:247 constructs GateReceiptScope at every enabled pending gate.
ReceiverInputs:303 proves compatibility of every enabled pending result.
The receipt deadline is e(l+1) = d(l) ≤ b₀. The gate can be after b₀.
These prefix services need no GST bound and no public receipt premise.

Tests/OutageServices:65 instantiates Clean/Closure:219 cleanHistoryAt_body and derives
htransfer from its actual joined projection. This closes the producer check against P-Cl1.
The existing P-Fd TSrc and named-source producers are unchanged.

## Deadline and handover producers

PersistenceDeadlines:95, outage_row_deadline_origin proves, for every retained row:

```lean
∃ j < i, ∃ s C, enabledGateAt p c E rho j x s ∧
  gateResultAt p c E rho j = some (some C) ∧ Block.Preceq row.1 C ∧
  row.2.2 = SA.gateTime p.toParams s + L p
```

The proof is an event induction from the empty initial obligations.
Delivery and restart add no row. Max renewal either retains an old row or gives the new
write deadline. Each new row has a real enabled gate origin.

PersistenceDeadlines:179, outage_conflicting_row_deadline proves row.deadline ≤ OutageEnd(r).
Its only remaining result input is bounded to this actual receiver prefix:

```lean
hResults : ∀ j s C, j < i → r < s → enabledGateAt p c E rho j x s →
  gateResultAt p c E rho j = some (some C) → Block.Compatible C B
```

Compatibility forces the conflicting row's origin label to be at most r.
ContinuationTiming:133 identifies OutageEnd(r) with d(r)+L and v(r+k+1).
PersistenceDeadlines:206/233 prove that the actual handover clock and tick contain no
conflicting rows. Expiry removes rows at deadline equality, even if the HEAD is suppressed.
Tests/OutageServices:81 checks this exact tick consumer.
This is a conditional handover proof; the global late-result producer remains open.

## Remaining P-Ou work

- ExactProposalReceipts:229: the complete InclusionReceiverInputs producer remains open.
  The new prefix services do not yet construct its relay and retained score fields.
- GoodVotes:176/322: hTargets at later labels remains open. Only the pending label is proved.
- GoodVotes:378: hResults after the first restored label remains open for every honest writer.
- Induction:120 and ContinuationInduction:37: both full joint inductions remain open.
  Their old all-honest seeds and NoRestart lanes were not replaced in this round.
- ContinuationJoint:671/871, Close:84, Outage/Suppliers and mixed Export:
  scoped read/duty closure and the full handover integration remain open.
- Tests/OutageInduction remains EXPECTED-FAIL with those consumers.

These are owned proof tasks, not missing inputs assigned to another package.
No false producer or public STOP was established in this round.

## Other-package boundaries

Owner P-Ar, ArmingSleep:699/713, fast equality construction:

```lean
hLast : ∃ C, (((b₀ - 6 * p.Δ) / (4 * p.Δ)).toNat, C) ∈
  cleanResults p c E rho (timeIdx rho b₀)
```

Owner P-Ar, RestoredBatch:377, continuation-prefix adapter:

```lean
∀ {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
  (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
  (fast : Bool) (T b₀ b₁ ΔF : Time),
  OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF →
  OutagePrefixReceipt p c E rho fast T b₀
```

The new pending seed accepts HealthyPrefixSleep₂ and therefore works at either arming
endpoint once a scoped certificate is supplied. It does not solve the P-Ar equality case
or convert lengthV into the eta budget of OutageSleep₂.

Owner P-As, Assembly/Outage:75 and Shared/Claims:30/39: the bounded Clean gate/output
projections and the remaining sleep recovery/scoped claim adapters retain the exact
round 4 handoff types. No source from another package was edited.

## Registration

45 TARGETS, 504 GREEN, 11 EXPECTED-FAIL: nine P-Ou and two S-Ap.
GREEN records compilation. It does not record public closure.
Two new owned production modules: ReceiverInputs and PersistenceDeadlines.
Local coverage: 182 commands, 158 production and 24 standalone test commands.
Production audit imports use production modules under the existing canonical key.

## Validation

Proof source 9ff21cea. DCK P-Ou PASS: 504 GREEN modules, 41 strict sources,
3,145 axiom results and all 24 controls. Complete GREEN exports: 316 proof modules,
253 exports, zero unaccepted and zero Gen exports. Complete local coverage and its
control PASS for 182 commands. Only propext, Classical.choice and Quot.sound occur.
Layers: 72 inherited findings, zero new. New prose/code lines and whitespace pass.
No checker, baseline, allowance or toolchain changed.

The actual remaining exporter and OutageInduction roots were attempted.
They fail in Induction, ContinuationReceipt and P-As-owned Shared/Claims.
The map retains their EXPECTED-FAIL status; public closure remains open.
Evidence: .lake/sleep-pou-r5/dck-final.log, exports-final.log,
coverage-controls.log, layers-final.log, group2-audits-build.log and open-consumers.log.
