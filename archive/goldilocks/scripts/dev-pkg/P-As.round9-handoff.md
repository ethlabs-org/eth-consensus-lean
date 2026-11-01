# P-As Round 9 handoff

Status: ASSEMBLY CLOSED / MANIFEST BLOCKED-PCSA.
Branch: sleep-pas9. Base: 082d9c89. Assembly commit: 7174ed2f.
The four returned P-H2 results are now supplied in Assembly. No P-As proof
obligation remains. All 68 assigned targets are GREEN; the map has no expected failure.

## Returned producer wiring

Assembly/ResetArrival supplies the complete telescope from P-H2.round9-handoff.md.
The following adapters have no assumed successor step or healing result:

- assembly_healing_inv_of_set uses healing_postReset_inv_recovery.
- assembly_healing_extension_of_set uses healing_h0_extension_recovery.
- assembly_healing_localInput_of_set uses healing_localInput_recovery.
- assembly_healing_fullInput_of_set uses healing_fullInput_recovery.

All common inputs have these named producers:

- RecoverySleep₂: the existing HealingSet premise.
- mono: fgsa_rMonoAll, including restarts.
- emittedNonempty: sourceDiscipline_emittedNonempty.
- emittedName: emittedName_window at the valid schedule.
- writes: fgsa_leaseOrigins_lastWrite at that schedule; joinedNow stays in its last-write law.
- xing: fgsa_rXing with idealization, linked seats, fault count and signatures.
- origin: sourceDiscipline_qcOrigin with Base, FaultQ and fgsa_rStore.
- cap: fgsa_rCap_channel.
- source: sourceDiscipline_tSrc.
- heldRows: held_chain_row_origin_before with signatures and the valid schedule.
- finalityCap: fgsa_finalityCap.
- hhead: cap_finality_head.
- rowCovered: rowPermission_covered E rho; its Base and fault inputs stay explicit.
- rows: fgsa_tRows_recovery at hset.toRecovery₂.
- emittedPairs: healing_reset_emittedName at hset.base.
- progressCoverage: fgsa_batchCoverage p ΔF .progress c E rho.
- hfold: fgsa_foldTrichotomy_progress p.
- faultQ: fgsa_faultQ_of_count p hset.fault.
- honestQuorum: kmid_honest_quorum with linked seats and the fault count.
- hbound and hδ: the existing LivenessBoundW and clock premises.

Assembly/Healing uses healing_proposal_receipt_recovery for the actual proposal
and receiver at the finite deadline. Permanence uses healing_tPerm_recovery with
mono, xing and joined last writes. Reset lease and lease/raw step adapters use
the returned RMonoAll and source arguments. No Proofs/Healing body or statement changes.

## Final public premises

The kernel types are saved in .lake/sleep-pas-r9/producer-checks.log.
The final claim entry points have no added producer premise:

- fgsaClaims: Params only; all fields have proved producers.
- healing_hTimeClaim and healing_hTimeClaim_all: Params only, returning HTimeClaim.
- healing_healingInputClaim: Params only, returning HealingInputClaim.
- healing_resetArrivalStatement and healing_resetArrivalFull: Params, G and ΔF only.
- fgsa_renewedPromotionClaim: Params only, returning RenewedPromotionClaim.

Applying these claims to a run uses their unchanged public premise packages.
Full reset arrival uses HealingSet, LivenessBoundW, the clock equation and the
complete recoveryStart + B'_resetF + Γ + 4Δ horizon. H-time uses HealingTimePrem
and its recoveryStart + B_HF horizon. Local input uses HealingInputPrem with its
selected H0 witness and tstar <= horizon. Promotion keeps its public selected
phase, witness and finite run premises. No new public premise is introduced.

The selected per-run Assembly lemmas no longer take extension, localInput,
fullInput or inv. assembly_healingInput_of_inv keeps its historical name but
constructs inv from the recovery producer. Only u and QStar change in extension.
Both finite HG.5 guards and the selected witness are retained.

Conditional composition APIs remain available. Their hypothetical search, step,
cone, extension and input arguments have the named producers above and the
existing healing_frontierSearch_of_set, healing_postReset_*Step_of_set and
healing_postReset_coneStep_of_set adapters. The final public claims and Root do
not require these hypothetical arguments.

There is no all-TF receipt, prior join for every node, bounded pre-GST transport,
future delivery past the horizon, or whole-run NoRestart premise. Public
Claims/Statements, budget constants, protocol sources and Proofs/Healing are unchanged.

## Fixtures and canonical coverage

HealingPackages, HealingReset and HealingFirst already pass the exact restart
time to restore in the merged base. They also have the current schedule and Base
fields. Fresh source checks pass for all three. Their horizons remain 310, 304
and 310. No extra fixture change is needed in this round.

The full build exposed eight obsolete Outage audit commands. These declarations
were removed before this round. Only those commands and coverage rows are removed.
The current scoped producers keep their existing audit commands.

Canonical coverage adds four new Assembly rows, two existing WeakContinuation
witness rows and two existing Root rows. It corrects 14 helper-proof owner labels from compiled module data.
It removes 36 misplaced test rows from the canonical key; those commands remain
in six local test audits, all checked strictly. All other rows and their order
stay unchanged. No baseline, allowance, snapshot or checker is changed.

## Validation

All cited logs are saved in .lake/sleep-pas-r9/.

```text
┌────────────────────────┬───────────────────────────────────────────────────┐
│ Check                  │ Result                                            │
├────────────────────────┼───────────────────────────────────────────────────┤
│ Assigned targets       │ 68/68 GREEN; map 530 GREEN; zero expected failures │
│ Full FG-SA libraries   │ PASS --wfail; all eight libraries/test libraries   │
│ DCK P-As               │ PASS; 62 strict groups, 7096 results, 24 controls  │
│ Canonical coverage     │ PASS; 6028 rows; all 12 audits                     │
│ Canonical exports      │ 860 proof modules; 1033 exports; 0 unaccepted      │
│ Inventory exports      │ 996 roots; 650 proof modules; 253 exports; 0 new   │
│ Other strict audits    │ PASS; FGSafety plus all six local test audits     │
│ Layers                 │ 72 inherited; 0 new                               │
│ Headers / sleep scopes │ PASS                                              │
│ Full manifest          │ BLOCKED: inherited PC-SA restore arity            │
└────────────────────────┴───────────────────────────────────────────────────┘
```

The full manifest passes FG-SA shallow/deep, legacy, V2, Generic and Compose.
Its claims snapshot imports every PC-SA proof module through
scripts/api-snapshot.py:56. There are 48 missing PC-SA import roots. The unchanged
prerequisite build fails at AvailableChainPCSARun/Model/Protocol.lean:449:
`restore d := ⟨initial p.n, d⟩` supplies a Node where Time -> Node is required.
A PC-SA protocol port is required to finish the unchanged script. The later
snapshot controls do not run. Full manifest PASS is not claimed.

Evidence: full-libraries-final.log, assembly-root-pass.log, dck.log,
coverage-pass.log, coverage-owner-changes.log, exports.log, producer-checks.log,
fixture-strict.log, healing-packages-source.log, healing-reset-source.log,
healing-first-source.log, strict-canonical-extra.log, strict-local-audits.log,
layers-final.log, headers-final.log, sleep-scopes.log, source-audit-final.log,
manifest.log, manifest-pcsa-prerequisite.log and manifest-prerequisites.log.
Final counts are in final-counts.log. Earlier diagnostic failures are retained.

The complete eight FG-SA libraries and test libraries pass --wfail:
AvailableChainFGSA, AvailableChainFGSARun, AvailableChainFGSAClaims,
AvailableChainFGSAClaimsTests, AvailableChainFGSAProofs,
AvailableChainFGSAProofsTests, AvailableChainFGSAInhabit and
AvailableChainFGSAInhabitTests. Root and selected time tests also pass --wfail.

An extra check-expose source probe reports six inherited findings in
Healing/RegressionFixture, Healing/SupportFrame, Healing/SupportRecovery and
Outage/ScopedPrefix. These files are byte-identical to the base. The complete
compiled export check has zero unaccepted exports. The source exposure-policy
findings remain with the lead's global G-S2 work; this package changes no closed
Healing declaration or exposure allowance. Evidence: expose.log and inherited-expose.log.

The lead owns global P23, G-S2 and release work. No push, merge, rebase, review,
agent, SSH, admission, new axiom, throttle bypass or lake update is used.
