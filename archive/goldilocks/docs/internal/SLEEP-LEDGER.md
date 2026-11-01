# Sleep premise ledger

Before G-S0, each package records one row per internal theorem that uses a proposed
premise. Use packet row IDs from plan §5.1. At G-S0, change each status to approved
or rework. P-Da keeps this file as a record.

```text
┌──────────────┬──────────────┬─────────────┬────────────────────┐
│ Theorem name │ File         │ Packet rows │ Status             │
├──────────────┼──────────────┼─────────────┼────────────────────┤
└──────────────┴──────────────┴─────────────┴────────────────────┘
```

## W2a — approved packet, 2026-10-10

Approval: `sleep-packet-approved.md`, P1–P24, G-S0 passed.
Each row below is approved. No additional premise or public claim text is proposed.

- `Reachable.restart` — `P24`, approved.
  `AvailableChainFGSA/Statements/Invariants.lean`.
  Repair: old reset → prior reachable wipe.

- `joinedNow; joinedAtTime` — `P24`, approved.
  `AvailableChainFGSA/Model/Store.lean`.
  Repair: inclusive previous slot, integer subtraction.

- `wipe; acRestart; reachable_acRestart` — `P24`, approved.
  `AvailableChainFGSA/Model/Restart.lean`.
  `AvailableChainFGSA/Proofs/Restart.lean`.
  Repair: durable fields kept, HEAD-only replay.

- `gateStep_fresh` — `P24`, approved.
  `AvailableChainFGSA/Proofs/Fields.lean`.
  Repair: add joinedNow at the gate input.

- `clockPre_eq` — `P24`, approved.
  `AvailableChainFGSA/Proofs/ActView.lean`.
  Repair: release gains the tick-time join guard.

- `clock_eq_saClock_offGate` — `P24`, approved.
  `AvailableChainFGSA/Proofs/ActView.lean`.
  Repair: add joinedAtTime at t.

- `clock_eq_saClockFrom_gate; gate'` — `P24`, approved.
  `AvailableChainFGSA/Proofs/ActView.lean`.
  Repair: add joinedAtTime at t.

- `storeInvariant; metadataInvariant` — `P24`, approved.
  `AvailableChainFGSA/Proofs/StoreInv.lean`.
  `AvailableChainFGSA/Proofs/Metadata.lean`.
  Repair: prior invariant supplies retained content.

- `rowsValidStored_reachable; stored_r6wW` — `P24`, approved.
  `AvailableChainFGSA/Proofs/Metadata.lean`.
  `AvailableChainFGSA/WindowAdmissionInvariant.lean`.
  Repair: retained rows keep their validity.

- `outputNesting_stored; base_headDomain_none` — `P24`, approved.
  `AvailableChainFGSA/Proofs/Nesting.lean`.
  `AvailableChainFGSA/Proofs/HeadDomain.lean`.
  Repair: F/S kept; headDomain cleared.

- `storeBundleInvariant` — `P24`, approved.
  `AvailableChainFGSA/Proofs/StoreBundle.lean`.
  Repair: all stored target bounds survive any w.

Constructor record: remove `AvailableChain.FGSA.Reachable.reset`;
add `AvailableChain.FGSA.Reachable.restart`. D0e-a must use the new spelling.
Run callers remain with W2b/W3; other owners are in `scripts/dev-pkg/W2a.txt`.

## W1a — 2026-10-10

Approved source: `sleep-packet-approved.md`, G-S0 approval of P1–P24 on 2026-10-09.
P1 option (a) adds the sleep parent in both engines. No weaker theorem conclusion
or extra theorem premise is proposed. The proof and fixture edits compile with `--wfail`.

P3: packet typo, r9 form `.restart v t`. The lead approved this correction on
2026-10-10. Both World.step branches now bind and pass the restart time.
This fixes an unbound name; it changes no approved meaning.

File keys (all relative to the repository):
- EngineLift: `AvailableChainEngineV2/Engine/Duty/Lift.lean`.
- Lift: `AvailableChainEngineV2/Conditions/Duty/Lift.lean`.
- Self: `AvailableChainEngineV2/Laws/SelfDelivery.lean`.
- DSelf: `AvailableChainEngineV2/Laws/Duty/SelfDelivery.lean`.
- Run/DRun: `AvailableChainEngineV2/Engine/{Run,Duty/Run}.lean`.
- Schedule/DSchedule: `AvailableChainEngineV2/Conditions/{Schedule,Duty/Schedule}.lean`.
- Delivery/DDelivery: `AvailableChainEngineV2/Conditions/{Delivery,Duty/Delivery}.lean`.
- Clock/DClock: `AvailableChainKitV2/{ClockLaws,DutyClockLaws}.lean`.

`approved; built` records text approval and successful compilation.
The writer does not claim that the required external reviews are complete.
The Lift theorem names below have the prefix `AvailableChain.V2.D.`.

```text
┌─────────────────────────────────────────────┬──────────────┬───────────┬─────────────────────┐
│ Declaration                                 │ File         │ Packet    │ Status              │
├─────────────────────────────────────────────┼──────────────┼───────────┼─────────────────────┤
│ sleepWellFormed_toD_iff                     │ Lift         │ P1(a)     │ approved; built     │
│ restartsAtWakes_toD_iff                     │ Lift         │ P1        │ approved; built     │
│ noRestartOn_toD_iff                         │ Lift         │ P1        │ approved; built     │
│ noRestartAfter_toD_iff                      │ Lift         │ P1        │ approved; built     │
│ linkReadyOn_toD_iff                         │ Lift         │ P1, P2    │ approved; built     │
│ processedByActionCut_toD_iff                │ Lift         │ P1, P2    │ approved; built     │
│ handledBetween_toD_iff                      │ Lift         │ P2        │ approved; built     │
│ deliveryService_toD_iff                     │ Lift         │ P2        │ approved; built     │
│ deliveryDemand_toD_iff                      │ Lift         │ P2        │ approved; built     │
│ scheduleWellFormed_toD_iff                  │ Lift         │ P1(a)     │ approved; built     │
│ partialSynchrony_toD_iff                    │ Lift         │ P2        │ approved; built     │
│ healthyPrefixDelivery_toD_iff               │ Lift         │ P2        │ approved; built     │
│ executionValid_toD_iff                      │ Lift         │ P1(a)     │ approved; built     │
│ ExecutionValid.snoc_selfDelivery            │ Self         │ P1(a)     │ approved; built     │
│ ExecutionValid.snoc_selfDelivery            │ DSelf        │ P1(a)     │ approved; built     │
│ ExecutionValid (sleep parent)               │ Schedule     │ P1(a)     │ approved; built     │
│ ExecutionValid (sleep parent)               │ DSchedule    │ P1(a)     │ approved; built     │
│ PartialSynchrony / HealthyPrefixDelivery    │ Delivery     │ P2        │ approved; built     │
│ PartialSynchrony / HealthyPrefixDelivery    │ DDelivery    │ P2        │ approved; built     │
│ World.step restart                          │ Run          │ P3        │ approved; built     │
│ World.step restart                          │ DRun         │ P3        │ approved; built     │
│ RestoreTimeLaw                              │ Clock        │ P3        │ approved; built     │
│ RestoreTimeLaw                              │ DClock       │ P3        │ approved; built     │
│ world_step_toD                              │ EngineLift   │ P3        │ approved; built     │
└─────────────────────────────────────────────┴──────────────┴───────────┴─────────────────────┘
```

Continuation corrections:

```text
┌───────────────────────────────────────────────────────────┬──────────────────────┐
│ Ledger row                                                │ Status               │
├───────────────────────────────────────────────────────────┼──────────────────────┤
│ P3: packet typo, r9 form `.restart v t`                   │ approved; built      │
│ P1: NoRestartOn/After event index annotated `(i : Nat)`   │ same predicate       │
│ P2: negative delivery test horizon set to its deadline, 2 │ fixture only; built  │
└───────────────────────────────────────────────────────────┴──────────────────────┘
```

The P1 annotation resolves an ambiguous List index instance in both twins.
It changes no quantifier domain from the intended event index in r9 and D0a.
The P2 fixture formerly ended at 1. Its deadline 2 is outside that horizon,
so the approved demand has no obligation. The local test now ends at 2.
No approved statement has a weaker conclusion, new premise, or changed quantifier.

Writer validation: DCK PASS (package W1a), with the brief's controls exception.
The normal run passed builds and strict audits, then the old P-PC control map
rejected the five new W1a modules. The NEG=0 run passed in 88.14 s.
Checker scripts are unchanged; the sleep-int controls fix was not merged.
The required Sol and Opus reviews remain with the lead.

## W2a continuation — lead rulings, 2026-10-10

The lead approved the two corrections after merge `02531030`.
`clock_namedBodies` in `AvailableChainFGSA/Proofs/NamedStore.lean`
keeps its type and uses `clock_proposals` from `Proofs/Fields.lean`.
This proof-only edit is approved outside plan §14.2.
Validation uses the default repository heartbeat config.
No source heartbeat limit is increased.

Two modules omitted from plan §14.6 are EXPECTED-FAIL, owner W3:
- `AvailableChainFGSARun.Proofs.AncestorDeadlinesStore`: gate unfolds
  at lines 455, 465 and 485 do not handle the unjoined branch.
- `AvailableChainFGSARun.Proofs.AncestorDeadlines`: imports that failed module.

Both modules stay REQUIRED at S1. The W2a package map now includes
the five new W1a modules from the merged S1 list as GREEN.
`NamedStore` is a W2a TARGET for the approved proof repair.

W1a merge failures are assigned by plan §14.6/§8.1 and the merged W1a map.
The failed modules are:
- `AvailableChainFGCompose.Statements.SafetyClient` — W3.
- `AvailableChainFGCompose.Statements.SafetyStore` — W3.
- `AvailableChainFGCompose.Tests.Restart` — W3.
- `AvailableChainFGSARun.Model.Protocol` — W2b.
- `AvailableChainGeneric.Proofs.V2.Fields` — W1b.
- `AvailableChainGeneric.Statements.V2.Duty.Receipt` — W1b.
- `AvailableChainGeneric.Statements.V2.Receipt` — W1b.
- `AvailableChainKitV2.DutyEngineClock` — W1b.
- `AvailableChainKitV2.DutyRecord` — W1b.
- `AvailableChainKitV2.EngineClock` — W1b.
- `AvailableChainKitV2.Tests.Toy` — W1b.

These 11 failures affect 106 prior GREEN entries through imports.
Additional EXPECTED-FAIL owners: W1b 34, W2b 32, W3 14, P-ShA 13, S-Ap 13.
The final W2a map has 34 TARGETS, 273 GREEN and 176 EXPECTED-FAIL entries.
All 110 W2a store/pin targets stay GREEN. No S1 entry moves to DEFERRED.
The W1b and W3 owners have approved statement repairs in plan r9.
This continuation changes no statement and adds no premise.

Writer checkpoint: DCK PASS (package W2a), with all controls, 109.716 s.
Default-config GREEN build: PASS, 273 module targets, 2.852 s.
Strict FGSA audit: PASS, 822 results, 42.343 s.
Scoped FGSA coverage: PASS, 0 unaccepted exports, 19.902 s.
The coverage inventory is unchanged. Astra review remains with the lead.

## W2b — approved work and stopped items, 2026-10-10

Approval: `sleep-packet-approved.md`, P1–P24; G-S0 passed.
The model text follows the approved `actS` and `fgsa` blocks.
Line breaks in `actS` keep lines at or below 100 characters.
No packet typo was found in these blocks.

- `actS; fgsa` — `P3, P24`, approved.
  `AvailableChainFGSARun/Model/Protocol.lean`.
  Repair: joined HEAD/proposal duties; keep the durable store and Λ.
- `fgsaClock; fgsa_clock_now` — `P3, P24`, approved, types kept.
  `AvailableChainFGSARun/Proofs/Restore.lean`.
  Move from ClockLaws to avoid the stopped Protocol and W1b proof imports.
- `fgsaRestoreTimeLaw; fgsa_restore_now` — `P3, P24`, approved.
  `AvailableChainFGSARun/Proofs/Restore.lean`.
  Repair: the clock equals the exact wake time.
- `restore_st; restore_rec; fgsa_restore_record` — `P3, P24`, approved.
  `AvailableChainFGSARun/Proofs/Restore.lean`.
  `restore_st` replaces `restore_st_retained`; `restore_rec` gains the wake argument.
- `fgsa_restore_restartTime; fgsa_restore_fg; fgsa_restore_rowPool` —
  `P3, P24`, approved, `AvailableChainFGSARun/Proofs/Restore.lean`.
- `fgsa_restore_proposals; fgsa_restore_namedBodies; fgsa_restore_blocks` —
  `P3, P24`, approved, `AvailableChainFGSARun/Proofs/Restore.lean`.
- `fgsa_restore_obligations; fgsa_restore_stableRecord` — `P3, P24`, approved.
  `AvailableChainFGSARun/Proofs/Restore.lean`.
- `fgsa_restore_reachable; fgsa_reachable_stateBefore` — `P3, P24`, approved.
  `AvailableChainFGSARun/Proofs/Restore.lean`.
  Use the pre-restart reachability proof, with no W1b declaration.
- `reachable_stateBefore; namedOrigin_reachable` — `P3, P24`, approved, types kept.
  `AvailableChainFGSARun/Proofs/{Reachable,NamedOrigins}.lean`.
  Both reset sites use the compiled retained-store reachability bridge.
  Their whole modules remain blocked by other statements/imports.
- `fgsa_restore_now_retained; fgsa_hrestore_now_retained` — `P3, P24`, superseded.
  `AvailableChainFGSARun/Proofs/ClockLaws.lean`.
  The new exact-wake laws replace the last-tick laws.
- `fgsa_hrestore_retained; fgsa_hrestore_field_retained` — stopped; ruling required.
  `AvailableChainFGSARun/Proofs/ClockLaws.lean`.
  Reset-to-genesis premises no longer apply. Keep their text pending a ruling;
  the new laws already prove the approved retained-field behavior.
- `stored_proposal_delivered` — stopped; meaning ruling required.
  `AvailableChainFGSARun/Proofs/Reachable.lean`.
  The current-epoch conclusion is false when proposals survive restart.
  Keep its text; do not add a premise or weaken the conclusion without a ruling.
- `act_prop` — stopped; meaning ruling required.
  `AvailableChainFGSARun/Proofs/Protocol.lean`.
  Its unconditional result conflicts with the approved joined `actS`.
  `act_prop_zero` needs a proof repair after this item is released.
- `fgsa_stateBefore_bounds` reset site — stopped; integration ruling required.
  `AvailableChainFGSARun/Proofs/Schedule.lean`.
  Its induction uses the superseded retained-clock helper and resets to genesis.
  The module also imports W1b clock proofs and contains the false strict bound below.
- `fgsa_preTick_now_lt; fgsa_release_votes_stamped` — stopped; meaning ruling required.
  `AvailableChainFGSARun/Proofs/Schedule.lean`.
  A wake at a tick time gives pre-tick now = tick time, and replay stamps can equal it.
  `SleepTests.wake_at_tick` is a valid-run counterexample to the strict clock bound.

The package is not closed. The stopped statements and the Schedule reset site
need a lead ruling and W3 integration. No stopped statement has changed meaning.

- `SleepTests.valid` — `P1, P3, P24`, approved.
  `AvailableChainFGSARun/Tests/Sleep.lean`; full engine validity is proved.

- `SleepTests.non_public_wake` — `P1, P3, P24`, approved.
  `AvailableChainFGSARun/Tests/Sleep.lean`; full engine validity is proved.

- `SleepTests.receipt_before_tick` — `P1, P3, P24`, approved.
  `AvailableChainFGSARun/Tests/Sleep.lean`; full engine validity is proved.

- `SleepTests.durable_run` — `P1, P3, P24`, approved.
  `AvailableChainFGSARun/Tests/Sleep.lean`; full engine validity is proved.

- `SleepTests.retained_not_fresh` — `P1, P3, P24`, approved.
  `AvailableChainFGSARun/Tests/Sleep.lean`; full engine validity is proved.

- `SleepTests.join_valid` — `P1, P3, P24`, approved.
  `AvailableChainFGSARun/Tests/Sleep.lean`; full engine validity is proved.

- `SleepTests.join_duties` — `P1, P3, P24`, approved.
  `AvailableChainFGSARun/Tests/Sleep.lean`; full engine validity is proved.

- `SleepTests.wake_at_tick` — `P1, P3, P24`, approved.
  `AvailableChainFGSARun/Tests/Sleep.lean`; full engine validity is proved.

- `SleepTests.initial_duties` — `P1, P3, P24`, approved.
  `AvailableChainFGSARun/Tests/Sleep.lean`; full engine validity is proved.
## W1b — 2026-10-10

Source: approved P2/P3/P24 packet and r9 §2.2, §4.1. The 15 replacement texts
match the packet exactly. No packet typo correction or meaning change was needed.
The old NoRestart and restartFree forms remain. Their companions state restore
preservation or RestoreTimeLaw. The old delivery lower bound adds receiver awake
at its public anchor, as r9 permits. The new full-sleep bound uses ExecutionValid.
Receipt wrappers now require readiness, history safety, and explicit acceptance.

File keys (paths are relative to this repository):
- B1: `AvailableChainGeneric/Proofs/V2/Duty/DeliveryBy.lean`.
- B2: `AvailableChainGeneric/Proofs/V2/Duty/Fields.lean`.
- B3: `AvailableChainGeneric/Proofs/V2/Duty/Induction.lean`.
- B4: `AvailableChainGeneric/Proofs/V2/Duty/Reads.lean`.
- B5: `AvailableChainGeneric/Proofs/V2/Duty/Receipt.lean`.
- B6: `AvailableChainGeneric/Proofs/V2/Duty/Sleep.lean`.
- B7: `AvailableChainGeneric/Proofs/V2/Fields.lean`.
- B8: `AvailableChainGeneric/Proofs/V2/Induction.lean`.
- B9: `AvailableChainGeneric/Proofs/V2/Reads.lean`.
- B10: `AvailableChainGeneric/Proofs/V2/Receipt.lean`.
- B11: `AvailableChainGeneric/Proofs/V2/Sleep.lean`.
- B12: `AvailableChainGeneric/Statements/V2/Duty/DeliveryBy.lean`.
- B13: `AvailableChainGeneric/Statements/V2/Duty/Receipt.lean`.
- B14: `AvailableChainGeneric/Statements/V2/Receipt.lean`.
- B15: `AvailableChainKitV2/DutyEngineClock.lean`.
- B16: `AvailableChainKitV2/DutyExecution.lean`.
- B17: `AvailableChainKitV2/DutyRecord.lean`.
- B18: `AvailableChainKitV2/DutySleep.lean`.
- B19: `AvailableChainKitV2/DutyStable.lean`.
- B20: `AvailableChainKitV2/Emission.lean`.
- B21: `AvailableChainKitV2/EngineClock.lean`.
- B22: `AvailableChainKitV2/Execution.lean`.
- B23: `AvailableChainKitV2/Sleep.lean`.
- B24: `AvailableChainKitV2/Stable.lean`.

Rows include the changed records, wrappers, and exported proof dependencies.
P1 denotes the adopted full-sleep vocabulary; P3 denotes exact restore time.
Status is statement approval; the final report gives build and audit results.

```text
┌──────────────────────────────────────────────────┬───────┬───────────┬────────────┐
│ Declaration                                      │ File  │ Packet    │ Status     │
├──────────────────────────────────────────────────┼───────┼───────────┼────────────┤
│ deliveryWithinOn_of_partialSynchronyBy_statement │ B1    │ P2, P24   │ approved   │
│ deliveryWithinOn_of_healthyPrefixBy_statement    │ B1    │ P2, P24   │ approved   │
│ accepted_by_deadline_on_statement                │ B1    │ P2, P24   │ approved   │
│ accepted_by_deadline_on                          │ B1    │ P2, P24   │ approved   │
│ ownRecord_fold_restart                           │ B2    │ P3, P24   │ approved   │
│ invariant_triple                                 │ B3    │ P3, P24   │ approved   │
│ invariant_clock_free                             │ B3    │ P3, P24   │ approved   │
│ holdsBefore_iff_exists_idx_restore               │ B4    │ P3, P24   │ approved   │
│ timely_of_relay_statement                        │ B5    │ P3, P24   │ approved   │
│ timely_of_relay                                  │ B5    │ P3, P24   │ approved   │
│ historySafeAt_of_fresh                           │ B5    │ P2, P24   │ approved   │
│ historySafeAt_of_processed_mono                  │ B5    │ P2, P24   │ approved   │
│ processed_by_deadline_of_service                 │ B5    │ P2, P24   │ approved   │
│ service_of_readyTrigger                          │ B5    │ P2, P24   │ approved   │
│ ready_broadcast                                  │ B5    │ P2, P24   │ approved   │
│ ready_relay                                      │ B5    │ P2, P24   │ approved   │
│ accepted_by_deadline_statement                   │ B5    │ P2, P24   │ approved   │
│ accepted_by_deadline                             │ B5    │ P2, P24   │ approved   │
│ restartFree_actionCut_idxBefore                  │ B6    │ P1, P3    │ approved   │
│ actionCut_le_idxBefore                           │ B6    │ P1, P3    │ approved   │
│ ownRecord_fold_restart                           │ B7    │ P3, P24   │ approved   │
│ invariant_triple                                 │ B8    │ P3, P24   │ approved   │
│ invariant_clock_free                             │ B8    │ P3, P24   │ approved   │
│ holdsBefore_iff_exists_idx_restore               │ B9    │ P3, P24   │ approved   │
│ timely_of_relay_statement                        │ B10   │ P3, P24   │ approved   │
│ timely_of_relay                                  │ B10   │ P3, P24   │ approved   │
│ historySafeAt_of_fresh                           │ B10   │ P2, P24   │ approved   │
│ historySafeAt_of_processed_mono                  │ B10   │ P2, P24   │ approved   │
│ processed_by_deadline_of_service                 │ B10   │ P2, P24   │ approved   │
│ service_of_readyTrigger                          │ B10   │ P2, P24   │ approved   │
│ ready_broadcast                                  │ B10   │ P2, P24   │ approved   │
│ ready_relay                                      │ B10   │ P2, P24   │ approved   │
│ accepted_by_deadline_statement                   │ B10   │ P2, P24   │ approved   │
│ accepted_by_deadline                             │ B10   │ P2, P24   │ approved   │
│ restartFree_actionCut_idxBefore                  │ B11   │ P1, P3    │ approved   │
│ actionCut_le_idxBefore                           │ B11   │ P1, P3    │ approved   │
│ PartialSynchronyBy                               │ B12   │ P2, P24   │ approved   │
│ HealthyPrefixDeliveryBy                          │ B12   │ P2, P24   │ approved   │
│ DeliveryWithinOn                                 │ B12   │ P2, P24   │ approved   │
│ AcceptedByDeadlineOnStatement                    │ B12   │ P2, P24   │ approved   │
│ AcceptedByDeadlineOnStatement_def                │ B12   │ P2, P24   │ approved   │
│ DeliveryWithin                                   │ B13   │ P2, P24   │ approved   │
│ ReadyTrigger                                     │ B13   │ P2, P24   │ approved   │
│ HistorySafeAt                                    │ B13   │ P2, P24   │ approved   │
│ ProcessedByDeadlineOfServiceStatement            │ B13   │ P2, P24   │ approved   │
│ TimelyOfRelayStatement                           │ B13   │ P3, P24   │ approved   │
│ TimelyOfRelayStatement_def                       │ B13   │ P3, P24   │ approved   │
│ AcceptedByDeadlineStatement                      │ B13   │ P2, P24   │ approved   │
│ AcceptedByDeadlineStatement_def                  │ B13   │ P2, P24   │ approved   │
│ DeliveryWithin                                   │ B14   │ P2, P24   │ approved   │
│ ReadyTrigger                                     │ B14   │ P2, P24   │ approved   │
│ HistorySafeAt                                    │ B14   │ P2, P24   │ approved   │
│ ProcessedByDeadlineOfServiceStatement            │ B14   │ P2, P24   │ approved   │
│ TimelyOfRelayStatement                           │ B14   │ P3, P24   │ approved   │
│ TimelyOfRelayStatement_def                       │ B14   │ P3, P24   │ approved   │
│ AcceptedByDeadlineStatement                      │ B14   │ P2, P24   │ approved   │
│ AcceptedByDeadlineStatement_def                  │ B14   │ P2, P24   │ approved   │
│ stateBefore_now_source                           │ B15   │ P3, P24   │ approved   │
│ stateBefore_now_le_event                         │ B15   │ P3, P24   │ approved   │
│ stateBefore_now_mono                             │ B15   │ P3, P24   │ approved   │
│ delivery_now_ge_public                           │ B15   │ P3, P24   │ approved   │
│ stateBefore_now_source_atRestart                 │ B15   │ P3, P24   │ approved   │
│ stateBefore_now_le_event_atRestart               │ B15   │ P3, P24   │ approved   │
│ stateBefore_now_mono_atRestart                   │ B15   │ P3, P24   │ approved   │
│ delivery_now_ge_public_atRestart                 │ B15   │ P3, P24   │ approved   │
│ stateBefore_stable_clock_atRestart               │ B15   │ P3, P24   │ approved   │
│ stateBefore_invariant_atRestart                  │ B15   │ P3, P24   │ approved   │
│ stateBefore_invariant                            │ B15   │ P3, P24   │ approved   │
│ stateBefore_stable_clock                         │ B15   │ P3, P24   │ approved   │
│ stateBefore_stable_clock_restore                 │ B15   │ P3, P24   │ approved   │
│ clock_field_origin                               │ B15   │ P3, P24   │ approved   │
│ clock_field_origin_of_subset                     │ B15   │ P3, P24   │ approved   │
│ stateBefore_field_prefix_restore                 │ B15   │ P3, P24   │ approved   │
│ stateBefore_tick_eq_stateBeforeTime              │ B16   │ P1, P3    │ approved   │
│ index_lt_actionCut_iff                           │ B16   │ P1, P3    │ approved   │
│ stateBefore_tick_eq_stateAfterRestartsAt         │ B16   │ P1, P3    │ approved   │
│ ownRecord_fold_interval_restart                  │ B17   │ P3, P24   │ approved   │
│ ownRecord_fold_restore                           │ B17   │ P3, P24   │ approved   │
│ restart_index_lt_event                           │ B18   │ P1, P3    │ approved   │
│ wake_restart_before_event                        │ B18   │ P1, P3    │ approved   │
│ state_after_restart                              │ B18   │ P1, P3    │ approved   │
│ asleep_state_frozen                              │ B18   │ P1, P3    │ approved   │
│ noRestartOn_of_awakeOn                           │ B18   │ P1, P3    │ approved   │
│ noRestartAfter_of_awakeOnClosed                  │ B18   │ P1, P3    │ approved   │
│ wake_between                                     │ B18   │ P1, P3    │ approved   │
│ stateBefore_stable_restore                       │ B19   │ P3, P24   │ approved   │
│ ownRecord_fold_interval_restart                  │ B20   │ P3, P24   │ approved   │
│ ownRecord_fold_restore                           │ B20   │ P3, P24   │ approved   │
│ stateBefore_now_source                           │ B21   │ P3, P24   │ approved   │
│ stateBefore_now_le_event                         │ B21   │ P3, P24   │ approved   │
│ stateBefore_now_mono                             │ B21   │ P3, P24   │ approved   │
│ delivery_now_ge_public                           │ B21   │ P3, P24   │ approved   │
│ stateBefore_now_source_atRestart                 │ B21   │ P3, P24   │ approved   │
│ stateBefore_now_le_event_atRestart               │ B21   │ P3, P24   │ approved   │
│ stateBefore_now_mono_atRestart                   │ B21   │ P3, P24   │ approved   │
│ delivery_now_ge_public_atRestart                 │ B21   │ P3, P24   │ approved   │
│ stateBefore_stable_clock_atRestart               │ B21   │ P3, P24   │ approved   │
│ stateBefore_invariant_atRestart                  │ B21   │ P3, P24   │ approved   │
│ stateBefore_invariant                            │ B21   │ P3, P24   │ approved   │
│ stateBefore_stable_clock                         │ B21   │ P3, P24   │ approved   │
│ stateBefore_stable_clock_restore                 │ B21   │ P3, P24   │ approved   │
│ clock_field_origin                               │ B21   │ P3, P24   │ approved   │
│ clock_field_origin_of_subset                     │ B21   │ P3, P24   │ approved   │
│ stateBefore_field_prefix_restore                 │ B21   │ P3, P24   │ approved   │
│ stateBefore_tick_eq_stateBeforeTime              │ B22   │ P1, P3    │ approved   │
│ index_lt_actionCut_iff                           │ B22   │ P1, P3    │ approved   │
│ stateBefore_tick_eq_stateAfterRestartsAt         │ B22   │ P1, P3    │ approved   │
│ restart_index_lt_event                           │ B23   │ P1, P3    │ approved   │
│ wake_restart_before_event                        │ B23   │ P1, P3    │ approved   │
│ state_after_restart                              │ B23   │ P1, P3    │ approved   │
│ asleep_state_frozen                              │ B23   │ P1, P3    │ approved   │
│ noRestartOn_of_awakeOn                           │ B23   │ P1, P3    │ approved   │
│ noRestartAfter_of_awakeOnClosed                  │ B23   │ P1, P3    │ approved   │
│ wake_between                                     │ B23   │ P1, P3    │ approved   │
│ stateBefore_stable_restore                       │ B24   │ P3, P24   │ approved   │
└──────────────────────────────────────────────────┴───────┴───────────┴────────────┘
```

`PCCompanion.lean` keeps NoRestart and its field text. Its execution, healthy,
and partialSynchrony dependencies have the new engine meaning. P-Da must include
this dependency change in the SLEEP-1 manifest. The 24 delivery producers keep
their outer signatures and now carry DeliveryDemand. No producer proves receipt.

Writer checks: both libraries and all tests pass `lake build --wfail`.
DCK PASS (package W1b), with all controls enabled. Strict audits pass for all
114 KitV2 and 852 Generic commands. Scoped Generic coverage passes, with zero
unaccepted equation exports. External review and integration are lead-owned.


### W1b fix — P2 pending objects and P3 companion laws (2026-10-10)

P2 text is unchanged. The lead ruling of 2026-10-10 selects a volatile pending
set: a node keeps an object refused for missing dependencies and retries it when
it processes a new object. A restart clears the pending set. Pending traffic after
a wake is covered by delivery counted from max(send, wake). Lean represents a
retry as another handler delivery; the per-anchor DeliveryDemand is this rule's
formal form. FG-SA pin v7 will state the pending set after the sleep migration.

The AcceptanceLaw-derived form is stated once in
`Gen.V2.Duty.AcceptanceLaw.processed_of_not_excluded`: a handled, well-formed
object with dependencies present, an invariant state, and timeliness is processed
if the resulting state does not exclude it. ExecutionValid alone does not supply
Inv or Timely, or the target checks for an object handled through another object.
Protocol owners must supply these inputs at each relevant handler. The companion
`processed_or_retried_of_service` states the current-state-or-retry form using
HistorySafeAt. Without safe history, old processing can meet demand even after
restore erased it. No re-delivery of such an erased receipt follows.

Owners: FG-SA W3/P-ShA prove the relevant acceptance, dependency, invariant,
timeliness, and history obligations. GridCO's protocol owner owns its instance;
GridCO is STABLE in r9 and has no W1b code change. Missing-parent refusal without
exclusion requires a pending retry once dependencies become present. The law does
not assert unconditional acceptance for such a refusal.

P3: both receipt twins add `timely_of_relay_public_actTime`, with public action
times and RestoreTimeLaw and no wake premise. Approved TimelyOfRelay text stays.
W2b/W3 must not use hwake for FG-SA. They must repair timely_of_relay_retained under
RestoreTimeLaw and prove public admission times (multiples of 4Δ, with the required
parameter alignment). Both KitV2 twins add `stateBefore_stable_clock_restartFree`:
Q need not survive restore when its index interval has no restart.

Owner notes from Opus 6–7: P-ShA must use fresh post-join vote anchors or prove
that each relevant receipt survives to the action cut. HEAD votes erased by sleep
cannot supply HistorySafeAt. W3 owns the Receipts clock call repair; W2b supplies
the clock foundation. P-H owns DescentTiming's call. Each must supply awake or use
delivery_now_ge_public_atRestart with full ExecutionValid.

The W1b package map now assigns the ready ReceiptCoverage core, Receipts,
SelfDelivery, AC, AncestorDeadlines, AncestorDeadlinesStore, Protocol, Schedule,
Statements.Receipts, and the final FGSARun audit repair to W3. The public
Statements.ReceiptCoverage text belongs to S-Ap. Map comments record shared work
with W2b; no downstream module is changed here.

Fix validation: the 290-module GREEN build passes --wfail (61.40 s). Scoped
Generic coverage passes (4.75 s). DCK W1b passes with all 24 controls (394.69 s).
Strict audits pass: Generic root 856, KitV2 root 116, DeliveryBy tests 53, and
KitV2 sleep tests 3. All results use only the three permitted axioms.

## W2b continuation — lead rulings applied, 2026-10-10

The earlier stopped rows are history. The 01:22 W2b ruling releases all five stops.
The 01:08 W1b ruling supplies pending-set service and public admission-time timeliness.
All three reset modules are now GREEN. W3 and the family owners keep their integration work.

- `stored_proposal_delivered` — internal statement, lead ruling 10-10.
  Delivery is at an earlier index in any epoch. The exact wire stays in durable storage at each
  index from j+1 through i. All consumers retain the delivery, wire and payload facts. The
  Schedule consumer now carries the storage interval instead of restartFree; every other existing
  consumer discards that final field.
  Consumers (proof calls; strict audits also cover each replacement):
  `AvailableChainFGSAProofs/Proofs/Finality/Receipt.lean:50`;
  `AvailableChainFGSAProofs/Proofs/Foundations/Accountable.lean:531`;
  `AvailableChainFGSAProofs/Proofs/Foundations/Carrier.lean:39`;
  `AvailableChainFGSAProofs/Proofs/Foundations/Sources.lean:252`;
  `AvailableChainFGSAProofs/Proofs/Shared/ScoreRun.lean:105`;
  `AvailableChainFGSAProofs/Proofs/Shared/ScoreRun.lean:218`;
  `AvailableChainFGSARun/Proofs/NamedDelivery.lean:50`;
  `AvailableChainFGSARun/Proofs/NamedDelivery.lean:63`;
  `AvailableChainFGSARun/Proofs/Roots.lean:107`;
  `AvailableChainFGSARun/Proofs/Schedule.lean:1008`;
- `act_prop` — internal statement, lead ruling 10-10.
  The equation has exactly the joinedNow guard from approved actS. Its direct proof consumer is
  act_prop_zero. NamedOrigins uses the same guard when it reads successful HEAD and proposal
  emissions.
  Consumers (proof calls; strict audits also cover each replacement):
  `AvailableChainFGSARun/Proofs/Protocol.lean:154`;
- `act_prop_zero` — internal statement, lead ruling 10-10.
  The conclusion is kept: slot zero gives none in both joined branches. The proof uses act_prop
  and the slot-zero proposal rule.
  Consumers (proof calls; strict audits also cover each replacement):
  no existing runtime caller; Tests/Axioms and SleepContinuationAxioms.
- `fgsa_hrestore_retained` — internal statement, lead ruling 10-10.
  A predicate must be preserved by acRestart of its retained input. A pre-state proof then gives
  the post-restore proof at the supplied wake. There is no runtime consumer beyond the audits.
  Consumers (proof calls; strict audits also cover each replacement):
  no existing runtime caller; Tests/Axioms and SleepContinuationAxioms.
- `fgsa_hrestore_field_retained` — internal statement, lead ruling 10-10.
  Restore introduces no member into a list field that acRestart keeps or clears. Schedule supplies
  acRestart_genuine and nil_subset. Family obligations use acRestart_obligations; saved-pair
  fields use acRestart_genuine; fast-pair fields use acRestart_fastWrite. Each gives the exact
  subset law needed by the clock-field origin consumer.
  Consumers (proof calls; strict audits also cover each replacement):
  `AvailableChainFGSAProofs/Proofs/Assembly/WeakContinuation.lean:237`;
  `AvailableChainFGSAProofs/Proofs/Foundations/Leases.lean:323`;
  `AvailableChainFGSAProofs/Proofs/Foundations/Leases.lean:494`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepFacts.lean:199`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:379`;
  `AvailableChainFGSARun/Proofs/Schedule.lean:222`;
- `fgsa_preTick_now_lt` — internal statement, lead ruling 10-10.
  The strict bound uses the exact epoch condition: every earlier local restart is strictly before
  this tick. fgsa_preTick_now_lt_iff proves necessity and sufficiency. fgsa_preTick_now_lt_joined
  supplies the strict bound directly for joined reads. fgsa_preTick_now_le covers a wake at the
  tick. The strict conclusions needed by consumers are kept. Family owners must use the joined
  bridge or prove the epoch condition; the .le use in Healing/PostResetRaw:901 can use the
  unconditional companion.
  Consumers (proof calls; strict audits also cover each replacement):
  `AvailableChainFGSAProofs/Proofs/Clean/StepGate.lean:511`;
  `AvailableChainFGSAProofs/Proofs/Healing/DescentLossNext.lean:289`;
  `AvailableChainFGSAProofs/Proofs/Healing/DescentLossUnanimous.lean:158`;
  `AvailableChainFGSAProofs/Proofs/Healing/FrontierSupportHeads.lean:153`;
  `AvailableChainFGSAProofs/Proofs/Healing/FrontierSupportProposal.lean:98`;
  `AvailableChainFGSAProofs/Proofs/Healing/OpeningServiceGate.lean:152`;
  `AvailableChainFGSAProofs/Proofs/Healing/PostResetConeReceipts.lean:125`;
  `AvailableChainFGSAProofs/Proofs/Healing/PostResetConeReceipts.lean:286`;
  `AvailableChainFGSAProofs/Proofs/Healing/PostResetRaw.lean:901`;
  `AvailableChainFGSAProofs/Proofs/Healing/PostResetRaw.lean:1383`;
  `AvailableChainFGSAProofs/Proofs/Healing/RepairGate.lean:504`;
  `AvailableChainFGSAProofs/Proofs/Healing/SupportHeads.lean:216`;
  `AvailableChainFGSAProofs/Proofs/Healing/SupportOutput.lean:198`;
  `AvailableChainFGSAProofs/Proofs/Healing/SupportProposal.lean:149`;
  `AvailableChainFGSAProofs/Proofs/Healing/SupportRelay.lean:92`;
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:283`;
  `AvailableChainFGSAProofs/Proofs/Shared/GateReceipt.lean:131`;
  `AvailableChainFGSAProofs/Proofs/Shared/Relay.lean:144`;
  `AvailableChainFGSAProofs/Proofs/Shared/Relay.lean:576`;
  `AvailableChainFGSAProofs/Proofs/Shared/RetainedEndpoint.lean:26`;
  `AvailableChainFGSAProofs/Proofs/Shared/RetainedReflect.lean:328`;
  `AvailableChainFGSAProofs/Proofs/Shared/SameLabel.lean:206`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Inclusion.lean:206`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:297`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:493`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepGateBatch.lean:242`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:1425`;
  `AvailableChainFGSARun/Proofs/Schedule.lean:544`;
  `AvailableChainFGSARun/Proofs/Schedule.lean:568`;
  `AvailableChainFGSARun/Proofs/Schedule.lean:610`;
  `AvailableChainFGSARun/Proofs/Schedule.lean:778`;
- `fgsa_release_votes_stamped` — internal statement, lead ruling 10-10.
  All vote stamps, including the default stamp, are strictly before release under the exact pre-
  tick epoch condition. The active-view projection equalities are kept. A same-time wake permits
  equality, covered by fgsa_preTick_votes_stamped_le. There is no runtime caller of this export
  beyond the audits.
  Consumers (proof calls; strict audits also cover each replacement):
  no existing runtime caller; Tests/Axioms and SleepContinuationAxioms.
- `fgsa_stateBefore_bounds` — internal statement, lead ruling 10-10.
  The statement is kept. Its reset case starts from the prior reachable store, applies
  Reachable.restart to wipe, and proves replay reachability and bounds. The wake clock is at least
  the old clock by RestoreTimeLaw and event order. Kept blocks remain within the wake slot;
  accepted replay stamps are within the wake clock. All block-slot and stamp projections used by
  consumers are kept.
  Consumers (proof calls; strict audits also cover each replacement):
  `AvailableChainFGSAProofs/Proofs/Clean/StepGate.lean:647`;
  `AvailableChainFGSAProofs/Proofs/Healing/DescentLossNext.lean:285`;
  `AvailableChainFGSAProofs/Proofs/Healing/DescentLossUnanimous.lean:154`;
  `AvailableChainFGSAProofs/Proofs/Healing/FrameZero.lean:106`;
  `AvailableChainFGSAProofs/Proofs/Healing/FrontierSupportHeads.lean:149`;
  `AvailableChainFGSAProofs/Proofs/Healing/FrontierSupportProposal.lean:94`;
  `AvailableChainFGSAProofs/Proofs/Healing/OpeningServiceGate.lean:146`;
  `AvailableChainFGSAProofs/Proofs/Healing/PostResetConeReceipts.lean:121`;
  `AvailableChainFGSAProofs/Proofs/Healing/PostResetConeReceipts.lean:282`;
  `AvailableChainFGSAProofs/Proofs/Healing/PostResetRaw.lean:1379`;
  `AvailableChainFGSAProofs/Proofs/Healing/RepairGate.lean:498`;
  `AvailableChainFGSAProofs/Proofs/Healing/SupportHeads.lean:212`;
  `AvailableChainFGSAProofs/Proofs/Healing/SupportProposal.lean:145`;
  `AvailableChainFGSAProofs/Proofs/Healing/SupportRelay.lean:93`;
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:556`;
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:724`;
  `AvailableChainFGSAProofs/Proofs/Shared/GateReceipt.lean:363`;
  `AvailableChainFGSAProofs/Proofs/Shared/HeadAdmit.lean:214`;
  `AvailableChainFGSAProofs/Proofs/Shared/OutputGrowthCausal.lean:47`;
  `AvailableChainFGSAProofs/Proofs/Shared/Relay.lean:145`;
  `AvailableChainFGSAProofs/Proofs/Shared/Relay.lean:577`;
  `AvailableChainFGSAProofs/Proofs/Shared/RetainedEndpoint.lean:35`;
  `AvailableChainFGSAProofs/Proofs/Shared/RetainedReflect.lean:337`;
  `AvailableChainFGSAProofs/Proofs/Shared/SameLabel.lean:207`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepGateBatch.lean:379`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:1564`;
  `AvailableChainFGSARun/Proofs/Schedule.lean:586`;
  `AvailableChainFGSARun/Proofs/Schedule.lean:613`;
  `AvailableChainFGSARun/Proofs/Schedule.lean:783`;
  `AvailableChainFGSARun/Proofs/Schedule.lean:843`;
- `fgsa_stored_block_origin` — internal statement, lead ruling 10-10.
  The origin is in any earlier epoch, with the exact wire retained from j+1 through i. The stored-
  wire, block and delivery projections are kept. Every existing external consumer discards the
  former restartFree field.
  Consumers (proof calls; strict audits also cover each replacement):
  `AvailableChainFGSAProofs/Proofs/Finality/MiddleSupport.lean:757`;
  `AvailableChainFGSAProofs/Proofs/Healing/Promotion.lean:35`;
  `AvailableChainFGSAProofs/Proofs/Shared/RetainedEndpoint.lean:47`;
  `AvailableChainFGSAProofs/Proofs/Shared/ScoreRun.lean:897`;
  `AvailableChainFGSAProofs/Proofs/Shared/ScoreRun.lean:1127`;
- `fgsa_tick_total` — internal statement, lead ruling 10-10.
  Tick existence is conditional on the honest node being awake at the public time, exactly as P1
  and ScheduleWellFormed.tick_total require. The unique-index conclusion is kept. The review
  handoff below identifies each exact awake source and each missing consumer premise.
  Consumers (proof calls; strict audits also cover each replacement):
  `AvailableChainFGSAProofs/Proofs/Assembly/WeakContinuation.lean:538`;
  `AvailableChainFGSAProofs/Proofs/Assembly/WeakContinuationGrowth.lean:377`;
  `AvailableChainFGSAProofs/Proofs/Assembly/WeakContinuationGrowth.lean:572`;
  `AvailableChainFGSAProofs/Proofs/Assembly/WeakContinuationGrowthSeed.lean:195`;
  `AvailableChainFGSAProofs/Proofs/Clean/Closure.lean:200`;
  `AvailableChainFGSAProofs/Proofs/Clean/Closure.lean:298`;
  `AvailableChainFGSAProofs/Proofs/Clean/Safety.lean:197`;
  `AvailableChainFGSAProofs/Proofs/Clean/StepGate.lean:212`;
  `AvailableChainFGSAProofs/Proofs/Clean/StepGate.lean:257`;
  `AvailableChainFGSAProofs/Proofs/Clean/StepGate.lean:447`;
  `AvailableChainFGSAProofs/Proofs/Clean/StepGate.lean:566`;
  `AvailableChainFGSAProofs/Proofs/Clean/StepGate.lean:569`;
  `AvailableChainFGSAProofs/Proofs/Finality/RowsPrem.lean:91`;
  `AvailableChainFGSAProofs/Proofs/Finality/TailFrame.lean:383`;
  `AvailableChainFGSAProofs/Proofs/Healing/FrontierSearchTasks.lean:211`;
  `AvailableChainFGSAProofs/Proofs/Healing/OpeningServiceBody.lean:197`;
  `AvailableChainFGSAProofs/Proofs/Healing/OpeningServiceOne.lean:29`;
  `AvailableChainFGSAProofs/Proofs/Healing/PostResetGate.lean:265`;
  `AvailableChainFGSAProofs/Proofs/Healing/PostResetOpening.lean:163`;
  `AvailableChainFGSAProofs/Proofs/Healing/PostResetRaw.lean:592`;
  `AvailableChainFGSAProofs/Proofs/Healing/PostResetRaw.lean:811`;
  `AvailableChainFGSAProofs/Proofs/Healing/PostResetService.lean:235`;
  `AvailableChainFGSAProofs/Proofs/Healing/SupportHeads.lean:110`;
  `AvailableChainFGSAProofs/Proofs/Healing/SupportOutput.lean:261`;
  `AvailableChainFGSAProofs/Proofs/Outage/ArmingBatch.lean:63`;
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:462`;
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:465`;
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:626`;
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:629`;
  `AvailableChainFGSAProofs/Proofs/Outage/ContinuationReceipt.lean:820`;
  `AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:299`;
  `AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:513`;
  `AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:519`;
  `AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:581`;
  `AvailableChainFGSAProofs/Proofs/Outage/ExactProposalRetained.lean:726`;
  `AvailableChainFGSAProofs/Proofs/Outage/InclusionGate.lean:55`;
  `AvailableChainFGSAProofs/Proofs/Outage/InclusionGate.lean:119`;
  `AvailableChainFGSAProofs/Proofs/Outage/InclusionGateBody.lean:55`;
  `AvailableChainFGSAProofs/Proofs/Shared/ExactHead.lean:193`;
  `AvailableChainFGSAProofs/Proofs/Shared/ExactService.lean:462`;
  `AvailableChainFGSAProofs/Proofs/Shared/GateReceipt.lean:269`;
  `AvailableChainFGSAProofs/Proofs/Shared/GateReceipt.lean:272`;
  `AvailableChainFGSAProofs/Proofs/Shared/HeadAdmit.lean:387`;
  `AvailableChainFGSAProofs/Proofs/Shared/OutputGrowthProposal.lean:32`;
  `AvailableChainFGSAProofs/Proofs/Shared/RetainedEndpoint.lean:293`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/ExactProposal.lean:214`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Inclusion.lean:78`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Inclusion.lean:332`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:203`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/Proposal.lean:750`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepGateBatch.lean:305`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepGateBatch.lean:308`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepInputs.lean:155`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepService.lean:201`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:44`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:811`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:1015`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:1488`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:1491`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:3074`;
- `fgsa_gate_clock_bridge` — internal statement, lead ruling 10-10.
  The anchored SA clock equation holds on the joined branch. The existing block, headDomain and
  fastWrite expressions are kept. Family consumers of fastWrite must supply joinedness.
  Consumers (proof calls; strict audits also cover each replacement):
  `AvailableChainFGSAProofs/Proofs/Healing/SupportWrite.lean:75`;
  `AvailableChainFGSAProofs/Proofs/Shared/ExactService.lean:218`;
  `AvailableChainFGSAProofs/Proofs/Shared/OpeningSource.lean:49`;
- `fgsa_release_clockPre` — internal statement, lead ruling 10-10.
  The release equation is conditional on the approved joined release guard. The active input and
  release body are unchanged. SupportTransfer.release_rows has no source for that join test;
  its arbitrary-store type needs the conditional repair in the review handoff below.
  Consumers (proof calls; strict audits also cover each replacement):
  `AvailableChainFGSAProofs/Proofs/Healing/DescentLossUnanimous.lean:291`;
  `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:72`;
  `AvailableChainFGSAProofs/Proofs/Healing/SupportTransfer.lean:306`;
- `fgsa_release_input_votes_stamped` — internal statement, lead ruling 10-10.
  The input view keeps the same votes and stamps. The exact epoch condition gives each accepted
  input vote its required strict release stamp. Its sole proof consumer, release_count_bridge,
  passes that condition.
  Consumers (proof calls; strict audits also cover each replacement):
  `AvailableChainFGSARun/Proofs/Schedule.lean:888`;
- `fgsa_release_count_bridge` — internal statement, lead ruling 10-10.
  The raw-pool and cutoff-pool equality and all count expressions are kept under the exact epoch
  condition. There is no runtime consumer beyond the audits.
  Consumers (proof calls; strict audits also cover each replacement):
  no existing runtime caller; Tests/Axioms and SleepContinuationAxioms.
- `fgsa_gate_saved_result` — internal statement, lead ruling 10-10.
  The genuine confirmation equation applies on the joined branch. fgsa_gate_saved_unjoined
  supplies the exact other branch: some none. Both use the fresh-gate proof and retain the same
  pre-gate active view. Family owners supply the approved gate join condition.
  Consumers (proof calls; strict audits also cover each replacement):
  `AvailableChainFGSAProofs/Proofs/Clean/StateGate.lean:32`;
  `AvailableChainFGSAProofs/Proofs/Shared/Reads.lean:161`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepGateHistory.lean:139`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepOutput.lean:29`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepService.lean:30`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransfer.lean:91`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuation/StepTransferReceipts.lean:415`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:639`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:1877`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:2153`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:2965`;
  `AvailableChainFGSAProofs/Proofs/WeakContinuationGrowth/Dynamics.lean:3121`;
- `timely_of_relay_retained` — internal statement, lead ruling 10-10.
  Relay timeliness now uses RestoreTimeLaw and public actTime through the additive W1b companion.
  No public-wake premise is used. fgsa_admissionTime_public proves every FG-SA admission threshold
  is a public multiple of 4Δ when E.Δ=p.Δ. Receipts:883,985 are W3 call repairs: supply that law
  and fgsaRestoreTimeLaw with the TimelyClock projection.
  Consumers (proof calls; strict audits also cover each replacement):
  `AvailableChainFGSARun/Proofs/Receipts.lean:883`;
  `AvailableChainFGSARun/Proofs/Receipts.lean:985`;

The public companions are in Schedule and RetainedClock. SleepContinuationAxioms has one
#print axioms for each new or replaced public proof (25 total). SleepContinuation has seven
valid-run regressions, each with its own #print axioms. No heartbeat option is changed.

NamedOrigins now contains its reset and successful-emission proofs. The two unchanged
trigger-scope helpers move to NamedDelivery, already EXPECTED-FAIL under W3. Their old
handler-only proof does not consume P2's ProcessedByActionCut-or-HandledBetween service.
W3 must repair both those consumers and their exact body-scope preconditions. Their types
are kept; no call or source obligation is removed. The REQUIRED scope is kept.

The obsolete local retained-clock source, bound and invariant helpers are removed from
RetainedClock. W3/Receipts and P-ShA/OutputGrowthCausal must use the shared exact-wake
stateBefore_now_source_atRestart, stateBefore_now_le_event_atRestart and step induction.
The run expected list includes every new public companion and test. The W2b map includes
the five added W1b sleep modules, both new tests, and all three reset sites as GREEN.

- New companions — P1, P3, P24, approved; exact forms of the 10-10 rulings.
  `fgsa_preTick_now_le`, `fgsa_preTick_restartTime_at_wake`,
  `fgsa_preTick_now_lt_joined`, `fgsa_preTick_now_lt_iff`,
  `fgsa_preTick_votes_stamped_le`, `fgsa_gate_saved_unjoined`,
  `fgsa_admissionTime_public`.
  Consumers: SleepContinuation; strict audits; the W3 and family calls listed above.
- `SleepContinuationTests.retained_origin`, `joined_strict`, `same_time_bound`,
  `retained_block_bound`, `wake_epoch_equiv`, `gate_empty`, `admission_public` —
  P1, P3, P24, approved. Consumers: strict audit and W2b GREEN/DCK acceptance.

## W3 — Compose restart laws (2026-10-10)

- P3/P24 approved field types: FGSafetyStoreLaws.restart_good takes the wake time.
  restart_tf now maps membership to the pre-restart TF. SafetyStore induction keeps
  the prior delivery origin. Consumers: safety_good_stateBefore and safety_stateBefore_origin.
- P3/P24 approved field type: FGSafetyClientLaws.restart_record takes the wake time.
  Consumer: safety_client_trace. The lossy and kept record controls take that time.
- P24 approved new record: FGSafetyRestartLaws and its restart_F field. It adds no
  field to FGSafetyStoreLaws. The inventory and SafetyAxioms audit include both names.
- N2 additive theorem: safety_F_mono_all uses restart_F and permits restarts.
  The old NoRestart theorem stays. The new theorem has a SafetyAxioms audit entry.
- Compose and Claims read fixtures now use the time-indexed restore arity.

## W3 — Internal statement repairs in progress (2026-10-10)

- internal statement, W3: ancestorDeadlines_restore used the old Time × RecordOnce
  durable type and concluded that obligations were empty. It now uses State ×
  RecordOnce, the wake time, and AncestorDeadlines of the pre-restart store.
  acRestart_obligations supplies the exact preserved result. Consumers:
  FGSAProofs/Proofs/Foundations/Leases.lean and FGSARun/Tests/Axioms.lean.
- internal statement, W3: fgsa_emits_head and fgsa_emits_proposal omitted the join
  guard of actS. The exact emission equations now include joinedNow of the clocked
  store. Run consumers: EmissionWellFormed, Receipts, and Roots. Family consumers:
  Shared/ExactService, HeadAdmit, OutputGrowthProposal, RetainedPersist,
  RetainedConsumers, Count, ScoreRun; Clean/StepGate; Finality/CoreServices;
  Outage/ExactProposal, ArmingDuty, PersistenceRelease, ContinuationReceipt;
  WeakContinuation/Proposal, StepGateBatch; WeakContinuationGrowth/Dynamics.
  Family owners must supply the joined premise only when they construct emissions.
- internal statement, W3: spec_restart_durable_retained and
  spec_restart_clock_retained asserted the old last-tick restore clock. They now
  use the complete durable store and the exact wake time. Consumers: run axiom audit.
- internal statement, W3: spec_prune_execution_valid and
  spec_revised_target_execution omitted SleepWellFormed. They now require that
  condition and preserve it through delivery pruning. Consumers: the latter uses
  the former; the run axiom audit uses both. No external proof consumer was found.
- internal statement, W3: spec_restart_retained_block_trace used now = 8 after
  the restart at 9. Its exact clock equation is now = 9. Consumer:
  Spec/Transfer.spec_restart_matched_cut_agreement discards that clock field.

## W3 — Sources, join bridges and provenance (2026-10-10)

- N11: fgsa_fgAction_unjoined_source_none uses saved-label provenance, tick
  uniqueness, and CStoreInv.fastDom. These give label freshness without a separate
  latest-wake search. A fresh unjoined gate writes an empty fast set for rR.
- N7: fgsa_joinedNow_of_joinedEnv uses the explicit restart clause in the approved
  joinedAt text. fgsa_joinedNow_of_caughtUp uses its marker and gate-time clauses.
  S-Ap can apply these without importing the future Claims/Statements/Join module
  into Run. The awake-closed companion also requires RestartsAtWakes.
- internal statement, W3: rowPool_provenance formerly concluded restartFree after
  its handler. That is false when a durable row crosses a restart. The exact new
  form keeps the handler origin and states row membership at every later index
  through the read. Consumers: SelfDelivery.fgsa_emitted_row_fresh;
  Foundations/Accountable; NonVacuity/HealingPackages. All discard the last field.
  The proof and its store helpers move to Run/Proofs/RowHistory.lean.
- N10 row core: fgsa_emitted_row_no_prior_processed covers every receiver and every
  index at or before the emitting tick. Retained row origin, unforgeable signatures,
  and durable send-once exclude an earlier occurrence.
- STOP N10 proposal form under ExecutionValid alone: a constant digest is permitted
  by Params. A valid run holds a slot-1 proposal of root 2 before the honest slot-2
  proposal of root 2 is emitted. processedS tests only that root and returns true.
  Evidence: Tests/EmissionFreshness.emitted_proposal_already_processed and its
  full ExecutionValid proof. A true freshness form needs an additional root/scope
  condition. Do not change an approved public statement to add it without a ruling.

## W3 — Approved-core STOP and exact AC forms (2026-10-10)

- STOP P23 fgsa_receiptCoverage_ready: receiver readiness does not fix the root-only
  processing exemption. Tests/ReceiptAlias proves DeliveryWithinOn, every unchanged
  ReceiptCoveragePremises field, full receiver readiness, ExecutionValid,
  NamedRootCollisionFree, and NoRestart on a concrete trace. The new required body
  is not stored at its deadline. The legacy coverage conclusion is false on that
  same ready trace. The proposed ready core has exactly that conclusion, so it is
  false too. This needs a lead decision about the approved public boundary. No
  premise, conclusion, quantifier, public protocol function, or statement was changed.
- The N10 proposal counterexample also satisfies NamedRootCollisionFree. Its scope
  contains genesis and the delivered slot-1 body; it does not contain the emitted
  slot-2 body. Changing named scope to include that emission changes public meaning.
- The handler-only NamedDelivery trigger helpers depend on the same missing exact
  body scope. Their old statement cannot be repaired from current P2 history alone.
  Keep them as a visible stopped item. Unrelated, true named-origin proofs move
  unchanged to Run/Proofs/NamedHistory. Roots and the safety adapter use that module.
- internal statement, W3: fgsaAC_gate_write now takes joinedNow on clockPre. The old
  unguarded gate equation is false for unjoined gates. Other-label preservation
  uses gateStep_other. Consumers: AC slot reads; Shared/Gate; Clean/StateGate,
  GateOutput; Healing/PostResetHealed, RepairGate, SupportOutput;
  Outage/InclusionGateBounds; WeakContinuation/Inclusion, StepOutput, StepService;
  WeakContinuationGrowth/Dynamics. Family owners use N7 at the read that they need.
- internal statement, W3: fgsaAC_laws and fgsaAC_slot_gate_reads now take the join
  clause at every gate in their returned aggregate. This is required by the
  unchanged Generic ACLaws record. No proof consumer outside AC was found; the
  audit commands keep their names. The old unconditional aggregate is false.
- fgsaAC_output_step keeps its statement. Restart uses the preserved-output branch.
- Shared/FGCompose now imports the needed Claims definitions directly and proves
  its source selector equation locally. It does not import the later Shared
  channel producers. Shared safety laws and their early audit now compile.

## W3 — Final internal receipt and append forms (2026-10-10)

- internal statement, W3: fgsa_vote_stamp_source and fgsa_block_stamp_source formerly
  asserted only a network origin through restart. Their network-only forms now
  take NoRestart. The exact general suppliers are fgsa_vote_stamp_source_or_restart
  and fgsa_block_stamp_source_or_restart. They add local replay or restamp origins
  with the actual wake time. They assert no network acceptance at restart.
  Consumers: Receipts vote/read/cap/acceptance suppliers; Shared/ReceiptFacts,
  GateReceipt, ScoreRun; WeakContinuation/ExactProposal and its family copies.
  Restart consumers use the general supplier. NoRestart consumers use the wrapper.
- R8: fgsa_block_accepted_origin keeps the original network acceptance through every
  restart epoch. fgsa_replayed_head_delivery_origin supplies the original delivered
  proposal and structural HEAD carriage, with no fabricated HEAD handler.
- internal statement, W3: fgsa_vote_accepted_before and fgsa_block_accepted_before
  now take ExecutionValid, rather than ScheduleWellFormed alone. An asleep raw
  receiver may have a stale clock under ScheduleWellFormed. Full sleep validity
  and RestoreTimeLaw give the exact public-time bound at a real delivery. The vote
  form keeps its NoRestart premise; the block form still permits restarts.
  Consumers: Shared/ReceiptFacts, GateReceipt, ScoreRun and family deadline readers.
- internal statement, W3: fgsa_head_cap_sources takes NoRestart for its network-only
  cap witnesses. Its only proof consumer in Run is fgsa_honest_head_receipt, which
  already has that premise. General stamp/replay suppliers cover restart consumers.
- internal statement, W3: fgsa_head_receipt and fgsa_honest_head_receipt take the
  receiver's AwakeOn window and dl t ≤ horizon. The old within premise is vacuous
  outside those guards. Their HEAD/stamp conclusions stay. Consumers: public
  ReceiptCoverage wrapper (stopped P23), Shared and family HEAD receipt readers.
- internal statement, W3: fgsa_proposal_receipt takes the same awake/horizon guards
  and NamedProposalInRun of the exact required body. Root-only history does not
  supply that body scope. The stored-body conclusion stays. Consumers: P23 core
  (STOP), Shared proposal receipt readers and their Clean/Outage/WC/WCG copies.
- internal statement, W3: proposal_trigger_in_scope and its root-scope projection
  now use DeliveryService plus an exact historical-scope callback. A handled
  service keeps the original handler origin; past root processing alone cannot
  scope the new body. Consumers: WeakContinuation/ExactProposal and
  Assembly/WeakContinuationGrowth must discharge that callback after the P23 ruling.
- internal statement, W3: fgsa_accepted_by_deadline_of_parentStored now follows the
  current generic core: ReadyTrigger, HistorySafeAt, actual horizon, action-cut
  restartFree, HooksSound and a handler Timely callback. Its parent and wire facts
  still supply dependencies. No proof consumer outside the Run audit was found.
- N3: fgsa_processed_by_deadline_ready instantiates the P2 service/acceptance core.
  History is current processing on NoRestart; full validity and the awake window
  supply earlier public ticks. Relay time uses RestoreTimeLaw and public actTime;
  no TimelyOfRelay hwake premise is used. fgsaTimelyClock_clock exposes the needed
  equality to the physical FG-SA clock without changing the clock definition.
- N10 HEAD: fgsa_emitted_head_no_prior_processed holds through sleep and replay.
  A replayed HEAD comes from an earlier carried signature, and its fixed-label
  action time excludes processing before the current scheduled emission.
- internal statement, W3: the requested proposal no-prior-processing form needs
  NamedProposalInRun for the emitted body as well as NamedRootCollisionFree and
  ExecutionValid. fgsa_emitted_proposal_no_prior_processed proves that exact scoped
  form. Consumers that need scope from P2 alone remain STOP under the proved alias.
- Own-row append/cut producers keep both P2 service branches and all demand guards.
  The cut carries full SleepWellFormed. internal statement, W3:
  healthyPrefixDeliveryBy_cut also takes t ≤ rho.horizon; extending the cut horizon
  would otherwise create obligations beyond the old demand domain. Consumers:
  Shared/Regimes at the valid action-time cut. No declaration in that family changed.
- Validation status: 399 GREEN modules compile with --wfail. The fixed package
  domain retains 60 EXPECTED-FAIL entries, including three S-Ap-P23-STOP roots:
  Run, Proofs/ReceiptCoverage and Tests/Axioms. No REQUIRED module is deferred.
  This is not W3 close or a full-run PASS. The lead owns the public P23 ruling.

## W3 — Audit and handoff limits (2026-10-10)

- W3 equation exports were repaired in FGSource and ProposalHistory. Schedule's
  process-bound caller uses a direct slot projection instead of exporting the
  model State.slot equation. No theorem type changed for that caller.
- STOP inherited W2b equation exports: Restore.lean is unchanged in W3, but the
  complete W3 and Shared export checks report 17 unaccepted matcher equations
  from that module (admitBlock, admitRow, process, headLabel?, resolvedBefore).
  The baseline is unchanged. W2b/lead must provide the review fix. This is a checker
  failure, not a project axiom or a failed kernel theorem.
- Run inventory rows use actual compiled owners from W3Axioms generation. Only
  the Run, SharedAxioms, SafetyAxioms and FGSafety sections changed. The late
  FGSafety source audit repeats the two new safety producers, as its coverage
  checker requires. That audit remains a P-Sa family target, not an S1 promotion.
- The Claims read test is an explicit package target outside S1, as r8 permits.
  New Run modules are S1 REQUIRED. No original REQUIRED or DEFERRED entry changed.
- DCK uses all normal controls. No baseline exception or audit exception is used.
  Full Run build remains stopped by the P23 wrapper; the exact ready core cannot
  be written under the approved statement. Root freeze and package close remain
  with the lead after both STOP items are resolved.

## W3 — Writer validation result (2026-10-10)

- Commit 0b6f3837 contains the completed W3 implementation, tests and explicit STOP map.
- Final DCK W3 PASS: 147.01 s, 399 GREEN modules, 30 strict audit roots,
  2,473 axiom commands/results, and all 24 normal controls. No audit exception.
- The map has 61 EXPECTED-FAIL entries. Three are the S-Ap P23 stopped roots;
  the late FGSafety audit remains P-Sa. The other entries retain their family owners.
- Final export check: 17 unaccepted exports, all in unchanged W2b Restore.lean.
  New W3 modules and the repaired Schedule caller have no unaccepted export.
- The P23 ready core is still STOP. No approved public text or stopped wrapper changed.
  DCK PASS certifies the explicit GREEN partition. It does not close W3 or G-S1.
- Full report: local, excluded claude-files/sleep-w3-report.md. Evidence: .lake/sleep-w3/.
## W2b review fixes — consumer handoff

### W3/P-ShA handoff: review use classifications

This replaces the earlier claim that every consumer needs only an argument repair.
Keep all W2b conditions. This is a source handoff; EXPECTED-FAIL consumers are not verified.
References use review base `4b697a95`. Run paths start at `AvailableChainFGSARun/`;
other paths start at `AvailableChainFGSAProofs/`. Each row is one direct proof/test use.
Audit references are proof-only repairs of the print command; they add no premise.
The four NamedOrigins guard splits at :77, :86, :146 and :160 are proof-only repairs.
They unfold the approved actS guard (P24, packet :8204), without changing an emission type.
These audit/guard references are separate from the 170 direct-use counts below.

P = proof-only repair. A = approved change of read/scope. F = false internal consumer type.
M = premise source missing; this is an extra flag, not a fourth classification.
The Owner column applies plan §14.6, with the family split in §8.1/§8.3.
For M rows the owner must trace the new condition through callers to the public boundary.
An added internal premise is a repair specification, not approval to add a public premise.
M records a missing receiver/time or branch source. It remains open with that owner.
No blanket participation inference applies.

Condition/source keys:

- K: keep the used origin/bound projections. No new condition is needed.
- Z: split joinedNow in act_prop_zero. Both branches give none; no new condition is needed.
- S: supply the restart subset law. Leases:323 uses acRestart_obligations equality;
  Leases:494 uses acRestart_fastWrite = []; the other saved-pair uses acRestart_genuine = [].
  Schedule:222 already supplies acRestart_genuine and nil_subset.
- L: use fgsa_preTick_now_le. Preserve the consumer conclusion: now ≤ tick, then slot
  monotonicity, or now ≤ tick < the live deadline. No awake/join condition is needed.
- E: keep strict now < tick with hEpoch = ∀ j w, j < i →
  rho.events[j]? = some (.restart v w) → w < t. Current NoRestart contradicts the event.
  For a sleep interface, derive hEpoch from joinedAtTime at this same tick; no inference
  from awake alone is valid. That sleep change must obtain its scope from the family packet.
- I: the Run caller already passes hEpoch, derives it from joinedAtTime, or proves the iff.
- J: the strict late-pool helper keeps its existing conclusion with hEpoch at its gate tick
  as an added premise (or joinedAtTime p pre.restartTime gateTime = true).
  No source exists inside its schedule-only type. Its callers have hN : NoRestart rho;
  pass hEpoch by contradicting each restart event. No new public premise is needed there.
- G: use the executed gate read from P11/D015, approved packet :4265–4274.
  Exact equation: savedGenuine post.base s = some (if joinedAtTime p pre.restartTime
  (SA.gateTime p.toParams s) then rawConfirmation else none). The same guard controls fastSet.
  Split the guard and use fgsa_gate_saved_result / fgsa_gate_saved_unjoined.
  A nonempty executed gateResult, gateResultAt, or GateService result implies this guard.
  A raw confirmation or a gate event alone does not. P11/D016 :4293 uses enabledGateAt;
  its exact definition at :4594–4598 supplies the marker bound w ≤ slotStartZ p s.
- GF: healing_support_fastWrite must require joinedAtTime at its gate and then keep
  its raw fastSet equality; alternatively give fastWriteAt post s = some
  (if joinedAtTime p pre.restartTime gateTime then fastSet p anchor view s else []).
  Its current schedule + gate type has no source for the joined branch. Its callers
  with a nonempty executed result/fast-write use G; the guarded equation needs no new premise.
- GR: clean_gate_raw must require the same gate guard for its raw equation, or state
  the guarded G equation. Its current schedule + gate type has no joined source:
  premise source missing. The approved guarded read does not prove an unconditional raw equality.
- RR: healing_support_release_rows must require joinedAtTime p st.restartTime
  (SA.releaseTime p.toParams s) = true. Then keep row ∈ (actView st1).obligations and
  releaseCount ... s row.1 < row.2.1. Without the guard the exact conclusion is conditional:
  row survives expiry and (joinedAtTime ... = true → releaseCount ... < row.2.1).
  An arbitrary store plus a surviving lease supplies no guard. Its three current callers
  can pass the guard from hrec.base.noRestart or hN (see caller checks below).
  Under sleep, use the conditional form for callers that need only expiry membership;
  a caller that needs the strict count must prove the release guard, as specified in RN.
- RN: current NoRestart gives pre.restartTime = none and thus the release guard.
  DescentLossUnanimous:291 uses hrec.base.noRestart; SupportTransfer:306 uses hN.
  The sleep form uses P8 RecoverySleep₂.suffixNoRestart (packet :2935–2941), bounds
  all earlier restarts by GST, and needs GST ≤ slotStartZ p v at releaseTime v.
  P8's τ scope (:2284) supplies that cutoff after recoveryStart; the old bound
  GST ≤ voteTime v alone is not that cutoff. Pass the guard also to release_rows.
- C: Schedule:888 passes its hEpoch without change.
- RT: Receipts uses fgsaRestoreTimeLaw for its aligned TimelyClock and
  fgsa_admissionTime_public with E.Δ = p.Δ. Keep actTime ≤ pubFloor(receiptTime).
  No public-wake premise is used. This is W3 integration with unchanged consumer conclusions.

`stored_proposal_delivered`:

```text
┌────────────────────────────────────────────┬──────┬────────┬───────┬──────┐
│ Consumer at review base                    │ Type │ Source │ Owner │ Open │
├────────────────────────────────────────────┼──────┼────────┼───────┼──────┤
│ Finality/Receipt.lean:50                   │ P    │ K      │ P-Fi  │ —    │
│ Foundations/Accountable.lean:531           │ P    │ K      │ P-Fd  │ —    │
│ Foundations/Carrier.lean:39                │ P    │ K      │ P-Fd  │ —    │
│ Foundations/Sources.lean:252               │ P    │ K      │ P-Fd  │ —    │
│ Shared/ScoreRun.lean:105                   │ P    │ K      │ P-ShA │ —    │
│ Shared/ScoreRun.lean:218                   │ P    │ K      │ P-ShA │ —    │
│ Tests/NonVacuity/FinalityClaims.lean:1012  │ P    │ K      │ P-As  │ —    │
│ Tests/NonVacuity/HealingClaims.lean:1008   │ P    │ K      │ P-As  │ —    │
│ Tests/NonVacuity/HealingPackages.lean:1003 │ P    │ K      │ P-As  │ —    │
│ Tests/NonVacuity/HealingRun.lean:1007      │ P    │ K      │ P-As  │ —    │
│ Run/Proofs/NamedDelivery.lean:50           │ P    │ K      │ W3    │ —    │
│ Run/Proofs/NamedDelivery.lean:63           │ P    │ K      │ W3    │ —    │
│ Run/Proofs/Roots.lean:107                  │ P    │ K      │ W3    │ —    │
│ Run/Proofs/Schedule.lean:1008              │ P    │ K      │ W3    │ —    │
│ Run/Tests/SleepContinuation.lean:18        │ P    │ K      │ W3    │ —    │
└────────────────────────────────────────────┴──────┴────────┴───────┴──────┘
```

Audit (proof-only): Run/Tests/Axioms.lean:171; Run/Tests/SleepContinuationAxioms.lean:9.

`act_prop`:

```text
┌──────────────────────────────┬──────┬────────┬───────┬──────┐
│ Consumer at review base      │ Type │ Source │ Owner │ Open │
├──────────────────────────────┼──────┼────────┼───────┼──────┤
│ Run/Proofs/Protocol.lean:154 │ P    │ Z      │ W3    │ —    │
└──────────────────────────────┴──────┴────────┴───────┴──────┘
```

Audit (proof-only): Run/Tests/Axioms.lean:72; Run/Tests/SleepContinuationAxioms.lean:5.

`act_prop_zero`:

No direct proof/test use. The audit is a proof-only repair.

Audit (proof-only): Run/Tests/Axioms.lean:73; Run/Tests/SleepContinuationAxioms.lean:6.

`fgsa_hrestore_retained`:

No direct proof/test use. The audit is a proof-only repair.

Audit (proof-only): Run/Tests/Axioms.lean:48; Run/Tests/SleepContinuationAxioms.lean:7.

`fgsa_hrestore_field_retained`:

```text
┌──────────────────────────────────────────┬──────┬────────┬───────┬──────┐
│ Consumer at review base                  │ Type │ Source │ Owner │ Open │
├──────────────────────────────────────────┼──────┼────────┼───────┼──────┤
│ Assembly/WeakContinuation.lean:237       │ P    │ S      │ P-As  │ —    │
│ Foundations/Leases.lean:323              │ P    │ S      │ P-Fd  │ —    │
│ Foundations/Leases.lean:494              │ P    │ S      │ P-Fd  │ —    │
│ WeakContinuation/StepFacts.lean:199      │ P    │ S      │ P-WC  │ —    │
│ WeakContinuationGrowth/Dynamics.lean:379 │ P    │ S      │ P-WC  │ —    │
│ Run/Proofs/Schedule.lean:222             │ P    │ S      │ W3    │ —    │
└──────────────────────────────────────────┴──────┴────────┴───────┴──────┘
```

Audit (proof-only): Run/Tests/Axioms.lean:49; Run/Tests/SleepContinuationAxioms.lean:8.

`fgsa_preTick_now_lt`:

```text
┌───────────────────────────────────────────┬──────┬────────┬───────┬──────┐
│ Consumer at review base                   │ Type │ Source │ Owner │ Open │
├───────────────────────────────────────────┼──────┼────────┼───────┼──────┤
│ Clean/StepGate.lean:511                   │ P    │ E      │ P-Cl1 │ —    │
│ Healing/DescentLossNext.lean:289          │ P    │ L      │ P-H1  │ —    │
│ Healing/DescentLossUnanimous.lean:158     │ P    │ L      │ P-H1  │ —    │
│ Healing/FrontierSupportHeads.lean:153     │ P    │ L      │ P-H1  │ —    │
│ Healing/FrontierSupportProposal.lean:98   │ P    │ L      │ P-H1  │ —    │
│ Healing/OpeningServiceGate.lean:152       │ P    │ L      │ P-H2  │ —    │
│ Healing/PostResetConeReceipts.lean:125    │ P    │ L      │ P-H2  │ —    │
│ Healing/PostResetConeReceipts.lean:286    │ P    │ L      │ P-H2  │ —    │
│ Healing/PostResetRaw.lean:901             │ P    │ L      │ P-H1  │ —    │
│ Healing/PostResetRaw.lean:1383            │ P    │ L      │ P-H1  │ —    │
│ Healing/RepairGate.lean:504               │ P    │ L      │ P-H1  │ —    │
│ Healing/SupportHeads.lean:216             │ P    │ L      │ P-H1  │ —    │
│ Healing/SupportOutput.lean:198            │ P    │ L      │ P-H1  │ —    │
│ Healing/SupportProposal.lean:149          │ P    │ L      │ P-H1  │ —    │
│ Healing/SupportRelay.lean:92              │ F    │ J      │ P-H1  │ —    │
│ Outage/ContinuationReceipt.lean:283       │ P    │ E      │ P-Ou  │ —    │
│ Shared/GateReceipt.lean:131               │ P    │ E      │ P-ShA │ —    │
│ Shared/Relay.lean:144                     │ F    │ J      │ P-ShA │ —    │
│ Shared/Relay.lean:576                     │ P    │ E      │ P-ShA │ —    │
│ Shared/RetainedEndpoint.lean:26           │ P    │ L      │ P-ShA │ —    │
│ Shared/RetainedReflect.lean:328           │ P    │ L      │ P-ShA │ —    │
│ Shared/SameLabel.lean:206                 │ F    │ J      │ P-ShA │ —    │
│ WeakContinuation/Inclusion.lean:206       │ P    │ L      │ P-WC  │ —    │
│ WeakContinuation/Proposal.lean:297        │ P    │ E      │ P-WC  │ —    │
│ WeakContinuation/Proposal.lean:493        │ P    │ L      │ P-WC  │ —    │
│ WeakContinuation/StepGateBatch.lean:242   │ P    │ E      │ P-WC  │ —    │
│ WeakContinuationGrowth/Dynamics.lean:1425 │ P    │ E      │ P-WC  │ —    │
│ Run/Proofs/Schedule.lean:544              │ P    │ I      │ W3    │ —    │
│ Run/Proofs/Schedule.lean:568              │ P    │ I      │ W3    │ —    │
│ Run/Proofs/Schedule.lean:610              │ P    │ I      │ W3    │ —    │
│ Run/Proofs/Schedule.lean:778              │ P    │ I      │ W3    │ —    │
└───────────────────────────────────────────┴──────┴────────┴───────┴──────┘
```

Audit (proof-only): Run/Tests/Axioms.lean:226; Run/Tests/SleepContinuationAxioms.lean:16.

`fgsa_release_votes_stamped`:

No direct proof/test use. The audit is a proof-only repair.

Audit (proof-only): Run/Tests/Axioms.lean:227; Run/Tests/SleepContinuationAxioms.lean:21.

`fgsa_stateBefore_bounds`:

```text
┌───────────────────────────────────────────┬──────┬────────┬───────┬──────┐
│ Consumer at review base                   │ Type │ Source │ Owner │ Open │
├───────────────────────────────────────────┼──────┼────────┼───────┼──────┤
│ Clean/StepGate.lean:647                   │ P    │ K      │ P-Cl1 │ —    │
│ Healing/DescentLossNext.lean:285          │ P    │ K      │ P-H1  │ —    │
│ Healing/DescentLossUnanimous.lean:154     │ P    │ K      │ P-H1  │ —    │
│ Healing/FrameZero.lean:106                │ P    │ K      │ P-H1  │ —    │
│ Healing/FrontierSupportHeads.lean:149     │ P    │ K      │ P-H1  │ —    │
│ Healing/FrontierSupportProposal.lean:94   │ P    │ K      │ P-H1  │ —    │
│ Healing/OpeningServiceGate.lean:146       │ P    │ K      │ P-H2  │ —    │
│ Healing/PostResetConeReceipts.lean:121    │ P    │ K      │ P-H2  │ —    │
│ Healing/PostResetConeReceipts.lean:282    │ P    │ K      │ P-H2  │ —    │
│ Healing/PostResetRaw.lean:1379            │ P    │ K      │ P-H1  │ —    │
│ Healing/RepairGate.lean:498               │ P    │ K      │ P-H1  │ —    │
│ Healing/SupportHeads.lean:212             │ P    │ K      │ P-H1  │ —    │
│ Healing/SupportProposal.lean:145          │ P    │ K      │ P-H1  │ —    │
│ Healing/SupportRelay.lean:93              │ P    │ K      │ P-H1  │ —    │
│ Outage/ContinuationReceipt.lean:556       │ P    │ K      │ P-Ou  │ —    │
│ Outage/ContinuationReceipt.lean:724       │ P    │ K      │ P-Ou  │ —    │
│ Shared/GateReceipt.lean:363               │ P    │ K      │ P-ShA │ —    │
│ Shared/HeadAdmit.lean:214                 │ P    │ K      │ P-ShA │ —    │
│ Shared/OutputGrowthCausal.lean:47         │ P    │ K      │ P-ShA │ —    │
│ Shared/Relay.lean:145                     │ P    │ K      │ P-ShA │ —    │
│ Shared/Relay.lean:577                     │ P    │ K      │ P-ShA │ —    │
│ Shared/RetainedEndpoint.lean:35           │ P    │ K      │ P-ShA │ —    │
│ Shared/RetainedReflect.lean:337           │ P    │ K      │ P-ShA │ —    │
│ Shared/SameLabel.lean:207                 │ P    │ K      │ P-ShA │ —    │
│ WeakContinuation/StepGateBatch.lean:379   │ P    │ K      │ P-WC  │ —    │
│ WeakContinuationGrowth/Dynamics.lean:1564 │ P    │ K      │ P-WC  │ —    │
│ Run/Proofs/Schedule.lean:586              │ P    │ K      │ W3    │ —    │
│ Run/Proofs/Schedule.lean:613              │ P    │ K      │ W3    │ —    │
│ Run/Proofs/Schedule.lean:783              │ P    │ K      │ W3    │ —    │
│ Run/Proofs/Schedule.lean:843              │ P    │ K      │ W3    │ —    │
└───────────────────────────────────────────┴──────┴────────┴───────┴──────┘
```

Audit (proof-only): Run/Tests/Axioms.lean:225; Run/Tests/SleepContinuationAxioms.lean:14.

`fgsa_stored_block_origin`:

```text
┌─────────────────────────────────┬──────┬────────┬───────┬──────┐
│ Consumer at review base         │ Type │ Source │ Owner │ Open │
├─────────────────────────────────┼──────┼────────┼───────┼──────┤
│ Finality/MiddleSupport.lean:757 │ P    │ K      │ P-Fi  │ —    │
│ Healing/Promotion.lean:35       │ P    │ K      │ P-H1  │ —    │
│ Shared/RetainedEndpoint.lean:47 │ P    │ K      │ P-ShA │ —    │
│ Shared/ScoreRun.lean:897        │ P    │ K      │ P-ShA │ —    │
│ Shared/ScoreRun.lean:1127       │ P    │ K      │ P-ShA │ —    │
└─────────────────────────────────┴──────┴────────┴───────┴──────┘
```

Audit (proof-only): Run/Tests/Axioms.lean:236; Run/Tests/SleepContinuationAxioms.lean:29.

`fgsa_tick_total`:

```text
┌──────────────────────────────────────────────┬──────┬────────┬───────┬──────┐
│ Consumer at review base                      │ Type │ Source │ Owner │ Open │
├──────────────────────────────────────────────┼──────┼────────┼───────┼──────┤
│ Assembly/WeakContinuation.lean:538           │ F    │ T01    │ P-As  │ M    │
│ Assembly/WeakContinuationGrowth.lean:377     │ F    │ T02    │ P-As  │ M    │
│ Assembly/WeakContinuationGrowth.lean:572     │ F    │ T03    │ P-As  │ M    │
│ Assembly/WeakContinuationGrowthSeed.lean:195 │ F    │ T04    │ P-As  │ M    │
│ Clean/Closure.lean:200                       │ F    │ T05    │ P-Cl1 │ M    │
│ Clean/Closure.lean:298                       │ F    │ T06    │ P-Cl1 │ M    │
│ Clean/Safety.lean:197                        │ F    │ T07    │ P-Cl1 │ M    │
│ Clean/StepGate.lean:212                      │ F    │ T08    │ P-Cl1 │ M    │
│ Clean/StepGate.lean:257                      │ P    │ T09    │ P-Cl1 │ —    │
│ Clean/StepGate.lean:447                      │ F    │ T10    │ P-Cl1 │ M    │
│ Clean/StepGate.lean:566                      │ P    │ T11    │ P-Cl1 │ —    │
│ Clean/StepGate.lean:569                      │ F    │ T12    │ P-Cl1 │ M    │
│ Finality/RowsPrem.lean:91                    │ P    │ T13    │ P-Fi  │ —    │
│ Finality/TailFrame.lean:383                  │ P    │ T14    │ P-Fi  │ —    │
│ Healing/FrontierSearchTasks.lean:211         │ P    │ T15    │ P-H2  │ —    │
│ Healing/OpeningServiceBody.lean:197          │ P    │ T16    │ P-H2  │ —    │
│ Healing/OpeningServiceOne.lean:29            │ F    │ T17    │ P-H2  │ M    │
│ Healing/PostResetGate.lean:265               │ P    │ T18    │ P-H2  │ —    │
│ Healing/PostResetOpening.lean:163            │ P    │ T19    │ P-H2  │ —    │
│ Healing/PostResetRaw.lean:592                │ P    │ T20    │ P-H1  │ —    │
│ Healing/PostResetRaw.lean:811                │ P    │ T21    │ P-H1  │ —    │
│ Healing/PostResetService.lean:235            │ P    │ T22    │ P-H2  │ —    │
│ Healing/SupportHeads.lean:110                │ F    │ T23    │ P-H1  │ M    │
│ Healing/SupportOutput.lean:261               │ P    │ T24    │ P-H1  │ —    │
│ Outage/ArmingBatch.lean:63                   │ F    │ T25    │ P-Ou  │ M    │
│ Outage/ContinuationReceipt.lean:462          │ P    │ T26    │ P-Ou  │ —    │
│ Outage/ContinuationReceipt.lean:465          │ F    │ T27    │ P-Ou  │ M    │
│ Outage/ContinuationReceipt.lean:626          │ P    │ T28    │ P-Ou  │ —    │
│ Outage/ContinuationReceipt.lean:629          │ F    │ T29    │ P-Ou  │ M    │
│ Outage/ContinuationReceipt.lean:820          │ F    │ T30    │ P-Ou  │ M    │
│ Outage/ExactProposalRetained.lean:299        │ F    │ T31    │ P-Ou  │ M    │
│ Outage/ExactProposalRetained.lean:513        │ P    │ T32    │ P-Ou  │ —    │
│ Outage/ExactProposalRetained.lean:519        │ F    │ T33    │ P-Ou  │ M    │
│ Outage/ExactProposalRetained.lean:581        │ F    │ T34    │ P-Ou  │ M    │
│ Outage/ExactProposalRetained.lean:726        │ F    │ T35    │ P-Ou  │ M    │
│ Outage/InclusionGate.lean:55                 │ F    │ T36    │ P-Ou  │ M    │
│ Outage/InclusionGate.lean:119                │ F    │ T37    │ P-Ou  │ M    │
│ Outage/InclusionGateBody.lean:55             │ F    │ T38    │ P-Ou  │ M    │
│ Shared/ExactHead.lean:193                    │ F    │ T39    │ P-ShA │ M    │
│ Shared/ExactService.lean:462                 │ F    │ T40    │ P-ShA │ M    │
│ Shared/GateReceipt.lean:269                  │ P    │ T41    │ P-ShA │ —    │
│ Shared/GateReceipt.lean:272                  │ F    │ T42    │ P-ShA │ M    │
│ Shared/HeadAdmit.lean:387                    │ P    │ T43    │ P-ShA │ —    │
│ Shared/OutputGrowthProposal.lean:32          │ P    │ T44    │ P-ShA │ —    │
│ Shared/RetainedEndpoint.lean:293             │ F    │ T45    │ P-ShA │ M    │
│ WeakContinuation/ExactProposal.lean:214      │ F    │ T46    │ P-WC  │ M    │
│ WeakContinuation/Inclusion.lean:78           │ F    │ T47    │ P-WC  │ M    │
│ WeakContinuation/Inclusion.lean:332          │ F    │ T48    │ P-WC  │ M    │
│ WeakContinuation/Proposal.lean:203           │ F    │ T49    │ P-WC  │ M    │
│ WeakContinuation/Proposal.lean:750           │ F    │ T50    │ P-WC  │ M    │
│ WeakContinuation/StepGateBatch.lean:305      │ P    │ T51    │ P-WC  │ —    │
│ WeakContinuation/StepGateBatch.lean:308      │ F    │ T52    │ P-WC  │ M    │
│ WeakContinuation/StepInputs.lean:155         │ F    │ T53    │ P-WC  │ M    │
│ WeakContinuation/StepService.lean:201        │ F    │ T54    │ P-WC  │ M    │
│ WeakContinuation/StepTransfer.lean:44        │ F    │ T55    │ P-WC  │ M    │
│ WeakContinuationGrowth/Dynamics.lean:811     │ F    │ T56    │ P-WC  │ M    │
│ WeakContinuationGrowth/Dynamics.lean:1015    │ F    │ T57    │ P-WC  │ M    │
│ WeakContinuationGrowth/Dynamics.lean:1488    │ P    │ T58    │ P-WC  │ —    │
│ WeakContinuationGrowth/Dynamics.lean:1491    │ F    │ T59    │ P-WC  │ M    │
│ WeakContinuationGrowth/Dynamics.lean:3074    │ F    │ T60    │ P-WC  │ M    │
│ Tests/InclusionGate.lean:71                  │ F    │ T61    │ P-Ou  │ M    │
└──────────────────────────────────────────────┴──────┴────────┴───────┴──────┘
```

Audit (proof-only): Run/Tests/Axioms.lean:215; Run/Tests/SleepContinuationAxioms.lean:12.

`fgsa_gate_clock_bridge`:

```text
┌──────────────────────────────┬──────┬────────┬───────┬──────┐
│ Consumer at review base      │ Type │ Source │ Owner │ Open │
├──────────────────────────────┼──────┼────────┼───────┼──────┤
│ Healing/SupportWrite.lean:75 │ F    │ GF     │ P-H1  │ —    │
│ Shared/ExactService.lean:218 │ A    │ G      │ P-ShA │ —    │
│ Shared/OpeningSource.lean:49 │ A    │ G      │ P-ShA │ —    │
└──────────────────────────────┴──────┴────────┴───────┴──────┘
```

Audit (proof-only): Run/Tests/Axioms.lean:224; Run/Tests/SleepContinuationAxioms.lean:13.

`fgsa_release_clockPre`:

```text
┌───────────────────────────────────────┬──────┬────────┬───────┬──────┐
│ Consumer at review base               │ Type │ Source │ Owner │ Open │
├───────────────────────────────────────┼──────┼────────┼───────┼──────┤
│ Healing/DescentLossUnanimous.lean:291 │ P    │ RN     │ P-H1  │ —    │
│ Healing/SupportTransfer.lean:72       │ F    │ RR     │ P-H1  │ —    │
│ Healing/SupportTransfer.lean:306      │ P    │ RN     │ P-H1  │ —    │
└───────────────────────────────────────┴──────┴────────┴───────┴──────┘
```

Audit (proof-only): Run/Tests/Axioms.lean:229; Run/Tests/SleepContinuationAxioms.lean:23.

`fgsa_release_input_votes_stamped`:

```text
┌──────────────────────────────┬──────┬────────┬───────┬──────┐
│ Consumer at review base      │ Type │ Source │ Owner │ Open │
├──────────────────────────────┼──────┼────────┼───────┼──────┤
│ Run/Proofs/Schedule.lean:888 │ P    │ C      │ W3    │ —    │
└──────────────────────────────┴──────┴────────┴───────┴──────┘
```

Audit (proof-only): Run/Tests/Axioms.lean:230; Run/Tests/SleepContinuationAxioms.lean:24.

`fgsa_release_count_bridge`:

No direct proof/test use. The audit is a proof-only repair.

Audit (proof-only): Run/Tests/Axioms.lean:232; Run/Tests/SleepContinuationAxioms.lean:26.

`fgsa_gate_saved_result`:

```text
┌────────────────────────────────────────────────┬──────┬────────┬───────┬──────┐
│ Consumer at review base                        │ Type │ Source │ Owner │ Open │
├────────────────────────────────────────────────┼──────┼────────┼───────┼──────┤
│ Clean/StateGate.lean:32                        │ F    │ GR     │ P-Cl1 │ M    │
│ Shared/Reads.lean:161                          │ A    │ G      │ P-ShA │ —    │
│ WeakContinuation/StepGateHistory.lean:139      │ A    │ G      │ P-WC  │ —    │
│ WeakContinuation/StepOutput.lean:29            │ A    │ G      │ P-WC  │ —    │
│ WeakContinuation/StepService.lean:30           │ A    │ G      │ P-WC  │ —    │
│ WeakContinuation/StepTransfer.lean:91          │ A    │ G      │ P-WC  │ —    │
│ WeakContinuation/StepTransferReceipts.lean:415 │ A    │ G      │ P-WC  │ —    │
│ WeakContinuationGrowth/Dynamics.lean:639       │ A    │ G      │ P-WC  │ —    │
│ WeakContinuationGrowth/Dynamics.lean:1877      │ A    │ G      │ P-WC  │ —    │
│ WeakContinuationGrowth/Dynamics.lean:2153      │ A    │ G      │ P-WC  │ —    │
│ WeakContinuationGrowth/Dynamics.lean:2965      │ A    │ G      │ P-WC  │ —    │
│ WeakContinuationGrowth/Dynamics.lean:3121      │ A    │ G      │ P-WC  │ —    │
└────────────────────────────────────────────────┴──────┴────────┴───────┴──────┘
```

Audit (proof-only): Run/Tests/Axioms.lean:235; Run/Tests/SleepContinuationAxioms.lean:27.

`timely_of_relay_retained`:

```text
┌──────────────────────────────┬──────┬────────┬───────┬──────┐
│ Consumer at review base      │ Type │ Source │ Owner │ Open │
├──────────────────────────────┼──────┼────────┼───────┼──────┤
│ Run/Proofs/Receipts.lean:883 │ P    │ RT     │ W3    │ —    │
│ Run/Proofs/Receipts.lean:985 │ P    │ RT     │ W3    │ —    │
└──────────────────────────────┴──────┴────────┴───────┴──────┘
```

Audit (proof-only): Run/Tests/SleepContinuationAxioms.lean:10.

Exact awake obligations (T01–T61):

A(v,t) means `E.awake v t = true`. The true tick consumer form is the existing
schedule, honesty, public-time and horizon premises plus A(v,t), giving
`∃! i, rho.events[i]? = some (.tick v t)`. Each T row supplies the exact v and t.
For an F row, this is the required replacement of the false unconditional tick subclaim;
the owner must propagate it through the enclosing helper and callers. It does not certify
all other sleep obligations of that enclosing theorem. Public premise changes need a ruling.
The three generic helpers keep their current existential conclusions after adding:
opening_action_tick: A(x,a(r)); healing_support_vote_tick: A(z,v(i));
arming_tick_exists: A(y,t), where t=mΔ. None currently has a public source for A.

Here a(r)=p.actionTime r, v(s)=SA.voteTime p.toParams s,
d(s)=SA.gateTime p.toParams s, e(s)=SA.earlyTime p.toParams s,
f(s)=SA.freezeTime p.toParams s, q(s)=SA.releaseTime p.toParams s,
t(s)=SA.proposalTime p.toParams s, and R=p.R. All times use p.Δ.
`seat(head s,k)` means rho.seatOf (.base (.head s)) k;
`proposer(s)` means V2.D.proposerOf rho (fgsaInterface p c) s.
Recovery sources use the unchanged Recovery₂.awake (approved P8, packet :2288–2325).
The cited H0Reset sources use synchronous and label (P8/D041, packet :2571–2597).

- T01: A(x,v(w.u+1)). Source: premise source missing; P-As must supply A at this exact time or
  avoid this tick.
- T02: A(x,v(pt.s)). Source: premise source missing; P-As must supply A at this exact time or
  avoid this tick.
- T03: A(x,d(pt.s)). Source: premise source missing; P-As must supply A at this exact time or
  avoid this tick.
- T04: A(x,v(w.u+1)). Source: premise source missing; P-As must supply A at this exact time or
  avoid this tick.
- T05: A(x,d(s)). Source: premise source missing; P-Cl1 must supply A at this exact time or avoid
  this tick.
- T06: A(y,v(s+1)). Source: premise source missing; P-Cl1 must supply A at this exact time or
  avoid this tick.
- T07: A(x,d(l)). Source: premise source missing; P-Cl1 must supply A at this exact time or avoid
  this tick.
- T08: A(x,2Δ). Source: premise source missing; P-Cl1 must supply A at this exact time or avoid
  this tick.
- T09: A(seat(head0,k),v(0)). Source: hka from (hH k).mp hk, at voteTime 0.
- T10: A(x,d(s)). Source: premise source missing; P-Cl1 must supply A at this exact time or avoid
  this tick.
- T11: A(y,v(s+1)). Source: the explicit hawake for selected voter y, at voteTime (s+1).
- T12: A(x,e(s+1)). Source: premise source missing; P-Cl1 must supply A at this exact time or
  avoid this tick.
- T13: A(y,v((pt.r+2)R)). Source: hK.set.awake y hy _ hGSTq (kmid_slot_horizon hK le_rfl).2.1.
- T14: A(y,v((pt.r+1)R)). Source: hT.set.awake y hy _ hGST hhorZ.2.1.
- T15: A(x,a(rG+2)). Source: hrec.awake x hx u₀ (hdelay implies GST ≤ u₀) hhor; hu₀ fixes a(rG+2).
- T16: A(y,a(r)). Source: hrec.awake y hy a(r); GST ≤ u ≤ proposalTime q ≤ a(r); har.trans hvh.
- T17: A(x,a(r)). Source: premise source missing; P-H2 must supply A at this exact time or avoid
  this tick.
- T18: A(x,d(s)). Source: hrec.awake x hx d(s); hgst bounds voteTime s, which is ≤ d(s);
  hGateHorizon.
- T19: A(x,v(v)). Source: hrec.awake x hx v(v); H0Reset.synchronous and w.sStar+2 ≤ v give GST ≤
  v(v); hh.
- T20: A(y,d(s+1)). Source: hrec.awake y hy d(s+1); hgst ≤ voteTime s ≤ d(s+1); hguard.
- T21: A(x,q(w.sStar)). Source: hrec.awake x hx q(w.sStar); h0r.synchronous ≤ q(w.sStar);
  hqg.trans hhor.
- T22: A(x,d(v)). Source: hrec.awake x hx d(v); postReset_synchronous_window hreset hv ≤ d(v);
  hGateHorizon.
- T23: A(z,v(i)). Source: premise source missing; P-H1 must supply A at this exact time or avoid
  this tick.
- T24: A(y,d(s+1)). Source: hrec.awake y hy d(s+1); hgst1 ≤ voteTime(s+1) ≤ d(s+1); hhor.
- T25: A(y,t=mΔ). Source: premise source missing; P-Ou must supply A at this exact time or avoid
  this tick.
- T26: A(y,v(s)). Source: the explicit hawake for selected voter y, at voteTime s.
- T27: A(x,e(s)). Source: premise source missing; P-Ou must supply A at this exact time or avoid
  this tick.
- T28: A(y,v(s)). Source: the explicit hawake for selected voter y, at voteTime s.
- T29: A(x,e(s)). Source: premise source missing; P-Ou must supply A at this exact time or avoid
  this tick.
- T30: A(x,f(s)). Source: premise source missing; P-Ou must supply A at this exact time or avoid
  this tick.
- T31: A(x0,d(q)). Source: premise source missing; P-Ou must supply A at this exact time or avoid
  this tick.
- T32: A(seat(head(q+1),w),v(q+1)). Source: (hH w).mp hw: selected honest awake voter at voteTime
  (q+1).
- T33: A(x,e(q+1)). Source: premise source missing; P-Ou must supply A at this exact time or avoid
  this tick.
- T34: A(y,e(q+1)). Source: premise source missing; P-Ou must supply A at this exact time or avoid
  this tick.
- T35: A(x,v(pt.s)). Source: premise source missing; P-Ou must supply A at this exact time or
  avoid this tick.
- T36: A(y,v(pt.s)). Source: premise source missing; P-Ou must supply A at this exact time or
  avoid this tick.
- T37: A(y,d(s-1)). Source: premise source missing; P-Ou must supply A at this exact time or avoid
  this tick.
- T38: A(x,d(pt.s)). Source: premise source missing; P-Ou must supply A at this exact time or
  avoid this tick.
- T39: A(y,v(s)). Source: premise source missing; P-ShA must supply A at this exact time or avoid
  this tick.
- T40: A(x,d(v)). Source: premise source missing; P-ShA must supply A at this exact time or avoid
  this tick.
- T41: A(y,v(s)). Source: the explicit hawake for selected voter y, at voteTime s.
- T42: A(x,e(s)). Source: premise source missing; P-ShA must supply A at this exact time or avoid
  this tick.
- T43: A(seat(head s,a),v(s)). Source: hawake _ hy, from the caller's all-selected-voters awake
  premise, at voteTime s.
- T44: A(proposer(s),t(s)). Source: ha for the chosen proposer at proposalTime s; he identifies
  this time.
- T45: A(y,v(s)). Source: premise source missing; P-ShA must supply A at this exact time or avoid
  this tick.
- T46: A(x,v(pt.s)). Source: premise source missing; P-WC must supply A at this exact time or
  avoid this tick.
- T47: A(x,v(pt.s)). Source: premise source missing; P-WC must supply A at this exact time or
  avoid this tick.
- T48: A(x,d(pt.s)). Source: premise source missing; P-WC must supply A at this exact time or
  avoid this tick.
- T49: A(y,d(s-2)). Source: premise source missing; P-WC must supply A at this exact time or avoid
  this tick.
- T50: A(x,e(q+1)). Source: premise source missing; P-WC must supply A at this exact time or avoid
  this tick.
- T51: A(y,v(s)). Source: the explicit hawake for selected voter y, at voteTime s.
- T52: A(x,e(s)). Source: premise source missing; P-WC must supply A at this exact time or avoid
  this tick.
- T53: A(y,d(s-1)). Source: premise source missing; P-WC must supply A at this exact time or avoid
  this tick.
- T54: A(y,d(s+1)). Source: premise source missing; P-WC must supply A at this exact time or avoid
  this tick.
- T55: A(y,v(s+1)). Source: premise source missing; P-WC must supply A at this exact time or avoid
  this tick.
- T56: A(y,d(s+1)). Source: premise source missing; P-WC must supply A at this exact time or avoid
  this tick.
- T57: A(y,d(s-1)). Source: premise source missing; P-WC must supply A at this exact time or avoid
  this tick.
- T58: A(y,v(s)). Source: the explicit hawake for selected voter y, at voteTime s.
- T59: A(x,e(s)). Source: premise source missing; P-WC must supply A at this exact time or avoid
  this tick.
- T60: A(y,v(s+1)). Source: premise source missing; P-WC must supply A at this exact time or avoid
  this tick.
- T61: A(x,d(pt.s)). Source: premise source missing; P-Ou must supply A at this exact time or
  avoid this tick.

P6 joined participation (packet :2080–2082, :2094–2097, :2110–2112) counts
joinedHonest at a specified time. Membership gives A at that time via joinedAt
(packet :4092–4097); it does not give A for an arbitrary honest receiver or another time.
Where a proof needs only an existential honest tick, choose its witness from a nonempty
counted awake/joined set at that requested time. Where it names a receiver, retain that
receiver and require its approved Ready/receiver window. No listed M row currently contains
that exact receiver/time premise, so this handoff does not claim that P6 closes it.


Tick existence also does not prove a duty emission. The approved HEAD target is
`∀ x ∈ rho.honest, joinedAt p E rho x s (SA.voteTime p.toParams s) → Q x`,
where Q is the kept HEAD/receipt conclusion (P10, packet :3876–3887).
A joinedAt witness supplies A at that vote time and both wake/restart bounds
(:4092–4097). A proposal emission needs the proposer's joinedDuty at proposalTime s
(P7, packet :2238), not only its awake premise. An executed gate conclusion uses
`enabledGateAt j x s → Q j x s` (P11, packet :4379–4381); its gate event supplies
that tick directly, and its marker bound supplies G. These are approved scope forms.
They do not supply earlier early/freeze ticks for a receiver. Those calls still need
A at the exact earlier times in T01–T61, or a proof that does not require those ticks.
No M row is closed by merely substituting an awake or counted-set fact at another time.

For G rows in WC/WCG, the current NoRestart also proves the marker is none.
The sleep port must instead use enabledGateAt or a nonempty executed result, with the
P11 guard above. In StepGateHistory:139, a raw nonempty confirmation is not an executed
result; establish enabledGateAt first. If its future sleep premises do not establish it,
that family owner must mark the premise source missing rather than infer it from raw data.
For Shared/ExactService:218 and OpeningSource:49, unfold GateService's executed result
through fgsaAC and guarded gateResult; the nonempty result is the source of the gate guard.
S-Ap writes the guarded public read; P-ShA proves the read bridge. The raw read remains diagnostic.

False helper caller checks (source only; these caller files stay with their owners):

- SupportTransfer.release_rows: DescentLossUnanimous:292, SupportTransfer:307,
  PostResetRawStep:205. Pass the same release guard. Recovery + τ or an executed joined
  receiver window can supply it; arbitrary survival cannot. DescentLossUnanimous:292
  and PostResetRawStep:205 have hrec.base.noRestart; SupportTransfer:307 has hN.
  PostResetRawStep:205 uses only the expiry-membership projection, so the conditional
  release_rows form also suffices. Owner P-H1/P-H2 (§14.6/§8.3).
- SupportWrite.fastWrite: SupportWrite:117, FrontierSupportTransfer:55, FrontierRead:81,
  SupportLease:273. Keep an unconditional equation only with the guard on fastSet.
  SupportWrite:117 and FrontierRead:81 have hres = some(some C), so G supplies joinedness.
  FrontierSupportTransfer:55 has hrec.base.noRestart; SupportLease:273 has hB in the
  actual fastWrite row. Gate freshness + the unjoined empty-row law makes that a joined witness.
  A raw fs equation cannot supply it. Owners P-H1/P-H2 must trace each premise (§14.6).
- StateGate.clean_gate_raw: StateGate:79,96,134,147,192; Transfer:63; GateOutput:41;
  StepGate:74,298,740; TransferFrame:133,320. Executed result some(some B) gives G.
  Calls that construct a result from raw confirmation must first establish enabledGateAt.
  P-Cl1 owns that source check (§14.6); a gate event alone leaves the premise source missing.
- OpeningServiceOne.opening_action_tick: OpeningServiceOne:86, FrontierOpen:172,
  Require A(x,a(r)); the applicable Recovery.awake plus
  GST ≤ a(r) ≤ horizon must be passed at each call. P-H2 owns these checks (§8.3/§14.6).
- SupportHeads.vote_tick: all callers in Healing must pass A at their requested voteTime.
  A counted voter supplies its own awake membership; Recovery/H0Reset must prove the
  exact lower and horizon bounds for other receivers. Owners P-H1/P-H2 (§14.6).
- ArmingBatch.arming_tick_exists: ArmingBatch:181,183 and ArmingGate:316.
  Require A(y,earlyTime(l+1)), A(q,voteTime(l+1)), A(y,gateTime(l+1)), respectively.
  Awake counted voter membership can supply the middle call only for that selected q;
  receiver readiness at one time does not cover the two other times. P-Ou owns the
  missing receiver/window sources (§14.6, family owner).
- Strict gate-late helpers: SupportRelay:92, Shared/Relay:144, Shared/SameLabel:206.
  Keep their strict lateVotes conclusion with J. Relay callers :626,628,629 use current
  NoRestart; SupportRelay:171,173,174 and SameLabel:295,297,298 must prove hEpoch
  or use an approved joined gate scope. P-H1 and P-ShA own those checks (§14.6).

Counts cover the 170 direct uses; M overlaps F. Audit commands and guard splits are excluded.

```text
┌───────────────────────────────┬───────┐
│ Classification                │ Count │
├───────────────────────────────┼───────┤
│ proof-only repair             │ 110   │
│ approved change of read/scope │ 13    │
│ false internal consumer type  │ 47    │
│ premise source missing        │ 42    │
└───────────────────────────────┴───────┘
```

### Other W2b review fixes

- P1/P3 valid-run test: Sleep.own_valid (:179) proves full ExecutionValid for ownRun.
  Sleep.own_record_retained (:248) checks an own FG row at time 28, nonempty sent entries
  before sleep on [31,35), and equal sent entries and full Λ after wake 35.
  Both new theorem audits use only propext, Classical.choice and Quot.sound.
- SleepContinuation.gate_empty (:64) is API coverage. Its raw fixture result is also empty;
  no discriminating skipped-versus-executed confirmation claim is made.
- Package map (§1.4/§8.1/§8.2): NamedDelivery and RetainedClock are TARGETS.
  ReceiptCoverage Statements is S-Ap; owners are W3 52, P-ShA 45, S-Ap 14.

## S-Ap part 1 — public statement slice (2026-10-10)

- Approved P5–P7, P10–P16, P18, P21/P22 vocabulary: Join, executed gate reads,
  joined participation and recurrence, recovery readiness, and store/frame companions.
- P23 and DECISION P23-A changes wait for part 2 and W3's new root definitions.
- Import routing: gatePassedAt moves from Reads to Join with the exact P11 body.
  Join needs Reads for IsGateTick/storeAt; the reverse import would form a cycle.
  Channels imports Join. Public names and predicate meanings stay as approved.
- Packet elaboration context: schedule-only parameters p/c are implicit when they
  occur only in rho's type. Read predicates keep the explicit packet arguments.
  Reads supplies a local Decidable instance for the optional restart cutoff.
- Packet typo, r9 form (P10/P11 slot-labelled caught-up gate): caughtUpAtIdx's `∃ s j` infers s : Int
  from `(s : Int)` before gateTime requires Slot. Use `∃ (s : Slot) (j : Nat)`.
  This is a type annotation; its gate label, cutoff and quantifiers are unchanged.
- Slice validation: all 58 manifest source modules build with --wfail; layers have
  zero new findings. Claims.Tests.Axioms builds with the added statement audits.
- Manifest generation uses an untracked copy of V2Manifest.lean with only the
  facade-import loop omitted. Every source module in all four public prefixes
  and FGSAClaims.FGSAClaims is still scanned; hashing and entry selection are unchanged.
  The full facades import unfinished fixtures/P23. No checker or baseline is changed.
  The regenerated document also records inherited W1–W3 changes. Allow pins change
  only for entries in S-Ap source files; P-Da owns the remaining baseline reconciliation.

### S-Ap part 1 — remaining public companions

- P8/P9: recoveryStart routes the ready windows, old-row cap, H0Reset,
  healing/reset horizons, finality premises and WC recovery endpoint through tauC.
- P10/P20: output service, growth, LiveDC and healed statement readers use the
  approved joined/confirmed scopes. The family Claims conclusions stay with their owners.
- P12–P18: OutageContinuationSleepPrem and the derived receipt/E1 contracts are added.
  OutageContinuationConcl and its Claims wrapper stay with P-Ou as family conclusion text.
- P19: CleanContinuationSleep₂, CleanGrowthContinuationSleep₂ and SourcePendingReceipt
  route the public WC/WCG regime, delivery and bounded-recovery types as approved.
- P21(a): FinalizedMonotonicityRestartClaim replaces the aggregate field type.
  FinalizedMonotonicityClaim and its NoRestart premise are retained byte for byte.
- P22: FGFoundation and FGFoundationNext use RStoreDurable/RStoreEpoch, RMonoAll,
  and RFrameNextEpoch. Old R6 definitions and equations are unchanged.
- Source check: all 121 packet blocks marked to keep old text are present unchanged.
  P23, all DECISION P23-A root-premise changes, and the two W3-owned files are deferred.
- Structural test transfer (02:45 ruling): the two unchanged Axioms equality examples
  for ServedFromGateAt/InclusionAt and JointGrowthAt/AvailableGrowthConcl move to
  Tests.OutageAlignment. The production aggregate supplies their family claims.
  P-Ou owns their EXPECTED-FAIL until its approved P10/P20 claim text lands.
  Their statements and rfl proofs are unchanged. No exception/baseline is added.
- P7/P8 rename the obsolete gapWin and formWinAt exports to gapWinReady and
  formWinAtReady as approved. The matching audit commands use the new names.
- Claims.Tests.Axioms inventory regenerated from 813 compiled command owners.
  Only that audit key changes in scripts/proof-audit-coverage.txt.
  Complete compiled coverage: zero unaccepted exports; the equation baseline is unchanged.

### S-Ap part 1 — validation result

- GREEN: 432 modules, lake build --wfail PASS (4.76 s final run).
- S-Ap DCK: PASS (151.89 s), 35 strict audits / 3,276 results and all 24 controls.
  Only propext, Classical.choice and Quot.sound appear.
- Complete export/coverage check: PASS (6.73 s), zero unaccepted exports.
  Tracked Claims coverage check: PASS (4.67 s), 813 command/owner rows.
- Layers: 72 accepted findings, zero new (0.61 s).
- Source checks: 113 selected Statements blocks match, 121 fixed blocks unchanged;
  new Lean lines at most 100; no sorry/admit/axiom; W3-owned files unchanged.
- EXPECTED-FAIL: 50 modules with explicit owners. The only new test handoff is
  OutageAlignment to P-Ou (unchanged equality examples; failure confirmed in 7.25 s).
- Manifest generation: 58-module slice 84.64 s; 59-module companion surface 104.32 s.
  No package-full or G-S3 claim is made; P23 and family work remain with their owners.
## W3 — P23-A receipt scope and bridge (2026-10-10)

- DECISION P23-A, lead 04:05: keep P23 option (a). The receipt idealization includes
  honest emitted bodies and their named ancestors. It replaces the old root premise
  in receipt suppliers. No per-required NamedProposalInRun premise is added to P23.
  This decision closes the W3 core stop recorded above. The old ReceiptAlias trace
  remains a counterexample to the old form; it fails the new receipt idealization.
- New internal statements, P23-A: NamedProposalReceiptScope and
  NamedReceiptRootCollisionFree in Run/Statements/Roots. The old direct and ancestor
  scopes are unchanged. The docstrings state that a global form over all values is
  false because root is a free field. This is an idealization under valid execution.
- New internal statements, P23-A: namedReceiptScope_of_namedScope embeds old scope;
  namedReceiptScope_emitted includes each honest emitted body and its ancestors;
  namedReceiptScope_ancestor closes that scope under ancestry.
  NamedReceiptRootCollisionFree.toNamedRootCollisionFree supplies root_injective,
  including both old tips' ancestor alternatives. Consumers: NamedDelivery,
  Receipts, the ready core, and S-Ap's pending Base2.idealization projection.
- New internal statements, P23-A: proposal_trigger_in_receipt_scope splits emission
  from relay source acceptance. proposal_processed_in_scope extracts the exact
  named body of a processed FG root (genesis or MetaInv.treeWire/wireTree), gives
  that witness old scope, and identifies it with the receipt-scoped required body.
  It needs an honest receiver; it needs no history persistence or deadline receipt.
  emitted_proposal_history_in_scope applies this extraction to ProcessedByActionCut
  for an honest emission. proposal_trigger_service_in_scope uses the history bridge
  in DeliveryService's history arm, proposal_handle_in_scope in its handled arm,
  and the source acceptance in the relay arm. The anchor may be after emission.
  Consumers: Receipts, the ready core, WC/WCG scope readers, and family sleep readers.
- Changed internal statement, P23-A: fgsa_proposal_receipt replaces hRoots with
  NamedReceiptRootCollisionFree and drops hScope. Its Trigger supplies receipt scope;
  processing at the deadline and proposal_processed_in_scope supply old scope.
  AwakeOn, horizon, validity, NoRestart, deadlines, and the exact receipt remain.
  The new ready core is its active in-package caller. The old ReceiptCoverage
  wrapper is unchanged for S-Ap's explicit option (a) retirement.
- Out-of-package proposal callers: replace the root argument with receipt collision
  freedom, keep the approved readiness/horizon inputs, and remove any hScope input.
  Base2 callers use receiptIdealization after S-Ap changes that field. Flat argument
  lists must carry the stronger premise. These are family-owned argument swaps:

```text
┌────────┬─────────────────────────────────────────────────────────────────────┐
│ Owner  │ AvailableChainFGSAProofs/Proofs caller                               │
├────────┼─────────────────────────────────────────────────────────────────────┤
│ P-ShA  │ Shared/HeldReceipt.lean:80; Shared/GateReceipt.lean:198                │
│ P-ShA  │ Shared/ScoreRun.lean:497                                             │
│ P-Ou   │ Outage/ExactProposal.lean:71                                         │
│ P-WC   │ WeakContinuation/ExactProposal.lean:233                               │
│ P-As   │ Assembly/WeakContinuationGrowth.lean:397                             │
│ P-H1   │ Healing/PromotionReceipt.lean:128,200                                │
│ P-H2   │ Healing/RiseOneAccept.lean:93                                        │
│ P-H2   │ Healing/SupportRelay.lean:380; Healing/DescentLossNext.lean:128        │
│ P-H2   │ Healing/PostResetRaw.lean:1291; Healing/PostResetLeaseMove.lean:102    │
│ P-H2   │ Healing/SourceTiming.lean:293; Healing/PhaseRelay.lean:145,435         │
└────────┴─────────────────────────────────────────────────────────────────────┘
```

- WC ExactProposal:254 and Assembly/WeakContinuationGrowth:418 can use
  proposal_trigger_service_in_scope with the same ready service, or supply
  emitted_proposal_history_in_scope to the existing scope callback. Relay readers
  can still use proposal_handle_in_scope directly. Their old helpers stay available.
- INTENTIONAL DC divergence: P2 permits a processed-root service instead of another
  handler. Main's handler delivery excluded the alias trace only implicitly.
  PC-SA has the same root-keyed processedS pattern. Its P2 receipt port remains an
  open PC-SA-owned item; apply route A there. No PC-SA declaration changes here.
- S-Ap owns Base2.receiptIdealization, its old idealization projection, the public
  sleep statement/equation, public assumption lists, and retirement of the three
  legacy P23 names. Safety-only statements retain NamedRootCollisionFree. Families
  own stronger fixture evidence and their caller changes. No FGSAClaims statement
  or Base2 declaration is changed by W3.

## W3 — P23-A ready core, tests, and owners (2026-10-10)

- New internal statement, P23-A: fgsa_receiptCoverage_ready in
  Run/Proofs/ReceiptCoverageReady. It replaces NamedRootCollisionFree with
  NamedReceiptRootCollisionFree and adds the approved awake receipt windows.
  ReceiptCoveragePremises is unchanged. There is no per-required scope argument.
  The full finality/output/HEAD/lease/path/stamp conclusion is unchanged. Proposal
  receipt uses the exact processed-body bridge; the deadline and horizon bounds
  follow from the unchanged record. New proofs use default heartbeats.
- The core is in a separate module so S-Ap can retire the old wrapper and statement
  files under option (a). The Run facade imports the new core, but its legacy import
  remains until that retirement. The legacy files are unchanged by this job.
- Family coverage argument swaps: Shared/Count.lean:169 (P-ShA) and
  Outage/ContinuationReceipt.lean:128,178 (P-Ou) replace fgsa_receiptCoverage with the
  ready core or the S-Ap sleep wrapper. Pass receipt collision freedom and the
  approved readiness inputs; do not add per-required scope to the public form.
  The concrete ReceiptCoveragePremises producers and their required predicates
  stay unchanged. Their sleep migration remains with the family owners.
- Kernel controls: Tests/EmissionFreshness.receipt_roots_false refutes the new
  idealization on the original valid alias run. Tests/ReceiptAlias is unchanged
  and retains the negative control for the old form. Tests/ReceiptReady supplies
  full ExecutionValid and receipt collision freedom on a nonempty trace ending
  before the colliding emission. Its nonempty required predicate names the accepted
  slot-1 proposal. coverage_ready applies the new core and obtains its exact body
  in the receiver's tree at deadline 9.
- Registration: ReceiptCoverageReady and ReceiptReady are S1 REQUIRED and W3
  TARGETS/GREEN. Roots and NamedScope are explicit W3 targets. W3Axioms prints every
  new public theorem and both new definitions. The full Run audit and fixed owner
  inventory contain the same new production declarations. Test-local audits print
  the negative control and positive validity/root/premise/coverage results.
- The three current S-Ap-P23-STOP map owners are replaced by S-Ap: Run,
  Proofs/ReceiptCoverage, and Tests/Axioms remain EXPECTED-FAIL for public retirement.
  The other S-Ap and family-owned EXPECTED-FAIL entries are unchanged. Historic STOP
  records above describe the old boundary; P23-A closes the W3 scope/core item.
- Restore export fix 672dbc93 is present through lead merge 2eba122b. The complete
  export check will rerun against this fix and the new ready core, with no new
  baseline, allow-list, or exception entry.

## W3 — P23-A final validation (2026-10-10)

- Implementation commits: 53112f9f (scope/bridge), 82bf0910 (ready core/tests/maps).
- Final validation passes on 406 GREEN modules. The map retains 61 owned
  EXPECTED-FAIL modules. No W3 P23-A STOP remains. S-Ap still owns the legacy
  public retirement and full Run/audit roots; family argument swaps remain owned.
- DCK PASS: 35 strict roots, 2,482 results, all 24 controls. Only propext,
  Classical.choice, and Quot.sound occur. ReceiptReady prints all seven public laws.
- Complete W3 export/audit coverage PASS: 116 proof modules, 250 exports,
  0 unaccepted. The generated inventory has 97 entries across W3Axioms and the
  three receipt controls. It uses the same explicit-root boundary as prior W3
  checks, now including the ready core and controls. The default roots still
  reach the S-Ap-owned legacy wrapper. The 17 Restore exports are removed.
- No baseline, checker, protocol/model, FGSAClaims, Base2, or legacy P23 file
  changed. Layer check: 72 findings, 0 new. New proofs use default heartbeats.

```text
┌────────────────────────────────────┬────────┬───────────┐
│ Check                              │ Result │ Wall (s)  │
├────────────────────────────────────┼────────┼───────────┤
│ Focused core/tests/audit --wfail   │ PASS   │ 6.58      │
│ Complete GREEN --wfail             │ PASS   │ 54.51     │
│ Final GREEN --wfail                │ PASS   │ 10.91     │
│ W3 DCK + strict audits + controls  │ PASS   │ 403.38    │
│ Layers: 72 findings, 0 new         │ PASS   │ 0.39      │
│ Complete export/audit coverage     │ PASS   │ 38.20     │
└────────────────────────────────────┴────────┴───────────┘
```

## P-ShA — independent core and S-Ap handoff (2026-10-10)

- R6: Shared/StoreRun.fgsa_store_durable keeps TF, blocks, proposals and rowPool
  across restarts. fgsa_store_cumulative_on keeps the complete six-field tuple
  on restartFree rho x i j. The legacy fgsa_store_cumulative statement stays
  fixed and follows from the epoch form. Index endpoints are i ≤ k < j.
- N4 core: Shared/CatchUp.fgsa_catchUp_before_freeze uses the exact ReadyTrigger,
  HistorySafeAt, service law and receiver epoch. Its deadline is at or before
  freeze. Processing at the strict-before deadline persists to the strict-before
  freeze. The ready handler branch has a receipt strictly before the deadline.
  The retained-history branch needs HistorySafeAt; wake alone supplies no history.
  A fresh post-join anchor can use historySafeAt_of_fresh instead.
  Count, HeadAdmit and retained-proposal adapters remain open until the S-Ap slice.
- N7 supplier: fgsa_gate_joined_of_joinedEnv takes the approved environment
  restart bound at this exact gate and returns joinedAtTime on its pre-tick store.
  Consumers P-Cl1, P-Ou and P-WC can pass the restart projection of joinedAt.
  fgsa_joinedNow_noRestart keeps the legacy callers working at an existing tick.
- P11 bridge: fgsa_gate_saved_guarded proves the saved equation in both join
  branches. Its unjoined result is some none. Shared/Reads remains EXPECTED-FAIL
  until S-Ap installs the guarded executed read. The candidate adapter is in
  claude-files/psha-reads-after-sap.patch; it has not been compiled.
- internal statement, lead ruling 10-10: Relay.relay_gate_late and
  SameLabel.sl_gate_late were false with schedule alone. They now require hEpoch
  at their gate and keep the same strict late-pool conclusion. Every current
  caller supplies hEpoch from its existing NoRestart premise. Consumers:
  Relay.relay_head_witness and SameLabel.sl_relay (private).
- internal statement, lead ruling 10-10: fgsa_vote_accepted_before_head_read now
  takes ExecutionValid, since the exact receipt clock uses the awake delivery
  and wake laws. Its consumer relay_head_witness already has that premise.
- internal statement, lead ruling 10-10: the two OutputGrowthProposal helpers
  ending in _of_awake_slot need the approved joined proposer restart bound.
  Awake alone allows a restart at the proposal tick, which gates the emission.
  The conclusion is fixed. Sources are the joined proposer clauses in P6 and
  the family packet. Consumers: Shared/Claims; Outage/Growth;
  WeakContinuation/Growth; WeakContinuationGrowth/Empty; Finality/MiddleSupport;
  Healing/PromotionCarrier, LiveDC and Repair. Those family ports remain open.
- P23-A: GateReceipt and ScoreRun now use NamedReceiptRootCollisionFree for
  proposal receipts. Their callers pass the same receipt premise. A safety-only
  equality in ScoreRun projects toNamedRootCollisionFree. No hScope is added.
- Receipt caller repair: GateReceipt, Relay, SameLabel and ScoreRun supply the
  exact receiver awake interval and horizon bound. In the legacy NoRestart
  route, ExecutionValid at the existing receiver tick gives the interval.
  GateReceipt T41 uses its explicit selected-voter hawake. Its early actor tick
  follows from the existing gate tick and NoRestart. This does not close the
  sleep T42 route; that route must use the enabled-gate source below.
- Proof-only K/L repairs keep origin fields and use the exact wake clock law.
  OutputGrowthCausal splits tick and restart clock sources. Slot bounds use
  non-strict now ≤ tick where strictness is unnecessary.
- Validation scope: 14 former P-ShA failures are GREEN, together with the new
  CatchUp module, five support modules, Tests/BoundsW and Tests/SharedAxioms.
  No remaining owned EXPECTED-FAIL repair is closed. Package inputs retain the
  W3-owned and S-Ap-owned classifications. Default heartbeats are unchanged.
- Core validation: the 22-module green build passed --wfail (3.880 s).
  P-ShA DCK passed with all controls (259.627 s). The complete export check
  scanned 138 proof modules / 251 exports: 0 unaccepted (4.556 s).
  The green proof audit checked 149/149 results: only propext, Classical.choice
  and Quot.sound (3.224 s). SharedAxioms has 20 strict results.
  check-layers reports 0 new findings. The broad transparency check still has
  two inherited ClientTrace findings; W3 owns that file and its review fix.

## P-ShA — prepared files, not closed (2026-10-10)

- P23-A forwarding is prepared in Count, ExactHead, ExactService, HeadAdmit,
  RetainedPersist, RetainedReflect, RetainedEndpoint and Regimes. Receipt routes
  take NamedReceiptRootCollisionFree. Regimes forwards base.receiptIdealization.
  These modules remain EXPECTED-FAIL and have not been compiled against S-Ap.
- T39 RESTRUCTURE: exactService_head_of_proposal now has the approved joined HEAD
  reader scope. Its two Regimes adapters keep that scope. There is no live public
  caller on this tree. T45 is the active retained-proposal route.
- T45 SOURCED: exactService_head_of_retained_proposal and its Regimes adapters
  now require the approved joined HEAD reader at voteTime s. joinedAt.1 supplies
  the exact awake tick. P10 ExactProposalAt and P11 ExactService supply this scope.
  Recovery can also use its explicit awake clause. WC/WCG must retain this guard.
- T40 SOURCED, still open: ExactService's gate reader must use confirmedReaderAtIdx
  at gateTime v, whose first projection is awake there. Recovery's awake clause
  supplies the same exact tick with the existing GST and horizon bounds.
- T42 SOURCED, still open: recovery uses its explicit awake clause. Clean/WC/WCG
  pass the actor's enabled gate at gateTime s; cutoff slotStartZ s and the awake
  gate tick give the earlyTime s actor tick. Pass this source through
  exactService_gate_receipts_of_head and exactService_gate_raw_of_head.
  confirmed gate-reader scopes also produce this enabled gate. No universal
  participation inference is permitted.
- internal statement, lead ruling 10-10, prepared: healing_held_block_receipt
  takes the receipt collision premise and the receiver's awake state at its
  deadline. An arbitrary honest sleeping receiver is outside the delivery bound.
  Its legacy NoRestart route derives the earlier exact awake interval from that
  state. Consumers: Healing/PostResetConeReceipts, SourceTiming and FrameRelay;
  Finality/TailMixed. Their public scoped sources still need verification.
- RetainedReflect and RetainedEndpoint slot bounds now use now ≤ tick. Their
  conclusions stay fixed. HeadAdmit's early receipt gets its horizon and awake
  interval from the existing early tick; T43 keeps the selected voter's hawake.
- Remaining work after S-Ap: compile these prepared files; apply and compile the
  executed Reads and SameLabel extraction patches; port R1–R3/R7, exact gate
  guards and epochs; thread the N4 service proof through Count, HeadAdmit and the
  retained-proposal route. Keep all 31 owned proof failures and nine test failures
  visible until each target passes. No approved public meaning change was made.
## S-Ap part 1 — public statement slice (2026-10-10)

## S-Ap Round 2 — review pin repair (2026-10-10)

Updated all 253 stale exact-hash pins to the current `docs/FGSA-API.md`.
The allow-name set and frozen baseline are unchanged. The frozen manifest
check passes (6.04 s). This closes review finding 1 before DECISION P23-A.

## S-Ap Round 2 — public fixture classification (2026-10-10)

Replaced the removed `Base₂.noRestart` field in Claims tests Regimes,
HealingW, and FinalitySafety with `restartsAtWakes`.
The fixture probe still fails: sleep-validity fields and the P2 delivery
contract need repair; FinalitySafety also needs `CleanSleep₂`.
Regimes and HealingW have horizon zero, so they do not prove useful read
inhabitation. Their replacement sleep generator belongs to P-Fx. The
FinalitySafety run and receipt-scope table witness belong to P-As.

- GREEN: 432 modules, lake build --wfail PASS (4.76 s final run).
- S-Ap DCK: PASS (151.89 s), 35 strict audits / 3,276 results and all 24 controls.
  Only propext, Classical.choice and Quot.sound appear.
- Complete export/coverage check: PASS (6.73 s), zero unaccepted exports.
  Tracked Claims coverage check: PASS (4.67 s), 813 command/owner rows.
- Layers: 72 accepted findings, zero new (0.61 s).
- Source checks: 113 selected Statements blocks match, 121 fixed blocks unchanged;
  new Lean lines at most 100; no sorry/admit/axiom; W3-owned files unchanged.
- EXPECTED-FAIL: 50 modules with explicit owners. The only new test handoff is
  OutageAlignment to P-Ou (unchanged equality examples; failure confirmed in 7.25 s).
- Manifest generation: 58-module slice 84.64 s; 59-module companion surface 104.32 s.
  No package-full or G-S3 claim is made; P23 and family work remain with their owners.

### P-ShA round 2 — guarded reads and compiled consumer ports

Base: da94c7c2, with the S-Ap part 1 slice at 7538ca0f. No Claims statement changed.
Base₂ stays with S-Ap. The receiptIdealization field is not in this tree yet.

- Reads.gateResult_eq_saved now equates the executed result in both join branches.
  The empty result is saved when the gate is disabled. gateResultAt_eq_gateResult
  keeps the same guard at the event index. SameLabel and Roots extract the raw
  branch only through Reads.fgsa_gate_raw_of_nonempty, which derives the raw branch
  and joined test from the executed saved result. It avoids exports of the home
  module's local Decidable matcher equations. No baseline is changed.
- N7: CatchUp.fgsa_gate_joined_of_enabled uses enabledGateAt at the exact gate tick.
  fgsa_enabledGate_noRestart supplies the same gate scope for legacy NoRestart callers.
  Gate.fgsa_gate_of_coveringBatch and fgsa_S_eq_of_exact require that enabled gate.
  Every OpeningSource gateService adapter passes it to fgsa_gate_clock_bridge.
  The source actor, event index, and gate label stay the same through each call.
- P23-A: Count.fgsa_active_path_of_coverage now calls fgsa_receiptCoverage_ready.
  Its added hAwake supplies the receiver's entire required-object service window.
  Its conclusion is unchanged. The old wrapper is no longer in Count's imports.
  Clean/StepGate, Clean/TransferFrame, WC/StepGateBatch, WC/StepTransferReceipts,
  and WCG/Dynamics must supply hAwake when they port their callers. Their owners
  already own the old ReceiptCoverage-to-ready migration. No sleep closure is claimed.
- Count's honest HEAD identity and awake facts now follow network or replay provenance.
  A replay is traced to the retained proposal's earlier delivery and carried signature;
  it is not called a fresh HEAD acceptance. No new NoRestart premise was added there.
- Compose.HealAC.tsMono uses ScopedMono at the event-prefix reader scope.
  HealAC.tExact takes confirmedReaderAtIdx at afterTicksIdx of the exact gate time.
  Healed.same_time uses confirmedReaderIdx for both readers at the same event index.
  OutputGrowthReads.fgsa_healed_output_mono takes that scope at both inclusive reads.
  These are the approved S-Ap scopes. Caller owners must retain them in their ports.
- ProposalRead and RowReads extract proposal content after the joined duty guard.
  RetainedConsumers passes the guarded proposal's payload projection to geometry.
  RetainedScores and its consumer families use NamedReceiptRootCollisionFree.
  The RetainedEndpoint test now keeps joinedAt at voteTime s and the receipt root form.
- ExactService passes enabled gates through Gate and OpeningSource; it returns the
  enabled event witness and gatePassedAt. The general gate reader uses the awake
  projection of confirmedReaderAtIdx at gateTime v (T40). Its retained NoRestart
  premise supplies the existing enabled gate. HeadTargetAtEmission's safety equality
  uses toNamedRootCollisionFree. Its public ExactService result keeps the joined HEAD
  and confirmed gate-reader scopes. This legacy route is compiled, not a new epoch port.
- SelfDelivery preserves restartsAtWakes through row append and prefix cut.
  Its current constructor still uses the old idealization field. After S-Ap part 2,
  it needs receiptIdealization and receipt-scope preservation through append and cut.
- Regimes.fgsa_clean_delivery_iff compares deadlines at every nonnegative ready anchor,
  not only at the send time. Prefix cuts pass their event-derived horizon bound.
  These source repairs compile up to the remaining regime adapter failures.

### P-ShA round 2 — exact remaining obligations

- HeadAdmit.fgsa_action_walk_batch still calls inclusion_head_receipt_early with
  hb.noRestart (line 406) and hb.receiptIdealization (line 404). The latter waits for
  S-Ap part 2. Base₂ permits restarts: the former needs the N4 service/epoch port,
  joined selected HEAD voters, and the receiver's exact early-read service scope.
  Awake at voteTime alone does not supply the joined duty guard.
- Shared.Export.fgsa_sameLabelClaim and fgsa_releaseClaim still request
  h.set.noRestart (lines 18, 37). Their core producers need the approved local epoch
  scopes from the restarted regime; restoring a global NoRestart field is invalid.
- Shared.Regimes has twelve open adapters: gate receipts, retained scores,
  suffix ghost transfer, proposal HEADs, retained HEADs, and exact service,
  each for clean and recovery. Their calls still request h.base.noRestart and
  h.base.receiptIdealization. The receipt field waits for S-Ap part 2. The other
  premise needs local receiver epochs, ready service, safe retained history, and N4.
  Keep T39/T45 joined HEAD scopes; pass T42's enabled source gate and T40's exact
  confirmed receiver scope. No blanket honesty-to-awake inference is authorized.
- Tests.RetainedConsumers is blocked by its import of Shared.Regimes. Its three
  production consumer imports compile. No test exception or baseline was added.
- The external ReceiptCoverage wrapper, FGSARun root, and Run.Tests.Axioms remain
  S-Ap-owned EXPECTED-FAIL. No P-ShA green target imports that wrapper now.
- No approved public statement was found false by this run. No new public STOP was
  asserted. N4's generic bridge is compiled, but threading it through restarted
  Count, HeadAdmit and retained proposal families is not closed.
All three modules are now EXPECTED-FAIL in S-Ap with those owners.
The FGSAInhabit witness modules and tests, OutageContinuationInhabit, and
RowPermission are also classified with P-Fx/P-As. Positive inhabitants for
HealthyPrefixSleep₂, CleanPrefixSleep₂, CleanSleep₂, RecoverySleep₂,
OutageSleep₂, OutageContinuationSleepPrem, and both continuation companions
remain OPEN until the owner evidence is available. A type audit is not an
inhabitation proof. No premise was weakened to make a fixture pass.

## S-Ap Round 2 — DECISION P23-A (2026-10-10)

- DECISION P23-A: retired `ReceiptCoverageStatement`,
  `ReceiptCoverageStatement_def`, and `fgsa_receiptCoverage`. Removed both
  theorem audit commands and their inventory rows. The old proof module is
  an import-only compatibility path to `ReceiptCoverageReady`.
- DECISION P23-A: installed the approved `ReceiptCoverageSleepPremises`,
  `ReceiptCoverageSleepStatement`, and its home equation. The statement and
  equation use `NamedReceiptRootCollisionFree`; neither has a per-required
  `NamedProposalInRun` premise. `ReceiptCoveragePremises` is unchanged.
- DECISION P23-A: `Base₂` has one `receiptIdealization` field.
  `Base₂.idealization` is now a theorem with the old safety result. Its local
  ancestor proof keeps Claims independent of proof-module imports.
- DECISION P23-A: all 17 full emission-supplier telescopes in each of WC
  and WCG use the receipt premise, from Init through SeededFramePath.
  This keeps the shared validity/delivery/receipt assumptions consistent
  across the intermediate supplier stages. Standalone LowFinalized and
  WCFinalityTargetEarlier interfaces retain the old root premise.
  Safety-only Claims text is unchanged. Clean/ExactProposal, HealingInput/
  HTime, GST availability and growth, and finality-liveness public premises
  obtain the stronger field through Base₂. Family owners must update proof
  caller arguments; those proof implementations are outside this edit.
- DECISION P23-A: docstrings state why a global premise over all values is
  false (root is a free field), and why the P2/DC difference is intentional.
- DECISION P23-A: ReceiptAlias keeps the exact retired contract under the
  test-only name `ReceiptAliasTests.legacyReceiptCoverageStatement`.
  Its kernel counterexample remains. No production code imports that test.
- DECISION P23-A: regenerated all 59 public manifest modules. Updated three
  existing pins (two retirements and Base₂.mk); all 919 existing allow pins
  match. No allow name or frozen/deep/frame/layer baseline changed.
- DECISION P23-A: added separate Run and proof-interface P23 axiom audits.
  The full Run audit has five inherited stale names and remains assigned to
  W2b-audit. This does not hide those failures in the package map.

### DECISION P23-A — fixture evidence and remaining owners

FinalitySafety now constructs receipt collision freedom from a kernel-checked
emission/store table. Its P2 delivery proof uses a handler before receipt and
processed history after receipt. The concrete run has horizon 17, a non-genesis
proposal, an enabled proposal gate before the horizon, and an audited confirmed
reader at time 11. It constructs HealthyPrefixSleep₂, CleanPrefixSleep₂,
CleanSleep₂, and RecoverySleep₂, with joined recurrence. It is GREEN.

Regimes and HealingW now compile with the receipt field, sleep validity, P2
anchors, and sleep regime constructors. Their horizon-zero evidence remains
insufficient for useful-read validation, so their package classification stays
EXPECTED-FAIL/P-Fx until the sleep generator replaces it. This classification
records missing validation, even though the current modules compile.

OutageSleep₂ and OutageContinuationSleepPrem need the P-Fx sleep generator;
OutageContinuationInhabit is EXPECTED-FAIL/P-Fx. The two continuation companions
need the W1 witness and remain OPEN/P-As through the FGSAInhabit modules.
RowPermission remains EXPECTED-FAIL/P-As. No public premise was weakened.

### DECISION P23-A — final validation

S-Ap DCK PASS in 169.90 s: 440 GREEN modules, 39 strict audits,
3,342 axiom results, and all 24 controls. Only propext, Classical.choice,
and Quot.sound occur. The separate GREEN build passed in 26.91 s.
The standard frozen manifest check passed in 24.01 s; all 919 pins match.
Complete Claims, Run P23, WC, and WCG export checks have zero unaccepted
exports. check-layers reports 72 accepted findings and zero new (0.32 s).
The three changed fixtures build with --wfail (18.10 s); strict smoke audits
also pass, without claiming useful reads from their horizon-zero runs.
Default heartbeats, no proof placeholders, no baseline changes.

The full supplier telescope changes cover these suffixes under both WC and
WCG, each ending in Statement: Init, StepDelivery, StepNoGateTick, StepGateTick,
StepRestart, Step, SeededInduction, Service4, SeededFrame, FinalBelow,
ProposalPivot, ProposalAdmission, ExactProposal, Inclusion6, Retrospective,
SeededFrameLive, and SeededFramePath.


## P-ShA round 3 — local receiver receipt APIs, with open targets

Base: 46a95cad (S-Ap parts 1 and 2; P-Fx). P-ShA is not closed.
The Base₂ receipt field now exists. No FGSAClaims statement or S-Ap proof was edited.

- Shared/SelfDelivery: Base₂.snoc_ownRow and Base₂.cutAt preserve the single
  receiptIdealization field. Delivered and held scope use the existing named-scope
  restrictions. Honest emitted scope uses emits_snoc_deliver_iff and emits_cut_iff.
- Shared/Release: fgsa_release_bound_restart uses the network signature source of
  an accepted or replayed HEAD. Replay obtains the earlier carried delivery from
  fgsa_replayed_head_delivery_origin. No receipt deadline or NoRestart is needed.
  The legacy API remains as a wrapper. Shared/Export's ReleaseClaim uses this core.
- Shared/CatchUp: fgsa_historySafeAt_of_emitted_head supplies safe history for the
  exact fresh emitted HEAD at its action cut. fgsa_head_receipt_on threads the
  exact ReadyTrigger, HistorySafeAt and restartFree from actionCut a to idxBefore
  freeze through N4. It returns current processing at the deadline and freeze.
- Shared/GateReceipt: fgsa_gateReceipt_stamps_on preserves vote and block stamps
  under restartFree rho x j i. The legacy wrapper derives that local interval.
- Tests/RestartEpochs: two kernel checks use local copies of the existing valid
  SleepTests fixtures. A bare HEAD processed before sleep need not be processed
  after restart; an awake HEAD tick need not pass joinedNow. The original full
  validity proofs remain in Run/Tests/Sleep, with no cross-test import added.

STOP: fgsa_action_walk_batch still concludes a WalkBatch over all honest selected
HEAD seats from hawake alone. Let the single honest validator wake and restart at
voteTime s, with horizon earlyTime s and no retained proposal or received HEAD.
Choose s = q * R + 1, Q = genesis, and the initial finalized floor. The two public
awake ticks exist, Base₂ and LabelSyncOn hold, and the batch count exceeds zero.
The HEAD duty is suppressed by joinedNow; the HEAD pool is empty. The WalkBatch
membership conclusion is false. This target needs joined selected voters and the
receiver's exact service scope. No changed public statement was installed.

STOP: fgsa_gateReceipt_clean and fgsa_gateReceipt_recovery quantify awake selected
HEAD voters and conclude their actual HEAD emission. A selected voter waking at
voteTime s has joinedNow = false and emits no HEAD. For Clean, keep other honest
validators awake so the strict prefix participation bound holds. For Recovery,
choose GST = voteTime s and wake the selected voter at GST; keep it awake thereafter.
Take genesis floors and covered prefix so the geometry implications hold. Delivery
cannot supply a nonexistent emission. Both adapters need the joined voter scope.

No false conclusion was established for the other ten Regimes adapters or for
SameLabelClaim. Their local receiver epoch and service ports remain unfinished.
Their current calls still request the removed Base₂.noRestart field. Do not infer
safe history for arbitrary retained HEADs: the tested valid ownRun fixture processes
ownHead at state index 12, but loses it at the restart action cut at time 35.
The exact retained service/history obligations must be discharged, not assumed.
Tests.RetainedConsumers still waits for a compiled Regimes module; its local
Composes statement also retains the old unguarded honest-reader quantifiers.

S-Ap input status: the retired ReceiptCoverage import path compiles in this merge.
Run.Tests.Axioms fails on fgsa_restore_now_retained, fgsa_hrestore_now_retained,
restore_st_retained, spec_prune_restart_mem and spec_prune_sleep. Run's facade
imports that audit. P23Axioms compiles. No S-Ap file was edited. The ReceiptCoverage
EXPECTED-FAIL map entry remains under S-Ap ownership after automatic review rejected
its proposed status change. The P-ShA map adds the required merged P23 audit input.

Validation and exact source locations are in claude-files/sleep-psha-report.md,
Round 3. Only compiled green modules are covered by the successful checks.

## P-H1 — internal helper repairs (2026-10-10)

Base: 1c777e973b07b6824debbe8e775401dabc6feb08, branch sleep-ph1.
The writer brief assigns FrameRelay and the other depth 0–12 Healing proof
modules to P-H1. FGSAClaims statements remain with S-Ap and are unchanged.
The job explicitly permits an internal statement that is false under sleep to
be replaced by its exact true form, with this ledger row. Lean `public` visibility
of a proof helper does not make it an approved FGSAClaims public statement.

- FrameSource/FrameZero: restart keeps the block store and clears fast writes.
  The induction uses the predecessor invariant, not an initial-store invariant.
  A fresh gate appends an empty fast row when its join guard is false.
- SupportSaved: gateStep_other preserves each other saved label in both branches.
- SupportWrite: healing_support_fastWrite needs the exact joinedAtTime guard at
  the gate. healing_support_phaseBody_of_write derives it from its executed
  nonempty gate result. A same-time wake can suppress an otherwise nonempty raw
  fast set, so the old unconditional equality is false (GF).
- SupportTicks: healing_support_vote_tick needs awake at its exact node and vote
  time. healing_support_honest_emits also needs joinedNow at that tick. A wake
  at the vote tick supplies awake but suppresses the HEAD duty (T23/JOINED-VOTER).
  The declarations move from SupportHeads into an independent owned helper.
- SupportRelease: healing_support_release_rows needs joinedAtTime at the release.
  The old strict count is false when a wake suppresses release. The declaration
  moves from SupportTransfer into an independent owned helper (RR).
- SupportRelay: healing_support_gate_late needs the gate epoch/join guard for
  strict stamps. Receipt suppliers use NamedReceiptRootCollisionFree (P23-A).
  Retained receipt paths keep explicit NoRestart; no retained history is inferred
  from earlier processing. No family sleep receipt closure is claimed.
- FrameRelay, proposed exact internal form: receiver awake at the receipt
  deadline guards healing_witness_relay and healing_witness_relay_phase.
  Counterexample to the old form: an honest receiver stays asleep throughout a
  no-restart prefix while a different honest source holds a non-genesis witness.
  Its initial finality is below the witness, but no delivery to that receiver is
  required. The unchanged source and frame premises cannot give receipt.
  Consumers: SupportFrame.healing_witness_relay_settled and
  SupportFrame.healing_head_witness_relay supply recovery awake at that deadline.
  No FGSAClaims statement or approved public meaning changes. This internal
  correction is within the job's explicit replacement rule; it is not a new
  premise on the approved public recovery claim.

### P-H1 prepared audit and exact forms

- PhaseRelay and SupportFrame: retained receipt consumers keep receiver awake at
  the exact deadline. The second evidence-spread arm derives earlier awake from
  its actual later receiver tick only with valid execution and explicit NoRestart.
- DescentTiming.healing_delivery_clock: valid execution supplies the public-action
  clock bound with exact wake-time restore. Mere ScheduleWellFormed does not
  require sleeping ticks to execute. The callers already provide valid execution.
- Tests/HealingDescentTiming: the restart at time 7 has clock 7, not the earlier
  action time 6. The fixture retains its event list and schedule/non-NoRestart checks.
- Time: the recovery-start horizon is used by HTimeStatement. Its composition
  retains the old stronger producer statements and proves GST ≤ recoveryStart.
  The proof has no exported generated equation and changes no FGSAClaims text.
- Strict prepared audit: 62 exported theorems from 14 owned core modules.
  Complete export check: 147 proof modules, 252 exports, 0 unaccepted.
  Global inventory and facade edits are serial lead work. The owned fragment is
  scripts/dev-pkg/P-H1.coverage-fragment.txt, under the existing full audit key.

### P-H1 PREPARED on sleep-ph1 (2026-10-10)

The prepared map has 98 targets: 75 assigned proof modules, 20 assigned tests,
two independent helpers, and one local strict audit. Its S1 REQUIRED union TARGETS
classification has 494 GREEN and 72 EXPECTED-FAIL entries. Later targets retain
P-H1 ownership; inherited REQUIRED failures retain P-ShA or S-Ap ownership.

- Final GREEN lake build --wfail: PASS, 5.03 s.
- DCK PASS (package P-H1), default controls: 433.59 s; 24 controls passed.
- Strict audits: 39 roots, 2,859 results; only the three permitted axioms.
- Complete prepared exports and coverage: 147 proof modules, 252 exports,
  0 unaccepted; 8.93 s. Local Healing audit: 62 results.
- Layers: 72 findings, 0 new; 0.35 s. git diff --check: PASS.

This status covers the checked prepared set on this branch. It does not assert
integration, review, family closure, or a full gate. P-ShA round 4, S-Ap roots,
P-Fd lease/service inputs, P-Fi MiddleSupport, later H1 epoch ports, and the lead's
serial audit integration remain open. No requested external or public-claim edit
was made. No protocol declaration, default heartbeat, checker, baseline, or
allowance changed. Evidence is under .lake/sleep-ph1/.

### P-H1 — prepared consumer extension (2026-10-10)

- PromotionCarrier.healing_promotion_slot_proposal needs the exact proposer
  restart/join bound. Awake alone is false: a proposer can wake at its proposal
  tick and have its duty suppressed. No proposal exists to carry its rows.
  The internal gap producer now takes RecoverySleep₂; it derives the selected
  proposer's join bound from suffixNoRestart and the existing lower proposal bound.
- FrontierSearchAge.frontierSearch_age_service uses the same approved sleep
  companion. Its carrier lower bound places the previous slot start after GST.
  It derives the exact join bound without a global NoRestart premise.
- LiveDC.healing_liveDCFromWindows proves the existing approved statement.
  It selects through joinedGap, restricts stable comparisons to confirmedReader,
  and preserves finality and strict-before acceptance through durable restore.
  It does not construct a new RMonoAll companion or change a public claim.
- PhaseRelay, SupportFrame, PromotionCarrier, PromotionRows, LiveDC, and
  FrontierSearchAge passed --wfail and move from P-H1 EXPECTED-FAIL to GREEN.
- Eight existing named awake witnesses are threaded through owned T23 callers.
  These later modules remain EXPECTED-FAIL. Joined duty and receiver epoch ports
  still need the P-ShA round 4 interfaces and the P-Fd producers.
- The expanded local strict audit has 81 commands. The serial integration
  fragment stays under the existing full audit key. No key or allowance is added.

### P-H1 final prepared extension — validation (2026-10-10)

Status: PREPARED on sleep-ph1; not CLOSED. The map still has all 98 TARGETS.
The final classification has 500 GREEN and 66 EXPECTED-FAIL entries: 38 assigned
GREEN targets, 60 assigned P-H1 targets still open, and 6 REQUIRED supplier failures
(counts corrected by the lead from the map, rev-ph1-astra finding 2).
No REQUIRED entry moved to DEFERRED or to a different repair owner.
H2 handoff: the complete caller checklist is rev-ph1-astra findings 1 and 6
(/Users/francesco/.claude/jobs/22f59f85/tmp/tmp/rev-ph1/review.md): held receipt, promotion
slot proposal restart bound, 19 healing_support_vote_tick calls, and the other changed interfaces.

- Final GREEN lake build --wfail: PASS, 2.49 s.
- Final DCK PASS (package P-H1): 179.93 s; all 24 default controls passed.
- Strict audits: 39 roots, 2,878 results; only the three permitted axioms.
- Expanded local strict audit and complete coverage: 81 declarations.
- Complete exports: 160 proof modules, 252 exports, 0 unaccepted; 7.30 s.
- Layers: 72 findings, 0 new; 0.60 s. git diff --check: PASS.

Closure still needs the P-ShA round 4 interfaces, S-Ap roots, P-Fd companion
producers, P-Fi MiddleSupport, remaining H1 epoch/caller ports, and serial audit
integration. The report lists each GREEN and EXPECTED-FAIL target, the changed
files and declarations, all internal replacements, and the exact caller audit.
The optional SupportRecovery module is not present: automatic approval review
rejected it as outside the prepared scope, and the text approval request is pending.
No FGSAClaims statement, protocol declaration, checker, baseline, allowance, or
heartbeat changed. Report: claude-files/sleep-ph1-report.md.
## P-Fd — durable and epoch Foundations suppliers (2026-10-10)

Base: 1c777e97, with sleep-int 8c838f3b and P-ShA rounds 1–3.
Only P-Fd proof, test, map, and ledger files are changed. S-Ap retains
Claims/Foundations.lean until its serial transfer. Public meaning STOP: none.

- RStoreDurable: fgsa_rStoreDurable uses Shared.fgsa_store_durable for TF,
  blocks, proposal wires, and signed rows across all restarts.
- RStoreEpoch: fgsa_rStoreEpoch uses fgsa_store_cumulative_on on the exact
  restartFree rho x i j interval for block and vote stamp prefixes.
- RMonoAll: fgsa_rMonoAll keeps F, (h_j, J), and h_max through acRestart_fg.
  RMono stays as the legacy NoRestart wrapper.
- RFrameNextEpoch: fgsa_rFrameNextEpoch keeps the existing local frame equations,
  uses durable proposal/row prefixes, and scopes stamp prefixes to the local epoch.
- Finalized monotonicity: the P21 restart companion uses the W3 kept-F restart law.
  FinalizedSafety uses RMonoAll and keeps the public conclusion.
- Lease K/S uses: retained obligations keep their actual gate source and deadlines;
  restart fast pairs are empty by acRestart_fastWrite. No empty-lock assumption
  remains. The target bound and ancestor deadlines survive retained-store replay.
- K origins in Accountable, Carrier, and Sources retain origin and bound projections.
  Emitted carriage/source proofs split the joined duty guard; no premise is added.
- RowPermission: lock carriers use durable TF membership. The actual RecoverySleep₂
  suffix supplies confirmedReaderAtIdx at an exact gate after its join cutoff;
  OpeningCovered and OpeningCoveredLower consume that evidence.
- Tests.RowPermission: the one-validator tick fixture supplies SleepWellFormed,
  RestartsAtWakes, and NamedReceiptRootCollisionFree. Its receipt scope has only
  genesis: there is no delivered proposal and no emitted object.

Internal statement replacement: fgsa_leaseOrigins_lastWrite now restricts the later
key exclusion to a joined pre-gate state. At an unjoined gate the retained view can
have raw confirmationFrom and gateWriteKeys, but the executed gate writes no lease.
The old raw-key exclusion does not follow. The source, deadline, chain, fast-write,
and ancestor conclusions are kept. Consumers: Healing SupportWrite/PostReset/Frontier/
RiseOne, Assembly Healing/ResetArrival, their tests, and NonVacuity.HealingRun.
They must pass the joined guard when they reason about the later executed gate.

Internal statement replacement: fgsa_rowService_receipt and T-ROWS producers use
P8's all-honest awake suffix. A permanent sleeper satisfies the old NoRestart and
vacuous P2 demand, but has no row at the deadline. Pre-GST sends use max(send, GST).
fgsa_rowsReceipt_carriage has the same conclusion and no NoRestart requirement;
it uses durable row and proposal prefixes.

The package-local FoundationsAxioms root checks all changed public theorem bodies.
The complete audit inventory and canonical-root registration are handed to the lead
as a fragment; no new canonical coverage key or allowance is installed.
Preparation validation and status are recorded below after the checks finish.

P-Fd PREPARED: DCK PASS on 490 GREEN modules and 7 EXPECTED-FAIL modules
(174.82 s), with 38 strict audit roots and the default controls PASS.
The local root has 108 audit commands. Complete exports and complete local
coverage: 147 proof modules, 251 exports, 0 unaccepted (6.23 s).
Layers: 72 baseline findings, 0 new (0.38 s). No allowance or baseline changed.
CLOSED still waits for the S-Ap Claims/Foundations transfer and P-ShA round 4.
The remaining owned RowService restart adapter is continued after this checkpoint.

### P-Fd — restart-safe row service follow-up

fgsa_rowService_receipt_sleep, fgsa_tRowsReceipt_sleep, fgsa_tRowsSync_sleep,
and fgsa_tRows_sleep use the exact receiver epoch from actionCut(max(send, GST))
to idxBefore(deadline). A restart at the anchor is already in the action cut.
Safe row history follows from durable rowPool prefixes, not from a claim about
retained HEAD processing. The valid run's exact wake clock proves row timeliness.
The prepared NoRestart interfaces remain wrappers with the approved awake suffix.

rowService_epoch_of_recovery derives the post-GST epoch from Recovery₂.awake
and Base₂.restartsAtWakes. Thus fgsa_tRows_recovery proves all three row clauses
from Recovery₂, with no global NoRestart assumption. RecoverySleep₂ can use it
through toRecovery₂.

The unchanged Foundations.Export target has three remaining ports: the
FGFoundationNext companion tuple, the approved P8 awake suffix, and the
RowServiceClaim call to fgsa_tRows_recovery. Four serial export fragments,
including the P21 public restart companion and the exact P8 predicate, compile
in isolation with strict permitted axioms (12.64 s). They are handed to the lead;
Claims/Foundations remains S-Ap-owned. No public meaning change is requested.
Final package validation is recorded below after the DCK finishes.

P-Fd follow-up validation: DCK PASS, 490 GREEN / 7 EXPECTED-FAIL, 38 strict
roots, 114 local audit commands, all default controls PASS (168.53 s).
Complete exports and complete local coverage: 147 proof modules, 251 exports,
0 unaccepted (5.19 s). Layers: 72 baseline findings, 0 new (0.46 s).
The package remains PREPARED. CLOSED requires the S-Ap claim transfer and
P-ShA closure. Archived P-ShA round 4 (8384eb34) is NOT CLOSED: Shared.Export,
Shared.Regimes and Tests.RetainedConsumers remain open. That supplier commit
is not installed here; this branch keeps its base classifications and interfaces.

## P-Fi prepared core — sleep-pfi at base 1c777e97

The P-Fi prepared set is in scripts/dev-pkg/P-Fi.txt. It has 473 GREEN modules
and 36 EXPECTED-FAIL modules. No package closure or full gate pass is claimed.
DCK PASS: --wfail, strict audits, and default negative controls (317.69 s).
Complete compiled exports: 104 proof modules, 251 exports, 0 unaccepted (15.16 s).
Layers: 72 accepted findings, 0 new. No heartbeat or baseline value changed.

- P-Fi / P9 / D045-D047, D051: Claims/Finality uses recoveryStart in first/GST
  deadlines, RecoverySleep₂ for KernelACSideClaim_W, and confirmedReader for
  record growth. These are the approved packet replacements, not new meanings.
  Strict checks are at the end of the owning claim module; no foreign audit
  import or new coverage key is needed.
- P-Fi / durable finality: Finality/RestoreReads proves strict-before acceptance
  from an index witness, deadline monotonicity, and ancestor monotonicity through
  restore. Finality/Accept uses the new index bridge. Consumer: fgsa_acceptBefore_W
  and fgsa_finalizePending_W. F remains durable; no global NoRestart is inferred.
- P-Fi / exact receiver scope: Finality/RecoveryScope bounds honest restarts by
  GST, derives restartFree on the specified event-index interval, and supplies
  joinedAt only when GST is below the inclusive join cutoff. Consumers: later
  Finality middle, tail, proposal, and receipt ports. These internal suppliers
  preserve all receiver, label, time, and horizon conditions.

P-ShA open imports: Shared/HeadAdmit and Shared/Regimes prevent validation of
Finality rows/frame/receipt consumers. Do not replace their interfaces locally.
P-Fi still owns the CoreServices, Rows, MiddleSupport, and later family ports.
S-Ap/Run audit inputs retain the map owners from the P-ShA handoff. The package
report carries the audit inventory and root-import fragments for lead integration.


## P-Fi second prepared group — exact current services and joined reads

The P-Fi map now has 43 TARGETS, 480 GREEN, and 31 EXPECTED-FAIL modules.
Frozen DCK PASS (170.53 s), default controls; 41 complete audit commands pass.
Compiled exports: 143 proof modules, 251 exports, 0 unaccepted (10.48 s).
Layers remain 72 accepted findings and 0 new. CLOSED is not claimed.

Internal false statement: fgsa_tVote previously took Base₂ alone and returned TVote.
The kernel-checked Tests/FinalityEpochs.base_not_tVote proves Base₂ and not TVote:
Δ=2, n=1, R=2, δt=4, events tick(0), tick(2), restart(7), tick(8).
The honest node sleeps on [3,7), emits HEAD-0 at 2, and has an unjoined proposal
read at 8. The vote pool is empty. LabelSyncOn uses dl(a)=max(a,2)+2 and cut=8;
its receiver-link premises are false on every demanded window. Receipt root scope
is only named genesis. This is a Base₂ counterexample, not a full counterexample
to KernelACSideClaim_W with RecoverySleep₂ and HealingInput.

Exact internal replacement: FinalityVoteReceipts records the current raw vote
membership at each exact batch and post-clock read. core_full_vote, fgsa_tVote,
and fgsa_coreServices require it and keep the full service conclusions. The
resolved-head filter is proved from those receipts. Consumers: Finality/Joined,
Finality/Export and Finality/Forward (Forward.lean:156 builds CoreServices without the
new receipt argument; lead note from rev-pfi-astra finding 1). Their supplier obligation remains open; do not infer it from
historical processing or from Base₂. No public claim was weakened or redefined.

JOINED-VOTER ports: kmid_honest_proposal_exists and kmid_head_held take joinedAt
for the exact proposer/voter, label, and time. kmid_source_of_exact takes the
confirmed gate reader. kmid_window_proposal derives its joined proposer from
Recovery₂, the full witness bounds, and the inclusive cutoff. The current HEAD
chain and held-target suppliers use that exact read and durable TF, not global
NoRestart. TickRead proves read equality from no restart at that same node/time;
the joined HEAD guard supplies this exclusion. Consumers: Middle, Kernel,
TailOpening, TailMixed, RowsPrem, and TailFrame; their call ports stay P-Fi-owned.

Finality/action source uses recoveryStart, joined HEAD readers, and the exact
confirmed gate reader. The full source/height/entry conclusion is unchanged.
The row-action proof now handles the joined branches of HEAD and proposal duties.
The other valid fixture proves a fresh honest HEAD can be processed, then erased
at restart while its receiver is awake. It does not use old processed history as
safe history. Both fixture validity proofs and all changed declarations have
strict checks with only propext, Classical.choice, and Quot.sound.

Serial audit fragment: claude-files/sleep-pfi-audit-fragment.txt. Add production
commands to the existing Proofs.Tests.Axioms key at integration; keep fixture
checks in their own module. Do not create an S1 key or import a test into a test.


## P-Fi final prepared handoff — receipt core

P-Fi remains PREPARED, not CLOSED. The final map has 43 TARGETS, 482 GREEN,
and 29 EXPECTED-FAIL modules: 23 P-Fi, 3 P-ShA, 3 S-Ap. All remaining P-Fi
import closures reach Shared/HeadAdmit or Shared/Regimes. No supplier file was
changed. The new current-scope caller obligations remain P-Fi-owned.

Final DCK PASS with --wfail, 39 strict audit sources, 2,866 commands, and
24 default controls (747.67 s, including global throttle waits). Complete
compiled exports: 152 proof modules, 251 exports, 0 unaccepted; 56 complete
coverage commands (63.68 s). Layers: 72 accepted, 0 new (0.50 s).
Receipt and TailReceipt build with --wfail (16.39 s). Default resource values
and all allow/baseline entries are unchanged.

Receipt/receipt_ready_of_delivery uses delivery_now_ge_public_atRestart and
the exported clock equation. It proves admission from the checked delivery,
public action time, dependency, freshness, parent, row, and finality facts.
No handler event is treated as acceptance by itself, and no public-wake
premise or global NoRestart is added.

Receipt/receipt_delivery consumes P23-A: the processed-root alternative gives
NamedProposalInRun through emitted_proposal_history_in_scope and the receipt
idealization. Scoped fresh emission excludes prior processing at the action
cut, so the demand supplies an actual handler strictly before the deadline.
The receiver's named awake suffix supplies its link window. Both F comparisons
use durable restore preservation. All receipt conclusion types are unchanged.
Consumers: receipt_acceptPrem_W and TailReceipt's four compiled suppliers.
The inherited receipt_stored_block already consumes the retained-content
stored_proposal_delivered interface; its durable historical origin was kept.

The lead receives 17 new production audit inventory entries in
claude-files/sleep-pfi-audit-fragment.txt for the existing Proofs.Tests.Axioms
key. Fixture checks stay in their own test file and package targets. No new
S1 key or test-to-test import is needed. Final report and declaration census:
claude-files/sleep-pfi-report.md; claude-files/sleep-pfi-declarations.txt.
No new public-meaning STOP was established. The Base₂-only TVote STOP and
exact current-receipt replacement remain recorded in the preceding P-Fi block.

### Lead notes after the P-Fi review (2026-10-10)
- scripts/dev-pkg/P-Fi.txt keeps AvailableChainFGSARun.Proofs.ReceiptCoverage as EXPECTED-FAIL, but that module
  now compiles as a retired import path over ReceiptCoverageReady (rev-pfi-astra finding 2; P-ShA round 4 map has
  it GREEN). The entry is stale, not an open proof. Reclassify it at the next P-Fi/S-Ap map refresh.
- docs/ARCHITECTURE.md:629 still describes the old restart model (keep last tick, ignore restart time). One docs
  pass updates ARCHITECTURE.md and MAP.md after the P-ShA supplier surface is final (rev-psha3 finding 8,
  rev-pfi-astra finding 3): RecoveryScope, RestoreReads, TickRead, CatchUp, CoreServices, joined middle reads.
## P-Cl1 — prepared gate and epoch suppliers (2026-10-10)

Base: 1c777e97 on sleep-pcl1. This block belongs to P-Cl1.
The package is PREPARED on the gate/epoch set. It is not CLOSED.
The full Clean induction and the arming export are still open.

- GR, internal statement, lead ruling 10-10: StateGate.clean_gate_raw now takes
  enabledGateAt. GateEpoch.clean_gate_executed gives the exact guarded equation.
  clean_gate_nonempty_raw extracts the enabled/raw branch from an executed result;
  clean_gate_unjoined gives some none for a suppressed gate. Consumers:
  StateGate, StepGate, TransferFrame, GateOutput. The last three remain open.
- GF, internal statement, lead ruling 10-10: clean_gate_writes appends fastSet only
  in the joined branch. Its suppressed row is empty. Lease and fast-write proofs
  derive the guard from the nonempty executed result. No raw-result premise was added.
- The Chain bridges include the guard required by S-Ap's cleanResults. The
  index-result bridges take ScheduleWellFormed, which their run consumers have.
- T08/T12 supplier: clean_enabledGate_awakeClosed proves the exact receiver's
  closed interval from t_s through gate(s). It uses the valid tick, wake restart,
  and the current stored marker. This includes label 0 and its early cutoff.
  The StepGate consumers are still open; these rows are not closed as use sites.
- T10 supplier: clean_joined_gate_witness chooses z from joinedHonest at the
  earlier gate time. It gives z's actual enabled gate and its awake interval.
  It does not claim that the later actor x had an enabled earlier gate.
  The ordering/transfer use in StepGate is still open.
- S/R7 supplier: clean_restart_fields keeps FG, blocks, leases and stableRecord,
  and starts empty genuine/fastWrite caches. cleanHist_step_restart preserves
  completed event history. clean_gate_fg_before_time compares only the kept FG
  fields with the strict time read; it does not assert whole-store equality.
  State/Closure still need their current-epoch induction port.
- N4 receiver supplier: clean_enabledGate_service_epoch returns restartFree on
  [actionCut a, idxBefore freeze] inside this gate's receiver interval.
  HistorySafeAt remains a separate input. Past processing does not supply it.
- Regression: Tests/CleanSuppressed has a well-formed schedule with wake 9 and
  a fresh HEAD at 10. At gate label 1 (time 20), raw confirmation is some genesis;
  the executed result is some none. This refutes the old unconditional raw equation.
- Public FGSAClaims statements and other owners' files were not edited.
  STOPs for approved public meaning changes: none.
- Audit/root inventory changes are in the P-Cl1 report and its audit fragment.
  The existing shared inventory and fixed S1 scope were not changed. These new
  Clean modules are outside the fixed S1 domain and are explicit package targets.
- Prepared validation: package DCK PASS with default controls (164.99 s; first
  cold package run 458.04 s). Prepared audit-root build --wfail PASS (4.78 s).
  The 48 core audit commands and three regression commands use only propext,
  Classical.choice and Quot.sound. Complete export/coverage check: 0 unaccepted
  (7.04 s). Layer check: 72 baseline findings, 0 new (0.30 s).

### P-Cl1 — current epoch invariant and joined batch (2026-10-10)

The prepared set now includes State, Action, GateOutput and Zero. The package
remains PREPARED, not CLOSED. Five P-Cl1 targets remain EXPECTED-FAIL.

- Internal statement, lead ruling 10-10: CleanHist.nonempty now requires
  enabledGateAt, including label 0. CleanHist.continues requires the joined
  voter at the exact next vote tick. CleanGateOutputStmt requires an enabled
  gate. These are the P6/P11 forms; no FGSAClaims file was edited.
- Internal statement, lead ruling 10-10: CleanState.saved requires the local
  restartFree interval and activeCompatible at the read. savedOnly and
  fastWrite origins include restartFree and an enabled origin gate. Durable
  S and lease origins still use completed event history from all epochs.
- Internal statement, lead ruling 10-10: CleanRestartStep no longer eliminates
  a restart. It states preservation of CleanState after the kept-state restart,
  under the existing foundation and source premises. State.clean_restartStateStep
  proves it. cleanState_of_hist now handles that event. Closure's restart branch
  uses cleanHist_step_restart; the full Closure module still waits for StepGate.
- R7: clean_gateInputs_from_rows uses the kept FG equality at the strict time
  cut. No whole-store equality or global NoRestart is used. The state proof
  uses RMonoAll and the durable/epoch foundation split. Zero excludes a restart
  at time 0 from RestartsAtWakes, rather than from global NoRestart.
- T07 source: clean_enabledGate_of_confirmedReader gives this gate's enabled
  guard from the exact confirmed reader at afterTicksIdx. Safety is still open.
- T10 core: clean_gate_head_prefixes_joined orders older results through z's
  earlier joined gate, then uses Continues for the joined voter y. The current
  actor x is used only for the F/frame part. It compiles with default heartbeats.
  StepGate.clean_gate_head_prefixes delegates to this exact interface.
- P6/T09/T11/T12 sender source: clean_gate_batch_joined counts joinedHonest at
  the vote tick. clean_joinedNow_of_joined_vote supplies the stored duty guard.
  StepGate now selects joined voters and keeps that guard in the HEAD emission.
  Its gate-zero and nonempty types require the enabled gate. N5 is still open.

P-ShA request: Shared/Count.lean:242 fgsa_late_rest_bound, :277
fgsa_gate_batch_premises, and :351 fgsa_gate_zero_of_receipts still require
all awake honest seats to be in H. The P6 joined set cannot satisfy that premise
when a voter wakes at its vote and has a suppressed duty. Add a joined-voter or
actual-emitter companion, with the same count conclusions and receipt outputs.
The joined-voter form replaces awake in hH by joinedAt at this exact vote tick.
Its proof must obtain joinedness from the actual honest emission; receiver
receipt callers still need ReadyTrigger, HistorySafeAt and their local epoch.
P-Cl1 did not edit Count or any other P-ShA file. The existing local stamp
supplier fgsa_gateReceipt_stamps_on is available and needs no replacement.

Open targets: TransferFrame needs receipt/root/epoch caller ports; Transfer,
StepGate, Closure and Safety then need their guarded consumer ports. These
remain P-Cl1 work after the needed Shared interfaces are available. No owned
repair with an EXPECTED-FAIL target is marked closed. clean_epoch_saved_row is
not yet supplied; P-Ar must not close against this checkpoint.

Validation: DCK PASS with default controls (250.37 s), including lake build
--wfail of all 475 GREEN modules. The local core audit has 112 commands; the
regression has three. All use only propext, Classical.choice and Quot.sound.
Complete export/coverage check on the prepared roots: 0 unaccepted (8.74 s).
Layer check: 72 baseline findings, 0 new. The expected-failure build fails in
TransferFrame and blocks its four dependent targets (5.81 s). Thus full-scope
export/audit closure remains open. No approved public meaning STOP occurred.

### Lead note after the P-Cl1 review (2026-10-10): Count deadline obstruction
rev-pcl1-astra finding 1: ReceiptCoverageSleepPremises (R/Statements/ReceiptCoverage.lean:64, :68, :78) forces
dl(a) = dl(t). Clean callers (C/StepGate.lean:562-564, C/TransferFrame.lean:379-382, :474-477) require objects
accepted at old times t with dl(t) = t + Δ, so a = t; a receiver that woke later (wake 24, acceptance 8, Δ = 2)
cannot meet deadline 10, and no Clean regime field supplies readiness/restartFree from t. WC/WCG
(dl(t) = max(t, GST) + Δ) force a = t after GST. These callers stay EXPECTED-FAIL. Choosing a = max(send, wake)
with the old deadline cannot work. Open: an anchor-relative deadline form (design check anchor-dl-sol running).
TransferFrame path interfaces (:335, :397) still need the joined receiver argument.

## P-ShA round 4 — joined voters and local services (2026-10-10)

Status: NOT CLOSED. Base: `1c777e97`. The JOINED-VOTER ruling applies to the
internal action-batch and two gate-receipt regime producers. No FGSAClaims
statement, Base₂ field, baseline or allow entry changed. Base₂ has no NoRestart
projection. Green is a compile status; it does not mean every legacy route is ported.

### Compiled interfaces and completed obligations

- `CatchUp.ReceiverService`: exact N4 inputs for one object and receiver. The
  ready anchor can follow a wake. The epoch starts at actionCut(anchor) and ends
  at idxBefore(freeze). Safe retained history remains an explicit input.
- `CatchUp.FreshHeadService.receipt`: processing and a strict freeze stamp for
  the exact emitted HEAD. History safety comes from
  `fgsa_historySafeAt_of_emitted_head`, at that same emission tick.
- `CatchUp.ReceiverService.proposal` and `fgsa_target_receipt_on`: exact named-body
  equality under P23-A, plus durable target membership. They do not equate roots
  without the named receipt scope.
- `Count.fgsa_receiptCoverage_on`: the sleep coverage branches, path receipts,
  vote-or-cap receipts, and strict stamps use receiver-local epochs. The exact
  handler WF/dependency/timeliness input remains explicit: for every required
  `o,t`, every handler at `u` with `t ≤ u < dl(t)` needs all three facts. This
  larger interval can include times before the receiver's ready anchor `a`.
  The Round 6 `_anchor_on` companion requires those facts only on `[a, dl(a))`.
  Both forms are stronger than the bare ReceiptCoverageSleepStatement input list;
  the Run sleep statement
  still has no proof on this base. No old-send awake premise is used by this route.
- `Count.fgsa_active_path_of_coverage_on`: the restarted active-path interface.
  The old `fgsa_active_path_of_coverage` type stays unchanged and remains legacy.
- `Count.fgsa_stored_honest_head_joined`, `fgsa_late_rest_bound_joined` and
  `fgsa_gate_batch_premises_joined`: joined HEAD origin and joined denominator.
- `GateReceipt.fgsa_gateReceipt_on`: joined selected voters, FreshHeadService,
  named target service, and the enabled gate actor. `GateReceiptScope` supplies
  the exact early-to-gate receiver epoch. The theorem also proves awake at the
  exact early read and the executed gate join test (T42).
- `GateReceipt.fgsa_gateReceipt_block_stamp_lt_on` and
  `fgsa_gateReceipt_block_to_tick_on`: local strict stamp and ready named receipt.
  The legacy stamp theorem is an explicit wrapper of the local form.
- `HeadAdmit.inclusion_head_receipt_early_on`: joined HEAD service at the exact
  early read, with a local read-to-tick epoch. `fgsa_action_walk_batch` now takes
  `joinedAt` for every honest node at the vote tick, and a joined participation
  count, plus the exact services. A guard only on selected seats is insufficient.
  `fgsa_action_walk_batch_legacy` keeps the awake form with explicit NoRestart.
- `ExactService.exactService_emitted_head_joined`, the receipt/raw/at/gate `_on`
  forms, `exactService_of_head_and_gate_on` and
  `exactService_participation_of_card_joined`: joined HEAD readers and selected
  voters. Gate service uses GateReceiptScope; the all-reader route keeps
  confirmedReaderAtIdx at the exact gate (T40).
- `SameLabel.fgsa_sameLabel_on`: local cross-reader service with a receipt-or-cap
  split. SameLabelServiceScope contains ready object service and exact enabled
  read epochs. It has no NoRestart field.
- `Regimes.fgsa_gateReceipt_clean` and `_recovery`: joined guard and the exact
  GateReceiptScope, under the internal ruling. Both compile in isolation.
  `_clean_legacy` and `_recovery_legacy` require explicit NoRestart.
- `ScoreRun.fgsa_scoreRun_metadata_retained_restart` and
  `fgsa_scoreRun_raw_subset_restart`: proposal metadata and the raw subset use
  durable storage across restarts.
- `RetainedPersist.fgsa_retained_proposal_mem_on_run_epoch`: ready named proposal
  service with explicit safe history. Membership persists to the actual HEAD
  tick through durable storage. This does not port the full retained geometry.
- `StoreRun.fgsa_votes_cumulative_on`: volatile vote persistence in one receiver
  epoch. Relay, SameLabel and ScoreRun keep their private legacy names and types
  as explicit wrappers of this local form.
- `Release.fgsa_release_bound_restart` remains the completed round 3 route.
  The explicit legacy release wrapper stays available.

### Exact blockers at the three open targets

`Export.fgsa_sameLabelClaim` still calls the legacy fgsa_sameLabel with the absent
Base₂.noRestart field. It needs a proof that SameLabelPrem.set plus its LabelSyncOn
supplies SameLabelServiceScope, or a direct proof with the same local obligations.
The conditional internal core now compiles. No false public conclusion is proved;
no extra public premise was added. Adding a NoRestart premise is not an accepted fix.

The following ten Regimes adapters still call legacy cores. Each failed projection
is from Base₂.noRestart. The two repaired gate-receipt adapters are not in this list.

- `fgsa_score_eq_on_clean_of_retained_proposal` and
  `fgsa_score_eq_on_recovery_of_retained_proposal`: port fgsa_score_eq_on_run through
  local frozen-vote, target-block and support receipts at the proposer/HEAD reads.
- `fgsa_ghost_transfer_sfx_on_clean` and `_recovery`: port the walk block/reflection
  routes and score equality, with their exact receiver epochs and ready services.
- `exactService_head_of_proposal_clean` and `_recovery` (T39): retain the joined
  HEAD-reader guard; port exactHead_of_proposal_on_run and its walk supplier.
- `exactService_head_of_retained_proposal_clean` and `_recovery` (T45): retain the
  joined HEAD-reader guard; port fgsa_retainedExactHead_geometry_on_run and the
  retained read suppliers. Each retained HEAD needs a replay object or explicit
  HistorySafeAt at its ready anchor. Past processing cannot supply that field.
- `exactService_of_head_clean` and `_recovery`: use exactService_of_head_and_gate_on
  with GateReceiptScope for each exact confirmed receiver and joined participation.
  The CleanSleep₂/HealthyPrefixSleep₂ companion contains joined count fields; the
  legacy CleanCut₂ fields count awake nodes. Recovery needs the joined window
  after GST. The old input HEAD premise also lacks the joined reader guard.

`Tests.RetainedConsumers`: Composes now has joined honest-reader quantifiers and
all test roots take NamedReceiptRootCollisionFree. Compilation still waits for
Regimes. Its `compose`, `check_H6`, `check_H6S`, `check_H17`, `check_L4R`, `check_HG1`,
`check_L2`, `q1_H6` and `q1_H6S` still test legacy read/geometry
suppliers with explicit NoRestart. Replacing only the reader quantifiers does not
finish their sleep path.

### Green legacy cores: theorem-level remaining work

The entries below still have only a legacy run-service proof on this base. Their
NoRestart premises are explicit. They must not be called final sleep APIs.

- `Shared/Relay.lean:509` — `fgsa_headVotes_provenance`.
- `Shared/Relay.lean:555` — `fgsa_vote_accepted_before_head_read`.
- `Shared/Relay.lean:649` — `fgsa_headVotes_backward_relay`.
- `Shared/Relay.lean:727` — `fgsa_cleanSupport_vote_forward`.
- `Shared/Relay.lean:887` — `fgsa_cleanSupport_forward_relay`.
- `Shared/ScoreRun.lean:350` — `fgsa_scoreRun_frozen_vote_relay`.
- `Shared/ScoreRun.lean:457` — `fgsa_scoreRun_raw_extra`.
- `Shared/ScoreRun.lean:592` — `fgsa_scoreRun_block_forward`.
- `Shared/ScoreRun.lean:636` — `fgsa_scoreRun_block_backward`.
- `Shared/ScoreRun.lean:718` — `fgsa_scoreRun_support_forward`.
- `Shared/ScoreRun.lean:785` — `fgsa_scoreRun_support_backward`.
- `Shared/ScoreRun.lean:907` — `fgsa_score_eq_on_run`.
- `Shared/ScoreRun.lean:986` — `fgsa_walkRun_frozen_block`.
- `Shared/ScoreRun.lean:1317` — `fgsa_walkRun_reflected_block`.
- `Shared/ScoreRun.lean:1427` — `fgsa_ghost_transfer_sfx_on_run`.
- `Shared/ExactHead.lean:95` — `exactHead_of_proposal_on_run`.
- `Shared/ExactHead.lean:171` — `exactService_head_of_proposal`.
- `Shared/RetainedPersist.lean:290` — `fgsa_retained_path_persists_on_run`.
- `Shared/RetainedPersist.lean:358` — `fgsa_retainedWalk_geometry_on_run`.
- `Shared/RetainedReflect.lean:235` — `fgsa_walkRun_reflected_old_child`.
- `Shared/RetainedReflect.lean:268` — `fgsa_retained_old_child_reflects_on_run`.
- `Shared/RetainedEndpoint.lean:189` — `fgsa_retainedExactHead_geometry_on_run`.
- `Shared/RetainedConsumers.lean:333` — `fgsa_retainedReads_H6`.
- `Shared/RetainedConsumers.lean:676` — `fgsa_retainedReads_H17`.
- `Shared/RetainedConsumersH6S.lean:19` — `fgsa_retainedReads_H6S`.
- `Shared/RetainedConsumersQ.lean:21` — `fgsa_retainedReads_L4R`.
- `Shared/RetainedConsumersQ.lean:60` — `fgsa_retainedReads_HG1`.
- `Shared/RetainedConsumersL2.lean:56` — `fgsa_retainedReads_L2`.
- `Shared/HeldReceipt.lean:22` — `healing_held_block_receipt`.

Relay provenance needs the restart replay branch of RelayCarried at the joined
HEAD read. The accepted-before-head-read supplier needs a strict local epoch and
an acceptance/replay origin. Its backward/forward relays need ready receiver
service for each vote or cap witness, with safe history and the exact freeze.

ScoreRun frozen-vote relay/raw-extra need the receiver's ready anchor, signed
object identity and frozen stamp bounds. Block forward/backward/frozen/reflected
routes need named target/ancestor services and exact endpoint floor compatibility.
Support forward/backward must convert those receipts into resolved vote support.
The score equality and ghost-transfer cores depend on those ports; a stored
proposal's durable metadata alone does not supply them.

ExactHead and the retained geometry/read suppliers need those score/walk ports.
The joined reader scopes in T39/T45 are already present; those guards do not prove
the missing service or retained history fields. HeldReceipt needs the same exact
ready service at its held-block cutoff.

### Family handoff: do not edit other packages

Use `fgsa_active_path_of_coverage_on E rho hvalid hdelta ... hcovSleep hpath hFK
hroots hReady`. This form requires, exactly, `∀ o t, required o t → ∀ j u,
t ≤ u → u < dl(t) → handlesAt E rho j x o u → wellFormed o = true ∧
depsPresent (stateBefore E rho j x) o = true ∧ fgsaTimely ... o`.
This larger interval `[t, dl(t))` starts at the original trigger, not the anchor.
Use `fgsa_active_path_of_coverage_anchor_on` to require handler readiness only on
`[a, dl(a))`. Its witness bundles the same `a` with ReadyTrigger, HistorySafeAt,
restartFree, the record's index/deadline/slot bounds, and handler readiness.
Supply HistorySafeAt explicitly for retained routes.

ReceiptCoverageSleepPremises restricts the anchor: `t ≤ a`, `dl(a) ≤ dl(t)`,
and `Monotone dl` imply `dl(a) = dl(t)`. With Clean `dl(t) = t + Δ`, this forces
`a = t`. With WC/WCG `dl(t) = max(t, GST) + Δ`, a later anchor is allowed only
when `a ≤ max(t, GST)`; for `t ≥ GST`, this also forces `a = t`.
Thus a general later post-wake anchor is not available from this record.
If a caller needs one, the exact S-Ap statement question is to allow
`dl(t) < dl(a)` and bound the anchored receipt by `dl(a)`, with corresponding
changes to the required-object and path deadlines and receipt conclusion.
The lead must decide that public statement change; P-ShA does not make it.

The following caller theorems must replace the legacy Count call. Their owners
must also use Base₂.receiptIdealization for receipt-body equality.

- Clean/StepGate: `gate_active_heads`.
- Clean/TransferFrame: `clean_transfer_receipt_path`,
  `clean_transfer_receipt_path_of_head`.
- WeakContinuation/StepTransferReceipts: `prefreeze_path`.
- WeakContinuation/StepGateBatch: `gate_active_heads`.
- WeakContinuationGrowth/Dynamics: `growthStepGateBatch_gate_active_heads`,
  `growthStepTransferReceipts_prefreeze_path`.

P-Fi consumers `Finality/RowsBatch.rowsPrem_action_walk_batch` and
`Finality/TailBatch.ktail_action_walk_batch` must use the ruled joined action API:
`joinedAt p E rho y s (voteTime s)` for every `y ∈ rho.honest`, where
`s = q * R + 1`, joinedHonest Batch, exact FreshHeadService/target service, and
the read-to-action receiver epoch. The producer's all-honest guard includes
honest nodes that are not selected HEAD seats.

For Recovery, use `Recovery₂.joinedAt_of_slotStart_le` in RegimesService with
`GST ≤ slotStart(s-1)` and `voteTime s ≤ rho.horizon`. Recovery.awake gives
continuous awake time on `[GST, voteTime s]`. A wake `u > slotStart(s-1)` would
have `awake(y,u-1) = false`, but the Recovery interval gives `true`. Thus all
wakes through the vote are at or before `slotStart(s-1)`. Base.restartsAtWakes
makes the same bound hold for each restart, which proves all three joinedAt
fields. `ActionTime.lean:14` gives only `GST ≤ voteTime s` and is too weak.
The old name is retained for the corrected
internal producer. The explicit old form is fgsa_action_walk_batch_legacy.

### Map and validation boundary

P-ShA map: 65 targets, 62 green including two input tests, three expected failures.
Owned targets: 60 green, three expected failures. Full map: 476 green, five
expected failures. HeadAdmit is now green. Run.Proofs.ReceiptCoverage is green
from its actual retired-import-path build; it does not prove the sleep statement.
Run and Run.Tests.Axioms stay S-Ap expected failures due to the five missing audit
names already recorded in round 3. No external source file was edited.

The new Regimes gate adapters and legacy companions have an isolated strict
Lean check. That check does not classify the full Regimes module as green.
The final checks and exact source lines are in claude-files/sleep-psha-report.md,
Round 4. Successful validation covers the green map only. Package closure still
requires every theorem-level blocker above to be resolved.

Final round 4 checks: DCK PASS (180.905 s), 42 strict
audits / 2,891 results, all 24 controls PASS. Complete green exports: 255 proof
modules / 253 exports / zero unaccepted. SharedAxioms coverage: 364 entries PASS.
Layers: 72 inherited / zero new. Expose and sleep scopes PASS. Two inherited W3
transparency findings remain. The open-target check confirms the ten Regimes
projections, Export's legacy call and the five missing S-Ap Run audit names.

## P-ShA round 5: exact gate service

The old Regimes declarations remain unchanged. Additive forms are in
`Proofs/Shared/RegimesService.lean`. `exactService_of_head_clean_on` and
`exactService_of_head_recovery_on` use joined HEAD readers, joined Batch and
release counts, and `GateReceiptScope` for each confirmed receiver at the same gate.
The Clean and Recovery consumer must supply these local scopes and, separately,
`hfast : releaseThreshold ≤ (joinedHonest p E rho (voteTime v)).card`.
Clean's joined majority field is not this releaseThreshold bound. Both forms
also require joined Batch. Their old awake counts do not prove these joined
counts. Recovery needs its join window after GST.
No `NoRestart` premise or restored Base field is used by these forms.

### Round 5: proposal HEAD, score and walk ports

Additive `ScoreServiceScope` supplies frozen HEAD ReceiverService and exact named
block TargetReceiptService in both directions. It also supplies the source epoch
from the strict proposal read to its tick. Each ReceiverService has its own
HistorySafeAt and handler window. No theorem takes the final score equality,
walk cover, or exact HEAD as a new service premise.

The score and support proofs use durable proposal metadata after restart.
The walk proof keeps both the frozen and authenticated proposal-path reflection
arms. `exactService_head_of_proposal_on` keeps the joined-reader guard.
Its Clean and Recovery consumers are the corresponding `_clean_on` and
`_recovery_on` adapters in RegimesService. Those consumers supply the scopes.
All previously compiled declarations remain unchanged.

### Round 5: SameLabel public Export

`fgsa_sameLabel_serviceScope` supplies the entire SameLabelServiceScope from
ExecutionValid, RestartsAtWakes, the delta equation and LabelSyncOn. Export uses
BaseSet's existing fields. The public SameLabelClaim type is unchanged.

The proof rejects future HEADs before the label's proposal tick. A replayed HEAD
comes from a raw list in a retained proposal. The raw label plus that proposal's
strict slot bound rules out a same-label replay before this tick. This also
handles the zero label, because RestartsAtWakes requires a positive wake time.
Enabled gates bound every prior local restart by the label's proposal time.
Those bounds give awake service at the early anchor, safe HEAD history, and the
exact epochs through the strict gate read. The receipt deadline uses the same
LabelSyncOn delivery law. No per-reader scope or history premise was added to
SameLabelPrem or to the public claim.

### Round 5: retained geometry and read services

`RetainedServiceScope` supplies the named proposal service and ScoreServiceScope for each candidate whenever both endpoint floors apply. Candidate services keep
HistorySafeAt per object; old processing is not used to fill that field.
`RetainedExactHeadRunGeometryOn` restricts admission, walk and endpoint suppliers
to joined readers. The new retained geometry theorem constructs those fields;
it does not accept an exact HEAD or final walk cover as a service premise.
The old geometry record and all its compiled consumers remain unchanged.

All six read suppliers have additive `_on` forms: H6, H6S, H17, L4R, HG1 and L2.
They use TargetReceiptService for the proposal and durable block storage to the
actual HEAD tick. The local service input is separate from elementary lane reads.

Named downstream suppliers (other families, not edited here):
- Healing `repair_head_exact` and `frontier_seed_qSucc_head`: H6/H6S object service.
- Healing `frontier_later_head`: HG1 object service and retained candidate services.
- WeakContinuation `wc_retainedReads` / `wc_exactProposal`: H17 object service,
  candidate services and safe retained replay history at each ready anchor.
- Assembly `wcg_exactProposal`: the analogous WCG retained object services.
- L4R and L2 callers supply the same object scope within their stop intervals;
  their private type checks in Tests.RetainedConsumers identify the complete input.

The Clean and Recovery retained `_on` adapters pass these inputs for each joined
reader. No caller may infer retained HistorySafeAt from a past processed result.

### Round 5: preserved original Regimes bodies — STOP on NoRestart

False required implication:
`ExecutionValid E rho ∧ RestartsAtWakes E rho → NoRestart rho`.
Counterexample: Run.Tests.Sleep `joinEnv 9` / `joinRun 9` is ExecutionValid and
restarts at wakes (`SleepTests.join_valid 9 (Or.inr rfl)`). Its event at index 1
is `.restart 0 9`. Thus NoRestart fails at exactly that index. The receiver is
awake at the slot-1 HEAD tick 10 but its wake exceeds the previous slot start 0;
Tests.RestartEpochs `awake_head_tick_not_joined` checks the suppressed duty.
The historical processing → HistorySafeAt implication is also false at wake 35
in `retained_head_history_not_safe` in that test module.

The ten original Regimes declarations still request `h.base.noRestart`. That
projection does not exist and cannot be restored under the approved model.
All their names and types are preserved as requested. This is a STOP on supplying
the false legacy premise, not a kernel refutation of all ten full conclusions.
Their new true forms are the ten `_on` declarations in RegimesService. They use
joined participation, per-receiver gate scope, ScoreServiceScope, or
RetainedServiceScope. No public FGSAClaims statement change is requested.
The original module remains EXPECTED-FAIL; its legacy bodies are not certified.

### Round 5: joined read suppliers

H6/H6S/H17/L4R/HG1/L2 now also have `_joined` forms. Every elementary reader
input, TargetReceiptService, and read-premise conclusion has the same joinedAt
guard at the actual HEAD tick. Tests.RetainedConsumers uses these forms and its
RetainedServiceScope input has that same guard. The earlier additive `_on`
forms remain unchanged for callers that supply all-reader service.

### Round 5: Relay and held-carrier inventory

`HeadRelayServiceScope` has one HEAD object, a strict freeze, its reader index,
its epoch, and a conditional ReceiverService. Scope suppliers are guarded by
membership of the actual HEAD candidate, or by equality with the actual clean
support wire. They do not require service for every possible payload.
New Relay forms cover provenance, backward late-pool relay, frozen clean-support
vote relay and forward support incidence. The existing path read input remains
explicit in the support-incidence form.

`fgsa_vote_accepted_before_local` excludes replay-only origins with a local
restart bound and the earlier label tick. Relay's joined HEAD-read supplier
constructs that tick and bound from joinedAt. No global NoRestart is needed.
The new frozen walk alias uses the named backward block service.
`healing_held_block_receipt_on` obtains the exact held FG carrier from its
TargetReceiptService. These forms cover the Relay and HeldReceipt entries in
round 4's legacy-only inventory. Legacy conditional APIs remain unchanged.
### P-H2 — sleep wave 3 prepared scope

Base: sleep-ph2 at 60cdcf652308640f3fadc39360e2b2042879f633.
P-H1 and P-Fd are PREPARED inputs. P-H2 is PREPARED; CLOSED stays open.

Internal T17 replacement: opening_action_tick requires awake at the exact opening.
An honest node that stays asleep has no tick there. Recovery supplies awake from
GST through the exact horizon. OpeningTicks holds the scheduled-run helper;
OpeningServiceOne and FrontierOpen pass their existing time bounds.

GF consumers: a nonempty scheduled fast write proves the exact gate join guard.
OpeningGateRead uses freshness, the unjoined empty row, and fast-label uniqueness.
It derives enabledGateAt before constructing GateService. An executed nonempty
result supplies its raw branch through fgsa_gate_raw_of_nonempty. The direct W3
clockPre gate-view bridge keeps its type. The slot bound uses non-strict pre-tick
clock order; it does not need a join premise merely to compare slots.

RR consumer: PostResetRawStep needs expiry membership only. ReleaseScope proves
that membership in both join branches. It does not infer a strict release count
from an unjoined clock. Strict release consumers still need their exact guard.

T23: all 19 H2 calls now pass awake at the exact node and vote. T15, T16, T18,
T19 and T22 also pass their exact recovery awake witnesses. These blocked high-depth
files remain EXPECTED-FAIL; source edits alone do not close their proofs.

H1 handoff: the held-receipt caller passes deadline awake and receipt idealization.
The three slot-proposal callers derive the exact proposer restart cutoff from
RecoverySleep₂.suffixNoRestart and their lower proposal bounds. RiseOneRise also
uses RecoverySleep₂. Named receipt callers use receiptIdealization where required.
Legacy NoRestart receipt and transfer suppliers remain explicit open inputs.

RecoveryScope consumes RStoreDurable, RMonoAll and RStoreEpoch as supplied channels.
Its proofs use exact event indices from actionCut to idxBefore for the receiver
stamp epoch. A restart at GST is permitted. No global NoRestart is inferred.
The direct Foundations.Store import was removed to keep the Healing layer valid.
P-Fd supplies the concrete producers through the package assembly interface.

Prepared validation: 85 TARGETS; 468 GREEN; 85 EXPECTED-FAIL. The target split is
6 GREEN and 79 open. Six REQUIRED supplier failures retain P-ShA/S-Ap ownership.
DCK PASS: 37 strict roots, 2,812 results, all 24 controls PASS.
Complete compiled exports: 111 proof modules, 251 exports, 0 unaccepted.
Layers: 72 baseline findings, 0 new. No public statement, protocol declaration,
checker, baseline, or allowance changed. The canonical audit fragment is in
scripts/dev-pkg/P-H2.coverage-fragment.txt for serial integration at close.

### P-H2 — reset join and durable retention follow-up

ResetScope proves GST + 6Δ ≤ τ, and 6Δ ≤ τ - GST ≤ 10Δ - 1 for nonnegative
integer GST. The first reset row is after the inclusive u₀ cut: otherwise
H0Reset.rowCap would give M+1 ≤ M. With cut_lower, this places GST before
slotStartZ(sStar). Later vote and gate cutoffs follow by slot order.
No bound is taken from the synchronous vote alone.

JOINED-VOTER internal replacement: the generic cone batch-seat helpers take
GST ≤ slotStartZ(label-1). An awake voter at GST need not be joined at that
vote. Recovery's closed awake interval supplies the exact joinedNow guard.
PostResetConePool passes the cutoff; PostResetConeInput derives it from
H0Reset and the shifted reset cut. Both honest_emits consumers pass joinedNow.
The generic helper's old vote-time-only scope was insufficient under sleep.

GF follow-up: the two PostResetLeaseStep fast-write consumers derive gate join
from the executed nonempty result. OpeningServiceGate supplies enabledGateAt
from its proposal lower bound and recovery interval. PostResetGate derives
its exact cutoff from H6's existing τ ≤ voteTime premise; no new H0 premise
or public meaning change is needed. The H6 signature test uses that approved
τ premise. These high-depth files remain EXPECTED-FAIL while suppliers are open.

Durable follow-up: opening_exact_stored no longer requires global NoRestart.
OpeningGateRead proves it with fgsa_store_durable; OpeningService and FrontierOpen
consume it. Reset/cone tree retention uses the same durable producer.
RecoveryScope also consumes the RFrameNextEpoch wire/stamp companion with the
exact receiver event interval. Assembly must supply the concrete P-Fd channels.
The generic channel lemmas do not close a blocked high-depth consumer.

Final validation and commit IDs are recorded in claude-files/sleep-ph2-report.md.
The final map has 86 TARGETS, with 7 GREEN and 79 open. Six other REQUIRED
supplier failures remain P-ShA/S-Ap-owned. The local audit has 27 commands.
The full audit import/command fragment is scripts/dev-pkg/P-H2.audit-fragment.txt.
No new canonical coverage key, allowance, or baseline is added.

P-H2 final follow-up validation: 469 GREEN --wfail PASS (1.77 s), DCK PASS,
37 strict roots, 2,822 permitted-axiom results, all 24 default controls PASS.
Complete compiled exports: 112 proof modules, 251 exports, 0 unaccepted.
Layers: 72 baseline findings, 0 new. The package remains PREPARED.
The 79 assigned open targets and six REQUIRED suppliers prevent CLOSED.


## P-ShA round 6 — CLOSED (2026-10-10)

RULING LEGACY-REGIMES is implemented. Each of the ten original declarations in
Shared/Regimes takes an explicit `hNR : NoRestart rho` after `E,rho`, with the
same conclusion. Each docstring says
"legacy: sleep consumers use the _on form in RegimesService".
No sleep regime supplies that premise. Regimes is GREEN. The false implication
recorded in Round 5 remains false; the ruling removes the failed projection.
Public FGSAClaims statements and Base fields are unchanged.

### Final interfaces

Sleep consumers import Shared/RegimesService and use these replacements:

- `fgsa_score_eq_on_clean_of_retained_proposal` →
  `fgsa_score_eq_on_clean_of_retained_proposal_on`.
- `fgsa_score_eq_on_recovery_of_retained_proposal` →
  `fgsa_score_eq_on_recovery_of_retained_proposal_on`.
- `fgsa_ghost_transfer_sfx_on_clean` →
  `fgsa_ghost_transfer_sfx_on_clean_on`.
- `fgsa_ghost_transfer_sfx_on_recovery` →
  `fgsa_ghost_transfer_sfx_on_recovery_on`.
- `exactService_head_of_proposal_clean` →
  `exactService_head_of_proposal_clean_on`.
- `exactService_head_of_proposal_recovery` →
  `exactService_head_of_proposal_recovery_on`.
- `exactService_head_of_retained_proposal_clean` →
  `exactService_head_of_retained_proposal_clean_on`.
- `exactService_head_of_retained_proposal_recovery` →
  `exactService_head_of_retained_proposal_recovery_on`.
- `exactService_of_head_clean` →
  `exactService_of_head_clean_on`.
- `exactService_of_head_recovery` →
  `exactService_of_head_recovery_on`.

`fgsa_receiptCoverage_on` and `fgsa_active_path_of_coverage_on` keep their types
and the larger handler interval `[t, dl(t))`. The two new `_anchor_on` companions
have the same conclusions. They bundle handler readiness on `[a, dl(a))` with
the same anchor's ReadyTrigger, HistorySafeAt, restartFree, index/deadline bounds,
well-formedness and HEAD slot bounds. They keep the inherited `dl(a) = dl(t)`
restriction. The exact family handoff above applies to both forms.

`Recovery₂.joinedAt_of_slotStart_le` supplies HeadAdmit's all-honest join input
from Recovery continuous awake time, restartsAtWakes, the previous-slot GST
bound, and the vote horizon. The joined `hfast` input of both exactService
adapters remains explicit, together with joined Batch and local gate scope.

The other final service interfaces are the Round 5 ScoreServiceScope,
SameLabelServiceScope, ReceiverService/FreshHeadService/TargetReceiptService,
GateReceiptScope, RetainedServiceScope and RetainedExactHeadRunGeometryOn.
The guarded H6/H6S/H17/L4R/HG1/L2 suppliers remain the `_joined` forms.
Retained history safety stays explicit for each object and anchor.

### Original-name family call inventory — owner port items

The source scan covers all ten original names in all repository Lean files.
These five executable family calls remain on this branch:

- P-H2: Healing/FrontierService.lean:69, `frontier_exactService_of_heads` calls
  `exactService_of_head_recovery`. Port to `_on`; supply joined HEAD, joined
  releaseThreshold/Batch, and GateReceiptScope.
- P-H1: Healing/RepairH6.lean:586, `repair_head_exact` calls
  `exactService_head_of_retained_proposal_recovery`. Port to `_on`; supply
  RetainedExactHeadRunGeometryOn and keep the joined reader guard.
- P-H2: Healing/FrontierSeed.lean:274, `frontier_seed_qSucc_head` calls
  `exactService_head_of_retained_proposal_recovery`. Port with the same retained
  geometry and joined reader inputs.
- P-Ou: Outage/ExactProposalRetained.lean:824, `inclusion_exact_head` calls
  `exactService_head_of_retained_proposal_clean`. Port to `_on`; supply retained
  geometry and use the joined reader scope for the exported HEAD clause.
- P-H2: Healing/Repair.lean:91, `repair_exact_service` calls
  `exactService_of_head_recovery`. Port to `_on` with joined HEAD/counts and
  exact gate scope.

The other seven original names have no executable family caller in this checkout.
Tests/Axioms has ten `#print axioms` references; these are audit commands, not
family calls. SharedAxioms now imports and audits the full GREEN Regimes module.
Owners must also port other legacy cores recorded in the Round 4/5 handoffs:
Count callers in Clean/WC/WCG, P-Fi RowsBatch/TailBatch, and retained read/score
suppliers in Healing/WC/WCG. Compilation of Shared does not complete those ports.

### Map and validation boundary

All 64 owned targets and both input tests are GREEN. P-ShA has no owned
EXPECTED-FAIL target. The full P-ShA map has 480 GREEN modules and two remaining
S-Ap EXPECTED-FAIL modules: the Run facade and Run.Tests.Axioms. The five S-Ap
audit names are left for S-Ap's running round 3.

The stale W3 map entry for Run.Proofs.ReceiptCoverage is reclassified GREEN.
It is an import-only compatibility path to ReceiptCoverageReady. The P-ShA map
states this boundary explicitly: GREEN here means the import path builds; it
does not certify ReceiptCoverageSleepStatement. Count's local companions have
explicit handler premises beyond that public statement.

DCK P-ShA, complete GREEN exports, layers, strict audits and SharedAxioms
coverage are recorded in claude-files/sleep-psha-report.md, Round 6.
No merge is made. Remaining family port items are assigned to their owners.

Final Round 6 validation: DCK PASS (218.795 s),
43 strict audits / 2,997 results, all 24 controls PASS. SharedAxioms coverage:
466 entries PASS. Complete GREEN exports: 258 proof modules / 253 exports /
zero unaccepted. Layers: 72 inherited / zero new. Expose and sleep scopes PASS.
The two inherited W3 transparency findings and five S-Ap audit names are unchanged.


## P-Fi — Round 2 resume (2026-10-10)

Base 381bd3df, branch sleep-pfi2. The sleep-pfi3 job kept the uncommitted
sleep-pfi2 work after the token_revoked error. All 23 former owned failures
now compile. This closes their module ports; it does not prove the remaining
receipt suppliers or close the unconditional public service contract.

### Exact consumer repairs

- RecoveryScope derives all-honest joined voters from continuous Recovery
  awake time, RestartsAtWakes, and GST before the previous slot start. It
  converts the joinedHonest batch to the same full honest seat set.
- RowsBatch and TailBatch supply that join proof for every honest voter.
  They pass exact HEAD and target services for each seat's headAtLabel,
  plus restartFree from idxBefore(actionTime q) to the actual receiver tick.
  The source of that interval is GST < actionTime q. Earlier wakes are allowed.
- MiddleSupport and TailOpening supply confirmed readers at exact gate reads
  and event-prefix reads. The healing gate has run; all wake events that can
  affect the read are in its prefix. RowsFrame, TailFrame, Forward, Local,
  Proposal, and Above pass these guards at both ends of each comparison.
- Forward uses the approved recoveryStart recurrence. The common healing
  witness proves recoveryStart <= tstar. RowsPrem and TailFrame use the
  recoveryStart bound at their exact H6 vote times. T13 and T14 keep awake
  at each selected node's exact vote tick. No count supplies arbitrary awake.
- Kernel and TailKernel preserve held rows at proposal reads through durable
  restore. Above, Local, and Proposal use restore-aware acceptance.
- TailMixed uses healing_held_block_receipt_on for the exact retained target.
  It retains the finality guard and named receipt root scope, then uses durable
  TF at the terminal read. Historical processing is not used as safe history.
- Sleep consumers use Shared/RegimesService. The explicit NoRestart legacy
  Regimes functions are not supplied from a sleep regime.

### Internal exact service forms and remaining suppliers

The new forms are proof-layer supplier contracts. FGSAClaims statements and
approved public meanings are unchanged. Each contract has a strict local audit.

1. FinalityVoteReceipts still quantifies every slot, honest receiver, time,
   matching postClock read, honest emitted HEAD, and matching label under
   LabelSyncOn. It has no GST, joined-reader, or healing-start restriction.
   CoreServices consumers are Joined, Forward, and Export. All now pass the
   receipt argument. Recovery's suffix bounds do not supply pre-GST receipts.
   The unconditional KernelACSideClaim_W producer remains open. Export makes
   its receipt supplier explicit; a conditional proof is not service closure.
2. FinalityActionReceipts supplies FreshHeadService and TargetReceiptService
   for each exact honest HEAD seat and action receiver, after GST and within
   the run horizon. RowsBatch and TailBatch consume it. Its deadline, epoch,
   handler readiness, non-exclusion, acceptance, and safe-history fields still
   need supplier proofs. Recovery supplies the local join/epoch bounds only.
3. TailHeadReceipts supplies the exact held action head to the honest terminal
   proposer at actionTime(r+1) + delta, with the derived finality guard.
   Consumers: ktail_head_delivered, ktail_mixed_final, ktail_hmixed_of_relay,
   tail_kernel_W_of_relay, tail_kernel_W_full_of, and fgsa_tailKernel_W_of.
   The service includes safe retained history; mere earlier processing is
   insufficient. Its producer remains open.

These replace removed global NoRestart arguments in internal consumers.
They are not added to Recovery, HealingInput, or any approved claim predicate.
The existing epoch fixtures refute the old Base₂/LabelSync receipt argument;
they do not prove the full RecoverySleep₂ + HealingInput claim false. No new
public-false STOP or public amendment is asserted in this round.

### Map and serial audit integration

ReceiptCoverage is GREEN: it is a compiled retirement import.
ReceiptCoverageSleepStatement remains a separate unproved contract.
Shared.HeadAdmit, Regimes, Export, and RegimesService are GREEN on this base.
The map has 44 TARGETS, 510 GREEN, and 3 EXPECTED-FAIL entries. No P-Fi entry
remains EXPECTED-FAIL. The other entries keep their owners: Run and Run.Tests.Axioms
are S-Ap; the full FGSAProofs.Tests.Axioms assembly audit is P-As. That audit is
a new TARGET only because this round applied the required serial fragment.

The local sleep audit has 175 commands. Export has 10 strict audit commands.
The full audit source and its existing inventory key received only P-Fi
production entries, including the Round 1 helpers. No old key or row was removed.
No coverage key, baseline, allowance, heartbeat, or recursion limit was added.
ARCHITECTURE and MAP now give the exact-wake design and helper roles.

Final checks and status are recorded below after validation.

### P-Fi Round 2 — final validation

DCK PASS (package P-Fi), 181.35 s, with all 24 default controls. Its complete
GREEN build uses --wfail. The 41 strict audit roots produced 3,148 results;
only propext, Classical.choice, and Quot.sound occur. The final family build
passed in 33.99 s. Complete exports and 204 audit commands passed in 13.41 s:
207 proof modules, 252 accepted exports, 0 unaccepted. Layers: 72 inherited
findings, 0 new, 0.42 s. git diff --check passed. Evidence: .lake/sleep-pfi2/.

Status: PREPARED, all owned module ports GREEN; not CLOSED. The exact receipt
producer obligations above and S-Ap/P-As assembly closure remain open.
No full gate, review, integration, push, merge, rebase, or public amendment
is claimed. The report is claude-files/sleep-pfi-report.md, Round 2.
## P-Ar wave 2 — receiver kernel (sleep-par, base 8384eb34)

Scope: the 13 existing Arming modules, new ArmingKernel, and Tests/OutageArming.
The package map is scripts/dev-pkg/P-Ar.txt. P-ShA files and public Claims
statements are unchanged. This block belongs to P-Ar.

T25, internal statement, exact sleep form: arming_tick_exists needs awake at
that receiver's named public time. arming_healthy_batch takes one receiver,
its early-time awake fact and exact read epoch, joined selected voters, and
P-ShA FreshHeadService / TargetReceiptService. Sender participation does not
supply receiver awake. Consumers at closure: ArmingMain and ArmingGate; P-Ou
accepts this T25 repair through the P-Ar handoff.

Internal statement, exact sleep form: arming_clean_of_tick and arming_max_label
need an enabled gate. cleanResults already has the enabled marker condition.
arming_enabled_of_pass gets this condition from an actual passed gate.
Consumers at closure: ArmingPrefix, ArmingGate, and ArmingMain.

The receiver kernel derives G-fast awake and restart-free on [t(j), g(j)].
G-slow starts at t(q0), not vote(q0). The event-index epoch starts at actionCut,
so a restart at t(q0) is before the epoch. arming_receiver_enabled proves the
inclusive marker bound at each scoped gate. No global NoRestart is used by
these sleep helpers.

arming_saved_interval_on, arming_slow_saved_on, and arming_slow_eligible_on
use only this receiver's current-epoch rows. The global no-restart wrappers
remain for the old certificate until closure. The sleep kernel does not use
hsavedKeep. Tests check erased saved rows, phase-zero wake reads, and no tick
while asleep.

arming_prefix_batch_receipt_on proves the exact prefix conclusion from local
ArmingBatchReceiptService. Its HEAD branch has the approved finality
alternative. Its proposal branch proves every ancestor and its strict stamp.
The service record is internal proof data; it is not an outage premise.
The public arming_prefix_batch_receipt : OutagePrefixReceiptDerivedClaim is
still OPEN. Closure must derive this service record from OutageSleep₂ and the
Clean joint induction, accept P-Cl1 clean_epoch_saved_row, port the seven
remaining certificate consumers, and apply the serial facade/audit fragments.
No public meaning change or public counterexample is asserted.

ArmingReceipt holds the local receipt proofs. It does not import ArmingPending,
so the public prefix theorem can consume it from ArmingPending at closure
without an import cycle. ArmingKernel also supplies the actual gate-tick epoch
and arming_tick_store_on for the exact receiver interval at equal-time phases.

P-Ar kernel validation: DCK PASS with default controls (24 PASS). All 473 GREEN
roots build with --wfail. Strict audits: 37 sources / 2,875 results, only the
three permitted logical axioms. Complete GREEN exports: 262 proof modules /
253 exports / zero unaccepted. Complete local coverage: 37 entries PASS.
Layers: 72 inherited / zero new. Kernel PREPARED; full P-Ar and the public
prefix receipt theorem remain OPEN on the closure inputs listed above.

### P-Ar Round 2 — joined transfer repair

Astra FIX-FIRST item 1: the T25 handoff at this block's first paragraph was
not prepared at 71fa5c6c. Its transfer premise still covered every honest
computed vHead read, including an unjoined node that emits no HEAD.
arming_head_ge_on now restricts transfer to joinedAt at vote(s + 1).
arming_healthy_batch uses that helper and passes its selected voter's hJoined.
arming_head_ge remains a separate legacy helper with its old type.
The T25 receiver and service scopes remain explicit. P-Ou must use the joined
transfer premise; no all-honest vHead premise is required by the fixed batch.

### P-Ar Round 2 — regime sources, receiver ports and public STOP

Astra item 2: hp := OutageSleep₂.sleepPre.toHealthyPrefix₂ supplies healthy,
cut and base. hp.base supplies valid, delta, cstar, linked and
receiptIdealization. arming_nonrow_delivery derives the healthy non-row
law with deadline a + p.Δ. arming_head_ready derives the fresh HEAD trigger
from honest emission and the protected receiver's awake window.
arming_fresh_head_service and arming_proposal_service derive transport,
readiness, timing and the receiver epoch. They still need local handler
acceptance, non-exclusion and proposal replay history proofs. No regime
field directly supplies these proof conclusions or TargetReceiptService.
The complete source map is claude-files/sleep-par-receipt-sources.md.

ArmingPrefix and ArmingOutput are GREEN. Existing names/types are kept.
The executed nonempty gate result supplies the enabled marker via
arming_enabled_of_result. Passed source and lease gates supply it via
arming_enabled_of_pass. arming_leases_interval_on and arming_S_interval_on
use one receiver's event-index epoch beside their legacy NoRestart forms.
arming_pending_rows_on consumes P-Cl1's intended current cut rows and
transfers them to the actual pending tick. clean_epoch_saved_row is absent
on this base and at the inspected sleep-pcl1 commit 075a92d6.

PUBLIC STOP: OutagePrefixReceiptDerivedClaim is false as currently approved.
Tests.OutageArming.EarlyCut.regime proves every OutageSleep₂ premise for
Δ = 2, T = 0, b₀ = b₁ = horizon = 8 and ΔF = 2. The sole honest node is
always awake and joined. Its slot-1 proposal is emitted at time 8 and is not
delivered. The healthy cut is 8, so its first deadline 10 is outside that
cut. coverLabel is 1 and the public claim requires this proposal processed
at earlyTime 1 = 12. It is not excluded, and it is absent at that read.
Tests.OutageArming.EarlyCut.prefix_claim_false proves the negation of the
approved claim. The run is valid, has the receipt collision idealization,
and meets all prefix, participation, protection, order, lag and budget
fields. This is not a missing service proof.

No public statement was changed. The lead must select an approved public
repair (for example the first-gate cut bound, or an early-cut scope repair).
The five remaining certificate consumers stay P-Ar EXPECTED-FAIL. Full
P-Ar remains NOT CLOSED; the joined T25 kernel is PREPARED. P-Ou must not
assume that the public receipt claim is available from this handoff.
## P-Ou — sleep wave 3 local kernel (2026-10-10)

Base: sleep-pou 15744443. Local kernel PREPARED; package OPEN.
No owned repair with a failing changed target is marked CLOSED.

- P15 local interface: RestoredReceipt.outage_restored_service uses
  max(send,wake), a strict receipt deadline, deadline <= cutoff, checked
  dependencies, history safety, finality exclusion, and the receiver epoch.
  Joined readers supply awake and restart freedom at the required times.
  outage_restored_receipt_with_service composes all three restored cuts;
  its service inputs and P-Ar prefix must still be derived from the regime.
  The public outage_restored_batch_receipt remains OPEN. No receipt field
  is added to Outage premises.
- P16: PersistenceSleep.outage_e1_of_e proves the approved E-to-E1 claim.
  outage_good_bad_disjoint isolates U=A union W. The strict release bound
  reuses outage_fault_lt_release. No good-vote premise is needed for E1.
- P12/P17: restart keeps coverage of B, the lock, and its deadline.
  outage_restart_live_lock limits the exception to wake < deadline.
  No extension of an old tip or newcomer record is asserted.
- Internal repair: a restarted block is traced to its original network
  acceptance by inclusion_acceptance_before_index. A replay is not used
  as a new acceptance. inclusion_receipt_of_compatible and
  inclusion_proposal_receipt now use joined reader scope and explicit N4
  service data. Their public Clean producer ports remain OPEN.
- ExactProposalHistory consumes the cleanResults enabled-gate conjunct.
- GateCount holds the four existing pure continuation count declarations.
  ContinuationGate imports it. The latter's remaining repairs are OPEN.

Ledger-use closure: P/E at ContinuationReceipt:283; P/K at :556 and :724;
T26-T30; T31-T38; and T61 remain OPEN pending the regime/consumer ports.
T25 belongs to P-Ar and waits on its closed handoff. The named reader
window/epoch lemmas are prepared inputs, not closure of those use sites.

Supplier closure inputs: P-Ar prefix and receiver arming, P-Cl1
clean_epoch_saved_row, P-ShA scoped Clean service adapters, S-Ap D013
OutageContinuationConcl, and P-Cl2 Growth/export fragments. Own closure
work: good votes, opponent denominator, late writes, joint induction,
handover, public receipts, exports, and the approved reader tests.

Package map and local complete audit inventory are in scripts/dev-pkg/P-Ou*.
Serial full audit/root/inventory fragments accompany the package report.
No allow entry, existing shared scope row, or foreign source is changed.

P-Ou prepared validation: the first DCK run passed with default controls.
The final map adds the compiled PersistenceHistory, PersistenceFrame, and
ContinuationFrame support modules. The complete local strict audit has
44 commands. Final export/coverage checks and a final DCK run follow.

## P-Ou — approved family claim scopes (2026-10-10)

Claims/Outage installs approved P10 joined proposal/HEAD reader scopes,
P17 finite output scopes and G-only covering-lock service, and P20 growth
reader guards at the trigger t and deadline d. No public meaning beyond
the approved packet is added. Claims/Statements remains untouched under
the explicit job restriction. The scalar argument changes are propagated
to OutageCompatClaim, FastP1Claim, and SlowP1Claim.

The neutral ServedFromGateAt and JointGrowthAt bodies are checked against
InclusionAt and AvailableGrowthConcl by equality. The first growth check
caught a local edit error (deadline reader at t); it was corrected to d
before the claim commit. Kernel commit: f560b7e8.

P-Ou final committed-source validation (kernel PREPARED, package OPEN):
DCK PASS on 479 GREEN modules, 37 strict sources, 2,882 axiom commands,
and 24 default negative controls. Complete GREEN exports/coverage PASS:
271 proof modules, 253 accepted exports, 0 unaccepted, 0 Gen exports;
44 local audit commands. Layers: 72 accepted, 0 new. Both neutral claim
body equalities and all 10 changed definition audits PASS. The 22
EXPECTED-FAIL entries remain explicit (18 P-Ou, 4 suppliers). No full
S1/S2/S3 gate or CLOSED family claim is asserted. Proof commits are
f560b7e8 and 57022bd2; exact reports/fragments are under claude-files/.
### P-WC — prepared guard, epoch and replay core (2026-10-10)

Base: sleep-pwc at 3939ba54, with P-Cl1 prepared at 075a92d6.
This is a PREPARED slice, not a CLOSED package. No owned EXPECTED-FAIL target
is closed. The package map has 47 targets, 477 GREEN and 38 EXPECTED-FAIL
modules. Six expected failures keep their P-ShA or S-Ap owner.

- Internal statements, approved P19/D116/D117: WCInv.nonempty requires an
  enabled gate; retrospective requires the joined voter at the exact next
  vote. Saved and fast origins use event-index restartFree. served and
  transitions use confirmedReaderIdx. WCReceiptOrigins includes the current
  restore stamp and its local epoch. WCDutyInput carries the stored duty guard.
- WC and WCG proof telescopes use RestartsAtWakes, joined vote counts,
  RStoreDurable with RStoreEpoch, RMonoAll and RFrameNextEpoch. The restart
  targets conclude WCInv at i+1. Their full step proofs remain open.
- T49/T53/T57 supplier: wc_joined_gate_witness selects the actor at the earlier
  gate time. wc_joined_retrospective_witness orders through that actor, then
  returns the HEAD read of the original joined voter. The all-time count is
  kept until that selection. The three caller ports are not closed.
- T48/T54/T56 supplier: wc_currentEpoch_result gets the later enabled gate
  from the confirmed reader's caughtUpAtIdx witness. It orders the old result
  below that result in the reader's current awake epoch. Output persistence
  and the complete current-epoch service theorem remain open.
- W3-G: wc_gate_raw_enabled calls the joined saved-result equation;
  wc_gate_suppressed calls the unjoined equation. The older WC/WCG callers
  remain open until each exact guard is supplied.
- WC replay transfers enabled guards, local event epochs, restore receipt
  origins, and guarded duty inputs. WCG local replay uses restore at the exact
  restart time. Both initialization proofs preserve the approved scoped WCInv.
- Receipt deadline constraint: wc_receipt_anchor_deadline proves equality
  when send <= anchor <= max(send,GST). wc_receipt_anchor_late proves that an
  anchor after that maximum cannot fit the old deadline. A later service copy
  needs its own receiver deadline or a proof of retained receipt/stamp safety.
  No S-Ap receipt record was changed.
- Supplier gap at this base: fgsa_receiptCoverage_ready and
  fgsa_active_path_of_coverage still take global NoRestart and the old
  ReceiptCoveragePremises. Count has no sleep/anchor-scoped path companion.
  Needed at StepGateBatch, StepTransferReceipts and the two Dynamics sites:
  the ready/safe/local-epoch core over ReceiptCoverageSleepPremises, with
  handler readiness on the same anchor interval. Joined count companions at
  Count:242/277/351 are also absent. These are P-ShA/W3 supplier requests.
- Prepared validation: the contract, epoch, replay and initialization targets
  build with --wfail and default heartbeats. The local strict audit has 116
  commands. The package DCK and complete export check are in progress.
  Layers: 72 baseline findings, 0 new. No public meaning STOP has occurred.
- Shared audit/root/scope integration is supplied as a P-WC fragment. No
  shared inventory, root facade, S-Ap statement or other package file changed.

### P-WC — guarded saved-result callers (2026-10-10)

Prepared checkpoint: a82b7533. This group keeps the package PREPARED, not CLOSED.
The map now has 48 targets, 478 GREEN and 38 EXPECTED-FAIL modules (32 owned).

- W3-G/W3-J: each saved-result caller in WC and WCG now passes the stored
  join guard. Existing nonempty executed results supply it through the Shared
  raw-result bridge. The WC/WCG gate-construction interfaces now require
  enabledGateAt explicitly. The gate-write callers pass the pre-gate guard.
  These caller modules remain EXPECTED-FAIL; the signature ports are not
  claimed as compiled repairs.
- The WCG gate guard adapters use Shared imports within their own lane.
  No cross-family proof import or architecture exception was added.
- WC guard replay now transfers each event/store field directly. This removes
  three unaccepted generated match-equation exports. No allow entry, baseline,
  checker code, checker rule or public claim was changed.
- The first prepared DCK passed with default controls. Final validation is
  running after the WCG guard target and audit update. The local audit has
  119 commands. Layers: 72 baseline findings, 0 new.
- The exact receipt and joined-count supplier requests are in the local
  P-WC handoff. Output persistence, the full restart/event induction, all
  four sleep receipt callers and the assembly-dependent tests remain open.

### P-WC — final prepared validation (2026-10-10)

- Final P-WC DCK PASS, with default controls. All 478 GREEN modules build
  with --wfail. The local audit has 119 results and uses only propext,
  Classical.choice and Quot.sound. All strict package audits pass.
- Complete prepared export and audit coverage PASS: 112 proof modules,
  251 exports, 0 unaccepted. No exception or baseline entry was added.
- Layer check: 72 baseline findings, 0 new. Source diff checks pass.
- The guarded caller build remains EXPECTED-FAIL in Safety, Frame,
  Growth/Frame, StepInputs, StepFacts and Shared/HeadAdmit. These failures
  block the higher caller modules. The full family is not validated or closed.
- PREPARED only. Thirty-two owned targets stay EXPECTED-FAIL. Closure needs
  the remaining P-WC proofs, the receipt/count supplier interfaces, closed
  P-Cl1 and S-Ap inputs, and the assembly/test integration window.

## S-Ap Round 3 — Run facade audit

P3 wake-clock successors: replace the retired audit names
fgsa_restore_now_retained, fgsa_hrestore_now_retained, and restore_st_retained
with fgsa_restore_now, fgsaRestoreTimeLaw, and restore_st. The exact wake time
replaces the old retained clock. No production statement changes.
The existing spec_prune_restart_mem and spec_prune_sleep checks keep their names;
import Proofs.Spec.Simulation so the audit can resolve them.
Run facade --wfail PASS (10.79 s). Regenerated the existing Run audit
coverage key (8.54 s); mark the Run facade and audit GREEN in S-Ap.

## S-Ap Round 3 — P8 claim transfer

D140: RowServiceBaseClaim now has the exact approved all-honest awake suffix
from GST through the horizon. NoRestart remains. A permanent honest sleeper
satisfies the old receiver demands vacuously but need not receive an emitted row.
P8 public route: RowServiceClaim now takes RecoverySleep₂. The compiled P-Fd
supplier fgsa_tRows_recovery accepts its toRecovery₂ projection. The base
supplier fgsa_tRows accepts the new awake suffix. No new premise is invented.
The P8 declarations and aggregate compile with --wfail (1.29 s). The broader
Claims build also checked inherited fixtures: FinalityGST, FinalityW,
HealedBest, WeakContinuation, OutageAlignment, and the kernel adapter example
in Claims.Tests.Axioms fail on prior sleep changes. They are not P8 failures.
The FGSA shallow/deep generator includes eight inherited P-Fi claim hashes.
The auxiliary API generator stops on the missing Claims.Tests.Axioms artifact;
its full source scope is kept. No generated entry is edited by hand.
The Run inventory generator now succeeds (791 entries, 25.01 s) and removes
the stale fgsa_receiptCoverage entry retired under DECISION P23-A.
FGSA shallow/deep regeneration PASS (243.02 s, 1,357 roots).

## S-Ap Round 3 — P17 D013/D014 continuation supplier

OutageContinuationConcl is the exact approved D013 body: scoped record/output
compatibility; inclusion only for coveredNodes; scoped emitted HEAD compatibility;
durable F compatibility for every honest receiver. It takes fast, T, b₀, b₁
and Fintype V. No proposal-parent extension is added.
OutageContinuationClaim is the exact D014 wrapper with
OutageContinuationSleepPrem and all four conclusion arguments. P-Ou's report
at lines 43, 92 and 145 requests this supplier; its family proof remains P-Ou-owned.
The two docstrings now describe the approved scopes.
D013/D014 and the claim aggregate compile with --wfail (3.47 s).
The claims inventory and auxiliary API writers stop on the inherited missing
Claims.Tests.Axioms artifact; their source scopes are unchanged.
FGSA shallow/deep regeneration PASS (238.12 s, 1,357 roots).

## S-Ap Round 3 — remaining public wrappers

P8 D034/D037/D048: HTimeConcl, ResetArrivalConcl, HTimeBestClaim, and
HTimeSearchClaim now use the exact approved recoveryStart bounds and search
origins. Their numerical budgets do not change. These supply P-H1's public route.

Serial P-Fd fragment: fgsa_fgFoundationClaim uses the durable/epoch companions
and RMonoAll; fgsa_rowServiceBaseClaim passes the approved awake suffix;
fgsa_rowServiceClaim uses fgsa_tRows_recovery with toRecovery₂; the new P21(a)
fgsa_finalizedMonotonicityRestartClaim exports its compiled Foundations body.
All four wrappers have local strict audit commands. No family proof is replaced.

The anonymous kernel adapter example in Claims.Tests.Axioms now takes an
explicit Recovery₂-to-RecoverySleep₂ supplier. P-Fi must prove that supplier;
the example checks only the composition with its new AC interface. No public
claim, KernelPrem_W, or KernelJoinedPrem changes. The attempted move to
FinalityW was discarded because CLAIM-USE forbids that import. No layer
exception is added. The two best/search audit examples use the approved τ
premises. Observed inherited fixture failures have family owners in S-Ap's map.

P-Fi's eight approved public changes are already present. P-Ar's derived receipt
claim type already exists. Neither report requests another S-Ap statement change.
Their current receipt producers remain family proof obligations. P-Ou's other
Claims.Outage replacements are prepared on sleep-pou; lead integration retains
that package's work. D013/D014 are supplied in this branch.
The serial Foundations wrappers compile. The final package --wfail build
passes (3,675 jobs). Claims audit coverage regeneration keeps the existing
814-entry key. Layer check: 72 accepted findings, zero new.
The full claims inventory and auxiliary API writers now reach the inherited
missing Tests.FinalityGST artifact. No failed family module is removed from
the generators' scope, and no generated entry is edited by hand.
Complete export check: all 471 GREEN roots, 279 proof modules, 253 exports,
zero unaccepted; zero non-exposed Statements predicates (5.39 s). Complete
coverage of the three changed audit sources also passes. DCK checks every
GREEN audit with Lean. The broader source-parser coverage probe cannot resolve
the inherited open-namespace command window_bit_add_of_row in WindowLiveness;
that probe is not reported as a complete package coverage pass.
Final FGSA shallow/deep regeneration PASS (243.60 s, 1,357 roots).

Validation correction: the first DCK passes its build and 41 strict sources
(4,017 commands), then the finality coverage control detects the missing
canonical audit command for fgsa_finalizedMonotonicityRestartClaim. Add that
command to Proofs.Tests.Axioms as required by the serial P-Fd handoff. The
local strict command remains. No coverage allowance changes.
The full canonical coverage writer is blocked by missing Shared.Regimes.
The new P21 row is instead taken from CheckProofEqns' compiled local coverage
output and rendered into the existing Foundations.Export owner block with
check-proof-coverage.py's section writer. All other rows and keys are kept.
The canonical source registration check passes: 24 modules, 227 declarations.
This fragment integration is not a full canonical-audit build or regeneration.

## S-Ap Round 3 — Count restriction, LEAD DECISION

ReceiptCoverageSleepPremises.slotWindow has t <= a and dl(a) <= dl(t).
Its deadline field makes dl monotone. Therefore dl(a) = dl(t).
For Clean dl(t) = t + Δ, a = t. For WC/WCG
 dl(t) = max(t, GST) + Δ, a <= max(t, GST).
The Lean evidence is count-restriction.lean and count-restriction.log.

The current Count handoff needs this correction: its hReady premise is over
[t, dl(t)), not only [a, dl(a)). An anchor-scoped internal companion can fix
that excess premise but cannot remove the public record's deadline restriction.
The exact handler premise is:

```lean
∀ o t, required o t → ∀ j u, t ≤ u → u < dl t →
  V2.D.Run.handlesAt E rho j x o u →
  (fgsa p c).wellFormed o = true ∧
  (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho j x) o = true ∧
  fgsaTimely p (V2.D.Run.stateBefore E rho j x) o
```

An approved consumer needs a later-anchor route: P19/P20
SourcePendingReceipt, used by PendingSourceDelivery₂ and
CleanGrowthContinuationSleep₂, quantifies over all a >= send. It uses
max(a, GST) + delay, including wakes in the continuation after GST.
The joined participation count does not forbid an individual receiver's wake.
The old source trigger cannot in general be replaced by a new emission or relay
at the wake. This affects the proposed Count ports of
WeakContinuationGrowth.Dynamics.growthStepGateBatch_gate_active_heads and
WeakContinuationGrowth.Dynamics.growthStepTransferReceipts_prefreeze_path.
The Clean and WC historical-path ports have the same restriction when an old
object must be supplied after a receiver wake. Fresh HEADs may instead use their
own current emission anchor; durable stored paths need no new receipt.

Concrete restriction witness: send = 0, GST = 1, wake/anchor = 3, Δ = 2.
The approved pending service can use deadline 5. The existing Count record
requires 5 <= 3. This is impossible. This arithmetic example refutes a general
adapter from later-anchor service to the old Count record; it is not a
counterexample to the full public continuation claim.

Proposed exact additive change: keep ReceiptCoverageSleepPremises and
ReceiptCoverageSleepStatement unchanged. Add
ReceiptCoverageAnchoredSleepPremises with the same parameters and four field
names. Copy within, compat and deadline byte for byte. Replace only slotWindow
by the following type. In this companion, required o a and paths refer to the
service anchor a; send is the original trigger time.

```lean
  slotWindow : ∀ o a, required o a →
    ∃ send, send ≤ a ∧ 0 ≤ a ∧ a < dl a ∧
    Gen.V2.Duty.ReadyTrigger E rho o send x a (dl a) ∧
    Gen.V2.Duty.HistorySafeAt E rho x o a ∧
    V2.D.restartFree rho x (V2.D.Run.actionCut rho a) (V2.D.Run.idxBefore rho D) ∧
    first ≤ V2.D.Run.actionCut rho a ∧
    (fgsa p c).wellFormed o = true ∧
    (∀ s signer K, (toWire p o).decode = some (.vote s signer K) →
      ((V2.D.Run.stateBeforeTime E rho (dl a) x).st.slot p ≤ s + 1) ∧
      ∀ i t', V2.D.Run.actionCut rho a ≤ i → i < V2.D.Run.idxBefore rho (dl a) → a ≤ t' →
        V2.D.Run.handlesAt E rho i x o t' →
        s ≤ (V2.D.Run.stateBefore E rho i x).st.slot p ∧
          (V2.D.Run.stateBefore E rho i x).st.slot p ≤ s + 1)
```

Add ReceiptCoverageAnchoredSleepStatement and
ReceiptCoverageAnchoredSleepStatement_def by copying the existing statement
and equation and changing only the record name and declaration names. Thus every dl t in the copied conclusion is the anchor deadline because
the required predicate is now indexed by anchors. The original send is kept
explicitly in ReadyTrigger. No old-send deadline is silently weakened.
Any internal producer must still take or derive exact handler readiness on
[a, dl(a)), safe history, and the receiver epoch. This proposal does not assert
that the current bare public receipt statement has a proof.

Decision needed: approve this additive anchor-indexed public contract, or require
families to use direct receiver-service proofs when a exceeds max(send, GST).
No public record, Count theorem, or consumer proof was changed for this item.

### S-Ap Round 3 final validation

DCK S-Ap PASS (169.98 s): 471 GREEN modules, 41 strict sources, 4,017 commands,
and all default controls. Only propext, Classical.choice and Quot.sound occur.
FGSA shallow API PASS (167.03 s): 1,357 entries, complete matching hashes.
FGSA deep API PASS (118.80 s): 1,357 roots, 3,818 dependency nodes.
All 55 deep-snapshot controls PASS (164.59 s). Complete GREEN exports PASS:
279 proof modules, 253 exports, zero unaccepted. Layers: 72 accepted, zero new.
All eight changed public definition bodies match the approved packet tokens.

Full claims inventory/API generation and the auxiliary check remain blocked by
Tests.FinalityGST. Snapshot controls pass V2/GEN/FGSA shallow, catalog-lock and
source-scope checks, then stop on that artifact at the mapped-root control.
Full canonical Proofs.Tests.Axioms coverage generation remains blocked by
Shared.Regimes; the new P21 row is integrated from compiled generator evidence.
These are recorded limits, not full API or family closure. No generator scope,
public statement, baseline or allowance was weakened to bypass them.

### Lead note at the S-Ap round 3 merge (2026-10-10)
The S-Ap round 3 proposal of a PUBLIC anchor-indexed receipt contract is SUPERSEDED by DECISION ANCHOR-DL
(sleep-join-port-notes.md): an additive internal ReceiptCoverageAnchorPremises with one explicit anchor function, in
the P-ShA proof layer; public P23 text unchanged. DECISION P15-CUT amends OutagePrefixReceipt (S-Ap round 4).
Open at integration (rev-sap3-sol finding 7): the Recovery₂ → RecoverySleep₂ supplier for the kernel adapter (P-Fi).

Base: 1c777e97 on sleep-pcl1. This block belongs to P-Cl1.
The package is PREPARED on the gate/epoch set. It is not CLOSED.
The full Clean induction and the arming export are still open.

- GR, internal statement, lead ruling 10-10: StateGate.clean_gate_raw now takes
  enabledGateAt. GateEpoch.clean_gate_executed gives the exact guarded equation.
  clean_gate_nonempty_raw extracts the enabled/raw branch from an executed result;
  clean_gate_unjoined gives some none for a suppressed gate. Consumers:
  StateGate, StepGate, TransferFrame, GateOutput. The last three remain open.
- GF, internal statement, lead ruling 10-10: clean_gate_writes appends fastSet only
  in the joined branch. Its suppressed row is empty. Lease and fast-write proofs
  derive the guard from the nonempty executed result. No raw-result premise was added.
- The Chain bridges include the guard required by S-Ap's cleanResults. The
  index-result bridges take ScheduleWellFormed, which their run consumers have.
- T08/T12 supplier: clean_enabledGate_awakeClosed proves the exact receiver's
  closed interval from t_s through gate(s). It uses the valid tick, wake restart,
  and the current stored marker. This includes label 0 and its early cutoff.
  The StepGate consumers are still open; these rows are not closed as use sites.
- T10 supplier: clean_joined_gate_witness chooses z from joinedHonest at the
  earlier gate time. It gives z's actual enabled gate and its awake interval.
  It does not claim that the later actor x had an enabled earlier gate.
  The ordering/transfer use in StepGate is still open.
- S/R7 supplier: clean_restart_fields keeps FG, blocks, leases and stableRecord,
  and starts empty genuine/fastWrite caches. cleanHist_step_restart preserves
  completed event history. clean_gate_fg_before_time compares only the kept FG
  fields with the strict time read; it does not assert whole-store equality.
  State/Closure still need their current-epoch induction port.
- N4 receiver supplier: clean_enabledGate_service_epoch returns restartFree on
  [actionCut a, idxBefore freeze] inside this gate's receiver interval.
  HistorySafeAt remains a separate input. Past processing does not supply it.
- Regression: Tests/CleanSuppressed has a well-formed schedule with wake 9 and
  a fresh HEAD at 10. At gate label 1 (time 20), raw confirmation is some genesis;
  the executed result is some none. This refutes the old unconditional raw equation.
- Public FGSAClaims statements and other owners' files were not edited.
  STOPs for approved public meaning changes: none.
- Audit/root inventory changes are in the P-Cl1 report and its audit fragment.
  The existing shared inventory and fixed S1 scope were not changed. These new
  Clean modules are outside the fixed S1 domain and are explicit package targets.
- Prepared validation: package DCK PASS with default controls (164.99 s; first
  cold package run 458.04 s). Prepared audit-root build --wfail PASS (4.78 s).
  The 48 core audit commands and three regression commands use only propext,
  Classical.choice and Quot.sound. Complete export/coverage check: 0 unaccepted
  (7.04 s). Layer check: 72 baseline findings, 0 new (0.30 s).

### P-Cl1 — current epoch invariant and joined batch (2026-10-10)

The prepared set now includes State, Action, GateOutput and Zero. The package
remains PREPARED, not CLOSED. Five P-Cl1 targets remain EXPECTED-FAIL.

- Internal statement, lead ruling 10-10: CleanHist.nonempty now requires
  enabledGateAt, including label 0. CleanHist.continues requires the joined
  voter at the exact next vote tick. CleanGateOutputStmt requires an enabled
  gate. These are the P6/P11 forms; no FGSAClaims file was edited.
- Internal statement, lead ruling 10-10: CleanState.saved requires the local
  restartFree interval and activeCompatible at the read. savedOnly and
  fastWrite origins include restartFree and an enabled origin gate. Durable
  S and lease origins still use completed event history from all epochs.
- Internal statement, lead ruling 10-10: CleanRestartStep no longer eliminates
  a restart. It states preservation of CleanState after the kept-state restart,
  under the existing foundation and source premises. State.clean_restartStateStep
  proves it. cleanState_of_hist now handles that event. Closure's restart branch
  uses cleanHist_step_restart; the full Closure module still waits for StepGate.
- R7: clean_gateInputs_from_rows uses the kept FG equality at the strict time
  cut. No whole-store equality or global NoRestart is used. The state proof
  uses RMonoAll and the durable/epoch foundation split. Zero excludes a restart
  at time 0 from RestartsAtWakes, rather than from global NoRestart.
- T07 source: clean_enabledGate_of_confirmedReader gives this gate's enabled
  guard from the exact confirmed reader at afterTicksIdx. Safety is still open.
- T10 core: clean_gate_head_prefixes_joined orders older results through z's
  earlier joined gate, then uses Continues for the joined voter y. The current
  actor x is used only for the F/frame part. It compiles with default heartbeats.
  StepGate.clean_gate_head_prefixes delegates to this exact interface.
- P6/T09/T11/T12 sender source: clean_gate_batch_joined counts joinedHonest at
  the vote tick. clean_joinedNow_of_joined_vote supplies the stored duty guard.
  StepGate now selects joined voters and keeps that guard in the HEAD emission.
  Its gate-zero and nonempty types require the enabled gate. N5 is still open.

P-ShA request: Shared/Count.lean:242 fgsa_late_rest_bound, :277
fgsa_gate_batch_premises, and :351 fgsa_gate_zero_of_receipts still require
all awake honest seats to be in H. The P6 joined set cannot satisfy that premise
when a voter wakes at its vote and has a suppressed duty. Add a joined-voter or
actual-emitter companion, with the same count conclusions and receipt outputs.
The joined-voter form replaces awake in hH by joinedAt at this exact vote tick.
Its proof must obtain joinedness from the actual honest emission; receiver
receipt callers still need ReadyTrigger, HistorySafeAt and their local epoch.
P-Cl1 did not edit Count or any other P-ShA file. The existing local stamp
supplier fgsa_gateReceipt_stamps_on is available and needs no replacement.

Open targets: TransferFrame needs receipt/root/epoch caller ports; Transfer,
StepGate, Closure and Safety then need their guarded consumer ports. These
remain P-Cl1 work after the needed Shared interfaces are available. No owned
repair with an EXPECTED-FAIL target is marked closed. clean_epoch_saved_row is
not yet supplied; P-Ar must not close against this checkpoint.

Validation: DCK PASS with default controls (250.37 s), including lake build
--wfail of all 475 GREEN modules. The local core audit has 112 commands; the
regression has three. All use only propext, Classical.choice and Quot.sound.
Complete export/coverage check on the prepared roots: 0 unaccepted (8.74 s).
Layer check: 72 baseline findings, 0 new. The expected-failure build fails in
TransferFrame and blocks its four dependent targets (5.81 s). Thus full-scope
export/audit closure remains open. No approved public meaning STOP occurred.

### Lead note after the P-Cl1 review (2026-10-10): Count deadline obstruction
rev-pcl1-astra finding 1: ReceiptCoverageSleepPremises (R/Statements/ReceiptCoverage.lean:64, :68, :78) forces
dl(a) = dl(t). Clean callers (C/StepGate.lean:562-564, C/TransferFrame.lean:379-382, :474-477) require objects
accepted at old times t with dl(t) = t + Δ, so a = t; a receiver that woke later (wake 24, acceptance 8, Δ = 2)
cannot meet deadline 10, and no Clean regime field supplies readiness/restartFree from t. WC/WCG
(dl(t) = max(t, GST) + Δ) force a = t after GST. These callers stay EXPECTED-FAIL. Choosing a = max(send, wake)
with the old deadline cannot work. Open: an anchor-relative deadline form (design check anchor-dl-sol running).
TransferFrame path interfaces (:335, :397) still need the joined receiver argument.

## P-ShA round 4 — joined voters and local services (2026-10-10)

Status: NOT CLOSED. Base: `1c777e97`. The JOINED-VOTER ruling applies to the
internal action-batch and two gate-receipt regime producers. No FGSAClaims
statement, Base₂ field, baseline or allow entry changed. Base₂ has no NoRestart
projection. Green is a compile status; it does not mean every legacy route is ported.

### Compiled interfaces and completed obligations

- `CatchUp.ReceiverService`: exact N4 inputs for one object and receiver. The
  ready anchor can follow a wake. The epoch starts at actionCut(anchor) and ends
  at idxBefore(freeze). Safe retained history remains an explicit input.
- `CatchUp.FreshHeadService.receipt`: processing and a strict freeze stamp for
  the exact emitted HEAD. History safety comes from
  `fgsa_historySafeAt_of_emitted_head`, at that same emission tick.
- `CatchUp.ReceiverService.proposal` and `fgsa_target_receipt_on`: exact named-body
  equality under P23-A, plus durable target membership. They do not equate roots
  without the named receipt scope.
- `Count.fgsa_receiptCoverage_on`: the sleep coverage branches, path receipts,
  vote-or-cap receipts, and strict stamps use receiver-local epochs. The exact
  handler WF/dependency/timeliness input remains explicit. This is stronger than
  the bare ReceiptCoverageSleepStatement input list; the Run sleep statement
  still has no proof on this base. No old-send awake premise is used by this route.
- `Count.fgsa_active_path_of_coverage_on`: the restarted active-path interface.
  The old `fgsa_active_path_of_coverage` type stays unchanged and remains legacy.
- `Count.fgsa_stored_honest_head_joined`, `fgsa_late_rest_bound_joined` and
  `fgsa_gate_batch_premises_joined`: joined HEAD origin and joined denominator.
- `GateReceipt.fgsa_gateReceipt_on`: joined selected voters, FreshHeadService,
  named target service, and the enabled gate actor. `GateReceiptScope` supplies
  the exact early-to-gate receiver epoch. The theorem also proves awake at the
  exact early read and the executed gate join test (T42).
- `GateReceipt.fgsa_gateReceipt_block_stamp_lt_on` and
  `fgsa_gateReceipt_block_to_tick_on`: local strict stamp and ready named receipt.
  The legacy stamp theorem is an explicit wrapper of the local form.
- `HeadAdmit.inclusion_head_receipt_early_on`: joined HEAD service at the exact
  early read, with a local read-to-tick epoch. `fgsa_action_walk_batch` now takes
  joined voters and a joined participation count, plus the exact services.
  `fgsa_action_walk_batch_legacy` keeps the awake form with explicit NoRestart.
- `ExactService.exactService_emitted_head_joined`, the receipt/raw/at/gate `_on`
  forms, `exactService_of_head_and_gate_on` and
  `exactService_participation_of_card_joined`: joined HEAD readers and selected
  voters. Gate service uses GateReceiptScope; the all-reader route keeps
  confirmedReaderAtIdx at the exact gate (T40).
- `SameLabel.fgsa_sameLabel_on`: local cross-reader service with a receipt-or-cap
  split. SameLabelServiceScope contains ready object service and exact enabled
  read epochs. It has no NoRestart field.
- `Regimes.fgsa_gateReceipt_clean` and `_recovery`: joined guard and the exact
  GateReceiptScope, under the internal ruling. Both compile in isolation.
  `_clean_legacy` and `_recovery_legacy` require explicit NoRestart.
- `ScoreRun.fgsa_scoreRun_metadata_retained_restart` and
  `fgsa_scoreRun_raw_subset_restart`: proposal metadata and the raw subset use
  durable storage across restarts.
- `RetainedPersist.fgsa_retained_proposal_mem_on_run_epoch`: ready named proposal
  service with explicit safe history. Membership persists to the actual HEAD
  tick through durable storage. This does not port the full retained geometry.
- `StoreRun.fgsa_votes_cumulative_on`: volatile vote persistence in one receiver
  epoch. Relay, SameLabel and ScoreRun keep their private legacy names and types
  as explicit wrappers of this local form.
- `Release.fgsa_release_bound_restart` remains the completed round 3 route.
  The explicit legacy release wrapper stays available.

### Exact blockers at the three open targets

`Export.fgsa_sameLabelClaim` still calls the legacy fgsa_sameLabel with the absent
Base₂.noRestart field. It needs a proof that SameLabelPrem.set plus its LabelSyncOn
supplies SameLabelServiceScope, or a direct proof with the same local obligations.
The conditional internal core now compiles. No false public conclusion is proved;
no extra public premise was added. Adding a NoRestart premise is not an accepted fix.

The following ten Regimes adapters still call legacy cores. Each failed projection
is from Base₂.noRestart. The two repaired gate-receipt adapters are not in this list.

- `fgsa_score_eq_on_clean_of_retained_proposal` and
  `fgsa_score_eq_on_recovery_of_retained_proposal`: port fgsa_score_eq_on_run through
  local frozen-vote, target-block and support receipts at the proposer/HEAD reads.
- `fgsa_ghost_transfer_sfx_on_clean` and `_recovery`: port the walk block/reflection
  routes and score equality, with their exact receiver epochs and ready services.
- `exactService_head_of_proposal_clean` and `_recovery` (T39): retain the joined
  HEAD-reader guard; port exactHead_of_proposal_on_run and its walk supplier.
- `exactService_head_of_retained_proposal_clean` and `_recovery` (T45): retain the
  joined HEAD-reader guard; port fgsa_retainedExactHead_geometry_on_run and the
  retained read suppliers. Each retained HEAD needs a replay object or explicit
  HistorySafeAt at its ready anchor. Past processing cannot supply that field.
- `exactService_of_head_clean` and `_recovery`: use exactService_of_head_and_gate_on
  with GateReceiptScope for each exact confirmed receiver and joined participation.
  The CleanSleep₂/HealthyPrefixSleep₂ companion contains joined count fields; the
  legacy CleanCut₂ fields count awake nodes. Recovery needs the joined window
  after GST. The old input HEAD premise also lacks the joined reader guard.

`Tests.RetainedConsumers`: Composes now has joined honest-reader quantifiers and
all test roots take NamedReceiptRootCollisionFree. Compilation still waits for
Regimes. Its `compose`, `check_H6`, `check_H6S`, `check_H17`, `check_L4R`, `check_HG1`,
`check_L2`, `q1_H6` and `q1_H6S` still test legacy read/geometry
suppliers with explicit NoRestart. Replacing only the reader quantifiers does not
finish their sleep path.

### Green legacy cores: theorem-level remaining work

The entries below still have only a legacy run-service proof on this base. Their
NoRestart premises are explicit. They must not be called final sleep APIs.

- `Shared/Relay.lean:509` — `fgsa_headVotes_provenance`.
- `Shared/Relay.lean:555` — `fgsa_vote_accepted_before_head_read`.
- `Shared/Relay.lean:649` — `fgsa_headVotes_backward_relay`.
- `Shared/Relay.lean:727` — `fgsa_cleanSupport_vote_forward`.
- `Shared/Relay.lean:887` — `fgsa_cleanSupport_forward_relay`.
- `Shared/ScoreRun.lean:350` — `fgsa_scoreRun_frozen_vote_relay`.
- `Shared/ScoreRun.lean:457` — `fgsa_scoreRun_raw_extra`.
- `Shared/ScoreRun.lean:592` — `fgsa_scoreRun_block_forward`.
- `Shared/ScoreRun.lean:636` — `fgsa_scoreRun_block_backward`.
- `Shared/ScoreRun.lean:718` — `fgsa_scoreRun_support_forward`.
- `Shared/ScoreRun.lean:785` — `fgsa_scoreRun_support_backward`.
- `Shared/ScoreRun.lean:907` — `fgsa_score_eq_on_run`.
- `Shared/ScoreRun.lean:986` — `fgsa_walkRun_frozen_block`.
- `Shared/ScoreRun.lean:1317` — `fgsa_walkRun_reflected_block`.
- `Shared/ScoreRun.lean:1427` — `fgsa_ghost_transfer_sfx_on_run`.
- `Shared/ExactHead.lean:95` — `exactHead_of_proposal_on_run`.
- `Shared/ExactHead.lean:171` — `exactService_head_of_proposal`.
- `Shared/RetainedPersist.lean:290` — `fgsa_retained_path_persists_on_run`.
- `Shared/RetainedPersist.lean:358` — `fgsa_retainedWalk_geometry_on_run`.
- `Shared/RetainedReflect.lean:235` — `fgsa_walkRun_reflected_old_child`.
- `Shared/RetainedReflect.lean:268` — `fgsa_retained_old_child_reflects_on_run`.
- `Shared/RetainedEndpoint.lean:189` — `fgsa_retainedExactHead_geometry_on_run`.
- `Shared/RetainedConsumers.lean:333` — `fgsa_retainedReads_H6`.
- `Shared/RetainedConsumers.lean:676` — `fgsa_retainedReads_H17`.
- `Shared/RetainedConsumersH6S.lean:19` — `fgsa_retainedReads_H6S`.
- `Shared/RetainedConsumersQ.lean:21` — `fgsa_retainedReads_L4R`.
- `Shared/RetainedConsumersQ.lean:60` — `fgsa_retainedReads_HG1`.
- `Shared/RetainedConsumersL2.lean:56` — `fgsa_retainedReads_L2`.
- `Shared/HeldReceipt.lean:22` — `healing_held_block_receipt`.

Relay provenance needs the restart replay branch of RelayCarried at the joined
HEAD read. The accepted-before-head-read supplier needs a strict local epoch and
an acceptance/replay origin. Its backward/forward relays need ready receiver
service for each vote or cap witness, with safe history and the exact freeze.

ScoreRun frozen-vote relay/raw-extra need the receiver's ready anchor, signed
object identity and frozen stamp bounds. Block forward/backward/frozen/reflected
routes need named target/ancestor services and exact endpoint floor compatibility.
Support forward/backward must convert those receipts into resolved vote support.
The score equality and ghost-transfer cores depend on those ports; a stored
proposal's durable metadata alone does not supply them.

ExactHead and the retained geometry/read suppliers need those score/walk ports.
The joined reader scopes in T39/T45 are already present; those guards do not prove
the missing service or retained history fields. HeldReceipt needs the same exact
ready service at its held-block cutoff.

### Family handoff: do not edit other packages

Use `fgsa_active_path_of_coverage_on E rho hvalid hdelta ... hcovSleep hpath hFK
hroots hReady`. Construct ReceiptCoverageSleepPremises with a valid post-wake
anchor per required object. Supply WF, dependencies and fgsaTimely only for the
named handler windows. Supply HistorySafeAt explicitly for retained routes.

The following caller theorems must replace the legacy Count call. Their owners
must also use Base₂.receiptIdealization for receipt-body equality.

- Clean/StepGate: `gate_active_heads`.
- Clean/TransferFrame: `clean_transfer_receipt_path`,
  `clean_transfer_receipt_path_of_head`.
- WeakContinuation/StepTransferReceipts: `prefreeze_path`.
- WeakContinuation/StepGateBatch: `gate_active_heads`.
- WeakContinuationGrowth/Dynamics: `growthStepGateBatch_gate_active_heads`,
  `growthStepTransferReceipts_prefreeze_path`.

P-Fi consumers `Finality/RowsBatch.rowsPrem_action_walk_batch` and
`Finality/TailBatch.ktail_action_walk_batch` must use the ruled joined action API:
joined selected voters, joinedHonest Batch, exact FreshHeadService/target service,
and the read-to-action receiver epoch. The old name is retained for the corrected
internal producer. The explicit old form is fgsa_action_walk_batch_legacy.

### Map and validation boundary

P-ShA map: 65 targets, 62 green including two input tests, three expected failures.
Owned targets: 60 green, three expected failures. Full map: 476 green, five
expected failures. HeadAdmit is now green. Run.Proofs.ReceiptCoverage is green
from its actual retired-import-path build; it does not prove the sleep statement.
Run and Run.Tests.Axioms stay S-Ap expected failures due to the five missing audit
names already recorded in round 3. No external source file was edited.

The new Regimes gate adapters and legacy companions have an isolated strict
Lean check. That check does not classify the full Regimes module as green.
The final checks and exact source lines are in claude-files/sleep-psha-report.md,
Round 4. Successful validation covers the green map only. Package closure still
requires every theorem-level blocker above to be resolved.

Final round 4 checks: DCK PASS (180.905 s), 42 strict
audits / 2,891 results, all 24 controls PASS. Complete green exports: 255 proof
modules / 253 exports / zero unaccepted. SharedAxioms coverage: 364 entries PASS.
Layers: 72 inherited / zero new. Expose and sleep scopes PASS. Two inherited W3
transparency findings remain. The open-target check confirms the ten Regimes
projections, Export's legacy call and the five missing S-Ap Run audit names.

## P-ShA round 5: exact gate service

The old Regimes declarations remain unchanged. Additive forms are in
`Proofs/Shared/RegimesService.lean`. `exactService_of_head_clean_on` and
`exactService_of_head_recovery_on` use joined HEAD readers, joined Batch and
release counts, and `GateReceiptScope` for each confirmed receiver at the same gate.
The Clean and Recovery consumer must supply these local scopes. Their old awake
counts do not prove a joined count. Recovery needs its join window after GST.
No `NoRestart` premise or restored Base field is used by these forms.

### Round 5: proposal HEAD, score and walk ports

Additive `ScoreServiceScope` supplies frozen HEAD ReceiverService and exact named
block TargetReceiptService in both directions. It also supplies the source epoch
from the strict proposal read to its tick. Each ReceiverService has its own
HistorySafeAt and handler window. No theorem takes the final score equality,
walk cover, or exact HEAD as a new service premise.

The score and support proofs use durable proposal metadata after restart.
The walk proof keeps both the frozen and authenticated proposal-path reflection
arms. `exactService_head_of_proposal_on` keeps the joined-reader guard.
Its Clean and Recovery consumers are the corresponding `_clean_on` and
`_recovery_on` adapters in RegimesService. Those consumers supply the scopes.
All previously compiled declarations remain unchanged.

### Round 5: SameLabel public Export

`fgsa_sameLabel_serviceScope` supplies the entire SameLabelServiceScope from
ExecutionValid, RestartsAtWakes, the delta equation and LabelSyncOn. Export uses
BaseSet's existing fields. The public SameLabelClaim type is unchanged.

The proof rejects future HEADs before the label's proposal tick. A replayed HEAD
comes from a raw list in a retained proposal. The raw label plus that proposal's
strict slot bound rules out a same-label replay before this tick. This also
handles the zero label, because RestartsAtWakes requires a positive wake time.
Enabled gates bound every prior local restart by the label's proposal time.
Those bounds give awake service at the early anchor, safe HEAD history, and the
exact epochs through the strict gate read. The receipt deadline uses the same
LabelSyncOn delivery law. No per-reader scope or history premise was added to
SameLabelPrem or to the public claim.

### Round 5: retained geometry and read services

`RetainedServiceScope` supplies the named proposal service and ScoreServiceScope for each candidate whenever both endpoint floors apply. Candidate services keep
HistorySafeAt per object; old processing is not used to fill that field.
`RetainedExactHeadRunGeometryOn` restricts admission, walk and endpoint suppliers
to joined readers. The new retained geometry theorem constructs those fields;
it does not accept an exact HEAD or final walk cover as a service premise.
The old geometry record and all its compiled consumers remain unchanged.

All six read suppliers have additive `_on` forms: H6, H6S, H17, L4R, HG1 and L2.
They use TargetReceiptService for the proposal and durable block storage to the
actual HEAD tick. The local service input is separate from elementary lane reads.

Named downstream suppliers (other families, not edited here):
- Healing `repair_head_exact` and `frontier_seed_qSucc_head`: H6/H6S object service.
- Healing `frontier_later_head`: HG1 object service and retained candidate services.
- WeakContinuation `wc_retainedReads` / `wc_exactProposal`: H17 object service,
  candidate services and safe retained replay history at each ready anchor.
- Assembly `wcg_exactProposal`: the analogous WCG retained object services.
- L4R and L2 callers supply the same object scope within their stop intervals;
  their private type checks in Tests.RetainedConsumers identify the complete input.

The Clean and Recovery retained `_on` adapters pass these inputs for each joined
reader. No caller may infer retained HistorySafeAt from a past processed result.

### Round 5: preserved original Regimes bodies — STOP on NoRestart

False required implication:
`ExecutionValid E rho ∧ RestartsAtWakes E rho → NoRestart rho`.
Counterexample: Run.Tests.Sleep `joinEnv 9` / `joinRun 9` is ExecutionValid and
restarts at wakes (`SleepTests.join_valid 9 (Or.inr rfl)`). Its event at index 1
is `.restart 0 9`. Thus NoRestart fails at exactly that index. The receiver is
awake at the slot-1 HEAD tick 10 but its wake exceeds the previous slot start 0;
Tests.RestartEpochs `awake_head_tick_not_joined` checks the suppressed duty.
The historical processing → HistorySafeAt implication is also false at wake 35
in `retained_head_history_not_safe` in that test module.

The ten original Regimes declarations still request `h.base.noRestart`. That
projection does not exist and cannot be restored under the approved model.
All their names and types are preserved as requested. This is a STOP on supplying
the false legacy premise, not a kernel refutation of all ten full conclusions.
Their new true forms are the ten `_on` declarations in RegimesService. They use
joined participation, per-receiver gate scope, ScoreServiceScope, or
RetainedServiceScope. No public FGSAClaims statement change is requested.
The original module remains EXPECTED-FAIL; its legacy bodies are not certified.

### Round 5: joined read suppliers

H6/H6S/H17/L4R/HG1/L2 now also have `_joined` forms. Every elementary reader
input, TargetReceiptService, and read-premise conclusion has the same joinedAt
guard at the actual HEAD tick. Tests.RetainedConsumers uses these forms and its
RetainedServiceScope input has that same guard. The earlier additive `_on`
forms remain unchanged for callers that supply all-reader service.

### Round 5: Relay and held-carrier inventory

`HeadRelayServiceScope` has one HEAD object, a strict freeze, its reader index,
its epoch, and a conditional ReceiverService. Scope suppliers are guarded by
membership of the actual HEAD candidate, or by equality with the actual clean
support wire. They do not require service for every possible payload.
New Relay forms cover provenance, backward late-pool relay, frozen clean-support
vote relay and forward support incidence. The existing path read input remains
explicit in the support-incidence form.

`fgsa_vote_accepted_before_local` excludes replay-only origins with a local
restart bound and the earlier label tick. Relay's joined HEAD-read supplier
constructs that tick and bound from joinedAt. No global NoRestart is needed.
The new frozen walk alias uses the named backward block service.
`healing_held_block_receipt_on` obtains the exact held FG carrier from its
TargetReceiptService. These forms cover the Relay and HeldReceipt entries in
round 4's legacy-only inventory. Legacy conditional APIs remain unchanged.


## P-H1 — Round 2, local recovery and retained service (2026-10-10)

Base eb5c6b65 on sleep-ph1b. Resume after login-token loss; all prior source
changes are retained. NEW-OWNED-MODULES approves Healing/SupportRecovery.lean.
No Claims statement, protocol rule, checker, baseline, or allowance changes.

Correction to the Round 1 summary: its committed map has 38 GREEN targets,
60 open targets, and six REQUIRED supplier failures. This Round 2 map has
99 targets: 54 GREEN and 45 open. Four REQUIRED suppliers remain open:
Shared/Regimes and Shared/Export (P-ShA), Run facade and Run audit (S-Ap).
P-Fd durable/epoch producers are present and checked in HealingPhaseSettle.

Internal replacements and consumers:
- PhaseOrder adds all-restart top, contest, and phase-order proofs using RMonoAll.
  PhaseRelay adds healing_frontier_mono_all. PhaseSettle adds a durable quiet
  window and healing_settle_start_on with per-carrier TargetReceiptService.
  AttemptSettle consumes those services instead of Base₂.noRestart. Its four
  row adapters keep their settlement conclusions. H2 must pass the same services.
- PromotionPhase uses RMonoAll and durable TF through quiet phase extensions.
  PromotionReceipt uses exact ReceiverService for the emitted proposal after
  proving its compatibility. The service contains object history, readiness,
  handler prerequisites, and the local event-index epoch. PromotionSource and
  PromotionAdvance now compile. Age/Renewed/Terminal thread the same service.
- FrontierSupportFrame adds frontier_F_below_all using durable TF; its original
  frontier_F_below is an explicit legacy wrapper. The legacy relay helpers take
  receiver awake at their exact deadline and receipt-scope root idealization.
- SupportRecovery bounds honest restarts by GST. It excludes later restarts on
  [idxBefore(GST + 1), j), while permitting a restart at GST. Its stamp and frame
  adapters use RStoreEpoch and RFrameNextEpoch on those exact indices. Durable
  TF, blocks, and finality use RStoreDurable and RMonoAll.
- SupportRecovery derives joinedAt from the previous-slot cutoff. It proves
  joinedHonest = honest and the batch/fast counts in that suffix.
  repair_exact_service_on consumes the P-ShA local gate geometry and receiver
  scopes. It does not reconstruct NoRestart from a recovery regime.
- repair_head_exact is the retained H6 supplier named by P-ShA Round 5. It uses
  fgsa_retainedReads_H6_joined and the retained Recovery _on service adapter.
  Each object retains its own HistorySafeAt inside TargetReceiptService; each
  actual reader has the same joinedAt guard in input, service, and conclusion.
  Elementary RetainedH6Input and RetainedServiceScope remain explicit inputs.
- PostResetRead adds healing_postReset_retainedReads_at_on using H17_joined.
  It keeps the common pivot and each reader's actual state. Retained cone inputs
  and exact object services are guarded by joinedAt at that reader's HEAD tick.

Scope limits and open suppliers:
- The base still contains ten invalid Base₂.noRestart projections in P-ShA's
  legacy Regimes. Their correction is on 80b08ce3 and is not in this base.
  This writer does not edit or merge that owned supplier.
- SupportTransfer still blocks the later support, repair, and reset modules.
  Its release/fast-write guards, receipt root form, and local relay scopes need
  further ports. No OPEN target is marked CLOSED by this ledger entry.
- RepairH6 reserves repair_head_exact for SupportRecovery and renames its old
  producer to repair_head_exact_legacy. RepairH6 remains EXPECTED-FAIL; its
  later lease/input proofs still need suffix epochs and local object services.
- No public STOP or public meaning change was introduced. Retained history
  cannot be inferred from past processing; JOINED-VOTER still applies.

Audit integration uses the existing full FGSAProofs audit key. The complete
132-row local inventory is in scripts/dev-pkg/P-H1.coverage-fragment.txt.
The lead must merge that fragment and its root import during serial integration.
P-H1 remains PREPARED on the certified set; full CLOSED is pending.

Round 2 gate/relay extension:
- SupportGate consumes fgsa_gateReceipt_on and the joined batch theorem.
  healing_support_gate_cover now takes RecoverySleep₂, the previous-slot
  cutoff covering GST, and GateReceiptScope at its actual receiver gate.
  The unchanged conclusion covers the raw confirmation. Awake alone cannot
  supply the former all-honest HEAD batch (JOINED-VOTER).
- healing_recovery_gate_scope derives enabledGateAt, receiver joinedAt and
  the early-read-to-gate index epoch from the recovery suffix. Its fresh HEAD
  and retained target services remain explicit, per object.
- SupportFrame adds healing_head_witness_relay_on. The source's actual HEAD
  carrier and height witness are unchanged. Each carrier's ready target
  service gives its ancestor path at the exact receiver deadline.
- SupportRelay adds healing_support_prefreeze_path_on. Strict read stamps use
  fgsa_block_stamp_before_read; their prefixes use fgsa_store_cumulative_on
  on [idxBefore(freezeTime s), receiver HEAD index). No global NoRestart.
- H2 must pass the cutoff and local GateReceiptScope at all gate-cover calls.
  SupportLease, SupportSlow and SupportOutput remain owned P-H1 port items.

Round 2 promotion extension:
- PromotionAge, PromotionRenewed and PromotionTerminal now use RecoverySleep₂
  at their emitted-proposal paths. The selected proposer restart bound follows
  from GST, the carrier/period budget and suffixNoRestart. A wake at GST is allowed.
- Age/renewed/terminal receipts thread the same per-proposal ReceiverService.
  Quiet extensions use RMonoAll. All three modules compile with --wfail.
- Terminal recurrence rounding is private arithmetic over Recovery₂.gap. It
  removes this module's import of the broken legacy Regimes alignment adapter.
  Its budget and conclusion are unchanged; no public alignment premise was added.

HealingAttemptTerminal now checks the terminal supplier with RecoverySleep₂,
RMonoAll and the same exact proposal service producer. Its inclusive grid and
maturity boundary test is unchanged. The test compiles with --wfail.

Round 2 final validation: DCK P-H1 PASS, 174.47 s; 519 GREEN roots, 39 strict
sources and 3,023 axiom results; only propext, Classical.choice and Quot.sound.
All 24 default controls and DCK controls pass. Complete GREEN exports: 316
proof modules, 253 exports, zero unaccepted (8.58 s). Complete local coverage:
132 rows PASS (6.51 s). Layers: 72 inherited findings, zero new. The all-target
build still fails in owned SupportTransfer and P-ShA legacy Regimes; all other
open targets remain classified under their actual owners. Full P-H1 NOT CLOSED.
## S-Ap Round 3 — Run facade audit

P3 wake-clock successors: replace the retired audit names
fgsa_restore_now_retained, fgsa_hrestore_now_retained, and restore_st_retained
with fgsa_restore_now, fgsaRestoreTimeLaw, and restore_st. The exact wake time
replaces the old retained clock. No production statement changes.
The existing spec_prune_restart_mem and spec_prune_sleep checks keep their names;
import Proofs.Spec.Simulation so the audit can resolve them.
Run facade --wfail PASS (10.79 s). Regenerated the existing Run audit
coverage key (8.54 s); mark the Run facade and audit GREEN in S-Ap.

## S-Ap Round 3 — P8 claim transfer

D140: RowServiceBaseClaim now has the exact approved all-honest awake suffix
from GST through the horizon. NoRestart remains. A permanent honest sleeper
satisfies the old receiver demands vacuously but need not receive an emitted row.
P8 public route: RowServiceClaim now takes RecoverySleep₂. The compiled P-Fd
supplier fgsa_tRows_recovery accepts its toRecovery₂ projection. The base
supplier fgsa_tRows accepts the new awake suffix. No new premise is invented.
The P8 declarations and aggregate compile with --wfail (1.29 s). The broader
Claims build also checked inherited fixtures: FinalityGST, FinalityW,
HealedBest, WeakContinuation, OutageAlignment, and the kernel adapter example
in Claims.Tests.Axioms fail on prior sleep changes. They are not P8 failures.
The FGSA shallow/deep generator includes eight inherited P-Fi claim hashes.
The auxiliary API generator stops on the missing Claims.Tests.Axioms artifact;
its full source scope is kept. No generated entry is edited by hand.
The Run inventory generator now succeeds (791 entries, 25.01 s) and removes
the stale fgsa_receiptCoverage entry retired under DECISION P23-A.
FGSA shallow/deep regeneration PASS (243.02 s, 1,357 roots).

## S-Ap Round 3 — P17 D013/D014 continuation supplier

OutageContinuationConcl is the exact approved D013 body: scoped record/output
compatibility; inclusion only for coveredNodes; scoped emitted HEAD compatibility;
durable F compatibility for every honest receiver. It takes fast, T, b₀, b₁
and Fintype V. No proposal-parent extension is added.
OutageContinuationClaim is the exact D014 wrapper with
OutageContinuationSleepPrem and all four conclusion arguments. P-Ou's report
at lines 43, 92 and 145 requests this supplier; its family proof remains P-Ou-owned.
The two docstrings now describe the approved scopes.
D013/D014 and the claim aggregate compile with --wfail (3.47 s).
The claims inventory and auxiliary API writers stop on the inherited missing
Claims.Tests.Axioms artifact; their source scopes are unchanged.
FGSA shallow/deep regeneration PASS (238.12 s, 1,357 roots).

## S-Ap Round 3 — remaining public wrappers

P8 D034/D037/D048: HTimeConcl, ResetArrivalConcl, HTimeBestClaim, and
HTimeSearchClaim now use the exact approved recoveryStart bounds and search
origins. Their numerical budgets do not change. These supply P-H1's public route.

Serial P-Fd fragment: fgsa_fgFoundationClaim uses the durable/epoch companions
and RMonoAll; fgsa_rowServiceBaseClaim passes the approved awake suffix;
fgsa_rowServiceClaim uses fgsa_tRows_recovery with toRecovery₂; the new P21(a)
fgsa_finalizedMonotonicityRestartClaim exports its compiled Foundations body.
All four wrappers have local strict audit commands. No family proof is replaced.

The anonymous kernel adapter example in Claims.Tests.Axioms now takes an
explicit Recovery₂-to-RecoverySleep₂ supplier. P-Fi must prove that supplier;
the example checks only the composition with its new AC interface. No public
claim, KernelPrem_W, or KernelJoinedPrem changes. The attempted move to
FinalityW was discarded because CLAIM-USE forbids that import. No layer
exception is added. The two best/search audit examples use the approved τ
premises. Observed inherited fixture failures have family owners in S-Ap's map.

P-Fi's eight approved public changes are already present. P-Ar's derived receipt
claim type already exists. Neither report requests another S-Ap statement change.
Their current receipt producers remain family proof obligations. P-Ou's other
Claims.Outage replacements are prepared on sleep-pou; lead integration retains
that package's work. D013/D014 are supplied in this branch.
The serial Foundations wrappers compile. The final package --wfail build
passes (3,675 jobs). Claims audit coverage regeneration keeps the existing
814-entry key. Layer check: 72 accepted findings, zero new.
The full claims inventory and auxiliary API writers now reach the inherited
missing Tests.FinalityGST artifact. No failed family module is removed from
the generators' scope, and no generated entry is edited by hand.
Complete export check: all 471 GREEN roots, 279 proof modules, 253 exports,
zero unaccepted; zero non-exposed Statements predicates (5.39 s). Complete
coverage of the three changed audit sources also passes. DCK checks every
GREEN audit with Lean. The broader source-parser coverage probe cannot resolve
the inherited open-namespace command window_bit_add_of_row in WindowLiveness;
that probe is not reported as a complete package coverage pass.
Final FGSA shallow/deep regeneration PASS (243.60 s, 1,357 roots).

Validation correction: the first DCK passes its build and 41 strict sources
(4,017 commands), then the finality coverage control detects the missing
canonical audit command for fgsa_finalizedMonotonicityRestartClaim. Add that
command to Proofs.Tests.Axioms as required by the serial P-Fd handoff. The
local strict command remains. No coverage allowance changes.
The full canonical coverage writer is blocked by missing Shared.Regimes.
The new P21 row is instead taken from CheckProofEqns' compiled local coverage
output and rendered into the existing Foundations.Export owner block with
check-proof-coverage.py's section writer. All other rows and keys are kept.
The canonical source registration check passes: 24 modules, 227 declarations.
This fragment integration is not a full canonical-audit build or regeneration.

## S-Ap Round 3 — Count restriction, LEAD DECISION

ReceiptCoverageSleepPremises.slotWindow has t <= a and dl(a) <= dl(t).
Its deadline field makes dl monotone. Therefore dl(a) = dl(t).
For Clean dl(t) = t + Δ, a = t. For WC/WCG
 dl(t) = max(t, GST) + Δ, a <= max(t, GST).
The Lean evidence is count-restriction.lean and count-restriction.log.

The current Count handoff needs this correction: its hReady premise is over
[t, dl(t)), not only [a, dl(a)). An anchor-scoped internal companion can fix
that excess premise but cannot remove the public record's deadline restriction.
The exact handler premise is:

```lean
∀ o t, required o t → ∀ j u, t ≤ u → u < dl t →
  V2.D.Run.handlesAt E rho j x o u →
  (fgsa p c).wellFormed o = true ∧
  (fgsa p c).depsPresent (V2.D.Run.stateBefore E rho j x) o = true ∧
  fgsaTimely p (V2.D.Run.stateBefore E rho j x) o
```

An approved consumer needs a later-anchor route: P19/P20
SourcePendingReceipt, used by PendingSourceDelivery₂ and
CleanGrowthContinuationSleep₂, quantifies over all a >= send. It uses
max(a, GST) + delay, including wakes in the continuation after GST.
The joined participation count does not forbid an individual receiver's wake.
The old source trigger cannot in general be replaced by a new emission or relay
at the wake. This affects the proposed Count ports of
WeakContinuationGrowth.Dynamics.growthStepGateBatch_gate_active_heads and
WeakContinuationGrowth.Dynamics.growthStepTransferReceipts_prefreeze_path.
The Clean and WC historical-path ports have the same restriction when an old
object must be supplied after a receiver wake. Fresh HEADs may instead use their
own current emission anchor; durable stored paths need no new receipt.

Concrete restriction witness: send = 0, GST = 1, wake/anchor = 3, Δ = 2.
The approved pending service can use deadline 5. The existing Count record
requires 5 <= 3. This is impossible. This arithmetic example refutes a general
adapter from later-anchor service to the old Count record; it is not a
counterexample to the full public continuation claim.

Proposed exact additive change: keep ReceiptCoverageSleepPremises and
ReceiptCoverageSleepStatement unchanged. Add
ReceiptCoverageAnchoredSleepPremises with the same parameters and four field
names. Copy within, compat and deadline byte for byte. Replace only slotWindow
by the following type. In this companion, required o a and paths refer to the
service anchor a; send is the original trigger time.

```lean
  slotWindow : ∀ o a, required o a →
    ∃ send, send ≤ a ∧ 0 ≤ a ∧ a < dl a ∧
    Gen.V2.Duty.ReadyTrigger E rho o send x a (dl a) ∧
    Gen.V2.Duty.HistorySafeAt E rho x o a ∧
    V2.D.restartFree rho x (V2.D.Run.actionCut rho a) (V2.D.Run.idxBefore rho D) ∧
    first ≤ V2.D.Run.actionCut rho a ∧
    (fgsa p c).wellFormed o = true ∧
    (∀ s signer K, (toWire p o).decode = some (.vote s signer K) →
      ((V2.D.Run.stateBeforeTime E rho (dl a) x).st.slot p ≤ s + 1) ∧
      ∀ i t', V2.D.Run.actionCut rho a ≤ i → i < V2.D.Run.idxBefore rho (dl a) → a ≤ t' →
        V2.D.Run.handlesAt E rho i x o t' →
        s ≤ (V2.D.Run.stateBefore E rho i x).st.slot p ∧
          (V2.D.Run.stateBefore E rho i x).st.slot p ≤ s + 1)
```

Add ReceiptCoverageAnchoredSleepStatement and
ReceiptCoverageAnchoredSleepStatement_def by copying the existing statement
and equation and changing only the record name and declaration names. Thus every dl t in the copied conclusion is the anchor deadline because
the required predicate is now indexed by anchors. The original send is kept
explicitly in ReadyTrigger. No old-send deadline is silently weakened.
Any internal producer must still take or derive exact handler readiness on
[a, dl(a)), safe history, and the receiver epoch. This proposal does not assert
that the current bare public receipt statement has a proof.

Decision needed: approve this additive anchor-indexed public contract, or require
families to use direct receiver-service proofs when a exceeds max(send, GST).
No public record, Count theorem, or consumer proof was changed for this item.

### S-Ap Round 3 final validation

DCK S-Ap PASS (169.98 s): 471 GREEN modules, 41 strict sources, 4,017 commands,
and all default controls. Only propext, Classical.choice and Quot.sound occur.
FGSA shallow API PASS (167.03 s): 1,357 entries, complete matching hashes.
FGSA deep API PASS (118.80 s): 1,357 roots, 3,818 dependency nodes.
All 55 deep-snapshot controls PASS (164.59 s). Complete GREEN exports PASS:
279 proof modules, 253 exports, zero unaccepted. Layers: 72 accepted, zero new.
All eight changed public definition bodies match the approved packet tokens.

Full claims inventory/API generation and the auxiliary check remain blocked by
Tests.FinalityGST. Snapshot controls pass V2/GEN/FGSA shallow, catalog-lock and
source-scope checks, then stop on that artifact at the mapped-root control.
Full canonical Proofs.Tests.Axioms coverage generation remains blocked by
Shared.Regimes; the new P21 row is integrated from compiled generator evidence.
These are recorded limits, not full API or family closure. No generator scope,
public statement, baseline or allowance was weakened to bypass them.

## P-Fd Round 2 — CLOSED (2026-10-10)

Base: fabc390e on sleep-pfd2. It includes the S-Ap Round 3 public P8 claims
and four Foundations export fragments. P-ShA closure 80b08ce3 is not on this base;
the interfaces needed by P-Fd are present in rounds 1–5. This entry closes P-Fd only.

- P8 base: Foundations/Export.lean:160 applies RowService.lean:317 to the installed
  RowServiceBaseClaim, including NoRestart and the exact all-honest awake suffix.
- P8 recovery: Export.lean:166 applies fgsa_tRows_recovery to h.toRecovery₂.
  Recovery supplies the awake suffix and the receiver epoch after GST. It needs
  no global NoRestart. Public RowServiceClaim keeps RecoverySleep₂.
- Export.lean:139 assembles the durable/epoch store, RMonoAll, and epoch frame tuple.
  Export.lean:200 supplies the P21(a) retained-store restart monotonicity claim.
  All four installed fragments compile against their installed public claim types.
- Register all 37 exports in FoundationsAxioms through Assembly.Foundations.
  Move the four temporary production audit commands to that test audit.
  Append 28 missing supplier commands to Tests.Axioms and 28 matching rows under
  its existing canonical coverage key. All 151 local declarations have canonical
  commands and owner rows. The root already exposes Assembly.Foundations.
- Owned consumers: Tests.RowService uses fgsa_rowService_receipt_sleep with the
  exact receiver epoch; Tests.FinalityApi uses restart monotonicity without NoRestart.
  No public meaning change, new STOP, allowance, baseline, or coverage key.
- Map: 30 TARGETS, 497 GREEN, 2 EXPECTED-FAIL. Six inherited failures now compile.
  Add the inherited S1 RegimesService entry. The remaining failures keep their owners:
  Shared.Regimes (P-ShA) and the canonical Tests.Axioms root (P-As). Shared.Regimes
  still projects removed Base₂.noRestart at ten legacy sites; its closed-branch fix
  must be integrated. It does not block the P-Fd suppliers, exports, or local audit.

Validation: DCK PASS (223.32 s), lake build --wfail on all 497 GREEN modules,
40 strict sources / 3,436 results, and 24 default controls PASS. Only propext,
Classical.choice, and Quot.sound occur. Complete GREEN export scan: 283 proof modules,
253 exports, 0 unaccepted (5.94 s), complete local coverage of 151 commands,
and export checker controls PASS. Inventory generation: 4.95 s. Canonical FGSafety
coverage: PASS (15.92 s). Layers: 72 accepted findings, 0 new (0.47 s).
Diff whitespace check PASS. No gate tier, review, agent, or dependency update.

The broader all-audit inventory attempt found the unrelated namespace-local
WindowLiveness name window_bit_add_of_row. The final export check uses complete
FoundationsAxioms coverage and scans all GREEN roots; DCK strictly checks every
GREEN audit source. Full canonical-root validation remains assembly integration work.
Report and validation evidence: claude-files/sleep-pfd-report.md (Round 2),
claude-files/sleep-pfd2/. Earlier PREPARED rows remain as session history.

### Lead note after the P-Cl2 review (2026-10-10 08:35)

Review rev-pcl2-astra: MERGE-AS-PREPARED (not CLOSED). Merged at sleep-int.
- The "wait for the anchor-relative design" item in scripts/dev-pkg/P-Cl2.ledger-fragment.md:48-55 is stale.
  DECISION ANCHOR-DL applies: ReceiptCoverageAnchorPremises and its Count proof are internal to P-ShA's
  Shared layer. Do not wait for S-Ap to repair ReceiptCoverageSleepPremises; public P23 is unchanged.
- Caller route for the P-Cl1 dependencies: Clean/StepGate.lean:562 anchor v_s, deadline e_s, with the
  receiver's enabled-gate guard through gate_batch_of_history:644 and gate_active_heads:462 (s + 1 for
  the successor-label call). Clean/TransferFrame.lean:379 and :474 anchor e_s, deadline f_s, with the
  receiving node y's joined guard through :335 and :397. Bind readiness, handler interval, HistorySafeAt,
  restartFree and path deadlines to the same anchor.
- P-Ou applies the exact growth handoff (ledger fragment :61-122) with its Claims/Outage port. The
  section-wide include lists at Outage/Export.lean:85 and :117 must not carry old all-honest
  hmono/history suppliers into the new theorem.
- DECISION P15-CUT is separate (S-Ap round 4). Record both decisions separately.
- Before CLOSED: P-Cl1 and S-Ap closure, the P-ShA anchor caller ports, proofs of both growth suppliers
  (proposal/history compatibility; scoped inclusion), the actual P-Ou consumer build, production
  Clean/Export compilation, canonical strict/export audits.

## P-ShA Round 7 — DECISION ANCHOR-DL internal supplier

The lead's 2026-10-10 08:12 decision permits this additive internal interface.
`Shared/Count.lean` now defines `ReceiptCoverageAnchorPremises` and
`ReceiptCoverageAnchorStatement`, with `anchor : Obj p → Time → Time`.
The fields match anchor-dl §1. The statement closes the final HEAD quantifier
with `)`; the design text omitted that delimiter. This is a syntax repair.
`fgsa_receiptCoverage_anchor` and `fgsa_active_path_of_coverage_anchor` use
`dl (anchor o t)` for every receipt, strict HEAD stamp, and path vertex bound.
They keep the requested path/read time D. No `dl(a) ≤ dl(t)` input is required.
The proposal branch uses `ReceiverService.proposal`, whose proof uses N4.
The HEAD branch uses the N4 receipt theorem or the cap alternative at dl(a).
The record includes handlers on exactly `[a, dl(a))` and the receiver epoch
from `actionCut(a)` to `idxBefore(D)`. The anchor need not be monotone.

This interface is in the P-ShA proof layer. The old Count interfaces and all
FGSARun/Statements and FGSAClaims declarations remain unchanged. The bare public
`ReceiptCoverageSleepStatement` is still open. No public P23 amendment is made.

The resume check found a missing required S1 scope entry for AnchorService.
`scripts/dev-scope-s1.txt` now registers the module as REQUIRED. The package map
and audit inventory already included it. No allowance or baseline was added.

### Common proposal suppliers and record construction

Import `AvailableChainFGSAProofs.Proofs.Shared.AnchorService` for service inputs
and `AvailableChainFGSAProofs.Proofs.Shared.Count` for the coverage result.

- `fgsa_historySafeAt_of_proposal` transfers each historical root witness through
  durable TF, including across restart. It needs the proposal decode, not roots.
- `fgsa_proposal_acceptance_facts` uses the original acceptance and validity for
  send nonnegativity and well-formedness.
- `fgsa_proposal_handlers_at_anchor` uses the original source acceptance, the
  delay equation, and a public awake receiver anchor. Its tick precedes every
  handler, including a same-time delivery. The source admission bound and the
  local receiver epoch give timeliness. Valid direct delivery gives dependencies.
- `fgsa_gate_path_anchor_service` takes THIS receiver's `enabledGateAt` hG,
  validity, RestartsAtWakes, the delay equation, and each honest original proposal
  acceptance before v_s. It derives ReadyTrigger at v_s through e_s, proposal
  HistorySafeAt at v_s, the epoch through idxBefore(e_s), and proposal handlers
  on `[v_s,e_s)`. `fgsa_enabledGate_anchor_epoch` supplies later strict reads up
  to the gate. Honesty or selected-voter joinedness does not replace receiver hG.
- `fgsa_transfer_path_anchor_service` takes
  `joinedAt p E rho y (s+1) (voteTime (s+1))`, the next-vote horizon bound,
  validity, the delay equation, and each honest original proposal acceptance
  before e_s. It derives ReadyTrigger at e_s through f_s, proposal HistorySafeAt
  at e_s, the epoch through idxBefore(v_(s+1)), and handlers on `[e_s,f_s)`.
  Restrict its epoch to idxBefore(f_s) by `fgsa_idxBefore_mono` and `.mono`.

Keep `first = 0` in all seven records. For gate paths select
`anchor := fun _ _ => v_s`; for transfer paths select
`anchor := fun _ _ => e_s`. Clean uses `dl(a) = a + Δ`. WC/WCG use
`dl(a) = max(a,GST) + Δ`; their GST bound at v_s makes the chosen deadlines
exactly e_s and f_s. Rewrite these equations in the supplier results.
Use the regime's healthy/sync field for `within`. Use base.valid, base.delta,
and base.receiptIdealization for validity, the delay equation, and receipt roots.
The acceptance remains at the original t; do not invent a trigger at the anchor.

The seven required predicates contain only proposals. Their `slotWindow` field
is vacuous: the block decode cannot also be a vote decode. Construct `service`
from the suppliers, the public time inequalities, `Nat.zero_le actionCut`, and
well-formedness from `fgsa_proposal_acceptance_facts`. Keep the callers' existing
compatibility, pathCoverage, proposalPaths, horizon/cut, ancestor, and F-below-target
proofs. Each path vertex now requires `dl(anchor o t) ≤ d`, not `dl(t) ≤ d`.
Call `fgsa_active_path_of_coverage_anchor` with the SAME anchor function.
No general retained-HEAD history claim follows from these proposal suppliers.

### Exact seven-caller owner port plan

The source lines below are the pinned anchor-dl §3 references, not moving lines
in this worktree. P-ShA has not edited Clean, WC, or WCG files.

```text
┌─────────────────────────────────────┬───────┬─────┬───────┬─────────┐
│ Count call                          │ Owner │ Node│ Anchor│ Read D  │
├─────────────────────────────────────┼───────┼─────┼───────┼─────────┤
│ Clean/StepGate.lean:562              │ P-Cl1 │ x   │ v_s+1 │ e_s+1   │
│ Clean/TransferFrame.lean:379         │ P-Cl1 │ y   │ e_s   │ f_s     │
│ Clean/TransferFrame.lean:474         │ P-Cl1 │ y   │ e_s   │ f_s     │
│ WC/StepGateBatch.lean:344            │ P-WC  │ x   │ v_s   │ e_s     │
│ WC/StepTransferReceipts.lean:260      │ P-WC  │ y   │ e_s   │ f_s     │
│ WCG/Dynamics.lean:1529               │ P-WC  │ x   │ v_s   │ e_s     │
│ WCG/Dynamics.lean:2810               │ P-WC  │ y   │ e_s   │ f_s     │
└─────────────────────────────────────┴───────┴─────┴───────┴─────────┘
```

Here `v_s+1` and `e_s+1` mean v_(s+1) and e_(s+1).

1. Clean StepGate: pass the existing nonempty theorem's exact receiver hG at
   :676 through `gate_batch_of_history` :644 and `gate_active_heads` :462.
   Use the gate supplier with label s+1. Acceptances at :337/:350 precede v_(s+1).
   Do not derive hG from the nonemptiness result that this proof establishes.
2. Clean TransferFrame :379: add the joined y guard to the interface at :335.
   Thread it from `CleanHist.continues`. Acceptances at :260/:267 precede e_s.
   Use the transfer supplier; restrict its longer epoch to f_s for Count.
3. Clean TransferFrame :474: add the same joined y guard at :397. Use the same
   transfer supplier. Keep the support-head path geometry and source e_s stamp
   at :468. A gate guard for source x does not supply receiver y's epoch.
4. WC StepGateBatch: split suppressed gates in the helper at :250. In the enabled
   branch pass THIS receiver's hG. Keep hGST at :251 and the acceptance cutoff
   at :130. Use the gate supplier and sync. Selected-voter joinedParticipation
   supplies selected voters; it does not join arbitrary receiver x.
5. WC StepTransferReceipts: add joined y to `prefreeze_path` :228 and its call
   at :473. Source it from P10's HEAD reader scope or the joined selected voter
   route. Keep hGST :225/:229, acceptances :231/:253, the source frame, and F bound.
   Use the transfer supplier and sync.
6. WCG Dynamics :1529: pass receiver hG through the enabled gate branch at
   :1434/:1441. Keep GST ≤ v_s and the source acceptance cutoff. Use the gate
   supplier and sync. Retained-set agreement does not make every receiver awake.
7. WCG Dynamics :2810: pass the exact joined y guard through
   `growthStepTransferReceipts_prefreeze_path` :2770. Keep GST :2777 and the source
   e_s stamp :2779. Use the transfer supplier and sync with the current honest
   source acceptances. SourcePendingReceipt for a removed original source is a
   separate route; it cannot supply a ReadyTrigger with a current honest source.

Count ends at a strict read. For stamps used at the consuming gate or next vote,
keep the receiver epoch through that action index as a separate owner obligation.
The enabled guard or joined guard supplies the receiver scope for that extension.
Do not infer an action-index epoch only from the Count record's idxBefore(D).
The family ports remain open with P-Cl1/P-WC until their own builds pass.

Final Round 7 validation: DCK PASS (262.407 s), 43 strict audits / 3016
results, 24 controls. All 481 GREEN modules passed --wfail. SharedAxioms
complete coverage: 485 entries PASS. Complete GREEN exports: 259 proof modules /
253 exports / zero unaccepted. Layers: 72 inherited / zero new. Expose and
sleep scopes PASS. The two inherited W3 transparency findings remain unchanged.
The two S-Ap EXPECTED-FAIL targets are unchanged. P-ShA is CLOSED; the public
P23 statement and the seven family-owner ports retain their stated open scope.

## S-Ap Round 4 — DECISION P15-CUT (2026-10-10)

Amend packet P15, “Additive: new declaration OutagePrefixReceipt”, with
`SA.earlyTime p.toParams q ≤ b₀` immediately before the BatchReceiptAt conclusion.
The bound applies to each selected label; equality is allowed. P15 now means:

> Derive receipt for the selected prefix arming labels whose early receipt
> cut is at most b₀, and for the restored batches q ≥ r.

The additive claim types and theorem signatures keep their written Lean text.
Their prefix conclusion refers to the corrected definition.
OutageContinuationReceipt's first conjunct inherits this correction. D109's
Outage₂ and D110's OutageContinuationPrem text stay unchanged. This amendment
adds no public service record or acceptance assumption.

The local `arming_prefix_batch_receipt_on` service input takes the same cut
premise. `outage_restored_receipt_with_service` passes hPrefix unchanged.
EarlyCut.regime still constructs the early-cut run. Its `missing` and
`prefix_claim_false` tests are replaced by the positive `prefix_receipt` test:
the selected q = 1 has earlyTime 1 = 12 > b₀ = 8. Thus this run does not refute
the corrected claim. The test does not assert general regime-derived receipt.
P-Ar still owns the joint-induction service proofs; P-Ou still owns the restored
service proofs. This amendment does not close those family obligations.

Source: DECISION P15-CUT in sleep-join-port-notes.md (08:21) and
outage-cut/outage-cut.md §§2–3, 5–6. No other public meaning changes.

The S-Ap package map adds the two direct receipt consumers and OutageArming to
TARGETS/GREEN. It also classifies Shared.RegimesService as GREEN: the integrated
required scope includes this module, but the inherited S-Ap map omitted it.
This changes validation data only.

Validation limit: full auxiliary API and claims inventory write/check commands
stop at the missing compiled Claims.Tests.FinalityGST fixture (EXPECTED-FAIL,
owner P-Fi). Their generated products remain unchanged. No generator scope or
baseline is changed. This inherited limit does not block the targeted receipt
build or complete S-Ap GREEN export check. The latter covers 293 proof modules
and 253 exports, with zero unaccepted exports and zero non-exposed Statements
predicates. The focused six-declaration receipt audit uses only permitted axioms.

The standard FGSA generator also refreshes 13 shallow hashes from the integrated
Claims.Outage source. That source is byte-for-byte unchanged from d825ed30 in
this job. The only new public source change is OutagePrefixReceipt. No manifest
names are added or removed, and no generated hash is edited by hand.

DCK S-Ap passes in 325.25 s: 475 GREEN modules, 42 strict audit sources,
4,227 permitted-axiom results, and 24 controls. The package has 126 TARGETS and
57 explicitly owned EXPECTED-FAIL modules. The targeted receipt build passes;
check-layers reports 72 accepted findings and zero new findings. The generated
FGSA shallow/deep write passes (1,357 roots, 3,817 dependency nodes). Complete
exports and strict receipt audits pass. Full auxiliary products have the limit
recorded above; no full family or canonical-audit closure is claimed.

FGSA generated checks pass: shallow 1,357 entries in 59 modules (163.66 s),
deep 1,357 entries (116.44 s). Isolated deep controls pass (104.69 s).
The final EarlyCut comment now records DECISION P15-CUT; its --wfail rebuild
passes (4.68 s). The DCK result above precedes this comment-only correction.

Snapshot controls pass V2/GEN/FGSA shallow, catalog-lock, and source-scope
checks, then stop at the mapped-root control because FinalityGST is missing
(262.83 s). This is the same inherited auxiliary-product limit above.
Task 3 needs no edit: the lead note at the Round 3 merge already marks the
public anchor proposal SUPERSEDED by DECISION ANCHOR-DL at base d825ed30.
No new LEAD DECISION item is needed.

## P-H1 — Round 3, first transfer scopes (2026-10-10)

Shared/Regimes and Shared/Export build on the joined base. Their two P-ShA rows
move to GREEN in the P-H1 map. The legacy Regimes names remain explicit NoRestart forms.

Internal replacement: SupportTransfer no longer projects Base₂.noRestart.
FirstTransferScope supplies the exact enabled source gate, joined release guard,
receiver event-index epoch, and per-object forward, backward, target and carrier services.
The release lower bound and the first transfer conclusions stay the same.
Receipt proofs use NamedReceiptRootCollisionFree. Safety root equality uses its projection.

The stored honest HEAD supplier handles both acceptance and restart replay origins.
It extracts the earlier carried delivery before it applies signature provenance.
HistorySafeAt is a ReceiverService input; earlier processing does not supply it.
SupportRelay adds raw reverse receipt, target path and transfer proposal service helpers.
The proposal service uses ANCHOR-DL: earlyTime is the anchor, freezeTime is the strict read.
FramePaths adds the frozen path theorem with the receiver's exact read epoch.

Strict audit: eight new commands in Tests/HealingSleepAxioms.
The serial coverage fragment has the corresponding rows. No public statement changed.
SupportHeads, SupportSlow and FrontierSupportHeads must thread these services.
Full package closure is still open until every assigned consumer builds.

P-H1 Round 3 HEAD consumers: SupportHeads uses NextTransferScope at the exact
later HEAD read. The scope supplies joined honest voters, fresh HEAD service,
retained HEAD read provenance, carrier services and the receiver's event-index epoch.
The induction asks for these scopes only at labels inside its interval.
Membership and FG bounds use durable storage; vote and block stamps use the local epoch.
Batch cardinality follows from CStar and the recovery fault bound.
HealingBase's legacy row receipt test now supplies the receiver awake service.
Public statements and conclusions stay unchanged; these are exact internal input forms.

P-H1 Round 3 fast lease, output and proposal consumers:
SupportLease uses RecoverySleep₂ and RMonoAll. FastSupportScope names only its
source label and bounded interval. It supplies first/later transfer services,
same-label local service, joined gate receipt scopes and per-carrier services.
A suppressed gate writes no lease. Restart keeps existing lock rows and deadlines.
SupportOutput preserves the stable record in the restart induction branch.
Gate effects require the exact joined guard; source and target frame membership is durable.
SupportProposal uses ProposalSupportScope at each required proposal read.
It keeps joined source votes, fresh receipt and the exact receiver epoch explicit.
An emitted proposal supplies its duty guard through the executable guarded branch.
The public Transfers/TPerm definitions and all public claim text stay unchanged.
Fifteen further strict commands and their serial coverage rows cover these ports.

P-H1 Round 3 slow, permanence and frontier consumers:
SupportSaved adds wake-safe saved-result origin: restart clears the cache, so a
surviving nonempty result has the actual gate origin. SlowSupportScope preserves
per-label same-label service over its saved window. Its later services are bounded
by the same interval as FastSupportScope. SupportPermanenceServices supplies the
exact object scopes only for active PhaseBody arms and their proposal reads.
The Transfers/TPerm conclusions remain unchanged; services are explicit internal inputs.

The inline last-write input now includes joinedNow at each candidate renewal gate,
matching P-Fd's actual last-write producer. Suppressed gates cannot renew a lock.
Capped frontier HEAD relay uses TargetReceiptService and durable membership.
The capped first/later transfer induction consumes FirstTransferScope/NextTransferScope.
ExactService callers keep the confirmed-reader guard at the actual gate cut.

HealingPromotion ports the renewed/age tests to RecoverySleep₂, RMonoAll,
SupportPermanenceServices, and per-emitted-proposal ReceiverService. Row receipt uses
P-Fd's fgsa_tRows_recovery producer. HealingSupport uses the same exact local inputs.
Its all-asleep tick trace was an invalid positive execution fixture under the new
ExecutionValid awake laws. It is now a negative execution test; structural frame
facts stay as structural facts. No public claim text or protocol rule changed.

P-H1 Round 3 retained repair, source and moving-frame ports:
RepairHeadServices keeps the prior proposal scope, target receipt service and
RetainedServiceScope explicit for each emitted repaired proposal. H6/H6S inputs
are proved from the frame and bounded proposal services. HEAD conclusions apply
to joined receivers. repair_head_exact_legacy keeps its existing spelling; its
internal statement now uses the receiver-local form through SupportRecovery.
The canonical sleep supplier remains SupportRecovery.repair_head_exact.

RepairGateScope supplies the actual enabled gate, joined release and retained
carrier services. Exact gate counts use joined voters and the recovery fault bound.
Suppressed gates and wake restarts keep the stable record in repair_output_bound.
FrontierReadScope bounds seed, later fast/slow, proposal, HEAD and carrier services
by the same cap endpoint. Its seed consumes the actual confirmed-reader guard.
Retained cone fields are proved from these scopes, not from earlier processing.

SourceTiming has all-restart durable retention helpers. Source delivery uses each
supporter carrier's TargetReceiptService; pre-GST delivery keeps ReceiverService
explicit, including HistorySafeAt. The moving-frame first/later transfer and lease
consumers use the same exact read epochs and object services. High-source same-label
compatibility uses SameLabelServiceScope. The old-row height set is cut at
recoveryStart on this base; recoveryStart ≥ GST supplies the original GST conclusion.
No public Claims statement changed. Remaining reset and descent callers need these inputs.

P-H1 Round 3 reset and descent closure:
LossServiceScope supplies high-source same-label, first/later HEAD, fast lease and
per-target receipt services. The original no-loss and compatibility conclusions
stay unchanged. Loss unanimity has the exact joined release-reader input.
DescentTiming adds clock bounds through RestoreTimeLaw and durable clock monotonicity.
The original explicit-NoRestart clock helpers remain available for legacy callers.
PostResetCompat/High use RecoverySleep₂, RMonoAll and LossServiceScope. A selected
source without an emitted row also uses the reset label's SameLabelServiceScope.
PostResetKeep/ResetTransfer require per-carrier TargetReceiptService at the source
vote's early deadline. Pre-GST source receipt keeps ReceiverService explicit.
PostResetLease uses restart-safe provenance clocks and the joined renewal guard.
RiseOneAdvance threads SupportPermanenceServices and durable monotonicity.

RawServiceScope supplies services only at the actual guarded source, release,
HEAD, proposal and gate reads. First/later replay uses receipt root collision
freedom. Reads use event-index restartFree from the exact strict-before time cut;
the reset suffix obtains the GST+1 epoch from RecoverySleep₂. Suppressed gates
write no lease; wake clears the cache and preserves existing lock deadlines.
The proposal proof uses prior vote provenance, fresh receipt, carrier receipt and
the receiver's own epoch. No HistorySafeAt is inferred from previous processing.
The raw-transfer conclusion keeps its existing honest-reader form; H5/H2A projection
fixtures use their existing headReader and confirmedReaderIdx guards.

All 99 assigned P-H1 targets are now in GREEN; final package validation follows.
The local audit root has 339 commands. The full-key serial fragment registers each
new declaration. No public Claims text, exception, baseline or allowance changed.

P-H1 CLOSED (Round 3, 2026-10-10): all 99 assigned targets GREEN; 569 total GREEN
map entries; no EXPECTED-FAIL or supplier blocker. Final DCK PASS in 170.25 s,
including the --wfail build, 41 strict sources / 3,666 results and negative controls.
Layers: 72 inherited findings, 0 new (0.51 s). Export check: 363 proof modules,
253 exports, 0 unaccepted (8.71 s). Complete local coverage: 339 commands,
0 unaccepted (5.08 s). The earlier six gate-proof matcher exports were removed
by use of the guarded saved-result supplier; no baseline entry was added.
The exact H2 handoff and owned declaration inventory are in the Round 3 report
and claude-files/sleep-ph1-round3-inventory.md. Public Claims are unchanged.
## P-H1 — Round 2, local recovery and retained service (2026-10-10)


## P-H2 Round 2 — opening support and receiver action epochs

Base: `4c6289ce`, branch `sleep-ph2b`. P-H1 round 2 types and closed P-ShA/P-Fd
suppliers are consumed. Public recovery statements and protocol files are unchanged.
The validated helper slice does not close the 79 original H2 proof/test targets.

- OPENING-SUPPORT: internal statement repair, as requested in the closure map §6.
  `opening_gate_support` moves from OpeningServiceGate to OpeningGateSupport.
  It requires RecoverySleep₂, an honest receiver, GST at or before the selected
  voter's previous slot start, and that receiver's GateReceiptScope. Joined
  participation supplies releaseThreshold and Batch; `fgsa_gateReceipt_on` supplies
  the exact receipts; the denominator uses `fgsa_late_rest_bound_joined`.
  The source body compiles independently of the open RepairGate import.
- OPENING-RESET: `opening_gate_support_of_reset` derives the previous-slot cutoff
  from H0Reset, and constructs the receiver's enabled gate and read epoch with
  `healing_recovery_gate_scope`. Per-object fresh HEAD and target services stay
  explicit. `healing_ready_vote_cutoff` derives the same voter cutoff from τ.
  Original high-depth callers still need these object-service producers.
- WAKE-AT-VOTE: Tests/HealingOpeningSupport proves an ExecutionValid run with
  Δ=1, GST=5, wake/restart before the label-1 vote at 5, and gate at 10. The node
  is awake at the vote but unjoined; no HEAD is emitted; joinedHonest is empty;
  the gate is suppressed; genesis prefix support is zero. Genesis HEAD coverage
  holds. This is a kernel-checked mechanism regression, not a full RecoverySleep₂
  counterexample: its linked/base/partial-synchrony fields are not packaged.
- RECEIVER-ACTION: `healing_recovery_action_epoch` keeps the receiver's epoch
  through any consuming action index. A restart at GST or the anchor remains
  before actionCut. `healing_recovery_action_stamps` consumes RStoreEpoch;
  `healing_recovery_action_frame` consumes RFrameNextEpoch, keeping wires durable
  and stamps local. Neither derives global NoRestart.
- ACCEPTED-TARGET: RecoveryService constructs ReceiverService and TargetReceiptService
  from the original proposal acceptance, its source index/time, a public awake
  anchor, the exact horizon and non-exclusion. AnchorService derives handlers and
  durable proposal HistorySafeAt. It does not infer retained HEAD history from
  past processing. Retained HEAD witnesses and the frontier ports remain open.
- H1-NAMES: RecoveryScope's three helper names that conflict with the landed H1
  SupportRecovery API now have the `healing_scope_` prefix: restart_bound, durable,
  and stamps. Local audits and canonical fragments name these exact declarations.
- MAP: six copied Shared/Run failures are now GREEN; AnchorService and RegimesService
  are added to the current REQUIRED domain. All 79 original H2 failures are retained.
  Three new targets compile. Map: 89 TARGETS, 480 GREEN, 79 EXPECTED-FAIL;
  target split: 10 GREEN, 79 open. No allowance or baseline changes.
- BLOCKER: a fresh OpeningServiceGate build stops in H1 SupportTransfer, including
  its removed Base₂.noRestart field and legacy receipt/release calls. All 79 original
  H2 targets import this module transitively. The report lists exact H1 requests,
  P-As ProgressAttempt/ResetArrival requests and concrete P-Fd channel types.
  Signature edits in those high-depth files are not counted as proof completion.
- AUDIT: local strict roots and full local coverage retain every new declaration.
  Canonical fragments use the existing Tests.Axioms key and move the opening support
  owner row to its new module. Full canonical integration and the default global
  export check remain open with the Assembly/Inhabit suppliers.

Round 2 evidence and final validation: `claude-files/sleep-ph2-report.md`, Round 2;
checked full helper types: `claude-files/sleep-ph2b/export-types.log`.

Audit integration uses the existing full FGSAProofs audit key. The complete
132-row local inventory is in scripts/dev-pkg/P-H1.coverage-fragment.txt.
The lead must merge that fragment and its root import during serial integration.
P-H1 remains PREPARED on the certified set; full CLOSED is pending.

Round 2 gate/relay extension:
- SupportGate consumes fgsa_gateReceipt_on and the joined batch theorem.
  healing_support_gate_cover now takes RecoverySleep₂, the previous-slot
  cutoff covering GST, and GateReceiptScope at its actual receiver gate.
  The unchanged conclusion covers the raw confirmation. Awake alone cannot
  supply the former all-honest HEAD batch (JOINED-VOTER).
- healing_recovery_gate_scope derives enabledGateAt, receiver joinedAt and
  the early-read-to-gate index epoch from the recovery suffix. Its fresh HEAD
  and retained target services remain explicit, per object.
- SupportFrame adds healing_head_witness_relay_on. The source's actual HEAD
  carrier and height witness are unchanged. Each carrier's ready target
  service gives its ancestor path at the exact receiver deadline.
- SupportRelay adds healing_support_prefreeze_path_on. Strict read stamps use
  fgsa_block_stamp_before_read; their prefixes use fgsa_store_cumulative_on
  on [idxBefore(freezeTime s), receiver HEAD index). No global NoRestart.
- H2 must pass the cutoff and local GateReceiptScope at all gate-cover calls.
  SupportLease, SupportSlow and SupportOutput remain owned P-H1 port items.

Round 2 promotion extension:
- PromotionAge, PromotionRenewed and PromotionTerminal now use RecoverySleep₂
  at their emitted-proposal paths. The selected proposer restart bound follows
  from GST, the carrier/period budget and suffixNoRestart. A wake at GST is allowed.
- Age/renewed/terminal receipts thread the same per-proposal ReceiverService.
  Quiet extensions use RMonoAll. All three modules compile with --wfail.
- Terminal recurrence rounding is private arithmetic over Recovery₂.gap. It
  removes this module's import of the broken legacy Regimes alignment adapter.
  Its budget and conclusion are unchanged; no public alignment premise was added.

HealingAttemptTerminal now checks the terminal supplier with RecoverySleep₂,
RMonoAll and the same exact proposal service producer. Its inclusive grid and
maturity boundary test is unchanged. The test compiles with --wfail.

Round 2 final validation: DCK P-H1 PASS, 174.47 s; 519 GREEN roots, 39 strict
sources and 3,023 axiom results; only propext, Classical.choice and Quot.sound.
All 24 default controls and DCK controls pass. Complete GREEN exports: 316
proof modules, 253 exports, zero unaccepted (8.58 s). Complete local coverage:
132 rows PASS (6.51 s). Layers: 72 inherited findings, zero new. The all-target
build still fails in owned SupportTransfer and P-ShA legacy Regimes; all other
open targets remain classified under their actual owners. Full P-H1 NOT CLOSED.

### Lead note after the P-H1 round 2 review: exact H2 handoff (2026-10-10 09:18)

Review rev-ph1c-astra (FIX-FIRST item 1 only: handoff completeness). P-H1 round 2 merged as PREPARED with this
handoff. Owner of every site below: P-H2 (sleep-wave-plan.md:982, :992, :994, :999, :1003, :1031, :1047).
- Healing/AttemptRows.lean:206 calls healing_attempt_settle_start with the old arguments: pass RMonoAll and the
  per-carrier TargetReceiptService producer before `crossing` (changed inputs Healing/AttemptSettle.lean:13, :15).
- Tests/HealingAttempt.lean:284, :312, :340, :368 call the four changed settlement adapters: thread the same
  monotonicity and carrier services (separate Assembly validation dependency, sleep-wave-plan.md:961, :1047).
- Healing/FrontierServiceGate.lean:164 calls frontier_head_relay with base.idealization: use
  base.receiptIdealization; hrelay x hx at :170 needs the receiver awake at voteTime s + Δ (changed result
  Healing/FrontierSupportFrame.lean:155). The legacy route needs explicit NoRestart; the sleep port supplies the
  local carrier service.
- Healing/Repair.lean:87 calls repair_head_exact with its former lease/phase interface; the name now resolves to
  Healing/SupportRecovery.lean:256. Supply the actual proposal tick/emission, joined-reader RetainedH6Input,
  per-reader target services and RetainedServiceScope. The exact-service call at :91 uses the local service route
  with its joined guards, geometry and scopes. Renaming the call to the legacy supplier is not a port.
- Legacy settlement sites Healing/FrontierSearchGap.lean:267, Healing/FrontierSearchTop.lean:454,
  Healing/FrontierSearchRepair.lean:216: use healing_settle_start_on, RMonoAll, carrier services and receipt
  idealization instead of base.noRestart.
- P-H1-owned, still OPEN: Healing/RepairH6S.lean:154 uses the former repair interface.


## P-Ou Round 2 — growth, prefix cut and local outage consumers (2026-10-10)

Base: babc0460, including S-Ap P15-CUT ddfe84be. P-Ou remains PREPARED, not CLOSED.
The closure handoff is scripts/dev-pkg/P-Ou.round2-handoff.md.

- P20: outage_cleanGrowthClaim_of is outside CleanClaims. Its only internal
  supplier parameters are the exact hcompatible and hinclusion from P-Cl2.
  No old hmono/history include reaches it. AvailableGrowthConcl already has
  the approved independent reader scopes; this round changes its comment only.
  GrowthConsumer builds the unfolded production result with the same deadline.
  The mixed Export still fails in its other imports and is EXPECTED-FAIL.
- Growth compatibility: clean_growth_compatible_of_outputs uses scoped Clean
  output compatibility and one confirmed gate-inclusion witness. The earlier
  reader can sleep before the gate or deadline. Both full regime suppliers
  remain OPEN: P-Cl1/P-Cl2 must close scoped Clean truncation; P-Ou must close
  exact proposal/history and later-reader inclusion. No global monotonicity
  or continuous awake condition for all honest receivers was added.
- DECISION P15-CUT: the prefix consumer derives 6*delta <= b0 from an origin
  gate, derives earlyTime q <= b0 for every selected label, and passes that
  bound to the corrected prefix predicate. Equality is allowed. The genesis
  branch uses its universal prefix order and needs no receipt. The restored
  three-cut composition still builds. Public regime receipts remain OPEN.
- DECISION ANCHOR-DL: the production active-path and exact-carrier consumers
  now use ReceiptCoverageAnchorPremises and the anchor corollary. Compatibility
  permits a target below F; the exact carrier still supplies the height bound.
  Their lower module builds. The remaining receipt callers must derive service
  at vote/early/freeze anchors and bind all N4 obligations to the same anchor.
- JOINED-VOTER: the strict HEAD read bridge now uses joinedAt at the vote.
  Its proof excludes only a local restart at that exact time. Earlier restarts
  and other nodes' same-time restarts are allowed. The old NoRestart input is
  removed from inclusion_head_read. Retained-walk callers still need the port.
- E/denominator: the good-seat cardinality and A union W late complement are
  proved from Base2 and E at every receiver store. Stored honest HEADs supply
  joinedness through authenticity. Receipt membership and compatible targets
  remain OPEN joint-invariant inputs. The full good-vote invariant is OPEN.
- Local late writes: every newly written gate row is compatible when its
  passed result is compatible. Old conflicting rows are permitted. Global
  exclusion of conflicting late writes, induction and handover remain OPEN.
- T61: the endpoint tick test now takes confirmedReaderAtIdx at the post-gate
  cut and gets the exact awake fact from that scope. Its sleeping-tick example
  now proves impossibility in a valid sleep run. InclusionGate* still blocks
  the test module. T31/T35/T37 remain OPEN; T25 remains with P-Ar.
- P-Ar: the prior unrestricted transfer defect is repaired in its landed
  joined forms. Closure still needs clean_epoch_saved_row from P-Cl1 round 2,
  protected origins/seeds, prefix receipt and lower write/gate helpers.
- P-As Shared/Claims is a separate failed supplier of the mixed exporters.
  P-ShA's landed Export, Regimes, AnchorService and RegimesService are GREEN.
  S-Ap D013/P15-CUT are installed; no new predicate defect was found. S-Ap's
  facade/audit targets remain EXPECTED-FAIL. Claims/Statements was not edited.

Map: 36 TARGETS, 486 GREEN, 20 EXPECTED-FAIL (18 P-Ou, 2 S-Ap).
GREEN is a build classification. It does not close a conditional supplier.
Canonical audit moves and three new module registrations are handed to P-Da.
All 59 local strict commands have P-Ou coverage rows. No shared baseline,
exception, allowance, checker or scope row was changed. Public-meaning STOPs: none.

Round 2 validation on the final proof sources:
- Proof commit: 7969754d. DCK P-Ou PASS; 38 strict sources, 3,022 results;
  all 24 default controls PASS. GREEN builds use --wfail and default heartbeats.
- Complete exports across all 486 GREEN roots: 279 proof modules, 253 exports,
  zero unaccepted exports and zero Gen exports. Export controls PASS.
- Local complete coverage: all 59 SleepAxioms commands have inventory rows;
  strict audit permits only propext, Classical.choice and Quot.sound.
- Layers: 72 inherited findings, zero new. Diff whitespace and new Lean/prose
  lines <=100 pass. Machine coverage rows retain the required three-token format.
- Actual mixed consumer build was attempted. It fails in Outage/Suppliers,
  ExactProposalRetained, P-Ar ArmingDuty/ArmingGate, and P-As Shared/Claims.
  This result is not replaced by the GREEN GrowthConsumer build.
- Logs: .lake/sleep-pou-r2/dck-final.log, exports-final.log, coverage.log,
  layers-final.log and consumer-build.log. No push, merge, rebase or supplier edit.

## P-Ou Round 3 — retained and inclusion cores

Base bf0c024d, branch sleep-pou2. The public claims are unchanged.
ExactProposalRetained and all four InclusionGate cores now build with --wfail.
Both owned inclusion test modules build. The public package remains OPEN.

T31 chooses an enabled joined gate receiver at d(q). T35 chooses a joined
vote reader at v(s). T37 chooses an enabled joined receiver at d(s-1);
its earlier vote uses the same restart bound. The witnesses include the
horizon endpoint. T32/T33/T34/T36 use their exact joined or emission guards.
T38 and T61 use confirmedReaderAtIdx at the post-gate cut.
These tick repairs do not establish the missing regime service producers.

Retained HEADs use InclusionReceiverInputs and receiver-local relay services.
No sleep consumer obtains NoRestart from a regime. The legacy score count
keeps explicit NoRestart for ContinuationFrame; the sleep caller uses _on.
No earlier processing event is used to infer retained HistorySafeAt.
The local proposal service must carry durable history at its exact anchor.

InclusionHistoryBounds is the field projection required from P-Cl1.
The old duplicate state induction in InclusionGateBounds is removed.
The post-gate consumer has confirmed-reader scope and scoped monotonicity.
The later-read consumer requires an actual enabled gate origin at or after s.
That origin supplier is P-Ou work; it is not a new public claim premise.

Classification for this group: 493 GREEN, 13 EXPECTED-FAIL, 36 TARGETS.
Seven owned modules move to GREEN. GREEN denotes compilation only.
Strict local audits cover the retained and gate kernels and the test fixtures.
Layer check: 72 inherited findings, zero new. Full DCK follows the last group.

### P-Ou Round 3 — exact proposal service anchors

RestoredReceipt produces ReceiverService for proposal paths at v(s)->e(s)
and e(s)->f(s). Base2, the actual source acceptance, and the enabled or
joined receiver supply readiness, handlers, the receiver epoch and durable
HistorySafeAt. The original acceptance time is retained.
The deadline and all local service fields use the same anchor.
Compatible finality at e(s) or f(s) discharges permanent exclusion.
That compatibility remains an exact joint-invariant input.

The two constructors build with --wfail. They do not establish the full
regime-only restored or prefix receipts. Fresh HEAD services, target
dependencies, finality bounds, the retained score scopes and the P-Ar
prefix remain closure work. No public receipt premise is added.

### P-Ou Round 3 — good receipts and all honest late keys

outage_good_heads_at_gate derives authentic target membership and strict
early stamps in the actual gate view from GateReceiptScope. It applies to
every honest enabled receiver, including W. The target-prefix and finality
floor bounds remain exact joint-invariant inputs.
outageV_gate_of_good_service connects these receipts to the actual
compatible-batch count with the A union W opponent bound.

outage_all_honest_late_gate_keys quantifies over all honest writers at all
late labels. It excludes conflicting targets from new write keys when
each enabled late result is compatible. It permits old conflicting rows.
Deriving that result invariant from E and the joint induction is still OPEN.
The three kernels build with --wfail; no regime closure is claimed.

### P-Ou Round 3 — joint restart step

outage_joint_restart preserves global source and duty histories across
a real restart event and preserves protection on the selected receiver
scope. It supplies the restart case of both joint inductions. It builds
with --wfail and keeps the G-only protection scope.

Both full inductions and the handover at v(r+k+1) remain OPEN. Their tick
and delivery cases need P-Ar origins/seeds and the regime-derived good
targets, receipt service and all-honest result invariant. P-Ar files are
unchanged; no producer is duplicated in this package.

### P-Ou Round 3 — growth witness and exact Clean consumer ports

clean_inclusion_gate_witness constructs one confirmed receiver at g(s)
whose inclusive store contains the honest proposal. It first constructs
the exact enabled gate, then proves that same-time deliveries keep the
proposal: the Clean history bounds successor F below P. There is no global
monotonicity or later-reader origin input.
clean_growth_compatible_from_history combines this witness with the scoped
public-output compatibility projection. It supplies the first growth input,
with independent earlier and witness readers, once the Clean and local
service inputs are produced. The production GrowthConsumer call is tested.

outage_supplier_history now accepts the exact scoped P-Cl1 fields:
confirmed gate readers for order, enabled nonempty gates, joined transfer
readers, and current-epoch saved/fast rows with compatibility retention.
Nonempty raw results supply their own confirmed-reader guards through the
compiled inclusion_ordered_of_scoped adapter. Suppliers moves to GREEN.

The mixed Outage/Export Clean consumers use these exact fields,
InclusionReceiverInputs, guarded GateReceiptScope and scoped monotonicity.
The later-read consumer keeps the exact P-Ou-owned gate-origin input.
The actual mixed exporter build fails in P-Ar ArmingDuty/ArmingGate and
P-As Shared/Claims. Its Clean wrapper edits are PREPARED and not counted
as a compiled exporter. No private exporter copy is used.

P-Cl1's clean_epoch_saved_row is present on the P-Ar round-3 base d60ff01d,
in Clean/EpochSaved:15. It is absent on this bf0c024d-based work tree.
The exact statement uses a receiver awake/epoch window from slotStartZ q
to b0 and a strictly earlier Clean origin r < q. The lead must land that
producer and the P-Ar closure here; this package does not copy them.

Final map for this group: 36 TARGETS, 494 GREEN, 12 EXPECTED-FAIL
(10 P-Ou, two S-Ap). Public closure remains OPEN. No public claim,
checker, scope, exception, allowance, baseline or toolchain is changed.

### P-Ou Round 3 — export-safe gate observation

The final export check found private equation copies from the gate guard's
decision instance. ExactProposalReceipts now observes the gate through the
existing gateResult_eq_saved and fgsa_gate_saved_result/unjoined API.
Its missing-tick branch uses direct reduction. The guard statements and
their meanings are unchanged. No new equation allowance is added.
The focused check passes: 129 proof modules, 252 accepted exports,
zero unaccepted and zero Gen exports. Full final checks follow this repair.

### P-Ou Round 3 — final validation

Final proof source commit: 502f1893.
DCK P-Ou PASS: 494 GREEN roots, 39 strict audit sources,
3,086 axiom results and all 24 default negative controls.
The complete GREEN export check passes: 285 proof modules,
253 accepted exports, zero unaccepted exports and zero Gen exports.
Complete local coverage passes for all 123 commands:
108 in SleepAxioms and 15 in Tests/InclusionExact.
Only propext, Classical.choice and Quot.sound occur.
Layer check: 72 inherited findings, zero new.
Diff whitespace, ownership and new-line length checks pass.
No heartbeat increase, proof placeholder, public claim change or new
checker/scope/baseline/allowance is added.

Kernel PREPARED; public package OPEN, not CLOSED.
Exact closure inputs and owned work are in the Round 3 section of
scripts/dev-pkg/P-Ou.round2-handoff.md. The mixed exporter remains open
after its actual build fails in the P-Ar and P-As imports.
Logs: .lake/sleep-pou-r3/. Public-meaning STOPs: none.

### G-S1 PASS (2026-10-10 09:24)

`bash scripts/dev-check.sh --stage s1` on sleep-int 8e12a02f: DCK PASS (stage s1), DCK controls PASS, wall 324 s.
Run on the NUC (tree wt-impl2, systemd scope MemoryMax=16G, lane-1 lock). Log nuc:/tmp/gs1-8e12a02.out.
Later merges (P-H1 r2, P-Ou r2) are not covered by this run; G-S2 checks the integrated tree.


## P-Cl1 Round 2 — CLOSED Clean core and ANCHOR-DL callers (2026-10-10)

Base: d2b00d72 on sleep-pcl1b. This block belongs to P-Cl1.
All 20 owned targets are GREEN. The package map retains the Run facade and
Run.Tests.Axioms as S-Ap EXPECTED-FAIL. Shared proof files, protocol declarations,
FGSAClaims and Clean/Export are unchanged.

- DECISION ANCHOR-DL: StepGate:644 uses anchor v_(s+1), deadline e_(s+1).
  The receiver's enabled guard passes through gate_batch_of_history:718 and
  gate_active_heads:551 into gate_path_coverage:424. Readiness, history,
  handler interval, receiver epoch and each path deadline use that anchor.
- TransferFrame:398/:497 use anchor e_s and deadline f_s. Both path interfaces
  (:351/:417) take the receiving node y's joined guard. The guard passes
  through the prefreeze and frame helpers from CleanHist.continues. The source
  gate's nonempty result supplies only the source guard. Receipt roots use
  base.receiptIdealization; the other root-resolution calls use its safety
  projection. Original source acceptance times stay unchanged.
- Internal statement, exact sleep form: clean_gate_stamps takes the local
  receiver restartFree interval. Durable block origins use accepted_origin;
  original early source acceptances survive restore. Strict-read stamps use
  the receiver epoch through the consuming gate or vote, beyond Count's D.
- JOINED-VOTER: gate batches use fgsa_gate_batch_premises_joined. The zero-label
  count uses a local joined form of the zero receipt proof. Same-label ordering
  uses fgsa_sameLabel_on with the supplied enabled-reader service scope.
- Clean/Service provides HEAD history before the label, retained HEAD provenance,
  local receiver service, the backward relay and the strict-freeze forward relay.
  Its private history/merge proofs adapt the existing Shared proofs because those
  suppliers are private. The restart branch rejects future-label retained raw
  proposals before t_s. It does not infer safe retained history from acceptance.
- N5 and R7 close through the actual Clean history/state induction. Closure has
  the restart branch; saved and fast-write origins carry the receiver epoch.
  T10 uses the earlier joined actor. Nonempty gates include label zero. The
  history, gate and truncation body types now match approved D018–D021.
- Clean/EpochSaved:15 exports clean_epoch_saved_row for P-Ar. It constructs a
  nonempty enabled gate on the receiver's protected interval and saves C above
  B, or current F covers B. Its source origin must have a strictly earlier label,
  or be genesis. A restart at the receiver window's start is allowed. The caller
  must derive that earlier-label bound from its arming origin and lag facts.
- Internal Safety repair: Safety:25 needs only all-node compatibility and
  monotonicity at the finite horizon. It drops unused history/frame/gate clauses
  from the old input body and returns the approved reader-scoped result.
  Safety:292 supplies that result from the completed Clean core. A scoped public
  CleanTruncAt cannot be passed as the stronger all-node pair by projection.
  P-Cl2 owns the exact wrapper repair in scripts/dev-pkg/P-Cl1.handoff.md.
  This is an internal supplier handoff; public CleanSafetyClaim is unchanged.
- Round-1 review finding 2: ARCHITECTURE marks the old Ruling Y restart account
  as superseded and records the Clean epoch modules. Stale noRestart comments
  in CleanInvariant, Zero, Closure and Safety are corrected.

Validation: the final package DCK, strict audit totals, complete local export
check, layer count and wall times are in claude-files/sleep-pcl1-report.md,
Round 2. The canonical audit/inventory additions are in the two P-Cl1 fragments
under scripts/dev-pkg. No audit key, baseline or allowance is added.

Public STOPs: none. P-ShA Round 7 defect found: none. P-Cl1 has no owned
EXPECTED-FAIL target. P-Cl2 public wrapper compilation and canonical serial
integration remain with their owners; P-Ar must apply the exact saved-row type.

### Lead note after the P-Cl1 round 2 review (2026-10-10 09:30)

Review rev-pcl1b-astra: Count port to ANCHOR-DL, restart closure, clean_epoch_saved_row and the Safety core pass;
the 20-target GREEN map is accurate. FIX-FIRST item 1 (validation only): AvailableChainFGSAProofs/Tests/
CleanEpochAxioms.lean lacks strict commands for clean_gate_batch (Clean/StepGate:89), clean_gate_head_prefixes
(:539), clean_gate_nonempty (:749, changed in this round) and sExtends (Clean/Closure:380). Merged as PREPARED.
P-Cl1 becomes CLOSED after a short audit round adds the four commands, regenerates the isolated inventory and
reruns DCK P-Cl1 and the local export/coverage check. P-Cl2 Safety wrapper repair: scripts/dev-pkg/P-Cl1.handoff.md.



## P-Fi Round 3 — review fixes and exact supplier queue (2026-10-10)

The internal FinalityActionReceipts service now requires
GST ≤ slotStart(s−1), s = qR+1. RowsBatch and TailBatch pass the cutoff from
their common healing witness. The receiver, honest HEAD seat, exact target,
action deadline and horizon remain explicit. Every action export inherits this
scope through the same record. No public regime field changes.
The rejected wider scope allowed Δ=2, q=0, vote=10, action=12, GST=wake=11.
Recovery permits that wake; FreshHeadService requires an epoch from vote to
action. This is an internal scope obstruction, not a public counterexample.

Exact queue (F = Proofs/Finality, Sh = Proofs/Shared):
- Universal current votes: P-Fi owns FinalityVoteReceipts and the service design;
  P-As owns assembly. Direct consumers: F/CoreServices.core_full_vote,
  fgsa_tVote, fgsa_coreServices; F/Joined.finality_kernel_prem_W_of_joined;
  F/Forward.forward_witness_FE_of; F/Export.fgsa_kernelACSide_W. The current
  universal form includes pre-GST and unjoined reads. ANCHOR-DL cannot restore
  those volatile pools. This is an open service-scope design obligation.
- Action fresh HEADs: P-Fi owns the producer, P-ShA owns FreshHeadService,
  P-As owns assembly. Direct record reads: F/RowsBatch.rowsPrem_action_walk_batch
  and F/TailBatch.ktail_action_walk_batch. F/Export threads the contract through
  kernel, joined kernel, Tail, FE/F4 liveness, proposal and frontier exports.
  Need exact emission, handlers, non-exclusion and vote-to-action epoch.
- Action target proposals: same owners and consumers. Sh/AnchorService's
  fgsa_historySafeAt_of_proposal gives durable history;
  fgsa_proposal_handlers_at_anchor gives handlers from original acceptance.
  Use anchor voteTime(s), deadline earlyTime(s)=actionTime(q), and ReceiverService.
  Original trigger, roots, time bounds and target non-exclusion remain explicit.
- Tail target proposals: P-Fi owns the producer, P-ShA owns ReceiverService and
  target helpers, P-As owns assembly. Consumers: F/TailMixed.ktail_head_delivered
  (healing_held_block_receipt_on), ktail_mixed_final, ktail_hmixed_of_relay,
  tail_kernel_W_of_relay; F/TailBatch.tail_kernel_W_full_of;
  F/Export.fgsa_tailKernel_W_of. Service anchor: actionTime(r+1); deadline: +Δ.
  The requested object is a NAMED PROPOSAL. Its processed history survives
  restore in durable TF. The erased-history warning applies to HEAD wires only.
  Keep the actual terminal proposer and F≤H at that receiver's deadline.

Direct single-target proofs use ReceiverService. Ancestor paths use
ReceiptCoverageAnchorPremises / fgsa_active_path_of_coverage_anchor with one
anchor for every bound. AnchorService gate/transfer wrappers are not generic
Finality read adapters. Do not restore Count's old deadline restriction.

The omitted P-Fi-owned Claims.Tests.FinalityGST fixture is now in this package
map. Its six late bounds use recoveryStart as the existing package fields require.
Round 2's all-GREEN statement covers only the 43 P-Fi targets in its map;
it did not include this fixture. S-Ap owns the auxiliary product refresh after
fixture validation. P-As still owns Assembly/Finality's supplier arguments.

FIX-FIRST validation: Finality.Export and Claims.Tests.FinalityGST build
with --wfail in 31.06 s. The action contract also names postClock and F≤K;
both callers derive F≤K from their existing common-prefix bounds.
The initial full Tests.Axioms build fails in inherited other-family ports.
No P-Fi proof failure remains in the focused build. The merged audit has
not been proved compilable; it remains P-As EXPECTED-FAIL.


## P-Fi Round 3 — exact suppliers, internal replacements and handoffs

The current Round 3 report supersedes the initial queue above. ReceiptSuppliers
proves fresh honest HEAD services, named target proposal services, the exact
action and Tail records, and FinalityScopedVoteReceipts. Action/Tail record
construction has only the explicit Shared genesis-constructor input left.
Both proposal routes use AnchorService's durable history and original acceptance
handlers, with vote/early anchors for action and action/+Δ anchors for Tail.
No Count deadline restriction or whole-run NoRestart is introduced.

Internal replacement: FinalityVoteReceipts now has exactly TVote's proposal
and action read shapes. The former arbitrary s,x,t scope is removed. The true
scoped form requires GST≤slotStart(s−1), earlyTime(s)≤read≤horizon and the actual
receiver postClock. Recovery proves it and the full resolved support filter.
The unchanged public TVote still requests pre-GST and unjoined reads. Its
compatibility supplier remains an explicit P-Fi design obligation. Export
requests it only with the consumer's actual witness, bound and HealingInput.
No public field or predicate is weakened. S-Ap owns any public scope decision;
P-As owns assembly. The report lists every exact consumer and current line.

Kernel counterexample: Tests/FinalityEpochs.short_recovery_sleep and
recovery_sleep_not_vote_receipts prove RecoverySleep₂ and failure of the exact
compatibility record. GST=7, Δ=2, events tick0,tick2,restart7,tick8, horizon8.
The proposal read is awake but unjoined and has no HEAD-0. Recovery starts at
the wake and satisfies its suffix; its joined start is beyond this horizon.
This refutes a Recovery-only receipt producer. It has no HealingInput and is
not a counterexample to the full public KernelACSideClaim_W.

Exact P-ShA API handoff: add fgsa_target_service_genesis in Shared/CatchUp.lean,
after TargetReceiptService (:410), with statement
TargetReceiptService E rho .genesis D x and body Or.inl rfl.
The definition is opaque to external modules and the named-proposal constructor
does not cover genesis. No new regime assumption is needed. P-Fi leaves
hGenesis explicit. Export removes the former hServices/hReceipts requests and
uses the proved records. P-As ports Assembly/Finality:113/:200 to this API input.

The FinalityGST fixture is GREEN after six recoveryStart bound ports. S-Ap can
refresh its blocked auxiliary products. P-Fi map has 46 targets / 513 GREEN /
three inherited failures with their original owners. These are map counts.
The serial audit adds 14 production commands, including 11 new-module theorems,
and retains all old inventory keys. Public vote adapter and full assembly remain
open. P-Fi is PREPARED; CLOSED is not claimed.

Round 3 validation: DCK PASS in 169.78 s, 513 GREEN modules, all 24 controls,
41 strict audit roots / 3,186 permitted results. Complete compiled exports:
209 proof modules / 252 exports / zero unaccepted; complete local coverage:
223 commands, controls PASS. Layers: 72 inherited findings / zero new.
The stable full Tests.Axioms build fails in 18 other-family/assembly producers
(26.45 s), with no Finality-family proof failure. It retains P-As ownership.
See .lake/sleep-pfi3/final-axioms.log and the final Round 3 report for exact names.
Added Lean lines are at most 100 characters; git diff --check passes.

### P-WC Round 2 — frame and occurrence replay ports (2026-10-10)

- Verified base 318c74a3 on sleep-pwc2, with P-Cl1 r2 and P-ShA r7 suppliers.
- Removed six stale Shared/Run EXPECTED-FAIL rows after their --wfail builds passed.
- WC and WCG Frame use the receipt-root premise's safety projection.
- StepInputs keeps all-time joined participation until it selects an enabled
  earlier gate actor. The retrospective read uses the original joined voter.
  The all-time input is an internal supplier requirement for its callers.
- WCG EventReplay matches local tick occurrences at each run's action cut.
  Same-time wake restarts are included. No NoRestart input is required.
- Confirmed-reader replay carries its current enabled gate and restart interval.
  Empty output replay uses confirmed readers and needs no participation or half cap.
- Four owned targets pass --wfail. The other 28 owned failures remain PREPARED.
  Count callers, full service, and event induction remain open at this checkpoint.

### P-WC Round 2 — anchor callers and current-epoch service (2026-10-10)

- WC and WCG gate Count callers use ReceiptCoverageAnchorPremises and
  fgsa_active_path_of_coverage_anchor with anchor v_s and deadline e_s.
  The exact receiver supplies enabledGateAt. Joined selected voters supply HEADs.
- WC and WCG transfer Count callers use anchor e_s and deadline f_s.
  prefreeze_path takes joinedAt for receiver y at v_(s+1). The separate receiver
  epoch continues through that vote action, beyond Count's strict read.
- RStoreDurable keeps TF and blocks across restart. RStoreEpoch keeps stamps
  on the exact receiver interval. RMonoAll replaces the old NoRestart FG bounds.
- The internal common telescope retains joined participation at all times from
  v_(u+1), inclusive. A vote-only count cannot select the earlier gate actor.
  The first vote must be included because it precedes the seed's completed gate cut.
  Public Claims/Statements remain unchanged. P-As must keep this all-time input.
- T53 and T57 now select a joined actor at the earlier gate and transfer to the
  original joined voter. T49's Proposal caller remains open.
- Full wc_service4 and wcg_service4 compile with their complete statement types.
  An early-marker reader gets its own next covered enabled gate. A late-marker
  reader gets a current-epoch enabled gate, whose result is ordered above B.
- wc_output_mono_of_inv and wcg_output_mono_of_inv preserve the kept output
  through delivery, ordinary ticks, enabled gates, suppressed gates, and restart.
  They use the complete finite history; they do not assume every intermediate
  reader is confirmed. Both original-gate and later-reader getter suppliers compile.
- T54/T56 service and the getter supplier needed by T48 are supplied. The
  Inclusion/StepOutput event callers remain open. Epoch helpers alone are not
  the service handoff. Full supplier types: scripts/dev-pkg/P-WC.handoff.md.
- WCG Dynamics now imports family-local input, gate, transfer, safety, and
  service suppliers. Its remaining finite facts and event-induction body are open.
- PREPARED: 57 targets, 35 GREEN and 22 EXPECTED-FAIL. The map has 505 GREEN
  entries and 22 owned expected failures. No owned failure is marked CLOSED.

### P-WC Round 2 — retained seed replay (2026-10-10)

- wcg_tickSourceReplay keeps the original equality direction and now reads
  after same-time restarts. Seed consumers use occurrence indices in each run.
- WCG Seed preserves enabled gate guards in gatePassedAt and in the exact
  gateResultAt matcher. Pre-tick, signed-row, and action reads need no NoRestart.
- WCG Empty consumes the new tick replay. Its source-reader safety adapters
  remain EXPECTED-FAIL. No participation or half-cap input was added.
- Updated map: 57 targets, 36 GREEN and 21 EXPECTED-FAIL; 506 GREEN entries.
  Remaining local proof errors include StepFacts, Proposal, and Dynamics.

### P-WC Round 2 — final implementation validation (2026-10-10)

- DCK PASS: 506 GREEN modules with --wfail, 39 strict audit roots,
  3521 axiom results, and all 24 default controls PASS.
- Local strict audit: 196 commands and 196 results, standard axioms only.
- Complete local export/coverage check: 152 proof modules, 251 exports,
  zero unaccepted, and 196 inventory rows. No baseline or allowance changed.
- Layers: 72 existing findings, zero new. GREEN import closures contain no
  EXPECTED-FAIL module. Added Lean lines are at most 100 characters.
- PREPARED. The package has 21 owned expected failures. Complete event induction,
  Proposal T49, and Empty source-reader adapters remain local proof work.
  The late P-As assembly audit is a separate bridge; it does not close those files.
- Full supplier types and serial instructions: scripts/dev-pkg/P-WC.handoff.md.

### Lead note after the P-WC round 2 review (2026-10-10 10:27)

rev-pwc2-astra: production changes support PREPARED (four Count callers on ANCHOR-DL, current-epoch WC/WCG service; 21 owned
targets open). Item 1: claude-files/sleep-pwc-round2-audit-fragment.txt:2 and scripts/dev-pkg/P-WC.handoff.md:286 import
Tests.WeakContinuationSleepAxioms into Tests.Axioms (forbidden TEST-USE). Apply RULING AUDIT-FRAGMENT
(codex/jobs/sleep-join-port-notes.md): import the production modules directly; the 196 coverage rows keep the existing key.

### P-Cl1 Round 2b — audit completion (sleep-par3, 2026-10-10)

The lead note after the P-Cl1 round 2 review is CLOSED. Tests/CleanEpochAxioms
now audits clean_gate_batch, clean_gate_head_prefixes, clean_gate_nonempty and
sExtends directly. A scan of all 20 owned modules also added direct commands
for CleanInterface, FGPart and the public CleanInvariant predicates. The local
root has 183 commands; CleanSuppressed retains its three commands.

DCK P-Cl1 PASS: 39 strict roots, 3,149 results and 24 default controls.
The regenerated isolated inventory has 186 entries. Both local audit roots pass
--roots-only --complete-coverage and the home-equation/audit control: 137 proof
modules, 251 exports, zero unaccepted, Gen zero exports. Layers: 72 inherited
findings, zero new. No canonical audit command, key, allowance or baseline changed.
Evidence: .lake/sleep-par-r3/pcl1-{dck,exports,exports-generate,layers}.log.


### P-Ar Round 3 — corrected public receipt and protected receiver ports (2026-10-10)

Base d60ff01d; branch sleep-par3. The P15-CUT public prefix receipt is CLOSED:
ArmingKernel:785 proves arming_prefix_batch_receipt with the exact
OutagePrefixReceiptDerivedClaim type and no extra service premise.
ArmingKernel:735 derives ArmingBatchReceiptService from OutageSleep₂. Proposal
history is durable; the vote anchor supplies timely handlers; checked delivery
supplies dependencies; target service uses original source acceptance across
restart; compatible finality and trigger validity supply non-exclusion. Honest
HEAD uniqueness supplies fresh HEAD non-exclusion. The authentic finality
alternative and strict target/ancestor stamps are retained.

ArmingDuty's joined action branches and receipt root type compile. The lower
lease-write helpers and enabled gate equation moved to ArmingStep:186–271.
ArmingGate:66 requires the actual joinedNow guard. ArmingGate:321 supplies
arming_gate_core_on for protected receivers with their exact equal-time epoch.
The legacy gate consumers require awake at the exact pending gate. No raw
result was used as an enabled gate witness.

ArmingKernel:792 supplies protected origins from the Clean state/history;
:837 supplies current slow saved rows with the finality alternative; :921
supplies joined T25 at protected receivers from regime-derived services.
ArmingKernel:464 consumes the exact P-Cl1 saved-row producer through an assembly
input. Tests/OutageArming:650 applies the actual clean_epoch_saved_row to this
consumer. Direct Clean proof imports into Outage were removed; layers stay clean.

All 16 owned P-Ar targets now compile. The map also checks the unchanged GREEN
ExactProposalReceipts supplier. Map: 17 targets, 485 GREEN, zero owned
EXPECTED-FAIL; the two Run facade/audit failures remain S-Ap-owned.
DCK P-Ar PASS: 38 strict roots, 3,129 results, 24 default controls. Complete GREEN
exports and 166-entry local coverage PASS: 288 proof modules, 253 exports,
zero unaccepted, Gen zero exports. Coverage control PASS. Layers: 72 inherited,
zero new. No checker, scope, baseline, allowance or public Claims file changed.

Full P-Ar remains PREPARED, not CLOSED. ArmingMain's fast_arming, slow_arming and
arming_cert are compiled legacy NoRestart producers. The protected certificate
construction must replace their all-honest gate/batch and saved-retention inputs,
keep joined denominators, and thread the current-row finality branch into pending
input and arming_gate_core_on. Public receipt closure is complete and independent
of that remaining construction. No new public STOP or counterexample was found.
Exact P-Ou handoff: scripts/dev-pkg/P-Ar.round3-handoff.md. Canonical audit and
coverage fragments: scripts/dev-pkg/P-Ar.{audit,coverage}-fragment.txt.
Evidence: .lake/sleep-par-r3/{arming-final-build6,par-dck-final,par-exports-final}.log.

### Lead note after the P-Ar round 3 review (2026-10-10 10:39)

rev-par3-astra: P-Ar round 3 proves the corrected public OutagePrefixReceiptDerivedClaim (P15-CUT); merged as PREPARED
(general sleep certificate construction OPEN, scripts/dev-pkg/P-Ar.round3-handoff.md). P-Cl1 production audit complete
(CleanEpochAxioms:169-173). Remaining bookkeeping, first items of the next P-Ar round:
- P-Cl1: add strict commands in Tests/CleanSuppressed.lean itself for p (:11), env (:16), head (:19), run (:21)
  (namespace AvailableChain.FGSA.Run.Tests.CleanSuppressed); regenerate the isolated inventory (190 commands);
  rerun DCK P-Cl1 and complete local coverage; then P-Cl1 is CLOSED.
- P-Ar: scripts/dev-pkg/P-Ar.audit-fragment.txt:14-18, :69-76, :167 list 14 declarations defined only in
  Tests.OutageArming; keep those commands in that test module and drop them from the canonical fragment (AUDIT-FRAGMENT).


## DECISION TVOTE-CUT — S-Ap Round 5 / P-Fi Round 4 (2026-10-10)

ADOPTED at 10:12 in sleep-join-port-notes.md. TVote serves proposal/action
pool reads whose previous-slot start is at or after GST. Add one GST cutoff
antecedent to each read clause in Statements/ComposeStmt.lean. All other
premises, full FullVoteService conclusions, and the emission clause stay fixed.
The proposal cutoff uses integer subtraction, including the negative v=1 cut.

Packet P8 public route, sleep-packet-approved.md:3069, KernelACSideClaim_W:
its RecoverySleep₂, LivenessBoundW and HealingInput premises stay fixed. Its
CoreServices conclusion uses the amended TVote scope. This is an approved
meaning change. Recovery supplies the scoped current receipts and full resolved
HEAD support filter. The original one-seat/two-node run fails the committee
premises; the regression must use the repaired two-seat, bijective-seat run
in tvote-check/check.md §1. Exact public text is in that file's §3.

The shallow/deep API products are regenerated by V2Manifest. The shallow
writer also refreshes 28 inherited hashes from the merged base; their source
is unchanged here. The full auxiliary Claims API still requires compiled
other-family test and assembly modules; its generator reports missing
Claims.Tests.OutageAlignment after the Claims audit root compiles.

P-Fi Round 4 internal part: FinalityVoteReceipts has the same two GST
cutoffs. finality_vote_receipts follows from finality_full_vote_at_scoped_read;
FullVoteService retains both membership and its resolved-head filter.
Joined, Forward, Local, Proposal, Above and all eight Export routes no longer
request a vote supplier. Their Recovery data supplies the record directly.
fgsa_kernelACSide_W proves KernelACSideClaim_W from its public premises.
No additional kernel-side premise remains. Other Finality exports still have
the existing genesis target API and lane supplier inputs; this change does
not close the whole Finality package or the P-As assembly.
The old short-run TVote failure uses an explicit LegacyTVote predicate.
The same short Recovery run now proves the amended receipts and TVote.

TVOTE-CUT regression: Tests/TVoteCut.lean generates the repaired two-seat
run through time 62 with the actual engine ticks, restore, and handlers.
The HEAD and FG seat maps are bijective. Its kernel-checked action_sync,
read_at, read_missing and unscoped_tVote_false prove the exact old TVote
failure at time 6. amended_action_at_read proves the amended clause vacuous
there. The module has its own 31 strict audit commands and P-Fi map entries;
it is not imported by Tests/Axioms. It does not assert a proved full
RecoverySleep₂/HealingInput witness for this generated run.

Final validation: S-Ap DCK PASS (477 GREEN, all controls); P-Fi DCK PASS
(514 GREEN, all controls). The strict audits have only the three permitted
Lean axioms. Complete GREEN exports: 336 proof modules, 253 accepted exports,
zero unaccepted; complete local coverage: 1,420 commands, controls PASS.
Layers: 72 inherited findings, zero new. Shallow/deep API checks PASS.
The final generators supersede the initial inherited artifact refresh: the
base-to-final shallow diff is TVote plus five inherited Clean hashes;
source in those modules is unchanged. Deep has 1,357 roots, 3,817 nodes,
and 73 changed root digests. No generated hash is edited by hand.
Full auxiliary API remains blocked by Healing.SupportTransfer (P-H2); its
read-only build fails on inherited proof obligations. OutageAlignment now
compiles. This supersedes the earlier missing-OutageAlignment note.
No other public source change, protocol change, baseline change or STOP.

Final frozen-source validation for this slice: DCK P-H2 PASS (480 GREEN roots,
40 strict audit sources, 3,366 axiom results, 24 controls); local complete coverage
PASS (41 commands); all-GREEN-root export check PASS (270 proof modules, 253 exports,
zero unaccepted); check-layers PASS (72 accepted, zero new); diff --check PASS.
These results validate the checked helper slice, not the 79 original open targets.


### P-WC Round 3 — audit imports and finite event suppliers (2026-10-10)

- RULING AUDIT-FRAGMENT: the round-2 serial fragment imports production modules.
  It keeps the same 196 commands, coverage rows, and Tests.Axioms key. The
  standalone WeakContinuationSleepAxioms audit remains registered by the test glob.
- Internal statement, sleep port: wc_receiptOrigins and wcg_receiptOrigins
  keep original network acceptances or the exact last local replay stamp.
  Each replay origin carries restartFree from the post-restart index to the read.
- WC StepFacts proves saved-result origins by event induction. Restart clears
  saved rows. A suppressed gate appends none. Nonempty rows have an enabled
  gate origin and an epoch from that gate to the current read.
- WCG StepFacts extracts the same family-local suppliers from Dynamics.
  wcg_finiteFacts and wcg_finiteStep need no WC proof import.
- wc_reconcileBound now scopes the later output reader by confirmedReaderIdx.
  This is an internal statement repair. Unconfirmed readers can expose received
  finality above their retained output, so wc_outputStep includes that third case.
- wc_outputStep handles restart, delivery, off-gate, enabled gate, and suppressed
  gate output cases. Its explicit finality-compatibility input remains a local
  obligation of the joint induction. The joint WCInv producer is still open.
- wc_finalBelow uses receipt collision freedom through its safety projection.
  Public Claims/Statements and public P23 remain unchanged.

### P-WC Round 3 — full restart preservation and T49 history (2026-10-10)

- wc_stepRestart and wcg_stepRestart prove their complete preservation statements.
  A wake keeps FG data, obligations, and outputs. Each historical result precedes
  the restart. Finite facts reestablish exact receipt and volatile-row origins.
  Both families keep the scoped served and transition fields. The original Step
  and Dynamics restart cases now use these proofs and no longer eliminate False.
- T49: wc_history_previousHeads keeps all-time joined participation until it
  selects z at the earlier gate. The original y stays the joined HEAD reader.
  wc_historyMax takes ScheduleWellFormed before it derives enabled results.
  Supplier module: WC/ProposalHistory. Proposal's path and Count work stays open.
- WCG StepOutput, StepReconcile, and FinalBelow are separate family suppliers.
  Their statements use the same local output cases and approved reader scopes
  as WC. Dynamics imports them. Its joint-induction body remains EXPECTED-FAIL.
- Copied private helper names are distinct by family. Private unfolding lemmas
  prevent imported storeAt equation exports. No baseline or allowance changed.
- Four original targets are GREEN. The remaining 17 original targets have owner
  P-WC. All five open family tests still have local owned proof dependencies;
  none is classified as waiting only for a P-As bridge.

### P-WC Round 3 — final prepared validation (2026-10-10)

- Final source DCK PASS: 519 GREEN modules, 39 strict roots, 3,539 results,
  and all 24 controls. The map has 66 targets: 49 GREEN and 17 EXPECTED-FAIL.
- Complete local exports/coverage PASS: 165 proof modules, 251 exports,
  zero unaccepted, and 214 audit rows. All 196 round-2 serial rows remain
  under the existing Tests.Axioms key. No coverage key or allowance was added.
- Layers: 72 inherited findings, zero new. Source scopes and whitespace pass.
  All added Lean lines are at most 100 characters. Public claims are unchanged.
- Empty's local restart step now supplies the exact wake time to restore.
  Its joined proposer supplies the awake and restart-cutoff projections.
  The stale source NoRestart argument was removed from the internal live adapter.
  Empty still has local reader-scope failures. Its no-participation/no-half-cap
  route was not strengthened. The full 21-target closure is not complete.
- Declarations, exact types, audit/coverage/architecture fragments, and remaining
  compiler diagnostics are listed in the P-WC Round 3 report and handoff.

### P-Cl1 Round 2c — fixture audit CLOSED (sleep-par4, 2026-10-10)

This block belongs to the assigned P-Cl1 audit repair. Tests/CleanSuppressed now
has direct strict commands for p, env, head and run in its own module. Production
commands remain in CleanEpochAxioms; no test import enters Tests/Axioms.
The isolated inventory has 190 rows: 183 production commands and seven fixture
commands. DCK P-Cl1 PASS, with 39 strict roots and all 24 controls. Complete local
export/coverage PASS with both roots: 137 proof modules, 251 exports, zero
unaccepted, Gen zero exports, coverage control PASS. Layers: 72 inherited, zero
new. No proof, public claim, protocol, allowance or baseline changed.
The lead note after the P-Ar round 3 review is CLOSED for P-Cl1.
Evidence: .lake/sleep-par-r4/pcl1-{dck,generate,exports}.log and pcl1-coverage.txt.


### P-Ar Round 4 — canonical fragment repair (2026-10-10)

This block belongs to P-Ar. Removed all 14 Tests.OutageArming declarations from
the canonical audit fragment and its owner group from the coverage fragment.
All 14 direct commands remain in Tests/OutageArming. The production fragment
has 145 commands and exactly 145 owner rows. Added its missing production
ArmingGate import. The production-only import closure compiles, and all strict
results use only the permitted standard axioms. No canonical test import, key,
allowance or baseline was added. Evidence: .lake/sleep-par-r4/ParFragment.lean
and par-fragment.log. The round-3 fragment defect is CLOSED.
General sleep certificate construction remains OPEN.


SourceTiming has all-restart durable retention helpers. Source delivery uses each
supporter carrier's TargetReceiptService; pre-GST delivery keeps ReceiverService
explicit, including HistorySafeAt. The moving-frame first/later transfer and lease
consumers use the same exact read epochs and object services. High-source same-label
compatibility uses SameLabelServiceScope. The old-row height set is cut at
recoveryStart on this base; recoveryStart ≥ GST supplies the original GST conclusion.
No public Claims statement changed. Remaining reset and descent callers need these inputs.

### P-H2 Round 3 — audit fragment repair (sleep-ph2c, 2026-10-10)

The serial production fragment imports production modules only. The six HealingOpeningSupport regression audits stay in their own module; the coverage fragment registers that owner as its audit root. All 41 declarations remain in scope. Layers: 72 inherited, zero new. No allowance or public claim change. Exact supplier contracts are in claude-files/sleep-ph2c/exact-handoff.md; source contracts do not claim closure.

### P-H2 Round 3 — recovery service and shifted reset cut (2026-10-10)

RecoveryScope proves the confirmed-reader guard at the actual enabled recovery gate,
including its post-tick cut. RecoveryService constructs ReceiverService from original
proposal emission and FreshHeadService from original HEAD emission. The exact handler
window and receiver exclusion remain explicit inputs. Proposal HistorySafeAt uses durable
history; fresh HEAD receipts use the exact emission history. Neither constructor derives
retained HEAD history from prior processing.

ResetCut now selects the first action at or after recoveryStart, as required by the
approved public H0Reset type. Row caps use durable tree membership and need no NoRestart.
HealingResetCut checks the shifted bounds (GST=10, delta=1: tau=18), simultaneous cuts,
empty runs, and the awake time-zero fixture. Public claims are unchanged.

Validation: --wfail passes for RecoveryScope, RecoveryService, ResetCut and both audit/test
roots. HealingH2RecoveryAxioms has 31 strict commands with permitted axioms only. Layers:
72 inherited, zero new. This group does not close the remaining H2 service producers.

### P-H2 Round 3 — opening, retained frontier and full search (2026-10-10)

The critical path compiles through FrontierSearchFull on H1 pin 615d203b. Opening gate
support at the original q gate comes from its saved fast write. Later gates retain the
exact selected-voter cutoff, enabled actor, GateReceiptScope and local release scope.
The opening/body/CommonEntry proofs use RMonoAll and durable store facts. CommonEntry
gets same-label service from its actual opening fast-write source.

FrontierServiceGate builds RepairGateScope from bounded FrontierReadScope object services.
FrontierService builds RetainedExactHeadRunGeometryOn and uses joined retained-read and
RegimesService _on APIs. Repair consumes the actual proposal tick/emission, retained H6
input, target service and RetainedServiceScope. Source, receiver and consuming read indices
remain explicit. No historical processing fact is used to infer retained HEAD HistorySafeAt.

Search settlement uses healing_settle_start_on, receipt idealization, RMonoAll and exact
carrier services. The gap/top-J arithmetic passes with default heartbeats after narrowing
its local arithmetic facts. The full search proof keeps carrier, original proposal and
bounded frontier scope producers as explicit inputs. Those inputs still need general H2
production suppliers. Source GREEN does not close those unconditional family obligations.

Validation: the 130-command service audit and three ready local boundary tests pass --wfail.
The four isolated inclusive-cut settlement examples pass, with permitted axioms only.
The AS1/AS2 composition bodies pass in an isolated check. Export's containing module and
mixed Assembly tests remain OPEN. Complete local coverage has zero errors. Export checking
has four unaccepted H1 matcher equations (SupportLease/SupportSlow); zero new H2 exports.
No allowance or baseline change. Layers: 72 inherited, zero new. DCK P-H2 passes on the
checked map; the final map/test extension is checked again below.

Exact H1 and P-As requests are in claude-files/sleep-ph2c/H1-requests.md and P-As-requests.md.
They include declaration names, file:line and complete current/proposed telescopes. H1
proposals are marked uncompiled. ResetArrival's two direct HealingReset calls are included.
Public claims unchanged. No public STOP. H2 production and final closure remain OPEN.

### P-H2 Round 3 — settlement and Assembly call-site handoff (2026-10-10)

AttemptRows threads RMonoAll and per-carrier TargetReceiptService into settlement.
HealingAttempt threads the same inputs through all four inclusive-cut adapters. All four
exact examples pass in the isolated settlement check. The handoff's listed “11” sites
contain 12 individual calls; every listed call is ported, including canonical retained
repair and the capped frontier relay. AttemptRows and the containing mixed test still
have open production/import dependencies; this is not a module closure claim.

Export's AS1 composition now takes RMonoAll and the full original-emission ReceiverService
producer. Its Recovery₂ callbacks use the exact RecoverySleep₂ projection. AS1 and AS2
bodies pass separately with permitted axioms only; their full telescopes are in the P-As
handoff. The containing Export remains OPEN through the post-reset cone. No public claim
meaning changed. No unconditional public claim producer is claimed by these _of wrappers.
### P-Ar Round 4 — scoped certificates and gate consumers PREPARED (2026-10-10)

This block belongs to P-Ar. New ArmingSleep supplies a protected pending-gate
certificate. It uses the joined batch denominator, the actual Clean origin and
comparison, current saved rows, and the receiver's three local epochs.
The current-F alternative from P-Cl1 reaches the post-gate S/F result.
Genesis uses direct prefix order. Existing public claims and protocol
declarations are unchanged; no NoRestart premise enters the new module.

slow_arming_on derives its last-label gate from a named slow protected receiver,
including equality at b₀. fast_arming_on still takes an actual last-label result;
the compiled fast consumer derives it when gateTime(l) < b₀. Both test consumers
use the actual clean_invariant, cleanState_of_hist, cleanHistoryAt_body and
clean_epoch_saved_row. They import Clean proofs only in the standalone test.

arming_sleep_gate_core consumes the enabled executed gate and returns stable
coverage plus a lease or current finality. pending_gate_lease_or_F_on also
returns the fullTree/frame-root alternative through the scoped frame theorem.
Its hRows input remains explicit: P-Ou must supply compatibility of all earlier
honest named rows from its source history. slow_gate_consumer applies the actual
slow producer and this gate consumer. No P-Ou file was edited.

Full P-Ar remains PREPARED. OPEN: fast construction at gateTime(l) = b₀ without
an actual label-l result, and the pre-pending HEAD/proposal and duty-history
ports. joinedPartBefore does not supply a count at b₀. A fast protected receiver
need not have an enabled previous-label gate. The legacy ArmingData and its
NoRestart producers are unchanged. The new scoped certificate does not supply
the legacy all-honest healthy_batch or pending_duties fields. No public STOP.

DCK P-Ar PASS: 18 targets, 486 GREEN, 38 strict roots, 3,148 axiom results,
24 controls. The two S-Ap EXPECTED-FAIL modules remain with their owner.
Complete GREEN exports/coverage PASS: 289 proof modules, 253 exports, zero
unaccepted, Gen zero exports, 185 local commands and coverage control PASS.
Canonical fragment: 161 production commands, exact owner rows, strict PASS.
All 16 explicit new production declarations have direct commands. Layers:
72 inherited findings, zero new. No checker, baseline, allowance or scope edit.

Exact P-Ou types and open inputs: scripts/dev-pkg/P-Ar.round4-handoff.md.
Evidence: .lake/sleep-par-r4/par-{dck,exports,generate,fragment-final,types}.log,
par-coverage.txt and layers-final.log.

### P-Ar Round 5 — general fast comparison construction (2026-10-10)

The equal-cut fast construction uses an earlier comparison result when no
label-l gate executes. ArmingSleepGateCert keeps an actual result at q <= l,
the comparison maximum, its FG lift, and the actual joined HEAD bounds.
The previous joined batch supplies the next HEAD through its receiver epoch.
It does not assume participation at the cut or an executed label-l result.
The actual Clean retained-history supplier supplies joined HEAD provenance.
The earlier gate witness follows from strict-before-cut joined participation.

The new fast_arming_scoped_on constructs this certificate at every cut.
pending_gate_lease_or_F_scoped_on returns the same full gate result and keeps
the explicit named-row compatibility boundary for P-Ou. slow_arming_scoped_on
converts the actual slow producer and includes its joined HEAD bounds.
The five Round 4 export names and types are unchanged.

Validation for this group: strict builds of ArmingConstruction and
Tests.OutageArming PASS; actual Clean-to-fast-to-full-gate consumer PASS.
All added production commands are in the standalone test and canonical
production-only fragment. No public claim or protocol declaration changed.
The duty-history group and full package checks remain in progress.
P-Ar remains PREPARED until those checks pass.

Round 5 first-group complete local audit: 218 commands, 168 proof modules,
252 accepted exports, zero unaccepted, Gen zero exports; coverage control PASS.
Layers: 72 inherited findings, zero new. Added Lean lines stay within 100 columns.
The receiver service and scoring modules are registered as owned P-Ar targets.

### P-Ar Round 5 — duty history and full construction CLOSED (2026-10-10)

P-Ar is CLOSED. All 22 owned targets are GREEN. The general fast construction
includes the equal cut without hLast or a strict-cut premise. The actual fast
and slow Clean suppliers construct ArmingSleepHistoryCert. The actual fast
producer also feeds the full pending-gate lease-or-F consumer.

The pre-pending ports use joined selected voters and local receiver epochs:
ArmingScores counts stored honest seats in the joined denominator;
arming_head_covers_on and arming_proposal_covers_on consume the retained local
batch; arming_duty_batch supplies that batch from the regime and certificate.
Actual HEAD and proposal emissions supply their joined guards. The history
certificate supplies pending_duties and inflight_heads with their original
actual-emission conclusions. It also supplies all-honest F compatibility.

Internal receiver-scope port: pending_cover now applies to protected confirmed
readers. Their current caught-up read bounds earlier restart markers and gives
an actual enabled label-l gate. The actual Clean gate-output supplier and
stable-state induction then give B below S before the pending gate. The old
all-honest ArmingData demand is not supplied from protected facts. Public
Claims/Statements are unchanged. The legacy NoRestart producers remain
explicit; no new sleep consumer calls them.

T25 is CLOSED for P-Ar. arming_healthy_batch_window uses joined selected
voters, a named local awake/restart-free receiver window, and regime-derived
HEAD/target services. arming_duty_batch supplies its actual duty consumers.
There is no extra transport premise or global NoRestart in these suppliers.
P-Ou retains its own downstream ports and its explicit hRows source-history
boundary. No P-Ou, P-H1, P-H2, P-WC, P-Cl1, or Shared source file changed.

Validation: DCK P-Ar PASS; 22 targets / 490 GREEN; 38 strict roots / 3,199
axiom results; all 24 controls PASS. Complete GREEN exports: 294 proof modules,
253 accepted exports, zero unaccepted, Gen zero exports. Complete local audit:
236 commands, 170 proof modules, 252 accepted exports, zero unaccepted;
coverage control PASS. Canonical production-only fragment: 207 strict results;
207 exact matching owner rows. Every new explicit public production declaration
has a direct command. Only propext, Classical.choice, and Quot.sound occur.
Layers: 72 inherited findings, zero new. Diff whitespace and 100-column checks
PASS. The two inherited EXPECTED-FAIL roots remain S-Ap-owned; no owned target
is EXPECTED-FAIL. No claim, protocol, checker, baseline, allowance, fixed scope,
toolchain, or dependency manifest changed. No public STOP was introduced.

Exact types and suppliers: scripts/dev-pkg/P-Ar.round5-handoff.md.
Evidence: .lake/sleep-par-r5/. Group 1 commit: 04281d84.
Final frozen-source validation for this slice: DCK P-H2 PASS (480 GREEN roots,
40 strict audit sources, 3,366 axiom results, 24 controls); local complete coverage
PASS (41 commands); all-GREEN-root export check PASS (270 proof modules, 253 exports,
zero unaccepted); check-layers PASS (72 accepted, zero new); diff --check PASS.
These results validate the checked helper slice, not the 79 original open targets.

### Lead note after the P-As round 2 review (2026-10-10 11:56)

rev-pas2-astra: P-As rounds 1-2 PREPARED (Finality on TVOTE-CUT exports; scoped Clean safety; Outage growth/prefix
receipt wiring; current-epoch continuation service; 39 open with owner contracts). This merge also brings P-H2 round 2
(aa4b6c3d; proofs accepted by rev-ph2b-astra). Its canonical fragment scripts/dev-pkg/P-H2.audit-fragment.txt:9/:55-65 and
P-H2.coverage-fragment.txt:54 still import Tests.HealingOpeningSupport: DO NOT APPLY (RULING AUDIT-FRAGMENT); P-H2 round 3
removes them (codex/jobs/sleep-ph2-pending-fixes.md item 1). The six commands stay in Tests/HealingOpeningSupport.lean:136.

## P-H1 — Round 4 scope and carrier repair (2026-10-10)

Base 37beb806, branch sleep-ph1e. The Round 3 CLOSED claim is withdrawn after
FIX-FIRST in rev-ph1d/review.md. Status is PREPARED. Compilation does not prove
that a scope can be constructed from RecoverySleep₂. Public Claims/Statements
are unchanged. No public statement was weakened and no public STOP occurred.

RawServiceScope.gates and FastSupportScope.gates now take the actual enabled
actor guard and SupportGateScope. They no longer demand the false sufficient
GST cutoff from a post-GST vote. SupportGateScope uses a selected joined-voter
batch; its cut-based partial producer requires the cut as an actual caller
input. A nonempty result supplies its source enabledness. Later gate actors
use their own slot cutoff. Suppressed gates create no service demand.

NextTransferScope and ProposalSupportScope no longer assert that every honest
voter is joined. They carry selected joined-seat batches and actual read-pool
rival bounds. Raw late/proposal factories take real source cutoffs; generic raw
consumers expose those cutoffs. The reset consumer derives the cutoff from its
shifted H0Reset cut and actual fresh row. The unused universal raw next factory
was removed. First factories take actual source/receiver guards. Fast's
firstReaders at the selected first read remains an explicit producer obligation.

All six reviewed carrier fields now use HeadCarrierScope. It selects one HEAD
K and carrier W per receiver, with fullTree membership, identity, ancestry,
source floor and compatibility with receiver finality. It does not demand service
for every durable TF block. The relay consumes this selected W; the capped
relay obtains K's membership per receiver. The W/C exclusion run does not force
an old conflicting W into the receiver's cache. Such W cannot supply the selected
ancestry and receiver-floor facts.

RepairHeadServices.prior is guarded by actual proposal emission. FrontierRead's
fast/slow factories take the actual written or eligible source arm. Loss's
first/fast factories take the actual nonempty result or fastWriteAt membership.
Settlement services now select only a carrier at the actual frontier height
and use its receiver-finality compatibility. The consumer proves this floor
fact from RXing, the cap and durable source membership.

Every aggregate producer below is OPEN. All ten rows are P-H1 obligations;
none is counted as accepted H2 assembly work. H2's ports remain separate.
Full context, fields, named partial suppliers and exact goals are in
scripts/dev-pkg/P-H1.round4-producers.md. Healing/ below means
AvailableChainFGSAProofs/Proofs/Healing/. Common variables are p,c,E,rho and
RecoverySleep₂ p c E rho G DeltaF, with the actual source/reset/phase/read guards.

```text
┌─────────┬──────────────────────────┬──────────────────────────────────────────┬───────┐
│ ID      │ Healing record site      │ Exact open goal                          │ Owner │
├─────────┼──────────────────────────┼──────────────────────────────────────────┼───────┤
│ H1e-P1  │ SupportTransfer:22       │ FirstTransferScope E rho ix iy x y s      │ P-H1  │
│ H1e-P2  │ SupportHeads:22          │ NextTransferScope E rho iy y s            │ P-H1  │
│ H1e-P3  │ SupportLease:44          │ FastSupportScope E rho s v x              │ P-H1  │
│ H1e-P4  │ SupportSlow:18           │ SlowSupportScope E rho s v x              │ P-H1  │
│ H1e-P5  │ SupportPerm:16           │ SupportPermanenceServices E rho           │ P-H1  │
│ H1e-P6  │ RepairH6:20              │ RepairHeadServices E rho s                │ P-H1  │
│ H1e-P7  │ RepairGate:17            │ RepairGateScope E rho s                   │ P-H1  │
│ H1e-P8  │ FrontierRead:21          │ FrontierReadScope E rho q v               │ P-H1  │
│ H1e-P9  │ DescentLossCause:43      │ LossServiceScope p c E rho                │ P-H1  │
│ H1e-P10 │ PostResetRaw:22          │ RawServiceScope p c E rho                 │ P-H1  │
└─────────┴──────────────────────────┴──────────────────────────────────────────┴───────┘
```

H1e-HDR, OPEN, owner P-Ar: full check-module-headers finds inherited import-all
errors in Outage/ArmingKernel:2,3. Both lines exist at 37beb806. P-H1 does not
edit another package's files. No checker, baseline or allowance was changed.

P-H1 Round 4 positive evidence: Tests/HealingSupport.PositiveSleep has a finite
ExecutionValid run with Delta=1, GST=9, restart at 9, and an enabled HEAD at 17.
The base HEAD/FG seat maps are bijective. Its fullTree read is nonempty and its
HEAD is actually emitted. A concrete HeadCarrierScope and the repaired relay
application both pass. The selected target is genesis; this does not establish
non-genesis network service or inhabit an aggregate RecoverySleep₂ scope.
The negative all-asleep validity test remains. The label-2 gate at 14 is
suppressed, saves no result and adds no lease or stable record. The label-0
no-restart actor passes the actual join guard while 0 <= slotStart(-1) fails.

P-H1 Round 4 equation export repair: the first export check found
joinedHonest.eq_1 and slotStartZ.eq_1 in SupportGate, plus the private
healingJoinedSeats.eq_1 in SupportTicks. Direct definition reduction and
kernel conversions remove these three exports. No baseline or allowance
changed. The selector is now a reducible abbreviation with the same type.
The repaired module cone checks with zero unaccepted exports.

P-H1 Round 4 final demand guards: carrier factories return HeadCarrierServices.
relay requires an actual HeadCarrierDemand before it supplies a selected receipt
scope. direct serves only the stored K that is the actual source HEAD, under
its receiver floor. Phase geometry produces the relay demand; P-Fd monotonicity
produces direct read floors; the capped relay now serves its actual receiver.
An unrelated or excluded HEAD creates no demand. The six carrier fields no
longer require even an existential receipt witness before admissibility is known.

RawServiceScope.gates now requires actual GateReceiptGeometry and returns only
GateReceiptScope. Its bounded moving-output consumer supplies actual joined
batches separately. An enabled empty gate no longer forces a global voter-batch
field. H2's new hBatches sites are PostResetRawStep:897,
PostResetLeaseStep:1577 and Tests/HealingPostResetRawStep:263. Exact contract:
scripts/dev-pkg/P-H1.round4-handoff.md. Aggregate producer rows H1e-P1..P10 stay
OPEN/P-H1. The audit fragment now has 349 exact production commands/owner rows.

P-H1 Round 4 final validation, source a58f6c2d: DCK PASS 202.52 s; 99 assigned
GREEN targets; 569 total GREEN; zero EXPECTED-FAIL. Strict audits: 42 sources,
3,685 results, only propext/Classical.choice/Quot.sound; 24 controls PASS.
Complete GREEN exports PASS 7.27 s: 363 proof modules, 253 exports, zero
unaccepted. Complete local coverage PASS 8.77 s: 349 exact commands/owner rows,
225 modules, 252 exports, zero unaccepted. Layers: 72 inherited, zero new.
Changed module headers PASS for all 27 Lean files. Full headers remain blocked
by inherited P-Ar ArmingKernel:2,3; no other package file or allowance changed.
Default global export scan also needs the unbuilt Inhabit.WeakContinuationW1;
the complete GREEN/local checks use explicit --roots-only scopes. No public edit.
Exact H2 omitted-site handoff and new guard/monotonicity inputs:
scripts/dev-pkg/P-H1.round4-handoff.md. These are consumers, not scope producers.
Status remains PREPARED: H1e-P1..P10 are OPEN/P-H1, pending a producer or explicit
lead acceptance as assembly work. The concrete positive relay uses genesis;
it does not close non-genesis object-service or aggregate recovery obligations.
Evidence: .lake/sleep-ph1-round4/{dck,exports,coverage}-complete.log;
layers-complete.log, headers-complete.log and own-headers.log.
## P-Ou Round 4 — FIX-FIRST

Base: 0c836aac. The round 3 review items 1–2 are repaired.
InclusionReceiverInputs.early requires a ≤ rho.horizon. The retained calls
supply the actual proposal and vote horizon bounds. The relay field requires
the actual vote tick at ih. The retained score call supplies hih.
Export uses the corrected internal record; the handoff has the same scope.
No public statement or protocol declaration changed. The affected retained
consumer and both inclusion tests build with --wfail.

### P-Ou Round 4 — P-Ar consumers and later gate origin

RestoredReceipt consumes arming_prefix_batch_receipt directly. The restored
service record has no prefix field. The protected non-genesis prefix adapter
uses arming_protected_origin_on to derive 6Δ ≤ b₀ and each in-cut label bound.
PersistenceSleep consumes ArmingSleepCert and arming_sleep_gate_core for
covered receivers. It keeps the current-F alternative. Its domain adapter
supplies P-Ar's hRows from outage_named_of_source_history and the actual
global source history. The pending source-history seed remains OPEN.

The proposer count now has a receipt-backed cover core, a joined _on form,
and the legacy awake-count form. Both forms require actual emitted and
resolved receipts for every counted seat. The awake form covers joined seats
through joinedAt.1. This restores the P-Ar ArmingCover consumer without
changing a P-Ar file or asking a sleep regime for an unjoined HEAD emission.

PersistenceStep imports the lower ArmingStep API and the exact AC/lease APIs.
The source step uses gatePassedAt's enabled guard. The suppressed gate branch
keeps protection and passes through normalization. PersistenceStep is GREEN.

InclusionOrigins proves the latest gate label and the enabled latest gate
for a caught-up reader. It uses the last restart marker, wake-restart law,
and receiver awake state. The later-origin adapter consumes Clean gate output
and scoped public monotonicity; it does not assume an origin at the later read.
The new production consumers and their strict audit build with --wfail.
Layer check: 72 inherited findings, zero new. Public claims are unchanged.

### P-Ou Round 4 — regime services, source boundaries and handover

RestoredBatch derives all restored services from Base₂, full-run synchrony,
GST ≤ b₁ and the joined read guards. Targets use original acceptance and durable
proposal history. Incompatible targets retain the public finality alternative.
The target/proposal anchors are v→e, e→f and f→t(next); fresh HEADs use v→e
with survival through the read. The continuation consumer still needs P-Ar's
separate continuation-prefix adapter. The public OutageSleep₂ prefix theorem
is consumed directly when that exact regime is available. No prefix service
is derived from a restored receipt.

Suppliers and mixed Export now use the proved later-reader origin. They ask
Clean assembly for gate output and bounded confirmed-reader monotonicity.
Tests/InclusionOrigins checks both fields with the real P-Cl1 producers.
The exact Clean section of Export checks with standard axioms after repair
of the receipt's joined-reader binder and the supplier include list.
The full mixed exporter still fails in the legacy outage lane and Shared/Claims.

GoodVotes proves the A-union-W release bound from compatible good targets.
PersistenceSleep proves the strict pre-pending global source seed and isolates
actual pending action compatibility. ContinuationTiming proves the exact
v(r+k+1) handover time. Expiry removes an old row at equality.
The full good-target/late-result producers, both joint inductions, deadline
bound on old conflicting rows and scoped handover remain P-Ou-owned OPEN work.
No all-honest seed or NoRestart is derived from a sleep regime.

The FIX-FIRST tests prove the finite-horizon service contradiction and the
early-tick relay-index contradiction. The new standalone tests check real
Clean origin assembly, restored receipt assembly, opponent release and expiry.
No test import is added to a production or canonical audit module.
Current map: 43 TARGETS, 502 GREEN, 11 EXPECTED-FAIL (nine P-Ou, two S-Ap).
Current exact handoff: scripts/dev-pkg/P-Ou.round4-handoff.md.

### P-Ou Round 4 — final validation

Proof groups: 08e6ddf2 (FIX-FIRST), 27f63349 (P-Ar consumers and latest gate),
c8885bf3 (restored services, origin assembly, release and handover boundaries).
DCK P-Ou PASS: 502 GREEN roots, 41 strict audit sources, 3,124 axiom results
and all 24 controls. Complete exports: 314 proof modules, 253 exports,
zero unaccepted, Gen zero. Complete local coverage: 161 commands; control PASS.
Layers: 72 inherited, zero new. The exact Clean section of mixed Export checks
with standard axioms. The full module remains EXPECTED-FAIL.
P-Ou remains PREPARED, not CLOSED. Public claims and protocol declarations
are unchanged. There is no public STOP. No checker, baseline, allowance,
heartbeat increase or toolchain change was added.
Logs: .lake/sleep-pou-r4/. Exact closure types: P-Ou.round4-handoff.md.

## P-Ou Round 5 — pending source seed (2026-10-10)

Public claims and protocol declarations are unchanged. This group closes the
all-honest pending-source input at PersistenceSleep.outage_arming_sources_on.
It does not close the full outage or continuation joint induction.

- PersistenceSleep.outage_enabled_gate_read_epoch and
  outage_enabled_gate_tick_epoch derive the actual receiver epoch from the
  enabled gate. outage_enabled_gate_joined derives the environment join guard.
- PersistenceSleep.outage_pending_frame_below extends the certificate's
  strict-cut F bound to every actual enabled pending tick, including W.
- GoodVotes.outage_pending_head_targets derives B and receiver-F prefixes
  for honest pending HEAD targets from the actual joined emission and the
  existing Clean transfer projection. Later labels remain joint proof work.
- ReceiverInputs.outage_prefix_head_service, outage_prefix_proposal_service
  and outage_prefix_batch_service use prefix transport with an explicit cut.
  These services need no GST bound. Retained targets use their original
  acceptance and durable proposal history.
- ReceiverInputs.outage_pending_receipt_scope and
  outage_pending_result_compatible cover every enabled pending receiver.
  The early deadline is d(l), at or before b₀; the gate itself can be after b₀.
- ReceiverInputs.outage_pending_sources_compatible discharges hPending for
  all honest actions, including W. outage_arming_sources_from_prefix gives
  the full all-ticks source seed from the sleep prefix, TSrc, the scoped
  certificate and the existing joined Clean transfer projection.
- Tests.OutageServices.pending_seed_consumer checks this exact producer call.

Still owned by P-Ou: the full InclusionReceiverInputs record; later-label
hTargets and hResults; both joint inductions; scoped continuation closure.
No false producer or public STOP was found in this group.

### P-Ou Round 5 — exact old-row deadlines and handover

- PersistenceDeadlines.outage_row_deadline_origin proves an actual enabled
  gate origin for every retained row and its exact deadline d(s)+L.
  Its event induction includes restart and replay. Renewal either retains
  an existing row or uses the new gate deadline; no NoRestart input is used.
- outage_conflicting_row_deadline uses compatibility of actual later
  results to show that a conflicting retained row has label at most r.
  Hence its deadline is at most OutageEnd(r) = v(r+k+1).
- outage_handover_rows_compatible and outage_handover_tick_rows combine
  that bound with the actual clock expiry filter. Deadline equality removes
  the row. An unjoined handover tick still runs expiry before its duty guard.
- The later-result input is bounded by j < i at this receiver. The global
  later-result producer remains P-Ou work; these conditional handover
  theorems do not close the public continuation claim.
- Tests.OutageServices.pending_seed_of_clean_history instantiates the
  actual Clean/Closure.cleanHistoryAt_body transfer projection.
  Tests.OutageServices.handover_rows_consumer checks the actual tick adapter.

The map retains the same nine P-Ou and two S-Ap EXPECTED-FAIL modules.
The two new production modules are registered GREEN after their own builds.
No public statement, protocol declaration, checker or allowance changed.

### P-Ou Round 5 — final validation

Proof source 9ff21cea. DCK P-Ou PASS: 504 GREEN modules, 41 strict audit sources,
3,145 axiom results and all 24 controls. Complete GREEN export check:
316 proof modules, 253 exports, zero unaccepted and zero Gen exports.
Complete local coverage and its control PASS for 182 commands.
Layers retain 72 inherited findings with zero new. Whitespace, ownership,
new prose/code line length and placeholder checks pass.
The actual remaining consumer roots still fail in Induction,
ContinuationReceipt and Shared/Claims. Nine P-Ou and two S-Ap modules remain
EXPECTED-FAIL. P-Ou remains PREPARED, not CLOSED. No public STOP was established.
Handoff: scripts/dev-pkg/P-Ou.round5-handoff.md. Report: Round 5 in the local report.
### Lead note after the P-Ou round 4 review (2026-10-10 12:24)

rev-pou4-astra: MERGE-AS-PREPARED for P-Ou rounds 3 and 4 together. Both
round-3 FIX-FIRST items are repaired (horizon bound on the early field;
actual reader tick on the relay field). Nine P-Ou targets stay open: the two
joint inductions, the continuation joint/receipt/gate modules, Close, both
Exports and Tests/OutageInduction. hTargets (GoodVotes:143/289) stays a
conditional local count premise; its producer must keep the F ⪯ B / B ⪯ F
split and must not become an unconditional assertion.
### P-Ar Round 5 — general fast comparison construction (2026-10-10)

The equal-cut fast construction uses an earlier comparison result when no
label-l gate executes. ArmingSleepGateCert keeps an actual result at q <= l,
the comparison maximum, its FG lift, and the actual joined HEAD bounds.
The previous joined batch supplies the next HEAD through its receiver epoch.
It does not assume participation at the cut or an executed label-l result.
The actual Clean retained-history supplier supplies joined HEAD provenance.
The earlier gate witness follows from strict-before-cut joined participation.

The new fast_arming_scoped_on constructs this certificate at every cut.
pending_gate_lease_or_F_scoped_on returns the same full gate result and keeps
the explicit named-row compatibility boundary for P-Ou. slow_arming_scoped_on
converts the actual slow producer and includes its joined HEAD bounds.
The five Round 4 export names and types are unchanged.

Validation for this group: strict builds of ArmingConstruction and
Tests.OutageArming PASS; actual Clean-to-fast-to-full-gate consumer PASS.
All added production commands are in the standalone test and canonical
production-only fragment. No public claim or protocol declaration changed.
The duty-history group and full package checks remain in progress.
P-Ar remains PREPARED until those checks pass.

Round 5 first-group complete local audit: 218 commands, 168 proof modules,
252 accepted exports, zero unaccepted, Gen zero exports; coverage control PASS.
Layers: 72 inherited findings, zero new. Added Lean lines stay within 100 columns.
The receiver service and scoring modules are registered as owned P-Ar targets.

### P-Ar Round 5 — duty history and full construction CLOSED (2026-10-10)

P-Ar is CLOSED. All 22 owned targets are GREEN. The general fast construction
includes the equal cut without hLast or a strict-cut premise. The actual fast
and slow Clean suppliers construct ArmingSleepHistoryCert. The actual fast
producer also feeds the full pending-gate lease-or-F consumer.

The pre-pending ports use joined selected voters and local receiver epochs:
ArmingScores counts stored honest seats in the joined denominator;
arming_head_covers_on and arming_proposal_covers_on consume the retained local
batch; arming_duty_batch supplies that batch from the regime and certificate.
Actual HEAD and proposal emissions supply their joined guards. The history
certificate supplies pending_duties and inflight_heads with their original
actual-emission conclusions. It also supplies all-honest F compatibility.

Internal receiver-scope port: pending_cover now applies to protected confirmed
readers. Their current caught-up read bounds earlier restart markers and gives
an actual enabled label-l gate. The actual Clean gate-output supplier and
stable-state induction then give B below S before the pending gate. The old
all-honest ArmingData demand is not supplied from protected facts. Public
Claims/Statements are unchanged. The legacy NoRestart producers remain
explicit; no new sleep consumer calls them.

T25 is CLOSED for P-Ar. arming_healthy_batch_window uses joined selected
voters, a named local awake/restart-free receiver window, and regime-derived
HEAD/target services. arming_duty_batch supplies its actual duty consumers.
There is no extra transport premise or global NoRestart in these suppliers.
P-Ou retains its own downstream ports and its explicit hRows source-history
boundary. No P-Ou, P-H1, P-H2, P-WC, P-Cl1, or Shared source file changed.

Validation: DCK P-Ar PASS; 22 targets / 490 GREEN; 38 strict roots / 3,199
axiom results; all 24 controls PASS. Complete GREEN exports: 294 proof modules,
253 accepted exports, zero unaccepted, Gen zero exports. Complete local audit:
236 commands, 170 proof modules, 252 accepted exports, zero unaccepted;
coverage control PASS. Canonical production-only fragment: 207 strict results;
207 exact matching owner rows. Every new explicit public production declaration
has a direct command. Only propext, Classical.choice, and Quot.sound occur.
Layers: 72 inherited findings, zero new. Diff whitespace and 100-column checks
PASS. The two inherited EXPECTED-FAIL roots remain S-Ap-owned; no owned target
is EXPECTED-FAIL. No claim, protocol, checker, baseline, allowance, fixed scope,
toolchain, or dependency manifest changed. No public STOP was introduced.

Exact types and suppliers: scripts/dev-pkg/P-Ar.round5-handoff.md.
Evidence: .lake/sleep-par-r5/. Group 1 commit: 04281d84.

### Lead note after the P-Ar round 5 review (2026-10-10 12:48)

rev-par5-astra: FIX-FIRST for CLOSED, merged as PREPARED. The equal-cut fast
construction is acyclic and every arming-record field has a producer. Open
before CLOSED: (1) remove `import all` at Outage/ArmingLocal.lean:2 and the two
inherited uses at Outage/ArmingKernel.lean:2-3 (check-module-headers);
(2) a positive finite-run witness for the arming certificates (non-genesis
stable read, protected receivers, fast equal-cut branch, slow instance).
hRows (ArmingConstruction:270) stays an OPEN P-Ou source-history obligation,
including actions at the pending time; do not project the old all-honest
pending_input.
## P-WC Round 4 — event induction, 2026-10-10

Status: PREPARED. Base e4fafd7b, branch sleep-pwc3.
The joint WC and WCG event proofs now preserve WCInv for delivery, off-gate
ticks, enabled gates, suppressed gates, and restart. Next-event finality has
an earlier target-action origin in the prior bounded history. This proves
compatibility before the local output update. All three output origins are
handled: retained output, gate result, and received finality.

Retrospective transfer uses joined next-slot readers and local HEAD service.
New family HeadRelay modules prove fresh or original accepted HEAD service,
strict receipt stamps, receiver epochs, and carried-pool provenance. No
global NoRestart premise is inferred. Saved and fast origins retain their
exact epochs. The full WC safety adapter now has the sleep telescope.
Internal adapter repair under the lead ruling of 2026-10-10; public claims
and Statements are unchanged. Consumers: StepTransfer, Step, Induction,
and WCG Dynamics.

New GREEN original targets: StepTransfer, Step, Induction, WCG Dynamics.
The two new HeadRelay modules are GREEN. Thirteen original targets remain
EXPECTED-FAIL with owner P-WC. Strict local audit passes; only propext,
Classical.choice, and Quot.sound. Complete export check: 173 proof modules,
251 exports, zero unaccepted. Layers: 72 inherited findings, zero new.
Serial audit and coverage fragments: claude-files/sleep-pwc-round4-*.txt.
Evidence: .lake/sleep-pwc-r4/event-*.log and induction.log.

### P-WC Round 4 — Proposal current-duty service

Proposal and its first eligible-slot test now compile. The current proposer
or HEAD reader can have no previous HEAD of its own. A joined earlier
source supplies the comparison path through the current receiver's duty
epoch. Count uses joined seats and exact original HEAD emissions. Receipt
stamps are before the previous early and freeze times.

The old retained path/stamp helpers now state NoRestart explicitly. They
are legacy helpers; no repaired sleep consumer uses them. The current
Proposal pivot uses the new current-duty path. Assembly callers are P-As
port items. No public Claims/Statements declaration changed.

Local strict audit passes. Complete export check: 189 proof modules,
252 exports, zero unaccepted. Layers: 72 inherited, zero new. Eleven
original targets remain EXPECTED-FAIL P-WC. Exact adoption and Empty are
still local work. Evidence: proposal-audit2.log, proposal-exports2.log.

### P-WC Round 4 — exact adoption and enabled gate suppliers

ExactProposal and its contract test now compile. ExactReceipts supplies
proposal service at a public receiver anchor, accepted-target service,
both retained score directions, and fresh emitted proposal service.
The retained score proof carries the source epoch, original frozen HEAD
acceptances, and forward/backward block service. Admission keeps the exact
named body and its strict original delivery, then retains it through the
joined consuming read. No global NoRestart is supplied.

StepGateBatch now exposes wc_gate_active_heads. InclusionGate proves the
raw exact gate result from joined receipt evidence. This supplier is
GREEN; the full Inclusion consumer remains EXPECTED-FAIL. The existing
public exact-adoption and admission Statements are unchanged.

Eight of the 17 original open targets are now GREEN. Nine remain
EXPECTED-FAIL, all owner P-WC: WC Inclusion, Growth, Live, Export; WCG
Empty and Export; the Inclusion, Growth, and GrowthEmptyAxioms tests.
The remaining failures are local P-WC work. None is only a P-As bridge.
Empty was not changed; no participation or half-cap premise was added.

Map: 71 targets, 62 GREEN / 9 EXPECTED-FAIL. Required union targets:
532 GREEN / 9 EXPECTED-FAIL. Strict audit: 285 local commands/results,
plus three Proposal test commands. Only propext, Classical.choice, and
Quot.sound. Exports: 200 proof modules, 252 exports, zero unaccepted.
Layers: 72 inherited, zero new. Final package DCK is running.
Evidence: .lake/sleep-pwc-r4/. Round 4 fragments are in claude-files/.

P-WC Round 4 final validation: DCK PASS. 532 GREEN modules, 40 strict
roots, 3,613 results, and 24 controls PASS. Exports: 200 proof modules,
252 exports, zero unaccepted. All 214 prior inventory rows remain in
the 285-row local inventory. Source scopes PASS: 1,361 active / 337
deferred PC-SA modules. Layers: 72 inherited / zero new. Nine targets
remain EXPECTED-FAIL P-WC. Public claims unchanged; no public meaning STOP.
Implementation head: 16e578fb. Tracked implementation tree is clean.

## P-WC Round 5 — exact inclusion and cached safety, 2026-10-10

- T47: Inclusion uses enabled gates and joined selected HEAD receipts. The old
  admission-at-vote and global NoRestart adapters are removed from this route.
- T48: A confirmed reader uses its own original gate when its current epoch
  covers that gate. A later wake uses the caught-up enabled gate and result order.
  Both output getters retain the exact public reader scopes.
- Inclusion's prior-result reader is joined at the next vote. Participation stays
  all-time joined until the required voter and enabled gate actor are selected.
- Internal additive evidence: WCInclusion6ResultStatement also returns the exact
  enabled original WCResult. WCInclusion6Statement and public claims are unchanged.
- Internal cached safety: WCCachedSafety, wc_cachedSafety, and wcg_cachedSafety
  expose compatibility, monotonicity, and seed preservation for stored outputs.
  The existing scoped safety statements are projections. This supplies the
  comparisons needed when a trigger reader sleeps before a growth deadline.
- Round-3 P3 evidence repair: both reconcile supplier entries are regenerated
  from their full source types, including all premises and conclusions.
- Inclusion and its two contract tests pass --wfail. The cached safety suppliers
  pass --wfail. Strict and full package checks follow in the final Round 5 block.

### P-WC Round 5 — Empty, Growth, Live, and tests

- Empty's finalBelow reader is confirmedReaderIdx. Local-prefix replay keeps its
  exact enabled source gate, awake interval, restart interval, and applied wakes.
  The least matching source occurrence has no later prefix time. Its source
  service call keeps the confirmed-reader guard instead of an honest-only guard.
- Empty's cached source safety supplies event and public output order, including
  terminal reads. Source cached coverage supplies the future proposal comparison.
  Retained honest identities can shrink; the source comparison witness is used
  in the source, and is not assumed honest in the continuation.
- The empty route has no continuation participation or half-cap premise. Its new
  internal component inputs are cached source safety and cached source proposal
  coverage. The source induction and exact original-gate result prove them.
- Growth's old honest-only deadline comparison did not fit scoped public readers.
  The internal implementation takes cached output safety and an original-result
  coverage witness. WC checkpoint proves both from its finite induction and
  wc_inclusion6_result. WCGrowthStatement and public JointGrowthAt are unchanged.
- Live and checkpoint consume RestartsAtWakes, receipt-root idealization,
  all-time joined participation, durable/epoch stores, RMonoAll, RFrameNextEpoch,
  and enabled lease/fast origins. No sleep regime supplies global NoRestart.
- All nine original EXPECTED-FAIL targets and all three remaining tests pass
  --wfail. The full local audit passes with only the three permitted axioms.
  No owned expected failure remains. P-As must port its unowned callers to the
  precise component types in the Round 5 handoff. Final package checks follow.

P-WC Round 5 final validation: DCK PASS. 541 GREEN modules, 43 strict
roots, 3,662 axiom results, and 24 controls PASS. Complete local exports and
coverage PASS: 207 proof modules, 252 exports, zero unaccepted, 313 inventory
rows. Layers: 72 inherited findings, zero new. Source scopes PASS. All nine
original failures are GREEN; no owned EXPECTED-FAIL target remains. PREPARED
for serial integration; the exact P-As caller ports remain in the handoff.

## P-WC Round 6 — authorized import repair (2026-10-10)

WC/ExactReceipts uses a public import of Shared.CatchUp. The private
TargetReceiptService adapter is removed. Accepted targets use the existing
fgsa_target_service_of_proposal. Genesis uses fgsa_target_service_genesis,
the one Shared addition authorized by sleep-pwc-pending-fixes.md item 1.
No public claim or existing statement changes. The module-header check passes.
The standalone sleep audit and serial fragments include the new theorem.

## P-WC Round 6 — SCOPE-NARROW audit (2026-10-10)

Audited 265 exported family theorem signatures and their full interfaces.
The report and handoff contain 79 grouped rows with producer anchors, open
owners, and finite-sleep truth. The exact 2,065 explicit binder entries are
in claude-files/sleep-pwc-round6-input-inventory.json. No false universal
receipt/gate/join/time-cut shape was found in the repaired owned service
routes. No public statement or claim changes. The recovered source snapshot
and four conditional NoRestart legacy helpers are not arbitrary-run facts.
The P-As source/epoch/cached-coverage caller ports remain open. PREPARED.
Headers PASS; layers zero new; exports zero unaccepted; DCK PASS (43 strict
roots, 3,663 results, 24 controls); strict local production audit 314 results.

### Lead note after the P-WC round 5 closure review (2026-10-10 13:06)

rev-pwc5-astra: MERGE-AS-PREPARED after the import fix; c914737e removes
`import all` at WC/ExactReceipts.lean:2 exactly as rev-pwc4 item 1 asked.
All 71 P-WC targets are GREEN. WCCachedSafety is proved by both seeded
inductions; every service record has a local producer; no SCOPE-NARROW
universal field. Open: P-As caller ports (Assembly/WeakContinuationGrowth
:543/:565/:578, Growth:35-38, Empty:608/609/686), the source seed and the
combined source-and-suffix joined count. Merge note: sleep-int already had
an identical fgsa_target_service_genesis (99ad1f9d); that copy is kept.

### Lead note after the P-As round 3 review (2026-10-10 13:24)

rev-pas3b-astra: MERGE-AS-PREPARED. Limits that stay visible: (1) build break
on sleep-int since the P-Ar r5 merge: Outage/ArmingScores re-declares
inclusion_proposer_prior_of_F_prefix_on and inclusion_reader_scores_on from
Outage/ExactProposalReceipts (P-Ou r3); owner P-Ar, fix queued (sleep-par
pending fixes item 3). (2) B18's fixture proves StrongRecoverySearchPrefix₂ ∧
CleanGrowthContinuation₂, not CleanGrowthContinuationSleep₂ (no
joinedParticipation adapter); complete non-vacuity of the public sleep claim
stays OPEN. Healing targets are out of P-As scope until P-H1 r4 lands.

### P-Ou Round 6 — integration name collision

Base 4b561a23 combines P-Ou round 5 and P-Ar round 5. ArmingScores
redeclared two P-Ou theorem names from ExactProposalReceipts. Rename the
owned copies to inclusion_receiver_proposer_prior_on and
inclusion_receiver_scores_on. Update ExactProposalRetained, the local
strict audit, and the complete coverage fragment. The two bodies and
all public claims stay unchanged. ArmingScores now compiles.

### P-Ou Round 6 — general pending seed and selected gate service

- ReceiverInputs.outage_arming_sources_scoped proves the all-ticks
  source history from ArmingSleepGateCert. Pending-time sources use
  fast support, the strict release bound from joined participation, and
  an actual honest joined HEAD above D. Sources in W are included.
- outage_arming_named_scoped converts this seed with P-Fd emitted names.
  outage_arming_protection_scoped discharges the full P-Ar row boundary
  and returns protection and domain on coveredNodes.
- outage_fast_seed_scoped consumes fast_arming_scoped_on. The hLast
  request is satisfied. OutageServices supplies the actual Clean state,
  history, transfer, provenance, and P-Fd named-source producers.
- OutageGateReceiptScope requests only selected HEADs. The restored
  producer uses actual enabled join, the receiver epoch, and F below B.
  outageV_gate_of_good_service_scoped keeps the B below F / F below B
  split. The finalized branch needs no receipt or count premise.
- outage_restored_result_of_good_targets produces every receiver
  service from transport and E's actual count. Its conditional good-HEAD
  target input and current F compatibility remain P-Ou joint obligations.
- Public claims and protocol declarations are unchanged. Both full
  scoped joint inductions and InclusionReceiverInputs remain open.
- ReceiverInputs and RestoredBatch now use public CatchUp imports and
  its public target-service constructors. Two inherited header findings
  are removed. Layers: 72 findings, zero new.

### P-Ou Round 6 — A union W source transition

ReceiverInputs.outage_fast_supporting_head_outside selects an actual
joined HEAD outside any bad set that contains the faults and has count
below the release level. The original faulty-only helper is its wrapper.
outage_e1_release_bound proves the fixed A union W bound before recovery.
outage_source_of_good_heads uses this bound for every actual honest
source, including a source in W. The caller must prove compatibility of
the selected good HEADs in the joint induction. This callback is an open
P-Ou obligation; it is not a producer and does not close the package.
All three declarations pass the strict local audit.

### P-Ou Round 6 — export repair

The complete export check found F_at.eq_1 in GoodVotes. The new proof
used simp on the imported predicate. Replace that step with change on
the exact confirmation type. The strict local roots compile after this
repair. No allowance, baseline, public declaration, or protocol changed.

### P-Ou Round 6 — final validation and closure status

Proof source 84255dd4. DCK P-Ou PASS: 504 GREEN modules, 41 strict
sources, 3,165 axiom results, and all 24 controls. Complete GREEN
exports: 321 proof modules, 253 exports, zero unaccepted and zero Gen
exports. Complete local coverage and its control PASS for 201 commands.
Layers retain 72 inherited findings with zero new. Module headers have
four inherited failures and no new failure; two owned failures were
removed. New prose/code line lengths and whitespace pass.

The actual consumer roots still fail in Induction and ContinuationReceipt.
All nine P-Ou and two S-Ap EXPECTED-FAIL entries remain. P-Ou is PREPARED,
not CLOSED. The full scoped joint inductions, later good-HEAD invariant,
global late-result producer, InclusionReceiverInputs, and final exports
remain P-Ou work. The fast hLast request is satisfied; the continuation
prefix adapter remains a P-Ar request. No public STOP was established.
Handoff: scripts/dev-pkg/P-Ou.round6-handoff.md. Its SCOPE-NARROW table
records every input role, named producer, and open owner. Report: Round 6
in claude-files/sleep-pou-report.md. Evidence: .lake/sleep-pou-r6/.

### P-Ou Round 7 — public release count API

GoodVotes uses the public fgsa_releaseCount_le_senders lemma appended to Shared/Release.
The lemma bounds the actual release witnesses by an explicit sender set. The A union W
proof and its conclusion are unchanged. The last P-Ou import-all is removed.
Headers have no P-Ou failure; three inherited P-Ar findings remain.

### P-Ou Round 7 — scoped pre-restoration joint induction

ScopedInduction:81 proves the full event induction before restoration, at an endpoint
at or before lease expiry. Sources and named history cover all honest nodes, including W.
Protection and post-pending duties cover G. Restart keeps durable protection and adds no
source or duty. Releases use the fixed A union W bound; good HEADs are covered before r.
ScopedInduction:351 supplies the seeds from the scoped certificate, P-Ar in-flight duties,
and the P-Fd source suppliers. Tests/OutageServices:155 uses the actual Clean and P-Fd
producers. ScopedInduction:386 gives the inclusive F and covered lease-or-F read.

Induction now imports the scoped implementation. Its former all-honest ArmingCert seed
and NoRestart lane were removed. The true empty duty seed remains. The old downstream
continuation and Close consumers still need a port to the scoped interface. This is an
internal proof replacement; public claims and protocol declarations are unchanged.

GoodVotes:559 and ReceiverInputs:757 prove restored result compatibility from fresh
HEAD service and compatible good targets. A good target below receiver F needs no body
receipt: its fresh HEAD enters the late denominator. Resolved targets are identified
with actual emitted bodies using named roots. The existing F <= B / B <= F split remains.
The good-HEAD history and counts outside the E window remain explicit P-Ou obligations.
This conditional result producer is not global hResults or full continuation closure.

Induction is GREEN; eight P-Ou consumer roots remain EXPECTED-FAIL. P-Ou is PREPARED.

### P-Ou Round 7 — export repair

337c0238 replaces fullTree and controls unfolds with explicit frame/control view
equalities. Complete GREEN exports have 325 proof modules, 253 exports, zero unaccepted
and zero Gen exports. No checker baseline or allowance changed. The complete local
212-command inventory and its coverage control pass.

### P-Ou Round 7 — independent induction tests

Tests/OutageInduction now audits the compiled scoped kernel through its production
import. The independent disclosure, contested-frame, lease, count, and phase tests
remain. The raw saved-result test has the actual joined-gate guard. Restart tests
check retained obligations and protection at the exact wake time. The old empty-lock
restart assertion was false under the approved retained-store restart. No public
claim changes. The test module is GREEN as a kernel test; Close and the public
exporters remain EXPECTED-FAIL and were checked separately.
The complete local inventory now has 225 commands.

### P-Ou Round 7 — final validation

Proof source 181f601e. DCK P-Ou PASS: 507 GREEN roots, 42 strict audit sources,
3,189 axiom results and all 24 default controls. Complete GREEN exports: 325 proof
modules, 253 exports, zero unaccepted and zero Gen exports. Complete local coverage
and its control pass for 225 commands. Layers: 72 inherited findings, zero new.
Headers: three inherited P-Ar failures, zero P-Ou failure. No checker, baseline,
allowance, toolchain, protocol declaration, or public claim changed.

Induction and the independent Tests/OutageInduction kernel audit are GREEN.
Seven P-Ou and two S-Ap roots remain EXPECTED-FAIL. P-Ou remains PREPARED.
The later good-HEAD invariant, global hResults, full InclusionReceiverInputs,
full continuation, handover and final public consumers remain open.
Handoff: scripts/dev-pkg/P-Ou.round7-handoff.md. Evidence: .lake/sleep-pou-r7/.
### Lead note after the P-Ou round 6 review (2026-10-10 13:33)

rev-pou6-astra: MERGE-AS-PREPARED for P-Ou rounds 5 and 6. hRows is
discharged by named source history at afterTicksIdx (gateTime (l+1)),
including pending-time sources in W, without the old all-honest
pending_input. The P-Ou score-theorem copies are renamed
(inclusion_receiver_proposer_prior_on, inclusion_receiver_scores_on), which
removes the ArmingScores duplicate-name build break on sleep-int. Header
residue: GoodVotes:2 (P-Ou r7) and ArmingKernel:2/3, ArmingLocal:2 (P-Ar r6).
### P-Ar Round 6 — public imports and declaration collisions (2026-10-10)

Base: dcdb4a06; branch sleep-par6. P-Ar remains PREPARED pending the
positive finite-run witnesses and full package validation.
ArmingKernel and ArmingLocal now use public CatchUp imports and the existing
fgsa_target_service_genesis / fgsa_target_service_of_proposal constructors.
The three P-Ar import-all findings are removed. No supplier module changed.
The merged base has two conflicting inclusion_*_on declarations in
ExactProposalReceipts and ArmingScores. The P-Ar copies now have distinct
arming_ names; their types and proof bodies are unchanged. ArmingCover and
the local audit consumers use those names. No public claim changed.
Production build: ArmingConstruction dependency cone PASS with --wfail.
Headers: no P-Ar failure; two P-Ou findings remain in GoodVotes/RestoredBatch.
Layers: 72 inherited findings, zero new. P-Ou owns both header repairs.

### P-Ar Round 6 — finite certificates and closure (2026-10-10)

P-Ar CLOSED. Both Round 5 review fixes now pass in the P-Ar scope.
All 22 owned targets are GREEN. Public claims and the principal arming
constructor/history/gate export types are unchanged. No public STOP.
Import repair commit: 244016e1. Final source: Tests/OutageArming.lean.
Finite.positive_fast:1363 and Finite.positive_slow:1375 have no proof inputs.
Both prove ExecutionValid, a non-genesis stable read, a protected receiver,
an arming certificate, and the executed pending-gate lease conclusion.
Fast: b0=earlyTime(3)=14, no label-2 result; the comparison result has label 1.
It inhabits ArmingSleepGateCert. ArmingSleepCert.max_mem at label 2 cannot
coexist with no_last; the slow witness inhabits that record instead.
Slow: label-2 result and current-epoch saved row; both gate proofs consume
the production exports and require an active lease, since F is genesis.
Parameters: Delta=1, n=1, k=2, R=2, eta=0; 25 events, horizon 18.
These are direct finite record/export witnesses, not full OutageSleep2
inhabitation claims. The sparse fast trace's late HEAD 2 violates healthy
prefix delivery; no healthy premise is assumed or fabricated. Existing
regime/Clean producer consumers and the negative EarlyCut tests still pass.
Default heartbeats are retained. The fixture has maxRecDepth=2048 for the
finite state reduction stack. No proof or project axiom was added.
DCK PASS: 22 targets / 490 GREEN; 38 strict roots / 3,225 results; 24 controls.
Local strict audit: 261 results; production fragment: 207 results.
Complete GREEN export check: 294 modules / 253 exports / zero unaccepted.
Complete local coverage: 261 commands / 170 modules / zero unaccepted.
Only propext, Classical.choice, Quot.sound occur. Layers: zero new.
Headers: no P-Ar failure; GoodVotes/RestoredBatch failures remain with P-Ou.
hRows remains the exact OPEN P-Ou source-history input at the pending cut.
No P-Ou, P-As, P-H1, P-H2, P-WC, Shared, or Model source was edited.
Handoff: scripts/dev-pkg/P-Ar.round6-handoff.md. Evidence: .lake/sleep-par-r6/.

### Lead note after the P-Ar round 6 review (2026-10-10 13:44)

rev-par6-astra: MERGE-AS-PREPARED. Headers clean in all 22 P-Ar targets;
finite fast (equal cut) and slow certificate witnesses are hypothesis-free
(V = Fin 1; not full OutageSleep₂). Open before CLOSED: a named producer
OutageContinuationSleepPrem p c fast E rho T b₀ b₁ ΔF →
OutagePrefixReceipt p c E rho fast T b₀ for RestoredBatch:377 (the existing
arming_prefix_batch_receipt takes OutageSleep₂, whose η budget and E1 the
continuation record does not supply); keep the per-label earlyTime q ≤ b₀ guard.

### P-Ar Round 7 — continuation-prefix producer CLOSED (2026-10-10)

Base: sleep-int 102d8f5b; branch sleep-par7. This block belongs to P-Ar.
The last closure item in the Round 6 lead note is now checked.
ArmingKernel:901 exports arming_continuation_prefix_receipt from
OutageContinuationSleepPrem to OutagePrefixReceipt. It uses h.pre and the
shared arming_prefix_receipt_of_healthy_prefix supplier at :892.
arming_batch_service_of_prefix at :831 needs only HealthyPrefix₂ and the
protected receiver/label premises. The seven lower service proofs are
factored into prefix suppliers, with the existing outage names/types kept.
All 28 existing ArmingKernel theorem signatures are unchanged.
The per-label earlyTime q ≤ b₀ guard remains, with equality allowed (P15-CUT).
No η budget or OutageE1 field is required. All needed premises are present.
No public meaning changed; no public STOP or missing-field STOP.

The exact application to the real outage_continuation_receipt_of_prefix
passes in .lake/sleep-par-r7/ContinuationConsumer.lean. RestoredBatch is
unchanged and builds with --wfail. The persistent prefix consumer and direct
strict commands are in Tests/OutageArming.lean. The production fragment has
216 commands and matching source-owner rows; it has production imports only.
Shared audit/coverage files remain for serial integration with their existing key.

P-Ar CLOSED. All 22 owned targets are GREEN; 490 total GREEN entries.
The two inherited S-Ap EXPECTED-FAIL roots are unchanged.
DCK PASS: 38 strict roots, 3,235 results, all 24 controls PASS.
Complete GREEN exports: 294 proof modules, 253 exports, zero unaccepted.
Complete local coverage: 271 commands; 170 modules, 252 exports, zero unaccepted.
Production strict audit: 216 results. Actual continuation call: 1 strict result.
Only propext, Classical.choice, and Quot.sound occur.
Layers: 72 inherited findings, zero new. Headers: no P-Ar failure;
GoodVotes:2 remains P-Ou's inherited import-all failure.
Added Lean lines are <=100; no proof placeholders or unsafe evaluation.
No non-arming Outage, Claims/Statements, supplier-owner, checker, baseline,
allowance, dependency, or shared inventory file was edited.
No P-Ar closure input remains. The merged P-Ou hRows producer supersedes the
old Round 6 hRows note. Handoff: scripts/dev-pkg/P-Ar.round7-handoff.md.
Evidence: .lake/sleep-par-r7/.
### P-Ou Round 7 — public release count API

GoodVotes uses the public fgsa_releaseCount_le_senders lemma appended to Shared/Release.
The lemma bounds the actual release witnesses by an explicit sender set. The A union W
proof and its conclusion are unchanged. The last P-Ou import-all is removed.
Headers have no P-Ou failure; three inherited P-Ar findings remain.

### P-Ou Round 7 — scoped pre-restoration joint induction

ScopedInduction:81 proves the full event induction before restoration, at an endpoint
at or before lease expiry. Sources and named history cover all honest nodes, including W.
Protection and post-pending duties cover G. Restart keeps durable protection and adds no
source or duty. Releases use the fixed A union W bound; good HEADs are covered before r.
ScopedInduction:351 supplies the seeds from the scoped certificate, P-Ar in-flight duties,
and the P-Fd source suppliers. Tests/OutageServices:155 uses the actual Clean and P-Fd
producers. ScopedInduction:386 gives the inclusive F and covered lease-or-F read.

Induction now imports the scoped implementation. Its former all-honest ArmingCert seed
and NoRestart lane were removed. The true empty duty seed remains. The old downstream
continuation and Close consumers still need a port to the scoped interface. This is an
internal proof replacement; public claims and protocol declarations are unchanged.

GoodVotes:559 and ReceiverInputs:757 prove restored result compatibility from fresh
HEAD service and compatible good targets. A good target below receiver F needs no body
receipt: its fresh HEAD enters the late denominator. Resolved targets are identified
with actual emitted bodies using named roots. The existing F <= B / B <= F split remains.
The good-HEAD history and counts outside the E window remain explicit P-Ou obligations.
This conditional result producer is not global hResults or full continuation closure.

Induction is GREEN; eight P-Ou consumer roots remain EXPECTED-FAIL. P-Ou is PREPARED.

### P-Ou Round 7 — export repair

337c0238 replaces fullTree and controls unfolds with explicit frame/control view
equalities. Complete GREEN exports have 325 proof modules, 253 exports, zero unaccepted
and zero Gen exports. No checker baseline or allowance changed. The complete local
212-command inventory and its coverage control pass.

### P-Ou Round 7 — independent induction tests

Tests/OutageInduction now audits the compiled scoped kernel through its production
import. The independent disclosure, contested-frame, lease, count, and phase tests
remain. The raw saved-result test has the actual joined-gate guard. Restart tests
check retained obligations and protection at the exact wake time. The old empty-lock
restart assertion was false under the approved retained-store restart. No public
claim changes. The test module is GREEN as a kernel test; Close and the public
exporters remain EXPECTED-FAIL and were checked separately.
The complete local inventory now has 225 commands.

### P-Ou Round 7 — final validation

Proof source 181f601e. DCK P-Ou PASS: 507 GREEN roots, 42 strict audit sources,
3,189 axiom results and all 24 default controls. Complete GREEN exports: 325 proof
modules, 253 exports, zero unaccepted and zero Gen exports. Complete local coverage
and its control pass for 225 commands. Layers: 72 inherited findings, zero new.
Headers: three inherited P-Ar failures, zero P-Ou failure. No checker, baseline,
allowance, toolchain, protocol declaration, or public claim changed.

Induction and the independent Tests/OutageInduction kernel audit are GREEN.
Seven P-Ou and two S-Ap roots remain EXPECTED-FAIL. P-Ou remains PREPARED.
The later good-HEAD invariant, global hResults, full InclusionReceiverInputs,
full continuation, handover and final public consumers remain open.
Handoff: scripts/dev-pkg/P-Ou.round7-handoff.md. Evidence: .lake/sleep-pou-r7/.

### P-Fd fast-write receiver epoch — 2026-10-10

Added fgsa_leaseOrigins_fastWrites_epoch in Foundations/Leases.lean:642.
Current fast writes have an enabled, passed gate origin in the receiver's
current epoch. Restart clears the cache; event induction supplies restartFree.
The existing origin theorem and public claims are unchanged. Consumer: P-As hfast.
P-Fd remains CLOSED. DCK PASS; strict audit PASS; exports zero unaccepted;
layers zero new; headers PASS. Report: claude-files/sleep-pfd-fast-report.md.

### P-H2 Round 4 — selected-witness service (sleep-ph2d, 2026-10-10)

RULING SCOPE-NARROW applies to the H2 carriers and heldServices inputs.
WitnessReceiptScope retains the actual tick, its joined guard, and the receiver
floor at the strict deadline. The held callback accepts a frontier-height witness.
The opening callback retains full-tree membership, HEAD equality, ancestry and lo.
No full-TF receipt factory is added. The selected services have an OPEN P-H2
producer obligation; healing_accepted_target_service supplies the object route
once original acceptance and handler/non-exclusion facts are available.

H1's current healing_support_frame_at and healing_settle_start_on still accept
full-TF callbacks. Their narrower contracts are in
claude-files/sleep-ph2d/H1-narrow-requests.md. H1 files are unchanged. The affected
H2 callers stay OPEN; their previous GREEN classification is withdrawn until
the narrower H1 APIs land. Compilation does not prove a producer exists.

Review evidence correction: round 3 had 183 canonical serial audits and six
separate HealingOpeningSupport audits, total 189. The new enabled-gate helper
adds one canonical audit. service-coverage-final.log reported 225 modules and
four unaccepted H1 exports; it did not prove the earlier claimed 236-module
zero-error coverage result. The frozen-exports log held the 236-module count.
The five truncated H1 telescopes and four empty consumer lists are corrected.
The four Foundations requests now bind p, In/V, DecidableEq V, c, E and rho.
The refuted reset full-TF and RequestedDescentServices.next proposals are withdrawn.

### P-H2 Round 4 — aggregate scope handoff (2026-10-10)

Opening/Repair permanence is indexed by the actual phase. Frontier permanence
also has the frontier endpoint bound. Repair and frontier head factories are
keyed to the original emitted proposal ip/x/N. The old heads factory's sufficient
cutoff at s-1 is removed; it cannot prove a join at the prior label s-1.
The requested H1 prior record must use the actual earlier emitted voters and
handle the genesis/empty-cohort case separately. That obligation remains OPEN.

The H2 projections use requested indexed H1 APIs, not the old global factories.
Exact complete types, source sites and owners are in
claude-files/sleep-ph2d/H1-narrow-requests.md. SupportPermanenceScope,
healing_tPerm_at, repair_lease_cover_one_at/two_at, and
healing_rise_one_advance_at are requests, not declarations on this base.
Affected modules are EXPECTED-FAIL. No compilation or producer closure is claimed
for this handoff. FrontierServiceCover/Support still need the lower H1 shapes.

The repair head factory now requires GST ≤ slotStart(s-2), at the earlier label.
Repair thresholds and the qualified frontier seed supply this bound. The saved
Δ=1, GST=4, s=2 review run does not meet the guard. frontier_seed_prior_cut proves
the seed bound by grid arithmetic. Per-reader joined guards stay in the lower API.
This corrects the earlier handoff note: the later cutoff is not merely removed;
it is replaced by the exact earlier cutoff, proved at the actual callers.

### P-H2 Round 4 — reset clock and durable ports (2026-10-10)

The internal reset/search cut, deadline and budget use recoveryStart. This matches
the approved ResetArrivalConcl; no public Claims/Statements file changes.
Reset rowCap/mu and fields use durable membership. The two base.noRestart reset
projections are gone. Reset compiles with --wfail and its ten strict audits pass.
FrontierSeedDefs holds the unchanged seed predicate independently of service APIs.
FrontierSearchStop now imports its phase proof helpers explicitly.

RiseOne uses RMonoAll for stopped-frontier/phase facts. RiseOneAccept uses the
original emitted proposal, its compatibility premise and ReceiverService.
The independently compiled Reset/RiseOne slice has 24 strict audit commands,
with only propext, Classical.choice and Quot.sound. The source-dependent
RiseOneRepair/RiseOneRise ports remain OPEN on the indexed H1 requests.

Durable post-reset membership ports also remove stale NoRestart arguments.
The assigned projection census is now 30, down from 52. The remaining 30 are
OPEN H2 repairs, not hidden prerequisites or transferred ownership. Exact sites:
claude-files/sleep-ph2d/noRestart-remaining.tsv. No global NoRestart premise is added.
The Assembly legacy ResetArrivalStatement adapter still has its old GST boundary;
P-As must use the approved shifted conclusion. The exact internal request is in
claude-files/sleep-ph2c/P-As-requests.md, Round 4 appendix.

### P-H2 Round 4 — final witness selection (2026-10-10)

The final callbacks select existential witnesses. A height or ancestry filter
alone would still request receipt for more blocks than the consumer selects.
PhaseWitnessReceiptScope selects the frontier/top/contest witnesses together
with their scoped services. HeadWitnessReceiptScope selects one K/W pair with
its full-tree, HEAD, ancestry and floor facts. Source HEAD factories also require
the actual joined source tick. Receiver service requires the actual joined read
and its strict-deadline floor. No all-cache receipt obligation remains in H2's
heldServices or opening carrier factory.

WitnessHeldScope is the guarded ancestor receipt result of a consumer. It is not
an object-service producer. FrontierServiceGate retains Kfg's source membership
and height, proves its receiver floor before receipt, and applies the scope only
at the actual joined gate. The exact H1 handoff has these final types.

### P-H2 Round 4 — final validation and open inventory (2026-10-10)

Status is PARTIAL / OPEN. The compiled reset/recovery/independent RiseOne slice
is PREPARED. The complete H2 critical path and all service producers are not closed.
The map has 93 assigned targets: 22 GREEN and 71 EXPECTED-FAIL, all with owner P-H2.
There are 492 GREEN roots. The 30 remaining NoRestart projections are open H2 work.
The local report has every open target and exact H1/P-As requested telescope.

DCK P-H2 passes: 42 strict sources, 3,429 permitted results, 24 controls.
All GREEN roots plus the three e9536241 H1 suppliers have 335 proof modules,
253 exports and zero unaccepted. The suppliers compile without source edits.
Layers have 72 inherited findings and zero new. Headers still fail on the same
four Outage import-all findings as c9e71fa5; there are zero H2 header failures.
No other owner's file, checker, baseline or allowance was changed.

The final canonical fragment has 205 unique commands and 205 coverage rows.
The six HealingOpeningSupport regression audits remain separate. Production-only
imports are preserved; serial integration remains with its assigned editor.
Public claims are unchanged. No complete production closure is claimed.

### P-H2 Round 5 — synchronous service factories (2026-10-10)

Internal scope repair, SCOPE-NARROW rule 5. OpeningServiceScopes.transfers now
takes the actual phase, selected fast-written B, source label bounds, the
post-GST vote bound, and LabelSyncOn. OpeningServiceGate passes its existing
hSync and phase facts. With delta = 1, s = 2 and GST = 20, the required
20 <= voteTime(2) = 9 is false. Joinedness and enabledness cannot enter this
factory in that run. This is an arithmetic exclusion, not a checked run fixture.

FrontierServiceScopes.read now takes the seed proposal's GST bound, interval
and horizon. All four consumers pass their phase/source bounds. Opening gates
and carriers already have their actual label cuts. Repair heads require the
prior-label cutoff; repair gates require their label cutoff. Permanence requests
use a post-GST phase. heldServices uses GST <= the actual source event time.
The accepted/emitted proposal and fresh HEAD service helpers keep their anchor
or send bound. Reset service uses H0Reset's recoveryStart qualification.
Lower H1 factories still need the exact rule-5 contracts in the Round 5 handoff;
this change does not prove those records. Public statements are unchanged.

### P-H2 Round 5 — complete H1 contract types (2026-10-10)

The healing_tPerm_at request now takes the explicit phase/body arguments and
SupportPermanenceScope after hphase, as its two opening consumers require.
Its conclusion is Transfers for that body and endpoint, not the global TPerm.
healing_rise_one_advance_at now has Fintype V. The local H1 handoff gives full
FirstTransferScope, NextTransferScope, ProposalSupportScope, FastSupportScope,
SlowSupportScope, SupportGateScope, RepairGateScope and FrontierReadScope types.
The joined-seat count and actual pool rival bounds are explicit. No undefined
“r4 shapes” remain as a type specification. The contracts are checked as
Prop-valued type declarations in .lake/sleep-ph2f/RequestContracts.lean.
This checks their telescopes; it does not prove their conclusions or producers.
The lower types and their consumers remain OPEN with the recorded owners.

### P-H2 Round 5 — committed H1 API reconciliation (2026-10-10)

The H1 interface pin is f1798112, after b1723ebf and fdf689c8. No merge or H1
source edit was made. RepairHeadServices uses the committed slot record; all
three consumers pass the actual proposal and emission to its projections.
Opening gate-cover consumers construct the committed SupportGateScope from
their real cut and GateReceiptScope. Frontier fast/slow projections now pass
the committed actual-source arguments. All affected bodies remain open until
the required lower interfaces land and their full proofs compile.

The local H1-r4-reconcile.md lists all 23 contract decisions and exact remaining
differences. H1's per-receiver selected carrier still lacks the actual joined
read and floor guards. Its permanence input is still global. Its reset and
settlement service callbacks still differ from the selected H2 contracts.
Those requests remain OPEN; none is silently declared supplied.

### P-H2 Round 5 — architecture boundary (2026-10-10)

ARCHITECTURE.md now records FrontierSeedDefs, the independent search-definition
import, the recoveryStart reset/search boundary, selected receipt records, and
the guarded opening/repair/frontier interfaces. It records 38 recovery and 24
reset/Rise audit commands. The 130-command service audit stays OPEN, as do
the lower H1 producers and mixed Assembly tests. Public statements are unchanged.

### P-H2 Round 5 — independent restart and reader ports (2026-10-10)

Internal sleep forms, no public statement change. PostResetJoint/Joint2 use
the restart-safe fProv supplier without NoRestart. The mixed frozen-membership
check uses durable storage. The RiseOne mixed check uses RMonoAll and the
existing sleep row-receipt supplier with suffixNoRestart and awake bounds.
PostResetOpening, H2Prime and LeaseMove use the wake-time event clock bound.
The frontier mixed cap check uses RMonoAll and frontier_cap_before_on.

PostResetHealed's selected high source is after the reset cut by durable height
and frontier bounds. Its positive clock after GST comes from a tick, since a
recovery restart cannot occur after GST. The cross-below and reconcile helpers
use RecoverySleep₂ and the actual confirmedReaderIdx required by H2A. Their
complete isolated bodies compile. The output induction excludes only restarts
in its healing suffix. The full H4 producer still needs the named bounded
reader supplier healing_recovery_suffix_readers, OPEN P-H2, and same-label
object services. P-As has its exact changed consumer type and three sites.

PostResetConeReceipts uses RMonoAll. Its HEAD receipt selects the source K/W
pair and proves the receiver floor before service at the actual joined read.
The two batch-seat consumers now take that exact scoped source factory and
read guard. Original object service and the remaining fresh/stamp ports stay
OPEN. The assigned NoRestart census is 18, down from 30; all are in open targets.

Isolated evidence: eight independent checks, six complete helper-body audits,
and one selected receipt audit. All 15 results use only propext, Classical.choice
and Quot.sound. These checks do not compile the containing open modules.

### P-H2 Round 5 — final validation (2026-10-10)

Proof source: 7a5632d3. DCK P-H2 PASS: 3,696 jobs, 42 strict sources,
3,429 permitted results, all 24 controls. Layers: 72 inherited, zero new.
Headers: zero H2 failures; the four inherited Outage failures remain.
All GREEN exports: 320 proof modules, 253 exports, zero unaccepted, Gen zero.
The 15 isolated proof results pass the strict DCK parser. Complete helper
bodies and selected receipt compile in isolation; containing modules stay OPEN.
The map retains 93 assigned targets, 22 GREEN and 71 open, all owned by P-H2.
The remaining NoRestart census is 18. Canonical coverage remains 205 commands
plus the six separate opening regression audits. Public statements are unchanged.
No H1 merge or source edit was made. The compiled slice remains PREPARED;
full critical-path, bounded reader and object-service producers remain OPEN.

### Lead note after the P-H2 round 5 review (2026-10-10 15:06)

rev-ph2f-astra: MERGE-AS-PREPARED for P-H2 rounds 3-5 (22 GREEN, 71 open).
This merge also brings P-H1 round 3 (e9536241) through the P-H2 base. Its
scope records are KNOWN FALSE in valid sleep runs (rev-ph1d, rev-ph1e): they
are explicit hypotheses of conditional theorems, not claims, and they are
superseded by the healing record contract (design job healing-contract-astra)
that the next P-H1 writer implements. No public statement depends on them.
Neither P-H1 nor P-H2 is CLOSED.

### P-Ou Round 8 — continuation-prefix consumption

RestoredBatch:388, outage_continuation_receipt, composes the actual P-Ar
arming_continuation_prefix_receipt with outage_continuation_receipt_of_prefix.
Tests/OutageServices consumes this regime-only producer. The P-Ar prefix
request is discharged. Its earlyTime q <= b₀ guard is kept by the producer.
Public claims and protocol declarations are unchanged. No new receipt input.
Headers PASS with zero failures. Evidence: .lake/sleep-pou-r8/prefix-build.log.

### P-Ou Round 8 — scoped inclusion producers and restored counts

The complete InclusionReceiverInputs producer is ReceiverInputs:982/:1059.
Early service requires the vote-time GST cut, an actual early tick, and
F_receiver <= K. Retained service requires the prior-label GST cut and the
actual proposal floor. Score service is produced for every selected floor D.
ExactProposalRetained:325 separates the cone proof from proposal service;
:820 proves the receiver floor before that service is requested.

The old relay field requested global receipt service for local pool entries.
A late local receipt does not imply a cross-node Delta deadline. Run sketch:
Delta=2, r=1, GST=0; joined y receives a faulty label-1 HEAD at time 17,
just before v(2)=18. No honest node processed it earlier. A joined peer
receives it at 19. Both receipts meet the model's Delta bound from the first
honest acceptance. The local HEAD pool can contain it at 18. The old record
still requests a cross-node service before 18. The new local provenance proof
uses the actual joined HEAD tick and its epoch. This is an internal scope
repair under SCOPE-NARROW rules 1 and 5. No public statement changes or STOP.

RelayKernel and InclusionServices port the needed merged P-WC proof kernels
inside the Outage lane. Direct cross-family imports fail the layer check.
No Shared or P-WC source was edited and no layer exception was added.
InclusionGateService produces gate scope from the actual enabled gate and
proved target floors. InclusionGateBody:16 derives the enabled gate from
the caught-up post-tick reader. The hInputs and hScopes export callbacks
are removed. The three changed Clean exporters pass an isolated exact compile.
The complete Outage exporter remains EXPECTED-FAIL on its older closure inputs.

ReceiverInputs:837 supplies the healthy result route with the faulty set only.
:1064 produces counts beyond E from joinedPartAfter. :1078 identifies the
canonical first restored label. :1097 covers every enabled gate after r:
E's A union W count inside its window; the healthy joined count after handover.
Its scoped actual HEAD history is still an OPEN P-Ou invariant input.
This conditional theorem is not an unconditional global hResults producer.
Later good HEAD compatibility and conditional hTargets remain OPEN.

### P-Ou Round 8 — P-Cl2 growth handoff

GrowthSuppliers:15 produces the gate witness, O-GROWTH-COMPAT and
O-GROWTH-INCLUSION from the closed Clean and Foundation field interfaces.
It constructs all receiver services and gate services itself. No hInputs
or hScopes callback remains. Tests/OutageGrowthSuppliers supplies every
field from the actual P-Cl2 and P-Fd producers and compiles the exact
unfolded P20 consumer with no compatibility or inclusion assumption.
P-As must apply the checked composition in its assembly file; it was not edited.
The public CleanGrowthClaim predicate and its deadline are unchanged.
Public assembly closure is not claimed from the independent test.

Proof group: 9fdada2a. Partition: 51 targets, 511 GREEN,
seven P-Ou and two S-Ap EXPECTED-FAIL. P-Ou remains PREPARED, not CLOSED.
DCK PASS: 43 strict sources, 3,221 results, all 24 controls PASS.
Complete GREEN exports: 331 proof modules, 253 exports, zero unaccepted.
Local coverage: 257 commands; its control PASS; zero unaccepted.
Production-only serial fragment: 231 strict results.
Layers: 72 inherited findings, zero new. Headers PASS: zero failures.
Only propext, Classical.choice and Quot.sound occur in the strict audits.
Evidence: .lake/sleep-pou-r8/. Handoff: P-Ou.round8-handoff.md.
The full continuation induction, handover closure, Close and both complete
exporters remain owned work. No future invariant is declared proved.

### P-Ou Round 9 — actual later HEADs and local result adapter

Base afc304e6. Protocol and public claim declarations are unchanged.
LaterHeads supplies durable marker persistence, clocked contested HEAD compatibility,
and the protected actual target before its lease expiry. The conditional target
adapter keeps the low receiver-F branch and derives its floor by transitivity.

outage_later_marker_receipt serves one actual stored carrier at the later joined HEAD
read. Its public anchor is that slot start; GST comes from the earlier marker label.
The receiver floor is derived only in the F-below-B branch. It uses retained acceptance
origins, exact local history and epoch, and the actual tick horizon. It requests no
joined-seat count and no universal receiver join or pre-GST deadline.

ReceiverInputs.outage_continuation_result_of_head_history takes only the actual gate
label's HEAD history. The existing global adapter now calls this local theorem.
ContinuationGate.outageV_restored_gate uses that scoped interface and the regime's
E-window or post-E joined count; its old NoRestart/awake batch lane is removed.
The local gate-step proof now handles the suppressed branch with normalization.

These are internal proof ports. Consumers: ContinuationJoint and the new scoped
continuation induction. A first marker and the finite restored prefix are still
P-Ou proof work; no unconditional public continuation closure is claimed here.
LaterHeads and ContinuationGate pass exact builds with default heartbeats.
The package map, local coverage and production-only audit fragment are updated.

### P-Ou Round 9 — causal marker suffix and expiry

ScopedContinuation.outage_continuation_event_induction handles kept-stable restarts,
delivery reconciliation, enabled gates, and suppressed gates. It carries global
source names and F compatibility, with stable inclusion only at covered receivers.
Its result input is bounded by the actual event prefix.

outage_marker_continuation_induction produces the healthy suffix's HEAD and gate
compatibility, source names, G stable inclusion and all-honest F compatibility.
The inputs name one actual marker and the finite prefix after its gate, with m>=r+k.
Earlier gate results give exact conflicting-row deadlines. The post-E HEAD expires
those rows; source names give the compatible frame; the actual joined marker service
then gives that HEAD's compatibility. The current gate consumes an earlier HEAD index.
No future result/HEAD/service callback or all-honest stable seed is assumed here.

The finite prefix and first marker are still OPEN P-Ou work. The no-marker branch and
restored labels before that cut remain OPEN. ContinuationJoint, Close and both complete
exporters are not closed by this conditional suffix. Their EXPECTED-FAIL status is kept.

Tests/OutageLaterHeads checks wake=9, GST=20 and the E-window boundary at delta=1,
r=2, k=2. The gate at 18 can be joined while the HEAD at 13 is suppressed. The marker
anchor 12 is pre-GST; anchor 24 is post-GST. The actual Foundation RMonoAll composition
also compiles. These are exact guard tests, not complete run counterexamples.

Map: 54 TARGETS, 515 GREEN, eight EXPECTED-FAIL (six P-Ou, two S-Ap).
New modules and the scoped gate port compile at default heartbeats. Headers PASS;
layers zero new; complete GREEN export check zero unaccepted. Final DCK and strict
results are in the Round 9 report. The 107-row SCOPE-NARROW table and exact finite
producer goals are in scripts/dev-pkg/P-Ou.round9-handoff.md. P-Ou remains PREPARED.

### P-Ou Round 9 — final validation

DCK P-Ou PASS: 44 strict sources, 3,245 axiom results, all 24 default controls PASS.
Map: 54 TARGETS, 515 GREEN, eight EXPECTED-FAIL (six P-Ou, two S-Ap).
Complete GREEN exports: 334 proof modules, 253 exports, zero unaccepted, zero Gen exports.
Complete local coverage: 281 commands; home-equation control PASS; zero unaccepted.
The serial production-only fragment has 250 strict results and imports no test module.
Only propext, Classical.choice and Quot.sound occur in the strict audits.
Headers PASS with zero failures. Layers: 72 inherited findings, zero new.
Whitespace, new Lean line lengths, placeholder scan and ownership checks pass.
Public claim/protocol declarations and all checker/baseline/allowance files are unchanged.
No heartbeat increase, throttle override, toolchain update, agent, review job, push,
rebase, merge or ssh was used. Only my sandbox-blocked build processes were stopped.

The entire requested Round 9 closure remains incomplete. P-Ou is PREPARED, not CLOSED.
Exact remaining finite prefix and first-marker goals are in P-Ou.round9-handoff.md.
Evidence: .lake/sleep-pou-r9/dck.log, exports.log, coverage.log, serial-strict.log,
first-group.log, later-tests.log, headers-final.log and layers-final.log.
- Lead 2026-10-10 15:22: merged sleep-pas5 cc0ccf1d (P-As r5) as PREPARED, 44/66 GREEN; review rev-pas5-astra MERGE-AS-PREPARED. OutageContinuationInhabit stays OPEN (fixture not sleep-valid; r6 replaces it). FAST port in r6.

### P-Ou Round 10 — restored seed and actual first-regression prefix

ScopedInduction:28/:102 adds the bounded vote-cut forms. The previous APIs are
wrappers, with their statements unchanged. ScopedPrefix:93 derives the auxiliary
arming regime by W-set inclusion. :151 constructs the initial seed at earlyTime r
from the actual arming certificate. :235 proves the no-regression continuation
without source, stable, result or service seeds. :55/:298 selects the first actual
regression event and produces its causal prefix, including same-label event order.
Global source and F facts stay global. Stable coverage stays G-only.

ScopedPrefix:338 replaces the frozen-path helper's global NoRestart premise with
an actual joined read and its exact receipt/freeze window. P-Fd durable TF and
RStoreEpoch preserve the selected body and stamp. :394 produces a durable marker
from an actual contested named frame. :415 consumes local retained scores and
uncontested filtered-path witnesses to prove contest. Their regime producers
remain P-Ou O10-2. No service is requested at an arbitrary sleeper or before GST.

ScopedContinuation:157 is the actual later HEAD producer. :194 permits early
markers by placing its finite start after gate max(m,r+k); it uses :157 directly.
The prefix after the first regression through that cut remains P-Ou O10-3.
No future HEAD, result or service callback is introduced.

ScopedCatchUp:16 produces the public W reader's actual post-End gate, batch at
its early cut, awake suffix and receipt epoch. The boundary gate can still use
an E-window HEAD; its time is not a healthy-count proof. :54 closes the finalized
output branch. The other actual W output seed is P-Ou O10-4.

Global hHeads, the early bridge and public consumer ports remain OPEN. The six
P-Ou and two S-Ap EXPECTED-FAIL entries remain. P-Ou is PREPARED, not CLOSED.
The complete Round 10 task is incomplete. Public claims and protocol declarations
are unchanged. No new cross-package supplier request or public STOP is claimed.
Exact goals and the 124-row scope table: scripts/dev-pkg/P-Ou.round10-handoff.md.

### P-Ou Round 10 — final validation

Proof group: dada200f, base aef1dd45, branch sleep-pou10.
DCK P-Ou PASS: 44 strict sources, 3,265 results, all 24 default controls PASS.
Map: 56 TARGETS, 517 GREEN, eight EXPECTED-FAIL (six P-Ou, two S-Ap).
Headers PASS, zero failures. Layers: 72 inherited findings, zero new.
Complete GREEN exports: 336 proof modules, 253 exports, zero unaccepted, zero Gen exports.
Local coverage: 301 commands, home-equation control PASS, zero unaccepted.
Serial production-only audit: 267 strict results, standard axioms only.
The public consumers were attempted; Close and ContinuationInduction still fail
at removed NoRestart projections and old all-honest induction calls.
No complete exporter or public claim is marked closed. P-Ou remains PREPARED.
Evidence: .lake/sleep-pou-r10/. Exact remaining goals: P-Ou.round10-handoff.md.
- Lead 2026-10-10 15:51: merged sleep-pas6 18d690c2 (P-As r6) as PREPARED, 45/66 GREEN; FAST CLOSED; outage fixture sleep-valid; review rev-pas6-astra MERGE-AS-PREPARED. Open: P-Ou closure/export (incl. Outage/Export → GrowthSuppliers), HTimeClaim (healing).

## P-H1 Round 7 — JOINED-START statements (2026-10-10)

Approval: RULING JOINED-START, lead 2026-10-10 16:45; Appendix 1 of
joined-start-plan.md. Delivery, phase services, proposal gap, attempts,
phase settlement, row permission and renewed promotion start at recoveryStart.
ResetArrival and its full companion use that origin with the existing budgets.
Saved-window GST bounds, structural reads, witness fields and top-level
healing deadlines and constants keep their text.

The changed shallow entries are pinned in docs/api/fgsa-joined-start-pins.json.
Each reason is "JOINED-START (lead ruling 2026-10-10)". Current snapshots
replace the old freeze gate on this base (4f134e83); no frozen baseline or
checker allowance is changed. The shallow manifest uses the required
V2Manifest --scope fgsa --write command. The current deep product is
regenerated. The auxiliary write is blocked by missing compiled roots from
the full proof/Inhabit scope; no auxiliary allowance is introduced.

Claims builds with its tests. Three inherited test adapters required the
existing RecoverySleep₂ and recoveryStart forms; HealingW now consumes
the corrected reset interfaces directly. Proof-family callers stay with
P-H1/P-H2/P-As according to the package map and the Round 7 handoff.

## P-H2 Round 6 — joined-start consumers (2026-10-10)

Status: PREPARED / OPEN. Independent proofs: 12aa13e0 and c5bb6663.
The promotion, selected-witness settlement, joined-gap and selected parent-floor
proofs compile. The phase and event starts use recoveryStart. Saved-window
transport uses GST. Claims, Statements and numeric constants were not edited.

P-H1 r7 merge is pending. The arithmetic producer consumed as readyCut by
healing_settle_start_on has the exact type:

```lean
∀ t, recoveryStart p E ≤ t →
  E.t_GST ≤ slotStartZ p (((slotAt p t : Slot) : Int) - 1)
```

Named producer: healing_ready_read_cutoff, ResetScope:68 at 4e506874, P-H1.
The actual reader tick and horizon are proved in the consumer.

P-H1's remaining local lease-cover obligations, consumed as explicit qualified
callbacks by tfSeed_qSucc_lease_cover, are exactly:

```lean
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

theorem repair_lease_cover_two_at [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
          p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    (hServices : SupportPermanenceServices E rho u v m J contested)
    {β : Slot} (hβ : u < SA.proposalTime p.toParams β) {s : Slot}
    (hls : SA.proposalTime p.toParams (β + 2 * p.k - 1) < SA.proposalTime p.toParams s)
    (hvs : SA.voteTime p.toParams s ≤ v) : RepairLeaseCover E rho s

theorem repair_lease_cover_one_at [Fintype V] (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) {G ΔF : Time}
    (hrec : RecoverySleep₂ p c E rho G ΔF)
    (mono : RMonoAll p c E rho) (crossing : RXing p c E rho)
    (writes : ∀ i x (row : Block × Nat × Time),
      row ∈ (storeAt p c E rho i x).base.obligations →
      ∃ j < i, ∃ s B, IsGateTick p c rho j x s ∧ gatePassedAt p c E rho j ∧
        gateResultAt p c E rho j = some (some B) ∧ Block.Preceq row.1 B ∧
        (row.1, row.2.1) ∈ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
          p.toParams.engine p.n
          (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s B ∧
        row.2.2 = SA.gateTime p.toParams s + SA.lifetime p.toParams ∧
        row.2.2 = SA.releaseTime p.toParams (s + p.k) ∧
        ∀ k w C, j < k → k < i → IsGateTick p c rho k x w →
          let pre := clockPre p (storeAt p c E rho k x) (SA.gateTime p.toParams w)
          joinedNow p pre = true →
          GridCO.savedGenuine pre.base w = none →
          SA.Root.confirmationFrom p.toParams (eraseFG pre.fg.F) (actView pre) w = some C →
          (actView pre).obligations.any (fun r => !Block.compatible r.1 C) = false →
          (row.1, row.2.1) ∉ @GridCO.gateWriteKeys GridCO.slowLeasePolicy .root
              p.toParams.engine p.n
            (actView pre) w C)
    {u v : Time} {m : Nat} {J : Option (FGBlock (Fin p.n))} {contested : Bool}
    (hready : recoveryStart p E ≤ u) (hphase : PhaseInterval p c E rho u v m J contested)
    (hServices : SupportPermanenceServices E rho u v m J contested)
    {b : Slot} (hb : u ≤ SA.voteTime p.toParams b)
    (hSync : E.t_GST ≤ SA.voteTime p.toParams (b + 1 - p.k)) {s : Slot}
    (hls : SA.proposalTime p.toParams (b + p.k) < SA.proposalTime p.toParams s)
    (hvs : SA.voteTime p.toParams s ≤ v) : RepairLeaseCover E rho s

end AvailableChain.FGSA.Run
```

The callbacks stop at the selected q+1 read and seed gate. They are not record
fields or whole-run services. The joined source domain keeps both adapters true
in finite sleep runs, including the four plan replays. No early cleanup is used.
P5 is still OPEN/P-H1; its ready phase factory is not proved by a consumer.

The later capped receiver floor, bounded frontier gate conversion, complete
RPhase producer, remaining post-reset scopes and full run fixtures are OPEN/P-H2.
See [the exact handoff](../scripts/dev-pkg/P-H2.round6-handoff.md).

P-H2 final proof update: ae971fff proves healing_capped_witness_reader_floor from
RXing, a selected held source witness, source retention and the current receiver
cap. It permits receiver F movement. No receipt or universal carrier premise is
added. The final local audit has 14 permitted results. Forty GREEN audit sources
passed with 3,345 results before this extra result; all 24 package controls pass.
The remaining selected source/capped-target plumbing stays OPEN/P-H2.
Validation: layers zero new; headers PASS; GREEN exports zero unaccepted.
DCK is blocked by the inherited ComposeStmt line warning. Full manifest is blocked
by missing Outage.ArmingDuty. No owner source or public statement was edited.
### P-H1 Round 7 — bounded consumers and source service

The single phase-indexed permanence API derives its source Window 1 from
recoveryStart <= u <= vote(s). healing_tPerm consumes RecoverySleep₂ and the
exact ready-phase SupportPermanenceServices factory. P5 remains OPEN/P-H1.
Both last-write splits use that same TPerm. repair_lease_cover_one/two now
construct RepairLeaseCover from those splits, with no assumed hCover.
Repaired proposal reads derive Window 2 and their prior Window 1.

General reads, actual HEAD/gate guards, the CStar seat counts, selected
carrier reads, fresh reset source readiness and high-source readiness are
proved. FastSupportScope.firstReaders was already absent at this base.
No other guarded contract-B field is removed. Source delivery callbacks
now keep K <= W (or CStar <= eraseFG W) and the receiver floor at early(s).
RMonoAll pulls that floor back from the actual consumer read. No arbitrary
all-TF receiver service is requested by these callbacks.

The positive finite HealingRun proves ExecutionValid, P23-A receipt roots,
per-anchor synchrony, RecoverySleep₂ and a nonempty actual ready PhaseBody.
It does not supply the open phase-service factory. Four separate kernel
clock regressions exclude the listed old sources and check the new split
thresholds. Full adversarial ExecutionValid replays remain OPEN/P-H1 with
exact obligations in P-H1.round7-fixtures.md.

D3 handoff: P-H1.round7-handoff.md lists all H2 sites and their new premises.
Promotion, AttemptStop, PhaseSettle and PhaseBoot fail directly after the
public start change. Their 18-module closure is EXPECTED-FAIL/P-H2 in the
P-H1 map. The strict local audit covers the compiled slice. Public closure
is not inferred from that slice; P-H1 remains PREPARED.

### P-H1 Round 7 — final validation

P-H1 DCK PASS: 3,736 build jobs, 44 strict sources, 3,730 permitted results,
all 24 controls PASS. Map: 104 assigned, 556 GREEN, 18 EXPECTED-FAIL/P-H2.
All GREEN exports: 345 proof modules, 253 exports, zero unaccepted, Gen zero.
Local complete coverage: 376 commands, control PASS, zero unaccepted.
Layers: 72 inherited findings, zero new. Module headers PASS.
Changed Lean source has no proof placeholder, project axiom, native_decide,
import all, new heartbeat option or new line above 100 columns.

check-fgsa-manifest.sh: shallow/deep FG-SA and legacy/V2/GEN/Compose products
PASS. The full checker exits 1 at the missing Outage/ArmingDuty.olean in the
auxiliary Claims/proof scope. No partial auxiliary snapshot was written.
Separate deep controls: all 55 PASS. API snapshot controls pass 11 cases,
then stop at the same missing Outage root. The remaining auxiliary write and
full control are exact P-As integration obligations after P-Ou/P-H2 builds.
The P-H1 package result is not a full manifest or healing closure result.
Evidence: /private/tmp/ph1h-dck-final.log, ph1h-manifest-final.log,
ph1h-coverage-final.log, ph1h-snapshot-controls.log and ph1h-deep-controls.log.
### P-Ou Round 11 — first actual regression marker

ScopedScores supplies the A union W bound for carried pools with actual stored
provenance. Selected prior good HEADs are received at the early tick, with their
votes and stamps retained through the current joined read. ScopedPrefix produces
those scores and an actual held covering source at the first regression. It uses
E in its fixed window and the healthy joined count after that window.

ScopedRoots supplies pending results from the general arming gate certificate.
The live root is compatible at G, outside-W, and post-End actual scoped readers.
Outside-W readers cannot have an enabled outage write after the pending label:
that write would put them in W. The pending result and old Clean maximum supply
the remaining row branches. No all-honest stable invariant is requested.

ScopedPaths serves each selected ancestor above the current receiver F before
freeze, using the actual joined reader, post-GST prior label and exact epoch.
An honest crossing source supplies any higher uncontested height witness.
outage_first_regression_marker produces the stored marker, B <= J(P), and
nonzero h_j(P). Scores, root and path are outputs. RQCOrigin is the named P-Fd
sourceDiscipline_qcOrigin supplier; its caller uses the existing FaultQ input.

O10-2 is proved. The post-marker finite bridge and public ports remain open.
Public claims and protocol declarations are unchanged. New scope checks include
restart-at-GST=20 and restart-at-9 with GST=20; these are guard checks, not full
ExecutionValid counterexample fixtures. P-Ou remains PREPARED.

### P-Ou Round 11 — finite bridge and global restored HEADs

ScopedPrefix.outage_continuation_of_results produces source and G stable seeds
from the arming certificate. Its only invariant input is the exact bounded result
history. The original no-regression API remains a wrapper with the same type.
The new no-lower-label forms handle all readers at the first regressed label.
Event-first selection proves this absence guard without assuming a marker in all runs.

ScopedRoots.outage_scoped_head_rows produces compatible live rows before or after
handover. ScopedPaths.outage_regression_marker_no_lower also proves compatibility
at the regressed reader itself. ScopedBridge.outage_regression_continuation uses
these local reads at the first label and exact marker receipt at subsequent labels.
Its event induction supplies the complete finite bridge with no future callbacks.
outage_first_marker_finite_prefix returns the exact seed after gate max(m,r+k).
O10-3 is proved, including early markers and same-label read order.

outage_continuation_scoped_heads joins the no-marker branch, first-label reads and
causal continuation. It produces global hHeads for actual emitted scoped joined
readers after r. O10-5's hHeads producer is proved; its legacy consumer ports remain open.
outage_continuation_event_state joins both first-event branches. The inclusive
public-read adapter proves G inclusion after the early-r seed. Public read assembly
before that seed remains open. ScopedCatchUp produces raw result compatibility at
the actual W gate, with its batch, awake suffix and receipt epoch. Post-gate W stable
compatibility remains open; raw result compatibility is not that stable seed.

The six P-Ou EXPECTED-FAIL consumers and two S-Ap entries remain. P-Ou is PREPARED.
Public claims, protocol declarations and healing files are unchanged.

### P-Ou Round 11 — P-As GrowthSuppliers visibility

Outage/Export now publicly imports Outage/GrowthSuppliers. Assembly/Outage keeps
its existing Outage/Export route to clean_growth_suppliers. This closes the P-As
round 6 visibility request and rev-pou10 item 2 without a new lane import or proof.
GrowthSuppliers compiles. The complete Export still waits on the P-Ou legacy ports.

### P-Ou Round 11 — exact remaining contracts and validation

P-Ou.round11-handoff.md gives the complete non-regression common context, the
regression-only selection guard, exact earlier public read/HEAD/F types, exact
W seed at j+1 and its continuation to timeIdx(t), and Close's separate OutagePrem
context. Every failed P-Ou consumer is mapped. The global hHeads and max-gate
finite prefix are proved declaration links. Later general covering-target callbacks
are removed from the active route, which uses actual target compatibility instead.
This resolves the exact-type findings in rev-pou9 and rev-pou10 item 1.

DCK PASS: 44 strict sources, 3,297 results, all 24 default controls PASS.
Map: 60 TARGETS, 521 GREEN, eight EXPECTED-FAIL. Headers PASS; layers zero new.
Complete GREEN exports: 340 proof modules, 253 exports, zero unaccepted.
Local coverage: 333 commands; serial production audit: 297 standard-axiom results.
The joinedHonest equation export was repaired by a local type conversion; no
checker, baseline or allowance changed. Public consumers were built and still
fail at legacy ports. P-Ou is PREPARED; the complete Round 11 task is incomplete.
No public claim, protocol declaration or healing file changed. No public STOP.

- Lead 2026-10-10 17:24: merged sleep-pou11 1b245e9e (P-Ou rounds 9-11) as PREPARED. Reviews rev-pou9/10/11-astra: proofs pass; rev-pou10 items 1-2 fixed. CORRECTION (rev-pou11 item 1): scripts/dev-pkg/P-Ou.round11-handoff.md:285 and the round 11 report claim every remaining contract elaborates in OpenTypes.lean; the saved log shows the O11-OUTAGE check FAILED (missing Claims imports; unknown FCompatBefore, LeaseOrFFrom). The six continuation goal types did elaborate. P-Ou r12 corrects the handoff.
### P-Ou Round 12 — finite early cuts and scoped outage protection

Base 1b245e9e; branch sleep-pou12. Proof commits: 88a2634c, 696b63f6,
a0d5801e and 41483e69. P-Ou remains PREPARED; the complete task is incomplete.

ScopedEarly proves O11-EARLY-READ/HEAD/F/DUTY at current finite cuts, including
runs whose restored seed lies after the horizon. Its early read takes the actual
CleanHist and enabled gate-output facts produced by P-Cl1. ScopedClose proves
O11-OUTAGE's protected-B result under OutagePrem, with no continuation premise.
It also produces joined duty provenance, the actual protected FG lift and a
certificate when G is empty. These inputs retain sleep and actual read scopes.

ScopedCatchUp proves O11-W-READ from S at j+1 through the inclusive timeIdx(t).
Its complete HEAD/F consumers use the early proofs and ScopedBridge's global
scoped HEAD/state producers. Its complete read consumer takes exactly the open
O11-W-SEED goal. Raw result compatibility does not supply that stable seed.
No new all-honest stable, NoRestart, pre-GST service or prior-label join input is added.

O11-W-SEED and complete public assembly remain P-Ou. The six P-Ou modules remain
EXPECTED-FAIL. Both complete exporters were built and fail at legacy ports in
Close and ContinuationInduction. The handoff states O12-PUBLIC-CONT and
O12-PUBLIC-OUTAGE with their exact unchanged types and caller contexts.
GrowthSuppliers remains visible through Outage/Export for P-As.

DCK PASS: 44 strict sources, 3,313 results, all 24 controls PASS.
Map: 62 targets, 523 GREEN, eight EXPECTED-FAIL (six P-Ou, two S-Ap).
Headers PASS; layers zero new. Exports: 342 proof modules, 253 exports, zero
unaccepted. Local coverage: 349 commands, zero unaccepted. Serial production
audit: 313 standard-axiom results. Exact original solved contracts are proved in
.lake/sleep-pou-r12/Contracts.lean. No protocol, public claim or Healing change.
Handoff: scripts/dev-pkg/P-Ou.round12-handoff.md, with the current scope table.
Report: claude-files/sleep-pou-report.md, Round 12. No public STOP.

- Lead 2026-10-10 17:59: merged sleep-pou12 de637290 (P-Ou r12) as PREPARED. rev-pou12-astra: proofs pass; open record items (round 13): finish the round 11 validation-record correction; architecture note for the new Scoped* modules and boundary. Open proofs: W-SEED, both public exporters.

- Lead 2026-10-10 18:09: merged P-H1 rounds 7-8 (ebbe73cc) as PREPARED: JOINED-START statements (4ad808d4, 396d90cc; RowPermission kept at GST by b021cfa3), Jst lemmas, joined-phase permanence, H6 floors, guarded assemblies, N4 release. Reviews rev-ph1h/rev-ph1i-astra: all PASS except the architecture note, added by the lead in this merge. Open: leaf factories, P5, TPerm wrapper, object services, ExecutionValid replays (P-H1 r9). Full manifest validation waits on the expected-fail Outage exporters.
### P-Ou Round 13 — actual W gate lease input

ScopedCatchUp proves outage_caught_up_gate_rows at each actual enabled gate
with s >= restoredLabel(b1) + k. Old incompatible rows expire by handover;
later enabled results come from the scoped event producer. No future cut,
all-honest join or pre-GST service is required. OutageWSeed records the exact
unchanged O11-W-SEED goal. This goal is still OPEN, P-Ou; the row proof does
not prove stable compatibility at j+1. Build evidence: .lake/sleep-pou-r13/w-rows-tests.log.

### P-Ou Round 13 — public Outage on the scoped interface

ScopedArming selects fast, slow and empty-G certificates. Close uses its own
OutagePrem and the proved protected result. Outage.Export returns the unchanged
OutageCompatAt and P1 types. Its named Clean input record has an actual producer
in Assembly/OutagePublicInputs; outage_public_suppliers proves OutageCompatClaim
without a new claim premise. Clean.Export exposes two existing producer modules.
No noRestart or duties_and_outputs call remains in Close or the public exporters.
Producer evidence: .lake/sleep-pou-r13/assembly-suppliers.log. W seed remains OPEN.

### P-Ou Round 13 — scoped continuation exporter and consumer ports

ScopedJoint selects arming for each actual initial read and joins the produced
public read, HEAD and F consumers. OutageContinuation.Export has the unchanged
OutageContinuationClaim result and the exact OPEN O11-W-SEED input. It is GREEN
and conditional. This is not public continuation closure.
The six P-Ou failed consumer entries are GREEN. ContinuationJoint, Induction
and Receipt route to the scoped producers. Retired all-honest helpers had no
current production caller. Their original sources are retained at de637290
and in .lake/sleep-pou-r13/legacy/. Current typed audits check the scoped types.
P-As still must update its three Assembly/Outage callers and the Root seed call.
Public claims, protocol and Healing files are unchanged. The package is PREPARED.

### P-Ou Round 13 — validation and remaining producer

Proof groups: d65236ae and b35a3548. DCK P-Ou PASS: 48 strict sources,
3,401 results; all 24 default controls PASS. Map: 69 targets, 536 GREEN,
two S-Ap EXPECTED-FAIL entries. Headers PASS: 1,744 library files.
Layers: 72 inherited findings, zero new. Complete GREEN exports: 375 proof
modules, 253 exports, zero unaccepted. Local coverage: 367 rows, zero unaccepted.
Production-only serial audit: 329 results; standard axioms only.
All cited evidence is saved in .lake/sleep-pou-r13/.
The OpenTypes claim from Round 11 is corrected. The exact Contracts rerun passes
with Claims imports; it checks the unproved W seed only as a Prop.
Handoff: scripts/dev-pkg/P-Ou.round13-handoff.md. Report: Round 13.
Both exporters are GREEN. O11-W-SEED remains OPEN, P-Ou; the continuation exporter
is conditional. P-As has three Outage caller repairs and the Root seed port.
The full Round 13 task is incomplete. P-Ou is PREPARED; no public STOP is asserted.

- Lead 2026-10-10 18:40: merged sleep-pou13 8bd2d9d7 (P-Ou r13) as PREPARED: outage supplier proved, both public exporters GREEN, continuation exporter conditional only on OutageWSeed. rev-pou13-astra: all pass except the architecture record (added by the lead in this merge). OutageWSeed truth check: wseed-derisk-astra.

## P-H2 Round 7 — selected receipts and bounded core ports

PhaseService proves selected retained receipt service at a recovery anchor, including
a non-public anchor. It keeps the original honest acceptance, public admission tick,
finite deadline, receiver floor, durable history and local receiver epoch. Its phase
witness producer selects the frontier/top/contest objects. Its strict spread and
frozen HEAD proof permit restarts. healing_rPhase_recovery produces all five clauses
from RecoverySleep₂, RMonoAll and RXing, with no service callback or NoRestart.

RepairCover closes the local one/two cover requests of Round 6 using the selected
phase's permanence services. FrontierGateScope bounds carriers by v. The later
frontier selects its source parent and proves the current receiver floor under the
cap before indexed .target/.scopes calls. The opening body consumes ReceiptProducers
for its selected HEAD carrier. No read factory is extended beyond v.

Core validation: .lake/sleep-ph2h/rphase-final.log and core-audit-build.log. The new
strict audit has 15 results, all with only propext, Classical.choice and Quot.sound.
Layers: 72 inherited, zero new (layers-core.log). Headers PASS (headers-core.log).
The aggregate H1 RecoveryProducers fails at 528/531 on this base; indexed heads and
phase/relay factories remain explicit named obligations. The package is PREPARED,
not CLOSED. Search and post-reset validation continues in the following group.
Public statements, attempt sums and GST saved-window bounds are unchanged.

P-H2 Round 7 search/attempt ports: the named selected phase receipt producer replaces
the heldServices callback throughout the search and four attempt rows. The named
self-proposal service replaces the search promotion callback. Attempt's outer
assembler now passes the exact opening/repair scopes and the enabled last-write
guard. The three required signature adapters compile. Evidence: core-audit-build.log,
gate-search-probe7.log. The new audit gains two consumer commands. Post-reset work
continues as a separate group; no new producer is claimed for all-cut induction.

P-H2 Round 7 post-reset leaf ports: ordinary/reset delivery uses the named recovery
adapters. The R-contract uses healing_rPhase_recovery and the durable provenance
producer. H6 asks for the actual post-GST enabled gate receipt under its selected
geometry. H2-prime uses the original accepted proposal at the early anchor, a
freeze-to-read epoch, and the actual joined next reader. Equal-label high-source
compatibility uses fgsa_sameLabel_serviceScope. Loss and next-transfer scopes stay
explicit H1 primitive obligations. The selected HEAD receipt producer closes the
standalone HeadWitnessReceiptScope request; the unused opening carrier field is removed.

Validation: ports-final-build.log and receipt-final-probe.log pass with --wfail.
The first DCK pass has 43 strict sources, 3,394 results, and all 24 controls. A final
DCK follows the last audit/map update. No all-cut producer is claimed closed.
Remaining all-cut opening/cone/raw/lease adapters stay OPEN/P-H2. In particular,
PostResetOpening still calls legacy global-epoch geometry; it requires a separate
port to selected retained services. No H1 module, public claim, constant, checker
allowance or baseline was changed.

Final P-H2 Round 7 checks: DCK PASS, 531 GREEN roots, 43 strict sources / 3,400
results, all 24 default controls. Complete GREEN exports: 398 proof modules,
253 accepted exports, zero unaccepted and zero Gen exports. Layers: 72 inherited,
zero new. Headers PASS. Evidence: .lake/sleep-ph2h/dck-final.log, exports-final.log,
layers-final.log, headers-final.log. The map has 114 assigned / 61 GREEN / 53 OPEN.
The required three repair/frontier signature adapters pass with --wfail.

The full manifest does not pass: its Claims API import stops at missing
Healing.PostResetOpening.olean. That H2 source remains unported at its legacy
global-epoch geometry. FG-SA shallow/deep, legacy, V2, generic and compose snapshots
pass. Separate P-Ou proof and legacy test probes pass on this base; no expected
P-Ou legacy failure was reproduced. See manifest-final.log, service-probe.log,
pou-legacy-all.log and pou-legacy-tests.log. H1 aggregate and H2 all-cut source
closure remain open. Exact types and ownership: P-H2.round7-handoff.md.
- Lead 2026-10-10 18:51: merged sleep-ph1j 9bc92b14 (P-H1 r9) as PREPARED; rev-ph1j-astra MERGE-AS-PREPARED. Open: P1/P2 HEAD relay (relay-derisk-sol checks the refused-after-equivocation case), P5, universal TPerm, four replays (P-H1 r10).

- Lead 2026-10-10 19:45: merged sleep-ph1k af55329c — P-H1 production CLOSED (rev-ph1k-astra MERGE-AS-CLOSED: P1-P10, RELAY-LOCAL incl. runs A/B, universal healing_tPerm_recovery from RecoverySleep₂; no false field). Remaining P-H1 item: four full ExecutionValid replays (fixture obligations, not producers).
## P-Ou Round 15 — OUTAGE-CONT-REPAIRED statement (2026-10-10)

Lead ruling: the old continuation output guarantee and O11-W-SEED are false.
The source certificate is codex/jobs/wseed-run/run.md; wseed-verify.md confirms it.
Node 7 retains conflicting S=A at 106 after a genuine genesis result.

The public companion now uses the exact recommended OutageRepairReady and
OutageContinuationConcl. Only continuation output reads require repair readiness.
HEAD and F clauses, Statements/Join.lean and FGSAClaims fields are unchanged.
This is an INTENTIONAL FG-SA sleep adaptation: conditional safety after a
repairing gate, not SAME as DC stableAsynchronyResilient. No repair deadline is claimed.

Current shallow and deep manifests are regenerated under DECISION P23-A's policy.
The two changed shallow entries are pinned in
docs/api/fgsa-outage-cont-repaired-pins.json with reason
OUTAGE-CONT-REPAIRED (lead ruling 2026-10-10). Frozen baselines are unchanged.
Statements compile: .lake/sleep-pou-r15/statements-build.log and claims-build.log.
Writer evidence: .lake/sleep-pou-r15/manifest-write.log.

## P-Ou Round 15 — qualified proof and integration limit (2026-10-10)

Proof commit dc6ce63b removes OutageWSeed. The used Round 14 no-veto and exact
repair iff lemmas compile; unused helper branches are dropped. outage_repair_gate_seed
uses the actual witness from OutageRepairReady. It derives result/F/live-row
compatibility and carries the seed through outage_stable_compatible_suffix.
ScopedJoint, the continuation exporter and Shared/Claims use the amended conclusion.
The complete outage_continuation_public_suppliers theorem has no added assumptions.
Both lane exporters are unconditional on their public conclusions and GREEN.

The negative-run source replay passes. The amended qualification excludes node 7
at 106 and includes it after the genuine Y repair at 110. It checks 668 qualified
node/time outputs through 106. This is source regression evidence, not a Lean
execution certificate. General qualified safety is kernel checked.

Final DCK P-Ou PASS: 48 strict sources, 3,406 permitted axiom results, all controls.
Map: 69 targets, 536 GREEN, two inherited S-Ap EXPECTED-FAIL entries.
Exports/complete local coverage: 375 proof modules, 253 exports, zero unaccepted;
372 coverage rows. Serial production audit: 335 results, standard axioms only.
Layers: 72 inherited findings, zero new. Headers PASS: 1,747 files.
Current shallow and deep public manifests PASS. Frozen baselines are unchanged.

Status PREPARED: full manifest validation remains blocked by inherited Assembly
and Healing build failures. The auxiliary Claims snapshot cannot be regenerated.
Assembly/Outage has three obsolete caller telescopes (P-As). Healing failures
include PhaseBoot, Promotion, PhaseSettle, FrontierSeed and four service modules
(P-H1/P-H2 integration); no Healing source was edited. These are validation blockers,
not additional proof premises. Do not report full closure until the full check passes.
P-As has a compiled exact Root replacement with named foundation and finite Clean
producers; no W-seed input. Handoff: scripts/dev-pkg/P-Ou.round15-handoff.md.
Evidence: .lake/sleep-pou-r15/dck-final.log, exports-final.log, coverage-final.log,
serial-final.log, serial-strict-final.log, root-request-final.log,
root-request-strict.log, layers-final.log, headers-final.log, scope-check.log,
repair-regression.log, manifest-check.log, claims-snapshot-blocked.log and
snapshot-all-deps-build.log. Every cited log is saved.

Full manifest result: shallow/deep, legacy, V2, Gen and Compose PASS. The script
FAILS at the auxiliary Claims snapshot on missing Healing/Promotion.olean.
Snapshot controls are not reached. Promotion:194 needs recoveryStart <= u but
passes only GST <= u; this inherited Healing caller must be repaired by its owner.
The saved writer and source-build failures are the validation limit for Round 15.

- Lead 2026-10-10 20:02: merged P-Ou 2d1ba450 — P-Ou CLOSED (rev-pou15-astra MERGE-AS-CLOSED) on RULING OUTAGE-CONT-REPAIRED: the public companion OutageContinuationConcl qualifies continuation output reads by OutageRepairReady (INTENTIONAL FG-SA sleep adaptation; old W seed refuted by codex/jobs/wseed-run). Both exporters unconditional. Open: P-As Root wiring (request in the P-Ou round 15 handoff).

- Lead 2026-10-10 20:26: merged P-H1 r11 82ad01bb (P-H2 phase-local lease-cover adapters repair_lease_cover_two_at/_one_at; local regression replays; full ExecutionValid replay goals OPEN). P-H1 stays CLOSED. rev-ph1l-astra item 1 OPEN (fixture goal): the full-run goal for the k=4 run must keep all three k=4 failures (clause 1 HEAD, clause 2 proposal, clause 3 output), not one.

- Lead 2026-10-10 20:40: merged sleep-pas7 aaa4dac0 (P-As r7) as PREPARED, 51/68; rev-pas7-astra MERGE-AS-PREPARED. INTEGRATION TODO (lead/P-Da): docs/api/legacy-api.json is stale for AvailableChain.KitFG.pins (AvailableChainKitFG/Pins.lean:182-183 say "unsaved joined gate"/"joined tick" since sleep dd102b06; main 4f134e83 snapshot has the old words; mismatch came in with merge 61769868). Regenerate and review the legacy snapshot and its digest; do not undo the wording or add an allowance.

- Lead (P-Da, 2026-10-10): regenerated docs/api/legacy-api.json for AvailableChain.KitFG.pins
  ("joined" wording from dd102b06; stale snapshot came in with merge 61769868). Only the
  pins entry/node bodies and their two digests change (cc1a3d43… → 20497544…), as
  rev-pas7-astra item 4 predicted. No allowance added.

- Lead (P-H2 rounds 7-8 merge, 2026-10-10): 105/114 P-H2 targets GREEN; 9 OPEN (post-reset
  lock/raw successor chain, joint inv, Healing.Export, 4 tests), all owned by P-H2.
  Correction (rev-ph2i-astra item 1): the RecoveryProducers P8 constructor failure was a P-H2
  interface integration regression from 87270af2 (removed FrontierReadScope.readers, inserted
  `first` after `seed`), inherited by round 7. The round 7 request that P-H1 repair its own
  producer was incorrect. db0590e8 adapts the constructor body only; the closed H1 producer
  statements are unchanged. Reviews: rev-ph2h-astra FIX-FIRST (both items fixed in round 8),
  rev-ph2i-astra FIX-FIRST (report attribution only; corrected here).

- Lead (P-H2 round 9 merge, 2026-10-10): P-H2 114/114 assigned targets GREEN (115 with the
  bounded support target). Returned producers for P-As: healing_postReset_inv_recovery,
  healing_h0_extension_recovery, healing_localInput_recovery, healing_fullInput_recovery.
  H1 healing_output_moving_suffix is byte-identical; its body wraps the bounded companion
  healing_output_moving_suffix_at (the old unbounded callback is false at the run horizon).
  Correction (rev-ph2j-astra item 1): Tests/HealingPhaseSettle (:89, :139) stays P-H2-owned
  (P-H1.txt:724), not H1; P-H2 round 10 ports it with Tests/HealingFrontierRead and the four
  P-H1 hand-offs missing from P-H2.txt. Review otherwise PASS (guarded steps, pre-GST lock
  covered by release, bounded companion, input producers).

- Lead (P-H2 round 10 merge, 2026-10-10): H1 test callers HealingPhaseSettle and
  HealingFrontierRead ported; PromotionPhase, PromotionSource, HealingPhaseSettle and
  HealingSleepAxioms registered in P-H2.txt. 120/120 P-H2 GREEN; DCK P-H1 and P-H2 PASS;
  695 non-Assembly modules build. Remaining before G-S2: P-As Assembly/NonVacuity ports
  (5 test roots, full build, full manifest). Review rev-ph2k-astra MERGE-AS-PREPARED.

- Lead (P-As rounds 8-9 merge, 2026-10-10): ASSEMBLY CLOSED, 68/68 GREEN; Root, HTimeClaim and
  FGSAClaims use only named producers (rev-pas9-astra MERGE-AS-PREPARED; rev-pas8 item 1 fixed).
  All FG-SA libraries build. Known limit: PC-SA is not ported to the sleep generic interface
  (AvailableChainPCSARun/Model/Protocol.lean:449, restore now takes the wake time). A least-change
  port is impossible (two PC-SA theorems lack NoRestart; see the PC-SA blocker report). User
  2026-10-10: land the sleep migration with PC-SA unbuilt; PC-SA needs its own port later.

## sleep-pcsa-off Round 2 — snapshot STOP (2026-10-10)

- Lead ruling A permits the retired fgsa_receiptCoverage root and nine PC-SA roots.
- bp.receiptCoverage.v2 now names ReceiptCoverageSleepStatement_def in its statement
  module and fgsa_receiptCoverage_ready in ReceiptCoverageReady. The sleep producer
  and paper alignment stay OPEN. Both mapped constants pass the kernel owner check.
- Candidate extraction passes: 1,617 roots and 4,250 nodes. Comparison with the
  committed snapshot finds 17 removals, 171 additions and 1,188 changed entries.
- STOP: seven removals and the changed FG-SA entries exceed the allowed delta.
  The candidate is not installed. No committed snapshot entry is removed or changed.
  Export fixes and remaining full-tier/DCK checks are pending under this STOP.

Candidate removals allowed by ruling A (not applied):

- `AvailableChain.FGSA.Run.fgsa_receiptCoverage`.
- `AvailableChain.PCSA.Run.pcsaSafetyFinalityClaims`.
- `AvailableChain.PCSA.Run.pcsa_safety_eventPrefixAgreementClaim`.
- `AvailableChain.PCSA.Run.pcsa_safety_faultCountSlashableBoundClaim`.
- `AvailableChain.PCSA.Run.pcsa_safety_finalizedMonotoneClaim`.
- `AvailableChain.PCSA.Run.pcsa_safety_honestNeverSlashedClaim`.
- `AvailableChain.PCSA.Run.pcsa_safety_pureAccountableClaim`.
- `AvailableChain.PCSA.Run.pcsa_safety_pureAgreementClaim`.
- `AvailableChain.PCSA.Run.pcsa_safety_wholeRunAccountableClaim`.
- `AvailableChain.PCSA.Run.pcsa_safety_wholeRunAgreementClaim`.

Additional candidate removals that require a lead ruling (not applied):

- `AvailableChain.FGSA.Reachable.reset`.
- `AvailableChain.FGSA.Run.Base₂.noRestart`.
- `AvailableChain.FGSA.Run.ReceiptCoverageStatement`.
- `AvailableChain.FGSA.Run.ReceiptCoverageStatement_def`.
- `AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂.toRecovery₂`.
- `AvailableChain.FGSA.Run.formWinAt`.
- `AvailableChain.FGSA.Run.gapWin`.

Evidence: `.lake/sleep-pcsa-off/round2/claims-diff.json` records every before/after
entry. `claude-files/sleep-pcsa-off-report.md`, Round 2, lists every changed root.
The blueprint check reports 181 remaining findings outside the corrected receipt row.
Layers: 0 new. Headers and UNPORTED controls: PASS. Export: six unaccepted findings.
No full manifest, 19-package DCK, aggregate self-test or NUC gate PASS is claimed.

## P-Da Round 3 — approved Claims API migration delta (2026-10-11)

Lead rulings A and A' approve this first refresh after the sleep migration.
The candidate has 1,617 roots and 4,250 nodes. The delta has 17 removed roots,
171 added roots and 1,188 changed roots. A changed digest can include reached
definitions; it does not by itself mean that the declaration type changed.

Names below use these prefixes:
- `F` = `AvailableChain.FGSA`.
- `R` = `AvailableChain.FGSA.Run`.
- `P` = `AvailableChain.PCSA.Run`.
Module names keep their library prefix.

### Removed roots and reasons

- `F.Reachable.reset`:
  A': reset is now the prior reachable wipe; use Reachable.restart.
- `R.Base₂.noRestart`:
  A': the sleep base permits restarts at wakes.
- `R.ReceiptCoverageStatement`:
  A' / DECISION P23-A: old receipt contract retired.
- `R.ReceiptCoverageStatement_def`:
  A' / DECISION P23-A: old receipt contract equation retired.
- `R.StrongRecoverySearchPrefix₂.toRecovery₂`:
  A' / 7538ca0f: structure now extends RecoverySleep₂.
- `R.fgsa_receiptCoverage`:
  A / DECISION P23-A: old receipt producer retired.
- `R.formWinAt`:
  A': renamed formWinAtReady; ledger ready-window record.
- `R.gapWin`:
  A': renamed gapWinReady; ledger ready-window record.
- `P.pcsaSafetyFinalityClaims`:
  A: PC-SA compiled roots are UNPORTED; retained sources and snapshots.
- `P.pcsa_safety_eventPrefixAgreementClaim`:
  A: PC-SA compiled roots are UNPORTED; retained sources and snapshots.
- `P.pcsa_safety_faultCountSlashableBoundClaim`:
  A: PC-SA compiled roots are UNPORTED; retained sources and snapshots.
- `P.pcsa_safety_finalizedMonotoneClaim`:
  A: PC-SA compiled roots are UNPORTED; retained sources and snapshots.
- `P.pcsa_safety_honestNeverSlashedClaim`:
  A: PC-SA compiled roots are UNPORTED; retained sources and snapshots.
- `P.pcsa_safety_pureAccountableClaim`:
  A: PC-SA compiled roots are UNPORTED; retained sources and snapshots.
- `P.pcsa_safety_pureAgreementClaim`:
  A: PC-SA compiled roots are UNPORTED; retained sources and snapshots.
- `P.pcsa_safety_wholeRunAccountableClaim`:
  A: PC-SA compiled roots are UNPORTED; retained sources and snapshots.
- `P.pcsa_safety_wholeRunAgreementClaim`:
  A: PC-SA compiled roots are UNPORTED; retained sources and snapshots.

### Added roots, grouped by module

`AvailableChainFGSA.Statements.Invariants` (1):

- `F.Reachable.restart`.

`AvailableChainFGSAClaims.Claims.Foundations` (1):

- `R.FinalizedMonotonicityRestartClaim`.

`AvailableChainFGSAClaims.Statements.ChannelProps` (6):

- `R.RMonoAll`.
- `R.RMonoAll_def`.
- `R.RStoreDurable`.
- `R.RStoreDurable_def`.
- `R.RStoreEpoch`.
- `R.RStoreEpoch_def`.

`AvailableChainFGSAClaims.Statements.FrameNext` (2):

- `R.RFrameNextEpoch`.
- `R.RFrameNextEpoch_def`.

`AvailableChainFGSAClaims.Statements.Join` (48):

- `R.AwakeClosed`.
- `R.B_FW_sleep`.
- `R.B_HF_sleep`.
- `R.B_resetF_sleep`.
- `R.BatchReceiptAt`.
- `R.DutiesExtendScoped`.
- `R.FirstRestored`.
- `R.OutageContinuationReceipt`.
- `R.OutageE`.
- `R.OutageE1`.
- `R.OutageEnd`.
- `R.OutagePrefixReceipt`.
- `R.OutageVoteMember`.
- `R.ReceiptObjectAt`.
- `R.RestartFreeTime`.
- `R.ScopedCompat`.
- `R.ScopedMono`.
- `R.ScopedServed`.
- `R.WakesAppliedAtIdx`.
- `R.caughtUpAt`.
- `R.caughtUpAtIdx`.
- `R.confirmedReader`.
- `R.confirmedReaderAtIdx`.
- `R.confirmedReaderIdx`.
- `R.coverDeadline`.
- `R.coverLabel`.
- `R.coveredNodes`.
- `R.enabledGateAt`.
- `R.fastCoveredSchedule`.
- `R.firstUpdateLabel`.
- `R.headReader`.
- `R.joinedAt`.
- `R.joinedDuty`.
- `R.joinedHonest`.
- `R.outageConfirmedReader`.
- `R.outageH`.
- `R.outageHeadReader`.
- `R.outageW`.
- `R.prefixTime`.
- `R.recoveryDelay`.
- `R.recoveryStart`.
- `R.restoredLabel`.
- `R.sleepyBad`.
- `R.slotAt`.
- `R.slotStartZ`.
- `R.slowCoveredSchedule`.
- `R.tauC`.
- `R.voteZ`.

`AvailableChainFGSAClaims.Statements.OutageContinuation` (10):

- `R.OutageContinuationSleepPrem`.
- `R.OutageContinuationSleepPrem.joinedFastPart`.
- `R.OutageContinuationSleepPrem.joinedPartAfter`.
- `R.OutageContinuationSleepPrem.joinedSleepy`.
- `R.OutageContinuationSleepPrem.mk`.
- `R.OutageContinuationSleepPrem.protection`.
- `R.OutageContinuationSleepPrem.sleepPre`.
- `R.OutageContinuationSleepPrem.sleepyAfter`.
- `R.OutageContinuationSleepPrem.toOutageContinuationPrem`.
- `R.OutageRepairReady`.

`AvailableChainFGSAClaims.Statements.OutageSleep` (3):

- `R.OutageContinuationReceiptDerivedClaim`.
- `R.OutageE1DerivedClaim`.
- `R.OutagePrefixReceiptDerivedClaim`.

`AvailableChainFGSAClaims.Statements.Reads` (1):

- `R.diagnosticGateResult`.

`AvailableChainFGSAClaims.Statements.Regimes` (28):

- `R.Base₂.receiptIdealization`.
- `R.Base₂.restartsAtWakes`.
- `R.CleanPrefixSleep₂`.
- `R.CleanPrefixSleep₂.joinedPartAt`.
- `R.CleanPrefixSleep₂.mk`.
- `R.CleanPrefixSleep₂.sleepPre`.
- `R.CleanPrefixSleep₂.toCleanPrefix₂`.
- `R.CleanSleep₂`.
- `R.CleanSleep₂.mk`.
- `R.CleanSleep₂.sleepPre`.
- `R.CleanSleep₂.toClean₂`.
- `R.HealthyPrefixSleep₂`.
- `R.HealthyPrefixSleep₂.joinedPartBefore`.
- `R.HealthyPrefixSleep₂.mk`.
- `R.HealthyPrefixSleep₂.toHealthyPrefix₂`.
- `R.OutageSleep₂`.
- `R.OutageSleep₂.joinedFastPart`.
- `R.OutageSleep₂.joinedSleepy`.
- `R.OutageSleep₂.mk`.
- `R.OutageSleep₂.protection`.
- `R.OutageSleep₂.sleepPre`.
- `R.OutageSleep₂.toOutage₂`.
- `R.RecoveryReadinessClaim`.
- `R.RecoverySleep₂`.
- `R.RecoverySleep₂.joinedGap`.
- `R.RecoverySleep₂.mk`.
- `R.RecoverySleep₂.suffixNoRestart`.
- `R.RecoverySleep₂.toRecovery₂`.

`AvailableChainFGSAClaims.Statements.WeakContinuation` (5):

- `R.CleanContinuationSleep₂`.
- `R.CleanContinuationSleep₂.joinedParticipation`.
- `R.CleanContinuationSleep₂.mk`.
- `R.CleanContinuationSleep₂.toCleanContinuation₂`.
- `R.StrongRecoverySearchPrefix₂.toRecoverySleep₂`.

`AvailableChainFGSAClaims.Statements.WeakContinuationGrowth` (5):

- `R.CleanGrowthContinuationSleep₂`.
- `R.CleanGrowthContinuationSleep₂.joinedParticipation`.
- `R.CleanGrowthContinuationSleep₂.mk`.
- `R.CleanGrowthContinuationSleep₂.toCleanGrowthContinuation₂`.
- `R.SourcePendingReceipt`.

`AvailableChainFGSAClaims.Statements.Windows` (2):

- `R.formWinAtReady`.
- `R.gapWinReady`.

`AvailableChainFGSAProofs.Proofs.Assembly.Clean` (1):

- `R.assembly_clean_state`.

`AvailableChainFGSAProofs.Proofs.Assembly.ContinuationReplay` (2):

- `R.assembly_joinedReplay`.
- `R.assembly_tickReplay_atWake`.

`AvailableChainFGSAProofs.Proofs.Assembly.ContinuationService` (3):

- `R.assembly_wcg_dischargeL`.
- `R.wcg_service4OfSeed`.
- `R.wcg_service_outputs`.

`AvailableChainFGSAProofs.Proofs.Assembly.Foundations` (2):

- `R.assembly_rows_of_healingSet`.
- `R.assembly_sleep_channels`.

`AvailableChainFGSAProofs.Proofs.Assembly.Healing` (1):

- `R.assembly_healing_proposal_service`.

`AvailableChainFGSAProofs.Proofs.Assembly.Outage` (2):

- `R.assembly_outage_clean_cut_supplier`.
- `R.fgsa_outagePrefixReceiptClaim`.

`AvailableChainFGSAProofs.Proofs.Assembly.OutagePublicInputs` (3):

- `R.outage_clean_cut_supplier`.
- `R.outage_continuation_public_suppliers`.
- `R.outage_public_suppliers`.

`AvailableChainFGSAProofs.Proofs.Assembly.ProgressAttempt` (6):

- `R.ProgressAttemptRows`.
- `R.ProgressAttemptRows.firstRow_contest`.
- `R.ProgressAttemptRows.firstRow_other`.
- `R.ProgressAttemptRows.mk`.
- `R.ProgressAttemptRows.raise_contest`.
- `R.ProgressAttemptRows.raise_other`.

`AvailableChainFGSAProofs.Proofs.Assembly.ResetArrival` (14):

- `R.assembly_hTimeClaim_of_reset_input`.
- `R.assembly_hTimeClaim_of_statement`.
- `R.assembly_hTime_at`.
- `R.assembly_healingInputClaim_of_input`.
- `R.assembly_healingInput_at`.
- `R.assembly_healingInput_of_inv`.
- `R.assembly_healing_extension_of_set`.
- `R.assembly_healing_fullInput_of_set`.
- `R.assembly_healing_inv_of_set`.
- `R.assembly_healing_localInput_of_set`.
- `R.assembly_healing_suffix_reader`.
- `R.assembly_healing_tPerm_of_set`.
- `R.assembly_resetArrivalFull_at`.
- `R.assembly_resetArrivalFull_of_extension`.

`AvailableChainFGSAProofs.Proofs.Assembly.ResetSource` (1):

- `R.assembly_reset_emittedName`.

`AvailableChainFGSAProofs.Proofs.Assembly.Root` (2):

- `R.assembly_weakContinuationClaims`.
- `R.assembly_weakContinuationGrowth`.

`AvailableChainFGSAProofs.Proofs.Assembly.WeakContinuation` (3):

- `R.wc_heightSeed_of_finite`.
- `R.wc_sourceJoinCut`.
- `R.wc_sourceParticipation`.

`AvailableChainFGSAProofs.Proofs.Assembly.WeakContinuationGrowth` (3):

- `R.AssemblyWCGInclusion6ResultStatement`.
- `R.wcg_inclusion6_result`.
- `R.wcg_sourceParticipation`.

`AvailableChainFGSAProofs.Proofs.Assembly.WeakContinuationGrowthSeed` (4):

- `R.wcg_heightSeed_of_finite`.
- `R.wcg_retainedSeed_of_finite`.
- `R.wcg_sourceJoinCut`.
- `R.wcg_sourceWitness_joined`.

`AvailableChainFGSAProofs.Proofs.Foundations.Export` (1):

- `R.fgsa_finalizedMonotonicityRestartClaim`.

`AvailableChainFGSARun.Proofs.ReceiptCoverageReady` (1):

- `R.fgsa_receiptCoverage_ready`.

`AvailableChainFGSARun.Statements.ReceiptCoverage` (8):

- `R.ReceiptCoverageSleepPremises`.
- `R.ReceiptCoverageSleepPremises.compat`.
- `R.ReceiptCoverageSleepPremises.deadline`.
- `R.ReceiptCoverageSleepPremises.mk`.
- `R.ReceiptCoverageSleepPremises.slotWindow`.
- `R.ReceiptCoverageSleepPremises.within`.
- `R.ReceiptCoverageSleepStatement`.
- `R.ReceiptCoverageSleepStatement_def`.

`AvailableChainFGSARun.Statements.Roots` (2):

- `R.NamedProposalReceiptScope`.
- `R.NamedReceiptRootCollisionFree`.

### Changed root counts, grouped by current module

- `AvailableChainFGSA.Proofs.Head.Walk`: 1.
- `AvailableChainFGSA.Proofs.Reconcile`: 1.
- `AvailableChainFGSA.Statements.Invariants`: 32.
- `AvailableChainFGSA.Statements.Store`: 12.
- `AvailableChainFGSAClaims.Claims.Clean`: 10.
- `AvailableChainFGSAClaims.Claims.Finality`: 19.
- `AvailableChainFGSAClaims.Claims.Foundations`: 37.
- `AvailableChainFGSAClaims.Claims.FrameNext`: 2.
- `AvailableChainFGSAClaims.Claims.Healing`: 11.
- `AvailableChainFGSAClaims.Claims.Outage`: 19.
- `AvailableChainFGSAClaims.Claims.OutageContinuation`: 1.
- `AvailableChainFGSAClaims.Claims.Shared`: 8.
- `AvailableChainFGSAClaims.Claims.WeakContinuation`: 2.
- `AvailableChainFGSAClaims.Claims.WeakContinuationGrowth`: 1.
- `AvailableChainFGSAClaims.FGSAClaims`: 65.
- `AvailableChainFGSAClaims.Statements.ChannelProps`: 77.
- `AvailableChainFGSAClaims.Statements.Channels`: 48.
- `AvailableChainFGSAClaims.Statements.ComposeNext`: 9.
- `AvailableChainFGSAClaims.Statements.ComposeStmt`: 87.
- `AvailableChainFGSAClaims.Statements.Counts`: 2.
- `AvailableChainFGSAClaims.Statements.FinalityApi`: 12.
- `AvailableChainFGSAClaims.Statements.Fold`: 45.
- `AvailableChainFGSAClaims.Statements.FrameNext`: 16.
- `AvailableChainFGSAClaims.Statements.Healed`: 32.
- `AvailableChainFGSAClaims.Statements.HealedBest`: 2.
- `AvailableChainFGSAClaims.Statements.Join`: 1.
- `AvailableChainFGSAClaims.Statements.LiveDC`: 4.
- `AvailableChainFGSAClaims.Statements.OutageContinuation`: 12.
- `AvailableChainFGSAClaims.Statements.OutputReads`: 4.
- `AvailableChainFGSAClaims.Statements.Packages.Finality`: 29.
- `AvailableChainFGSAClaims.Statements.Packages.FinalityGST`: 16.
- `AvailableChainFGSAClaims.Statements.Packages.Healing`: 40.
- `AvailableChainFGSAClaims.Statements.Packages.Inclusion`: 10.
- `AvailableChainFGSAClaims.Statements.Packages.Outage`: 3.
- `AvailableChainFGSAClaims.Statements.Packages.Safety`: 28.
- `AvailableChainFGSAClaims.Statements.Phases`: 64.
- `AvailableChainFGSAClaims.Statements.Reads`: 34.
- `AvailableChainFGSAClaims.Statements.Regimes`: 47.
- `AvailableChainFGSAClaims.Statements.WeakContinuation`: 37.
- `AvailableChainFGSAClaims.Statements.WeakContinuationGrowth`: 25.
- `AvailableChainFGSAClaims.Statements.WeakContinuationLive`: 7.
- `AvailableChainFGSAClaims.Statements.Windows`: 8.
- `AvailableChainFGSAClaims.Statements.Witness`: 29.
- `AvailableChainFGSAProofs.Proofs.Assembly.Clean`: 5.
- `AvailableChainFGSAProofs.Proofs.Assembly.Finality`: 9.
- `AvailableChainFGSAProofs.Proofs.Assembly.Healing`: 2.
- `AvailableChainFGSAProofs.Proofs.Assembly.Outage`: 7.
- `AvailableChainFGSAProofs.Proofs.Assembly.ProgressAttempt`: 1.
- `AvailableChainFGSAProofs.Proofs.Assembly.ResetArrival`: 19.
- `AvailableChainFGSAProofs.Proofs.Assembly.Root`: 7.
- `AvailableChainFGSAProofs.Proofs.Assembly.WeakContinuation`: 9.
- `AvailableChainFGSAProofs.Proofs.Assembly.WeakContinuationGrowth`: 14.
- `AvailableChainFGSAProofs.Proofs.Assembly.WeakContinuationGrowthSeed`: 9.
- `AvailableChainFGSAProofs.Proofs.Clean.Action`: 1.
- `AvailableChainFGSAProofs.Proofs.Clean.Export`: 9.
- `AvailableChainFGSAProofs.Proofs.Clean.Transfer`: 1.
- `AvailableChainFGSAProofs.Proofs.Finality.CoreServices`: 1.
- `AvailableChainFGSAProofs.Proofs.Finality.Export`: 10.
- `AvailableChainFGSAProofs.Proofs.Foundations.Accountable`: 1.
- `AvailableChainFGSAProofs.Proofs.Foundations.Export`: 34.
- `AvailableChainFGSAProofs.Proofs.Foundations.FGSafetyBridge`: 5.
- `AvailableChainFGSAProofs.Proofs.Foundations.Sources`: 2.
- `AvailableChainFGSAProofs.Proofs.Healing.CommonEntryHeight`: 3.
- `AvailableChainFGSAProofs.Proofs.Healing.Descent`: 1.
- `AvailableChainFGSAProofs.Proofs.Healing.Export`: 2.
- `AvailableChainFGSAProofs.Proofs.Healing.Phase`: 1.
- `AvailableChainFGSAProofs.Proofs.Healing.PhaseOrder`: 1.
- `AvailableChainFGSAProofs.Proofs.Healing.PostResetHealed`: 1.
- `AvailableChainFGSAProofs.Proofs.Healing.PostResetJoint`: 1.
- `AvailableChainFGSAProofs.Proofs.Healing.PostResetRaw`: 2.
- `AvailableChainFGSAProofs.Proofs.Healing.PostResetService`: 1.
- `AvailableChainFGSAProofs.Proofs.Healing.Repair`: 2.
- `AvailableChainFGSAProofs.Proofs.Healing.SupportPerm`: 1.
- `AvailableChainFGSAProofs.Proofs.Outage.ExactProposalReceipts`: 1.
- `AvailableChainFGSAProofs.Proofs.Outage.Export`: 8.
- `AvailableChainFGSAProofs.Proofs.OutageContinuation.Export`: 1.
- `AvailableChainFGSAProofs.Proofs.Shared.Claims`: 11.
- `AvailableChainFGSAProofs.Proofs.Shared.Export`: 4.
- `AvailableChainFGSAProofs.Proofs.Shared.HeadGeometry`: 1.
- `AvailableChainFGSAProofs.Proofs.Shared.Release`: 1.
- `AvailableChainFGSAProofs.Proofs.Shared.ScoreRun`: 1.
- `AvailableChainFGSAProofs.Proofs.WeakContinuation.ExactProposal`: 1.
- `AvailableChainFGSAProofs.Proofs.WeakContinuation.FinalBelow`: 1.
- `AvailableChainFGSAProofs.Proofs.WeakContinuation.Frame`: 1.
- `AvailableChainFGSAProofs.Proofs.WeakContinuation.Inclusion`: 1.
- `AvailableChainFGSAProofs.Proofs.WeakContinuation.Induction`: 1.
- `AvailableChainFGSAProofs.Proofs.WeakContinuation.Live`: 1.
- `AvailableChainFGSAProofs.Proofs.WeakContinuation.Origins`: 2.
- `AvailableChainFGSAProofs.Proofs.WeakContinuation.Proposal`: 1.
- `AvailableChainFGSAProofs.Proofs.WeakContinuation.ReceiptOrigins`: 1.
- `AvailableChainFGSAProofs.Proofs.WeakContinuation.Replay`: 3.
- `AvailableChainFGSAProofs.Proofs.WeakContinuation.Safety`: 1.
- `AvailableChainFGSARun.Statements.AC`: 1.
- `AvailableChainFGSARun.Statements.Acceptance`: 3.
- `AvailableChainFGSARun.Statements.Client`: 4.
- `AvailableChainFGSARun.Statements.Emission`: 4.
- `AvailableChainFGSARun.Statements.Excludes`: 5.
- `AvailableChainFGSARun.Statements.Interface`: 3.
- `AvailableChainFGSARun.Statements.ReceiptCoverage`: 6.
- `AvailableChainFGSARun.Statements.Roots`: 7.
- `AvailableChainFGSARun.Statements.Slashing`: 2.

### Public Statements/Claims types

64 existing public roots have a different direct kernel type.
Constructors and fields are included. The source commits below are the changes
to each owning source module since snapshot commit 4f134e83. The exact before/after
types and source history are saved in Round 3 `public-type-sources.json`.
A' approves the migration delta. This list records provenance for lead review.

`AvailableChainFGSAClaims.Claims.Outage`:

- `R.LeaseOrFFrom`:
  Source commits: `e3b119dd`, `7969754d`, `57022bd2`.
- `R.OutageCompatAt`:
  Source commits: `e3b119dd`, `7969754d`, `57022bd2`.
- `R.P1Concl`:
  Source commits: `e3b119dd`, `7969754d`, `57022bd2`.

`AvailableChainFGSAClaims.FGSAClaims`:

- `R.FGSAFinalityClaims.finalizedMonotone`:
  Source commits: `7538ca0f`.
- `R.FGSAFinalityClaims.mk`:
  Source commits: `7538ca0f`.

`AvailableChainFGSAClaims.Statements.ChannelProps`:

- `R.RActive_def`:
  Source commits: `4ad808d4`, `ef361de0`.
- `R.RRec_def`:
  Source commits: `4ad808d4`, `ef361de0`.

`AvailableChainFGSAClaims.Statements.ComposeNext`:

- `R.FGFoundationNext.cumul`:
  Source commits: `7538ca0f`.
- `R.FGFoundationNext.frame`:
  Source commits: `7538ca0f`.
- `R.FGFoundationNext.mk`:
  Source commits: `7538ca0f`.
- `R.FGFoundationNext.mono`:
  Source commits: `7538ca0f`.

`AvailableChainFGSAClaims.Statements.ComposeStmt`:

- `R.FGFoundation.cumul`:
  Source commits: `396d90cc`, `4ad808d4`, `b3155000`, `7538ca0f`.
- `R.FGFoundation.frame`:
  Source commits: `396d90cc`, `4ad808d4`, `b3155000`, `7538ca0f`.
- `R.FGFoundation.mk`:
  Source commits: `396d90cc`, `4ad808d4`, `b3155000`, `7538ca0f`.
- `R.FGFoundation.mono`:
  Source commits: `396d90cc`, `4ad808d4`, `b3155000`, `7538ca0f`.
- `R.RPhase_def`:
  Source commits: `396d90cc`, `4ad808d4`, `b3155000`, `7538ca0f`.
- `R.ResetArrivalFullStatement_def`:
  Source commits: `396d90cc`, `4ad808d4`, `b3155000`, `7538ca0f`.
- `R.ResetArrivalStatement_def`:
  Source commits: `396d90cc`, `4ad808d4`, `b3155000`, `7538ca0f`.

`AvailableChainFGSAClaims.Statements.Healed`:

- `R.HTimeStatement_def`:
  Source commits: `7538ca0f`.

`AvailableChainFGSAClaims.Statements.HealedBest`:

- `R.HTimeBestConcl_def`:
  Source commits: `7538ca0f`.

`AvailableChainFGSAClaims.Statements.Join`:

- `R.gatePassedAt`:
  Source commits: `4ad808d4`, `ac7ad87f`, `ef361de0`.

`AvailableChainFGSAClaims.Statements.LiveDC`:

- `R.LiveDCConcl_W_def`:
  Source commits: `7538ca0f`.
- `R.LiveDCFromWindowsStatement_def`:
  Source commits: `7538ca0f`.

`AvailableChainFGSAClaims.Statements.OutageContinuation`:

- `R.OutageContinuationConcl`:
  Source commits: `2bf83b53`, `8695c4e2`, `7538ca0f`.

`AvailableChainFGSAClaims.Statements.OutputReads`:

- `R.JointGrowthAt_def`:
  Source commits: `7538ca0f`.
- `R.ServedFromGateAt_def`:
  Source commits: `7538ca0f`.

`AvailableChainFGSAClaims.Statements.Packages.Finality`:

- `R.FinalitySet_W.core`:
  Source commits: `7538ca0f`.
- `R.FinalitySet_W.mk`:
  Source commits: `7538ca0f`.
- `R.FinalitySet_W.recur`:
  Source commits: `7538ca0f`.
- `R.FirstFinalityPrem_W.hhor`:
  Source commits: `7538ca0f`.
- `R.FirstFinalityPrem_W.mk`:
  Source commits: `7538ca0f`.

`AvailableChainFGSAClaims.Statements.Packages.FinalityGST`:

- `R.AboveFrontierGSTPrem_W.late`:
  Source commits: `7538ca0f`.
- `R.AboveFrontierGSTPrem_W.mk`:
  Source commits: `7538ca0f`.
- `R.FinalityLivenessGSTPrem_W.late`:
  Source commits: `7538ca0f`.
- `R.FinalityLivenessGSTPrem_W.mk`:
  Source commits: `7538ca0f`.
- `R.ProposalFinalGSTPrem_W.late`:
  Source commits: `7538ca0f`.
- `R.ProposalFinalGSTPrem_W.mk`:
  Source commits: `7538ca0f`.

`AvailableChainFGSAClaims.Statements.Packages.Healing`:

- `R.HealingTimePrem.hhor`:
  Source commits: `7538ca0f`.
- `R.HealingTimePrem.mk`:
  Source commits: `7538ca0f`.
- `R.ResetArrivalFullPrem.hhor`:
  Source commits: `7538ca0f`.
- `R.ResetArrivalFullPrem.mk`:
  Source commits: `7538ca0f`.
- `R.ResetArrivalPrem.hhor`:
  Source commits: `7538ca0f`.
- `R.ResetArrivalPrem.mk`:
  Source commits: `7538ca0f`.

`AvailableChainFGSAClaims.Statements.Reads`:

- `R.gateResult_def`:
  Source commits: `ef361de0`.

`AvailableChainFGSAClaims.Statements.Regimes`:

- `R.Base₂.idealization`:
  Source commits: `04e0a138`, `ef361de0`.
- `R.Base₂.mk`:
  Source commits: `04e0a138`, `ef361de0`.

`AvailableChainFGSAClaims.Statements.WeakContinuation`:

- `R.SSafeFromCut₂.compatible`:
  Source commits: `7538ca0f`.
- `R.SSafeFromCut₂.finalBelow`:
  Source commits: `7538ca0f`.
- `R.SSafeFromCut₂.mk`:
  Source commits: `7538ca0f`.
- `R.SSafeFromCut₂.monotone`:
  Source commits: `7538ca0f`.
- `R.SSafeFromCut₂.outputs`:
  Source commits: `7538ca0f`.
- `R.SSafeFromCut₂.seed`:
  Source commits: `7538ca0f`.
- `R.StrongRecoverySearchPrefix₂.endpoint`:
  Source commits: `7538ca0f`.
- `R.StrongRecoverySearchPrefix₂.mk`:
  Source commits: `7538ca0f`.

`AvailableChainFGSAClaims.Statements.WeakContinuationGrowth`:

- `R.BoundedGrowthRecovery₂_def`:
  Source commits: `7538ca0f`.
- `R.PendingSourceDelivery₂.mk`:
  Source commits: `7538ca0f`.
- `R.PendingSourceDelivery₂.sourceBroadcast`:
  Source commits: `7538ca0f`.
- `R.PendingSourceDelivery₂.sourceRelay`:
  Source commits: `7538ca0f`.

`AvailableChainFGSAClaims.Statements.WeakContinuationLive`:

- `R.BoundedSafetyLivenessRecovery₂_def`:
  Source commits: `7538ca0f`.

`AvailableChainFGSAClaims.Statements.Witness`:

- `R.H0Reset.cut_lower`:
  Source commits: `4ad808d4`, `7538ca0f`.
- `R.H0Reset.cut_upper`:
  Source commits: `4ad808d4`, `7538ca0f`.
- `R.H0Reset.mk`:
  Source commits: `4ad808d4`, `7538ca0f`.
- `R.H0Reset.rG_after`:
  Source commits: `4ad808d4`, `7538ca0f`.
- `R.H0Reset.rG_first`:
  Source commits: `4ad808d4`, `7538ca0f`.

### UNSOURCED

None among the 64 direct public type changes. Owning-module commit sources are
listed above; lead review must confirm each semantic adaptation.

## P-Da Round 3 — blueprint map refresh (2026-10-11)

Ruling C: refresh 180 stale type fingerprints and move wc_receiptOrigins to
WeakContinuation.ReceiptOrigins. No mapped theorem is missing on this branch.
All statuses and OPEN reasons stay unchanged: 65 PROVED, 16 PARTIAL, 22 OPEN,
2 HISTORICAL; 36 OPEN items. Receipt coverage stays PARTIAL. The sleep producer
and paper alignment stay OPEN. Regenerated FGSA-BLUEPRINT-OPEN.md is byte-identical.
The compiled blueprint check passes; PC-SA safety remains source/map only.

## P-Da Round 3 — exports and strict source guard (2026-10-11)

Ruling B: the replay fixture uses public reducible aliases instead of an exposed
section. All 42 definition bodies and all four caller proofs are unchanged.
The existing B8 acceptance list gains only these five predicates:

- Healing/SupportFrame.lean HealingJoinedTick: other modules unfold the joined premise.
- Healing/SupportFrame.lean HealingCarriersAt: other modules unfold the carrier premise.
- Healing/SupportRecovery.lean HealingWindow: recovery and post-reset callers unfold it.
- Healing/SupportRecovery.lean StrongHealingWindow: recovery callers unfold it.
- Outage/ScopedPrefix.lean OutageScopedRegression: ScopedPaths and LaterHeads unfold it.

Paths above are under AvailableChainFGSAProofs/Proofs. Lead review is required
for these exact acceptance rows. The claims source guard uses the same list;
section, theorem, attribute-command, unlisted and wrong-owner exposures still fail.
The fixture and selective TickRead open compile with unchanged theorem statements
and proof bodies. Layers have zero new findings; headers and exports pass.

The full source guard also required these migration repairs:

- ORDER now includes Join after Counts, and OutageSleep after OutageContinuation.
- F-28 stays strict on production Claims; owning Tests may contain test theorems
  and read the owning assembled Claims contract. Layer test rules still apply.
- DECISION P23-A / 04e0a138 supplies the exact Base₂.idealization projection.
  A source signature hash pins this one theorem. Changed-type and owner/name twins fail.
- 6accfefd supplies the exact Outage.ArmingKernel -> Statements.CleanInvariant edge.
  The other Outage internal-statement negative control still fails.
- A module with explicit public/private declarations may use a plain section,
  as FrontierOpen does. A bare theorem in that section still fails the guard.
- TickRead opens only V2.Event and V2.D.Engine; its statement and proof are unchanged.
- Claims facade adds OutageSleep. Proofs facade adds eight missing production imports:
  Assembly.ContinuationReplay, ContinuationService, OutagePublicAxioms,
  OutagePublicInputs, ResetSource; Healing.RegressionFixture;
  Outage.Induction and Outage.SleepAxioms. No source coverage exception is added.

The unchanged strict inventory writer refreshes fgsa-claims-expected.txt:
6,035 -> 7,819 public declarations/projections; 1,846 additions and 62 retired
compiled names. Other four audit inventories are byte-identical. The exact name
delta is saved in Round 3 inventory-delta.json. Source inventory covers 6,578
explicit declarations. Source guard and its positive/negative controls pass.
The inventory comparison, compiled audit and every existing control remain required.

## P-Da Round 3 — all current API products (2026-10-11)

Ruling D: scripts/write-api-snapshots.py --write completes every active scope.
Only docs/api/fgsa-claims-api.json differs from the Round 3 base (group A').
The final compiled extraction confirms that same 1,617-root / 4,250-node candidate.
Every other written product is byte-identical: V2-API.md, GEN-API.md, FGSA-API.md,
v2-deep.json, gen-deep.json, fgsa-deep.json, legacy-api.json and compose-api.json.
PCSA-API.md and pcsa-deep.json are skipped by the single UNPORTED switch.
The two FG-SA ruling pin files and frozen baselines are unchanged.
Writer log: .lake/sleep-pcsa-off/round3/snapshots-write.log.

Generated snapshots and audit inventories keep their writer format. Their long
kernel-name strings can exceed 100 columns. New source and ledger lines stay
within 100 columns; no generated value is shortened or reflowed to hide that limit.

## P-Da Round 3 — inherited transparency placement (2026-10-11)

The first full Mac gate stops at the two inherited ClientTrace findings recorded
in this ledger's W3 review. The source has the same transparency option before
the theorem and as the first tactic. Remove only the redundant outer option.
fgsa_tick_rows_of_seats keeps its exact statement and complete proof body,
including the inner option and its reason. Compile with --wfail: PASS.
The unchanged transparency checker passes; no allowance or baseline is changed.
The initial manifest read overlapped this rebuild and could not find its olean;
that attempt is retained as manifest-prebuild-fail.log. The final gate rebuilds
before its compiled checks. The precheck failure is also retained in Round 3 logs.

## P-Da Round 3 — strict test and package scope repair (2026-10-11)

The Claims source guard accepts test theorems only in the owning Tests module
and the AvailableChain.FGSA.Run.Tests namespace. An unscoped theorem in
Claims.Tests.Axioms still fails F-28, as the original precheck fixture requires.
The added control, all source fixtures and the real source guard pass.
The aggregate self-test remains blocked before that fixture by 54 inherited
GLY findings (F-13: 42; F-23: 11; F-28: 1). Remaining self-tests run separately.

P-Fx's old package map omitted five dependencies of its current targets:
Statements.Join (Claims); Shared.AnchorService, CatchUp and RegimesService
(Proofs); Tests.P23Axioms (Run). Add these to GREEN, keeping all existing targets
and checks. The full build passes; the package rerun checks these exact modules
and every strict audit. No module is marked EXPECTED-FAIL to bypass coverage.

## P-Da Round 3 — V2 coverage and current Catalog lock (2026-10-11)

The complete active build exposes 29 unanchored sleep engine entries. Add the
exact V2Manifest --anchor references to the existing Unit-valued dutyAnchor.
This coverage definition changes no proof or theorem statement. Framework builds
with --wfail. Refresh the current Catalog lock: only V2.anchor and V2.dutyAnchor
change; all 252 locked names remain. Run the complete API writer again after the
build: every active product completes, PC-SA is skipped, and every API file stays
byte-identical to the first Round 3 write. Only the approved Claims API file and
the two current Catalog lock digests differ from the Round 3 base.

Old-read audit data loses only seven obsolete height rows: wc_finiteFacts,
wc_heightSeed, wc_outputStep, wc_proposal_gates, wcg_heightSeed, wcg_outputStep
and wcg_retainedSeed (all in AvailableChain.FGSA.Run). Eleven new height-only
readers stay unlisted for lead review. No new old-read exemption is added.
All frozen API baselines and GLY allowance/baseline files are unchanged.

## P-Da Round 3 — Claims policy fixture scope (2026-10-11)

The precheck self-test's main-policy F-28 case now runs the real Claims source
checker and guard-list merge in its temporary policy copy. Its target guard
remains permissive; the main guard must reject the planted unscoped theorem.
Unrelated production GLY findings remain in the real full gate. Only the test
fixture's scope changes. Both planted rejections, every guard-list/data case,
and the no-Lean/no-build sentinel pass. The independent precheck self-test passes.
No production precheck, GLY rule, baseline or allowance is changed by this repair.

## P-Da Round 3 — remaining package dependency maps (2026-10-11)

A source-graph check of all 19 maps finds the same missing migration dependencies
in six later packages. Add only omitted current dependency modules to GREEN:
W1a 40, W1b 35, W2a 35, W2b 22, W3 5 and sleep-ppc 45. Keep every original
TARGETS and EXPECTED-FAIL row. The existing validator still checks the exact
source closure and the full package run still builds GREEN with --wfail and
runs strict axioms and all default controls. Every added module is active and
was in the complete successful build. No module or check is excluded.
The exact per-package module list is saved in package-map-dependency-delta.json
under the Round 3 logs. Complete package validation follows these map updates.

## P-Da Round 3 — Run facade and final build (2026-10-11)

The independent FG-SA Run check finds two production modules missing from its
root closure: TestSupport.EmissionFreshness and TestSupport.Sleep. Add only
these public imports to AvailableChainFGSARun.lean. The facade builds; every
one of the 19 package maps still passes the exact source closure check.
The complete active build is repeated after all final facade/anchor changes:
4,569 jobs PASS. This refreshes downstream Registry oleans for cone and shake.
No theorem statement or proof body is changed. Coverage checks retain their rules.

The serialized check driver is stopped with only its verified same-user child
processes. Completed results and the interrupted FG-SA log are retained. The
remaining independent checks run with one shared gate-slot directory and the
normal wrapper. Initial cone/shake results with stale downstream oleans are
retained; their final checks follow the successful full rebuild.

## P-Da Round 3 — final Mac validation (2026-10-11)

Full manifest and all 19 DCK packages PASS, with every default control.
Complete active build PASS (4,569 jobs); eight strict axiom audits PASS.
Blueprint, Claims source guard, Catalog/V2/Gen, headers and export checks PASS.
Layers: zero new. Proof coverage/equations, cone, shake, transparency and full FG
research checks PASS. The complete gate self-test chain and extra graph/fail-fast
controls PASS. All theorem statements and complete proof bodies are unchanged.
PC-SA sources and both retained snapshots are unchanged; PC-SA stays UNPORTED.

The complete full gate FAILS. Source GLY has 54 inherited findings (F-13 42,
F-23 11, F-28 1); compiled GEN-FIRST adds two, for 56 full GLY findings.
Old-read audit has 11 unlisted height-only readers; no new exemption is added.
Compiled Claims has 15 findings (one private export, 13 generated helper uses,
one legacy GridCO proof use). Run has seven TestSupport import-policy findings.
These four categories require lead review; no full-pass receipt or stamp exists.
All remaining Mac checks ran independently after the real gate precheck failure.
Evidence: .lake/sleep-pcsa-off/round3/. Final effective results: final-mac-results.json
and dck-results.json. Exact failure lists and all initial/rerun logs are retained.
Report: claude-files/sleep-pcsa-off-report.md, Round 3. NUC work remains with the lead.
