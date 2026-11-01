Use **Route A, with an early SWITCH on the integration branch and one atomic landing on main**. Stage 0 contains additive work only. WP13 and WP14 follow the core landing.

**Historical record — superseded 2026-10-09.** This document records its
original source basis. Freeze rules, port totals, ownership paths, and exact
exception rows are not current acceptance data. Future changes use generated
current snapshots and reviewed diffs. Open proof obligations remain open.
The old API data remains in Git at
`6c36d4810cb070655f2f4aadb3346db6c76aa0a3`. No checker reads this record.


This r2 applies both reviews. The later derisks replace r1’s global resolution change with the minimum change to `proposerSupport`. They also close the combined-rule paper check. Lean validation remains required.

I verified main `7acdc143d87eb6f5b259ed253aa63c496e8c7581` and both archive hashes:

```text
┌─────────────┬──────────────────────────────────────────────────────────────────┐
│ Input       │ SHA-256                                                          │
├─────────────┼──────────────────────────────────────────────────────────────────┤
│ Spec        │ bb21bbd4a1f0a6841bb31cf997832cb9c4601dd70cd160d78a0262bc89a6f026 │
│ Lean notes  │ 8e65c96920b83fe43db2ab129a5419186026533234c822d6dd8a7caa7a990fe4 │
└─────────────┴──────────────────────────────────────────────────────────────────┘
```

Implementation starts from checked main **after P13 lands**. `b033d223` adds the field-supplier map; its inherited-history record still has `P13.tip = null`. Close that package at its checked revision before the port records changes.

No files were edited. No scratch files, builds, gates, or agents were used.

**Scope and source rules**

The following rules apply to every WP:

- Switch canonical FG-SA names in place. Retained old readers belong to `FGSA.Legacy` and must call legacy dependencies throughout.
- Keep shared KitFG names and bodies. Add `treeStoreControlsView`, `treeStoreFrameView`, `treeFjControlsView`, `treeFjFrameView`, and their proof counterparts.
- For (h), change only the executable `proposerSupport` body. Keep confirmation, revocation, the frozen arm, and the FG-head support implementation. Prove their local correspondence.
- For (j), change proposal selection, the voter tree, and the carried merge. Keep cumulative metadata.
- Keep `H` and justified-pair selection cumulative.
- Resolve roots in the cumulative domain before the prefix filter. Preserve ambiguity.
- Keep GridCO and SA source unchanged.
- Keep PC-SA source, behavior, and compiled statement dependencies unchanged. Existing FG-SA lemmas used by PC-SA keep their signatures. Add new lemmas where needed.
- Keep `FGSA/Model/{Objects,ProposalContent,WindowViews,WindowStore}.lean` unchanged. The correspondence layer must use these representations.
- Keep claim bounds, observation scopes, and the hypothesis-free `fgsaClaims` binder structure.

`Φ.tree` means accepted blocks above `F`. It is distinct from `fullTree`, which also applies the viable frame filter. WP00t owns its declaration.

The [census report](</Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/reports/reviews/derisk2-port-census-sol.md>) records 369 source declarations that select **876 manifest entries: 799 original frozen entries and 77 later entries**. Use this as the source census. Confirm it against the compiled dependency closure before SWITCH and at final closure.

```text
┌───────┬──────────────────────────────────────────────────────────────────────┐
│ Class │ Required record                                                      │
├───────┼──────────────────────────────────────────────────────────────────────┤
│ A     │ Same-event transport preserves the read. Give its equality argument. │
│ B     │ Meaning changes through a reader, object, witness, or run premise.   │
│       │ Attribute it to the one recorded h+i+j protocol switch.              │
│ C-i   │ Contest reads agree in a stated context. Give the invariant and      │
│       │ premises. This does not reclassify the complete bare declaration.    │
└───────┴──────────────────────────────────────────────────────────────────────┘
```

Clean contest equality requires the Clean invariant. `FaultQ` alone is insufficient. Recovery equality uses `RXing` and the current finality carrier at each local read. Neither argument requires equal honest finalized roots.

The permitted statement-source surface is:

`RFrameExact`, `RFrame`, their equations, `FrameAt`, `FrameClaim`, `FGFoundation`, `FGFoundationClaim`, `FGSASafetyInterfaces`, and the frame antecedent of `CleanCutPosClaim`.

Keep `FullVoteService`, `TVote`, and `KernelACSideClaim_W` text unchanged. The inline service clause is A-local; the whole emission-dependent service remains B. Add a proposer-support membership bridge when a caller needs it. A text change to these three declarations needs a concrete necessity argument and an attributed diff.

**Revised WP table**

Paths below are relative to the repository:

- `F/` = `AvailableChainFGSA/`
- `R/` = `AvailableChainFGSARun/`
- `C/` = `AvailableChainFGSAClaims/`
- `P/` = `AvailableChainFGSAProofs/Proofs/`
- `K/` = `AvailableChainKitFG/`
- `I/` = `AvailableChainFGSAInhabit/`

`Sol` means `gpt-6.1-sol`; `Astra` means `gpt-6-astra`. Use standard effort and the required fast service setting. Each package has one writer and a different reviewer.

Repair codes:

```text
┌──────┬─────────────────────────────────────────────────────────────────────┐
│ Code │ Obligation                                                          │
├──────┼─────────────────────────────────────────────────────────────────────┤
│ H    │ Proposer prefix filter; local equality above F; projected leases.    │
│ J    │ Retained proposal selection; carried-head filter; ordered merge.    │
│ S    │ Score bridge needs separate F_dst ⪯ N retention.                    │
│ T    │ Guarded top-height-extends-J helper needs F ⪯ W.                    │
│ P    │ Contest persistence needs RXing or destination top retention.       │
│ E    │ F-indexed EC, guarded phase bits, and matching frame bridges.        │
│ X    │ Combined retained, frontier, cpPrefix/cpCompat, exact-head suppliers.│
│ C    │ Core spec correspondence, with exact event and digest mapping.      │
│ D    │ DCA, saved-head observation, and output companions.                 │
│ F    │ Census, shallow/deep freeze, P13 data, and attributed differences.  │
└──────┴─────────────────────────────────────────────────────────────────────┘
```

`FULL` means a complete gate on a green main candidate. `TARGET` means a module or family build on the red integration branch, plus applicable audits. It is **partial evidence**.

```text
┌────────┬──────────────────────────────────────┬────────┬──────────────────────┬────────┬─────────┐
│ WP     │ Result                               │ Writer │ Prerequisites        │ Repairs│ Evidence│
├────────┼──────────────────────────────────────┼────────┼──────────────────────┼────────┼─────────┤
│ 00a    │ Base, inventory, ownership, census   │ Sol    │ P13 checked landing  │ F      │ FULL    │
│ 00t    │ Accepted tree above F declaration   │ Sol    │ 00a                  │ H,J    │ FULL    │
│ 01a    │ New proposer resolution functions   │ Sol    │ 00t                  │ H      │ FULL    │
│ 02     │ New guarded contest/frame functions │ Sol    │ 00t                  │ E      │ FULL    │
│ 01b    │ New merge and selection functions   │ Astra  │ 01a,02               │ J      │ FULL    │
│ 03a    │ New pure support/carry helpers       │ Astra  │ 01a,01b              │ H,J,S  │ FULL    │
│ 04a    │ New pure guarded frame helpers       │ Astra  │ 02                   │ T,P,E  │ FULL    │
│ 12a    │ Pure core correspondence definitions│ Astra  │ 00a; readers as used │ C      │ FULL    │
│ 14p    │ Pure common-ancestor lemmas          │ Sol    │ 00a                  │ D      │ FULL    │
│ 00b    │ Additive frame declarations          │ Sol    │ 01b,03a,04a          │ E,F    │ FULL    │
│ 00c    │ Deep checker and pre-SWITCH baseline │ Astra  │ All Stage 0 landings │ F      │ FULL    │
├────────┼──────────────────────────────────────┼────────┼──────────────────────┼────────┼─────────┤
│ SWITCH │ Canonical model and frame switch     │ Astra  │ Stage 0 accepted     │ H,J,E,F│ TARGET  │
│ 05a    │ Local proof adapters                 │ Sol    │ SWITCH,03a,04a       │ H,E    │ TARGET  │
│ 05b    │ Run laws, reads, emissions, receipts │ Sol    │ 05a                  │ H,J,E  │ TARGET  │
│ 06a    │ Shared geometry and walk foundations │ Sol    │ 05b                  │ E,X    │ TARGET  │
│ 05c    │ Foundation suppliers, including RXing│ Astra  │ 06a                  │ E,X    │ TARGET  │
│ 03b    │ Run count, relay, and score bridges  │ Astra  │ 05b,06a,03a          │ H,J,S  │ TARGET  │
│ 06b    │ Retained and exact-head chain        │ Astra  │ 03b,06a              │ S,X    │ TARGET  │
│ 03c    │ Clean/Recovery score wrappers        │ Sol    │ 06b                  │ S      │ TARGET  │
│ 06c    │ Remaining Shared services and growth│ Sol    │ 03c,05c              │ H,J,X  │ TARGET  │
│ 09a    │ Healing Base adapter                 │ Sol    │ 05c,06a              │ X      │ TARGET  │
│ 04b    │ Run phase helpers                    │ Astra  │ 09a,06c              │ T,P,E  │ TARGET  │
│ 07     │ Clean family                         │ Sol    │ 06c,05c              │ H,J,E  │ TARGET  │
│ 08     │ Outage, inclusion, continuation     │ Astra  │ 06c,05c; 07 closure  │ J,S,X  │ TARGET  │
│ 09b    │ Remaining Healing family            │ Astra  │ 04b,09a,06c          │ H,J,S,X│ TARGET  │
│ 11     │ Finality suppliers and kernels      │ Sol    │ 04b,06c,05c          │ H,E,X  │ TARGET  │
│ 10     │ WC and corruption-growth families   │ Astra  │ 06c,05c; 09b closure │ J,S,T,X│ TARGET  │
│ 12b    │ Core run simulation and transfer     │ Astra  │ 12a,05b,06c          │ C      │ TARGET  │
│ 13v    │ Core fixtures, tests, inhabitation  │ Sol    │ Each tested supplier │ All    │ TARGET  │
│ 15     │ Claim adapters and closed assembly  │ Astra  │ 07–12b,13v           │ X,F    │ Joint   │
│ 16     │ Final pins, maps, freeze and docs    │ Sol    │ Stable WP15 code     │ F      │ FULL*   │
├────────┼──────────────────────────────────────┼────────┼──────────────────────┼────────┼─────────┤
│ 13     │ Saved-head monitor and output reads │ Sol    │ Atomic core landing  │ C,D    │ FULL    │
│ 14a    │ Structural/safety output companions │ Astra  │ 13,14p, record claims│ D      │ FULL    │
│ 14b    │ Awake-reader inclusion/availability │ Astra  │ Fallback derisk;14a  │ D      │ FULL    │
└────────┴──────────────────────────────────────┴────────┴──────────────────────┴────────┴─────────┘
```

`FULL*`: **WP15 and WP16 form one final gate unit**. Generate and review all data before that gate. WP15 has no separate FULL promise.

Outage and WC may develop conditional proofs while Clean and H-time are in progress. Their closed assembly waits for those suppliers. Lanes use premise interfaces; Assembly joins lane exports.

**Stage 0 packages ready for handoff**

READY means the task scope is closed. It does not override the requirement that P13 lands before implementation. New paths below are proposed paths.

```text
┌─────────┬─────────────┬────────┬──────────────────────────────────────────────┐
│ Package │ WPs         │ Writer │ Files                                        │
├─────────┼─────────────┼────────┼──────────────────────────────────────────────┤
│ S0-I    │ 00a         │ Sol    │ docs/plans/fgsa-port-r2.md                    │
│         │             │        │ docs/FGSA-PORT-CENSUS.md                      │
│         │             │        │ docs/FGSA-PORT-OWNERS.json                    │
│         │             │        │ docs/ARCHITECTURE.md                         │
│         │             │        │ P13 inherited-history closure record        │
├─────────┼─────────────┼────────┼──────────────────────────────────────────────┤
│ S0-T    │ 00t         │ Sol    │ F/Model/Tree.lean                            │
│         │             │        │ F/Proofs/Port/Tree.lean                      │
│         │             │        │ F/Tests/PortTree.lean                        │
├─────────┼─────────────┼────────┼──────────────────────────────────────────────┤
│ S0-H    │ 01a         │ Sol    │ F/Model/Resolution.lean                      │
│         │             │        │ F/Proofs/Port/Resolution.lean                │
│         │             │        │ F/Tests/PortResolution.lean                  │
├─────────┼─────────────┼────────┼──────────────────────────────────────────────┤
│ S0-IJ   │ 02,01b      │ Sol →  │ K/TreeFrameDef.lean                          │
│         │             │ Astra  │ F/Model/ContestFrame.lean                    │
│         │             │        │ F/Model/VoteMerge.lean                       │
│         │             │        │ F/Model/FrameNext.lean                       │
│         │             │        │ F/Model/Legacy/Frame.lean                    │
│         │             │        │ F/Tests/PortMerge.lean                       │
│         │             │        │ K/Tests/TreeFrame.lean                       │
├─────────┼─────────────┼────────┼──────────────────────────────────────────────┤
│ S0-P    │ 03a,04a     │ Astra  │ F/Proofs/Port/{Support,Carry,LocalReads}.lean │
│         │             │        │ K/Tree* proof modules listed below          │
│         │             │        │ K/Tests/TreeFrameHelpers.lean                │
├─────────┼─────────────┼────────┼──────────────────────────────────────────────┤
│ S0-C    │ 12a         │ Astra  │ F/Model/Spec/{Objects,Frame,ACState,          │
│         │             │        │ Transitions,Codec}.lean                     │
│         │             │        │ F/Proofs/Spec/{Frame,Locks,Clock,            │
│         │             │        │ Handlers,Codec}.lean                        │
├─────────┼─────────────┼────────┼──────────────────────────────────────────────┤
│ S0-D    │ 14p         │ Sol    │ AvailableChainModel/Objects/                 │
│         │             │        │ CommonAncestor.lean                         │
│         │             │        │ AvailableChainGeneric/Statements/Pure/      │
│         │             │        │ CommonAncestor.lean                         │
│         │             │        │ AvailableChainGeneric/Proofs/Pure/          │
│         │             │        │ CommonAncestor.lean                         │
│         │             │        │ AvailableChainGeneric/Tests/                │
│         │             │        │ CommonAncestor.lean                         │
├─────────┼─────────────┼────────┼──────────────────────────────────────────────┤
│ S0-F    │ 00b,00c     │ Sol →  │ C/Statements/FrameNext.lean                  │
│         │             │ Astra  │ C/Claims/FrameNext.lean                      │
│         │             │        │ scripts/V2Manifest.lean                     │
│         │             │        │ scripts/check-fgsa-manifest.sh              │
│         │             │        │ Separate frame/deep baseline files          │
└─────────┴─────────────┴────────┴──────────────────────────────────────────────┘
```

Split each arrow into separate reviewed commits. No file has two writers.

Every Stage 0 package lands with a **FULL gate** and a review at its fixed commit. New declarations, modules, imports, checker code, and freeze data do not qualify for r1’s proof-only MERGE shortcut.

Validation and acceptance for these packages:

- **S0-I:** verify the P13 landing, close its history package, expand the complete ownership register, and preserve both S0 manifests. Record PC-SA source and compiled statement-dependency baselines.
- **S0-T:** prove accepted-tree membership means held and above `F`. Preserve cumulative storage and the cumulative resolution domain. Do not require ancestor closure below `F`.
- **S0-H:** prove cumulative resolution followed by the prefix test. Check ancestor omission, ambiguous roots, slots, and strict stamps. Add `proposerSupportNext`; canonical `proposerSupport` remains unchanged on main.
- **S0-IJ:** test guarded contest, retained proposals, carried-head exclusion, raw participation, equivocation, list order, and deduplication. `headVoteNext` depends on the guarded frame from WP02. Preserve the old `stXs` result through `Legacy.headSupport`; add the new-rule empty-support result.
- **S0-P:** add repaired helpers under new names. Pure lemmas quantify stores, lists, cuts, and supplied laws. They must not assert facts about the new run while `fgsa` still denotes the old protocol.
- **S0-C:** prove pure representation parts. This package does not claim a complete run simulation or output correspondence.
- **S0-D:** prove DCA prefix, maximality, compatibility transfer, and inclusion equivalence. It does not add a clamped monotonicity theorem.
- **S0-F:** check the complete current shallow manifest, the separate frame baseline, and the deep baseline. Run positive and negative controls. Attribute every generated data change.

WP16’s Sol data owner handles facade, import-policy, expected-name, manifest, and coverage updates at **each** green Stage 0 landing. These updates cannot wait until final integration.

New Stage 0 model modules must not import canonical `Model/Frame.lean`. Otherwise the later canonical wrapper imports can create a cycle. Define their readers under `FGSA.Next`, with an entirely new-reader dependency chain. Reuse unchanged lower-level helpers or pass them as parameters.

**Exact ownership and handoffs**

Brace lists expand to exact `.lean` paths. The inventory register must contain each expanded path, its WP, and its writer. A newly discovered file receives an owner before a writer edits it.

WP04a owns these **new** KitFG modules:

`K/{TreeFrameBridge,TreeCorrespondence,TreeFrameGeometry,TreeFrameChannels,TreeHeightBridge,TreeTwoChanges,TreeInBandLock,TreeRecordHighDef,TreeRecordHigh}.lean`.

It also owns the comparison audit of the existing `FrameBridge`, `Correspondence`, `FrameGeometry`, `FrameChannels`, `HeightBridge`, `TwoChanges`, `InBandLock`, `RecordHighDef`, and `RecordHigh` modules. Their existing names, bodies, and consumers stay unchanged. FG-SA consumers use the new counterparts.

The run-phase split is exact:

```text
┌────────┬──────────────────────────────────────────────────────────────────────┐
│ Owner  │ Exact Healing files                                                  │
├────────┼──────────────────────────────────────────────────────────────────────┤
│ WP09a  │ Base.lean                                                            │
├────────┼──────────────────────────────────────────────────────────────────────┤
│ WP04b  │ PhaseFrame, PhaseOrder, Phase, PhaseRelay, PhaseSettle, PhaseBoot,    │
│        │ PromotionPhase                                                       │
├────────┼──────────────────────────────────────────────────────────────────────┤
│ WP09b  │ FrontierSearchDefs, FrontierSearchStop, FrontierSearchAge,            │
│        │ FrontierSearchRepair, FrontierSearchGap, FrontierSearchTop,          │
│        │ FrontierSearchCompose, FrontierSearchHG2a, FrontierSearchTail,       │
│        │ FrontierSearchRise, FrontierSearchBudget, FrontierSearchTasks,       │
│        │ FrontierSearchFull, Descent, ResetTransfer, PostResetKeep            │
└────────┴──────────────────────────────────────────────────────────────────────┘
```

WP09a closes `Base` before WP04b starts. This removes the dependency through `PhaseRelay → Base`. WP04b hands off the reviewed phase API before WP09b repairs its consumers. WP09b does not edit WP04b files.

The Shared split removes the WP03↔WP06 cycle:

```text
┌────────┬──────────────────────────────────────────────────────────────────────┐
│ Owner  │ Exact Shared files                                                   │
├────────┼──────────────────────────────────────────────────────────────────────┤
│ WP06a  │ StoreRun, Roots, Reads, RowAuth, RowReads, Channels, HeadCover,       │
│        │ HeadGeometry, KeepExact, RetainedWalk, RetainedWalkStore, Gate,       │
│        │ GateReceipt, OpeningSource, FGCompose, FGSafetyClient,                │
│        │ FGSafetyStore, FGSafetyScope                                         │
├────────┼──────────────────────────────────────────────────────────────────────┤
│ WP03b  │ Count, Relay, ScoreRun                                               │
├────────┼──────────────────────────────────────────────────────────────────────┤
│ WP06b  │ RetainedScores, RetainedReflect, RetainedPersist, ExactHead,          │
│        │ RetainedEndpoint, RetainedConsumers, RetainedConsumersH6S,           │
│        │ RetainedConsumersL2, RetainedConsumersQ, ExactService                 │
├────────┼──────────────────────────────────────────────────────────────────────┤
│ WP03c  │ Regimes                                                              │
├────────┼──────────────────────────────────────────────────────────────────────┤
│ WP06c  │ BoundsW, Compose, GridSchedule, HeadAdmit, HeadAfterSettlement,       │
│        │ Healed, HealingFixture, HeldReceipt, HonestQuorum, OpeningAfterGate, │
│        │ OutputGrowth, OutputGrowthProposal, OutputGrowthCausal,              │
│        │ OutputGrowthReads, ProposalRead, ReceiptFacts, Recurrence, Release, │
│        │ SameLabel, SelfDelivery, WindowTerminal                              │
├────────┼──────────────────────────────────────────────────────────────────────┤
│ WP15   │ Claims, Export                                                       │
└────────┴──────────────────────────────────────────────────────────────────────┘
```

Inside WP06b, use this order:

`RetainedScores → RetainedReflect → RetainedPersist → RetainedEndpoint/RetainedConsumers*`.

`ExactHead` can proceed after ScoreRun and the walk foundations. `ExactService` needs Count and OpeningSource. Finish both before WP03c.

WP06c verifies Release and SameLabel without an h-specific semantic repair. Their arbitrary-target laws stay. The compatible-target equality and projected-state correspondence are in WP03a/WP12.

The remaining ownership assignments include every unowned item in Opus §3:

```text
┌────────┬──────────────────────────────────────────────────────────────────────┐
│ Owner  │ Files and responsibility                                             │
├────────┼──────────────────────────────────────────────────────────────────────┤
│ WP05a  │ F/Proofs/{ActView,NamedReachable,SetEq,HeadResolution,FrameViews,      │
│        │ WindowReaders,StoreInv,StoreBundle,LeaseOutput,Head}.lean;           │
│        │ Head/{Pool,Score,Transfer,Walk}.lean and local proof prerequisites.  │
│        │ Preserve existing PC-SA-used signatures; add new adapters.          │
├────────┼──────────────────────────────────────────────────────────────────────┤
│ WP05b  │ R/Proofs/{Protocol,ClockLaws,Reachable,ReadFacts,Emission,             │
│        │ EmissionWellFormed,ReceiptCoverage,Receipts,RootResolution,          │
│        │ HeadIdentity,Content,Hooks,Interface,Readiness,AC,ClientTrace,        │
│        │ Acceptance,Roots,NamedScope,NamedOrigins,NamedDelivery,              │
│        │ Schedule,SelfDelivery,Excludes,Slashing,WindowExclusion,             │
│        │ RootLease,AncestorDeadlines,AncestorDeadlinesStore}.lean.            │
├────────┼──────────────────────────────────────────────────────────────────────┤
│ WP05c  │ P/Foundations/{Store,Leases,Reconcile,Carrier,Certificates,Client,    │
│        │ ClientOrigin,FGSafetyBridge,Accountable,Counts,Crossing,Cap,         │
│        │ FinalityApi,FinalizedSafety,HonestNeverSlashed,Sources,Timing,       │
│        │ RowService,RowPermission,OpeningCovered,OpeningCoveredLower}.lean.  │
├────────┼──────────────────────────────────────────────────────────────────────┤
│ WP07   │ P/Clean/{Action,Chain,Closure,Export,Frame,GateOutput,Interface,      │
│        │ Safety,State,StateGate,StepGate,Transfer,TransferFrame,Zero}.lean.   │
├────────┼──────────────────────────────────────────────────────────────────────┤
│ WP08   │ All exact Outage groups listed below; OutageContinuation/Export.    │
├────────┼──────────────────────────────────────────────────────────────────────┤
│ WP11   │ Finality record, row, tail, kernel, supplier and export modules.    │
├────────┼──────────────────────────────────────────────────────────────────────┤
│ WP13v  │ F/Tests/Smoke.lean, including stXs and contest fixtures;            │
│        │ F/Tests/{Axioms,Support,RootCollision}.lean; R/Tests;                │
│        │ I/{WeakContinuationW1,WeakContinuationWitness,WitnessPositive}.lean│
│        │ and I/Tests/{Axioms,WeakContinuationW1,WitnessPositive}.lean.        │
│        │ All 99 existing AvailableChainFGSAProofs/Tests files.               │
├────────┼──────────────────────────────────────────────────────────────────────┤
│ WP15   │ P/Shared/Claims.lean; P/Foundations/Export.lean; all Assembly files; │
│        │ claim and proof facades.                                            │
├────────┼──────────────────────────────────────────────────────────────────────┤
│ WP16   │ Pins, maps, manifests, expected-name lists, coverage, checker data, │
│        │ S0 history, architecture and final reports.                         │
└────────┴──────────────────────────────────────────────────────────────────────┘
```

“Local proof prerequisites” and the finality set are verification scopes in this table. WP00a must expand them from the checked base into explicit paths before handoff; a writer does not receive permission to edit an unspecified directory.

WP08’s exact groups are:

- `Outage/Arming{,Arith,Batch,Cover,Duty,Gate,History,Input,Main,Output,Pending,Prefix,Step}.lean`
- `Outage/{Close,Induction,Suppliers,Export,Growth}.lean`
- `Outage/ExactProposal{,History,Receipts,Retained}.lean`
- `Outage/InclusionGate{,Body,Bounds,Service}.lean`
- `Outage/Persistence{Defs,Frame,History,Release,Step}.lean`
- `Outage/Continuation{Frame,Gate,Induction,Joint,Receipt,Timing}.lean`
- `OutageContinuation/Export.lean`

Thus `Arming`, `ArmingGate`, `ArmingMain`, `Close`, and `Induction` have explicit owners.

WP09b also owns the named positive-support files:

`Healing/{SupportProposal,SupportHeads,DescentLossNext,DescentLossUnanimous,FrontierSupportFrame,FrontierSupportProposal,FrontierSupportHeads,FrontierSupportTransfer,FrontierService,FrontierServiceCover,FrontierServiceGate,FrontierServiceSupport,PostResetConeReceipts,PostResetRaw,PostResetOpening,RepairH6,RepairH6S}.lean`.

The complete remaining Healing set goes into the WP00a register as exact paths, excluding `Base` and the seven WP04b files. Assembly files remain with WP15.

WP13v owns test edits centrally. Family writers provide the test obligation and expected result. They do not concurrently edit test files. The inventory must enumerate all 99 test paths, including `NonVacuity/*`, phase tests, axiom tests, retained tests, continuation tests, and assembly-axiom tests.

GridCO `resolvedBefore` and other shared read helpers receive **no implementation edit**. WP03a owns the FG-SA correspondence lemmas for their use. This resolves the former unowned GridCO row without changing GridCO.

**Required helper repairs**

These obligations come from the [minimal derisk](</Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/reports/reviews/derisk2-port-minimal-astra.md>) and the [combined derisk](</Users/francesco/ethereum/research/async-resilient-committees/tip-stability/codex/reports/reviews/derisk2-port-combined-astra.md>).

1. **WP03a: positive proposer support and local correspondence.**
   Positive spec resolution needs a held, uniquely resolved head with `F ⪯ H` and the slot bound. Prove support incidence and score equality above `F`. Prove confirmation and selected-head equality for a fixed local frame and fixed raw pool. For confirmation, include clean-support non-equivocation; fixed-raw equality alone is insufficient.

   Prove release equality only for compatible retained targets. Project fast sets and leases to the tree above `F`. Do not assert equality of internal support lists, release snapshots, or stored fast sets below `F`.

2. **WP03b: proposal retention is separate from candidate geometry.**
   Strengthen `fgsa_score_eq_on_run` with:

   `Block.Preceq (eraseFG dst.fg.F) N.erase`.

   Keep admission/storage as a separate premise. Pass retention through positive raw carry, support carry, and score equality. For support, also supply the held head above destination `F`.

   In `fgsa_ghost_transfer_sfx_on_run`, prove `D ⪯ N.parent` **before** the score call. Then derive `F_dst ⪯ N.parent ⪯ N`.

3. **WP06b: every retained-score call receives the parent bound.**
   Derive proposal retention once from `hA.target_floor` and `N.parent ⪯ N`. Pass it to the count call and every candidate-specific score call. A rival candidate’s geometry does not retain `N`.

4. **WP03c: name the wrapper changes.**
   Add the same explicit destination-retention premise to new strengthened forms of:

   - `fgsa_score_eq_on_clean`
   - `fgsa_score_eq_on_recovery`

   The suffix-walk wrappers `fgsa_ghost_transfer_sfx_on_clean` and `_on_recovery` can derive retention through their walk geometry. Preserve their conclusion and derive the premise before calling the repaired bridge.

5. **WP04a/WP04b: repair the guarded frame helpers.**
   The new top-height-extends-`J` theorem requires `F ⪯ W`. Guard EC witnesses by `F`; reprove `effFrame_of_bits` and the phase algebra for that evidence.

   Pure contest persistence takes destination top retention, including the retained old `J` carrier when `J` changes. Run persistence supplies that fact through `RXing`. Pass it through `healing_phase_contest_persist`, `healing_phase_order`, settlement, and promotion callers.

6. **WP06a and downstream families: preserve the combined suppliers.**
   Reprove `cpPrefix` and `cpCompat` with new witness extraction. Keep `cpCompat`’s universal conclusion over cumulative top-height off-`J` blocks.

   Retained geometry establishes proposal admission before score transport. Frontier proofs obtain local top-block extension from `RXing`; required HEAD batches enter through the frozen arm. Use the actual new-run proposal and its actual root.

7. **WP08/WP10/WP11: preserve their existing scopes.**
   Outage continuation gains no slashing premise. WC permits sleeping readers and different local `F`. Corruption growth uses its existing whole-run slashable bound, including historical carriers. Finality tail witnesses receive the existing `F ⪯ Q` fact.

These are helper repairs. They do not authorize new claim premises or larger bounds.

**SWITCH commit**

One writer, Astra, prepares and reviews the complete SWITCH commit. It contains:

- Canonical `F/Model/Frame.lean` bodies for guarded `controls` and `fullTree`.
- Canonical `proposerSupport` with the additional prefix test.
- Canonical retained `proposalsAt`, revised `voterBlocks`, and carried-head filtering in `headSupport`.
- Canonical `headVote` using the new KitFG frame function.
- Transitive use of these readers by `liveRoot`, `eligible`, `getHead`, `propose`, `fgSource`, `fgInputs`, `attest`, and run duties.
- The canonical frame-source changes and their equation exports in `C/Statements/ChannelProps.lean`, with any necessary frame-surface edits in `ComposeStmt`, `Claims/Foundations`, `Claims/Clean`, and `FGSAClaims`.
- The one protocol-change record, canonical/legacy name map, and measured model/statement dependency diff.
- Canonical fixture expectations that are ready at this point; unresolved proof and fixture failures remain visible.

Keep the frozen arm and FG-head inline support filter. Their local representation correspondence implements (h); their selected results can still change through the new frame and merge.

Keep canonical signatures where possible. Stage 0 `FrameNext` declarations provide the reviewed target. At SWITCH, canonical frame consumers acquire that meaning from day one. Do not leave a family on an old exact-frame statement while its protocol uses new controls.

Retained legacy readers must use a complete legacy reader chain. A legacy reader copy does not justify an old run theorem. Retaining such a theorem would also require a separate legacy protocol; this port does not need one.

Compile the model and statement targets at SWITCH. Record the expected proof failures. **Do not call this commit FULL or MERGE-green.**

**Red-window validation and final freeze**

Every WP review uses a fixed commit and lists the exact targets checked. Typical family targets are:

- `AvailableChainFGSAProofs.Proofs.Clean.Export`
- `AvailableChainFGSAProofs.Proofs.Outage.Export`
- `AvailableChainFGSAProofs.Proofs.OutageContinuation.Export`
- `AvailableChainFGSAProofs.Proofs.Healing.HealingInputExport`
- `AvailableChainFGSAProofs.Proofs.Healing.Export`
- `AvailableChainFGSAProofs.Proofs.Finality.Export`
- `AvailableChainFGSAProofs.Proofs.WeakContinuation.Export`
- `AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Export`

Use exact module targets for local/run/Shared work and the assigned test modules. A target failure can expose an upstream obligation; its owner repairs it before the consumer proceeds.

No `sorry`, `admit`, project axiom, `native_decide`, import removal, omitted target, or checker weakening is permitted. `decide +kernel` remains allowed. Partial evidence never substitutes for the final gate.

Keep three distinct records:

1. Claim text, premises, conclusions, bounds, and read scopes.
2. Shallow manifest hashes.
3. Deep dependency digests and P13 supplier/type fingerprints.

The deep checker follows the census proposal:

- Root it at every current FG-SA manifest entry.
- Traverse public and private constants across libraries.
- Traverse types, definition/data values, and inductive constructors. Traverse theorem types; exclude theorem proofs.
- Serialize deterministic kernel expressions with explicit lengths and a format version. Include names, kinds, universes, types, applicable values, constructor and binder data, reducibility, and instance status.
- SHA-256 those bytes. Do not hash only the existing 64-bit `ownHash` values.
- Keep a dependency digest list and report one dependency path for each changed root.
- Record the exact compiled basis commit, Lean pin, and package pin.

Use separate files:

` scripts/fgsa-deep-frozen.json`, its SHA-256 file, and a separate exact deep-change allow file.

Capture the baseline from **post-P13, pre-SWITCH main after Stage 0**. Preserve it after SWITCH. Record exact old/new digests, cause, census class, and plan revision for exceptions. Reject stale, mismatched, or unexplained entries.

Keep `FGSA-API-frozen.md` and its SHA unchanged. Regenerate the current shallow manifest with measured `expect=<hash>` allowances. Preserve prior exceptions.

The separate frame baseline contains the additive new frame declarations and generated entries. Check it against the **complete current manifest**, with its own SHA and its own empty allow file. Require all baseline files to exist. Its controls cover missing files, changed entries, removed entries, and wrong SHA.

Run mandatory frame and deep checks before the `NEG=0` early exit in `check-fgsa-manifest.sh`. Add controls where:

- A public model-body edit fails despite an unchanged shallow hash.
- A theorem-proof-only edit passes.
- A wrong expected deep digest fails.
- A missing required baseline fails.

WP16 attributes **every** regenerated fingerprint, expected-name row, audit-scope row, import-policy row, and checker-data row. Each attribution gives the old/new value, changed declaration or dependency, reason, WP, and reviewed commit. Equal source text does not justify a changed fingerprint.

P13’s `--write` can refresh aggregate binder counts. Compare those counts independently with the accepted hypothesis-free aggregate. Preserve supplier scopes and names; preserve unrelated OPEN items.

Record all qualifying S0 byte changes, intermediate commits, parents, and merge resolutions in a separate port package. Do not rebase recorded history. Preserve both S0 byte manifests.

Final acceptance is one WP15+WP16 unit:

- `fgsaClaims (p) : FGSAClaims p`, without added hypotheses.
- All 48 leaf guarantees and both existing continuation companions.
- Complete source census reconciled with the compiled dependency closure.
- Shallow, frame, deep, P13, S0/history, axiom, equation, import, coverage, and non-vacuity checks.
- Zero PC-SA source and compiled statement-dependency change.
- NUC FULL and Mac `check-fg` at the same final commit.

This port touches the FG closure. The `check-fg` landing skip does not apply.

**Core correspondence and later outputs**

WP12a/WP12b establish the core simulation. Define:

`digestSpec(parent, slot, rows, raw, support) = digestLean(parent, slot, 0, rows, raw, support)`.

Apply the recursive embedding to all relevant wire objects and named ancestors, including adversarial and rejected deliveries. `unitCodec` alone only restricts honest inputs. Preserve signed identities, ordered lists, duplicates, exact parents, digest checks, roots, root order, and refusal behavior.

The initial simulation scope is initialized, ordered, always-awake scheduled runs, with:

- The fixed participant/seat map and parameter restrictions.
- Exact tick and cutoff order.
- Immediate self-delivery represented by Lean delivery events.
- Equality at matched cuts after those deliveries.
- Restart reset with durable `Λ` retained.
- Normalized record equal to spec `C`.

For claim transfer, construct a revised Lean execution for each spec execution in this scope. Preserve regimes, time bounds, and observations. Do not claim arbitrary-`Reachable` or arbitrary-app equivalence.

The atomic landing closes this **core** correspondence. Output simulation follows WP13.

WP13 adds an explicit saved-head trace monitor and getters. Its writer policy is fixed:

- Every awake node writes at vote time, committee member or otherwise.
- Sleeping nodes do not write.
- The vote write follows revocation and head selection.
- `ac_to_fg` writes after confirmation and head selection, before any no-source or suppressed-attestation return.
- Emission is not required.
- Proposal processing does not write.
- Restart resets the saved head to genesis.

The monitor must account for awake noncommittee nodes explicitly. The engine’s owned-seat `act` call cannot supply those writes by itself. Prove that monitor projection leaves the core run unchanged.

Use viable-head membership for the saved-head test. Membership in `fullTree` is insufficient. A fallback anchor can be an ancestor of a viable head.

WP14a proves, for valid represented states:

- `F ⪯ K ⪯ C`
- `K ⪯ H`
- `fc_root ⪯ H`
- `B ⪯ K ↔ B ⪯ C ∧ B ⪯ H`
- Clean and healed-suffix clamped safety from repaired record compatibility.
- Growth conditional on head inclusion at the endpoint.

WP14b starts only after a fallback-anchor derisk closes its exact read scope. It must cover receipts between duties, expiry, revocation, and frame changes. Scheduled HEAD coverage alone is insufficient.

**Forbid clamped safety from finality alone and all clamped monotonicity claims.** Sleeping-reader inclusion is false under the fixed writer policy. Awake-reader inclusion and availability remain separate targets; their candidate bounds are not yet established.

**Waves and main-merge checkpoints**

Count integration, data, and test writers in the limit of four.

```text
┌──────┬──────────────────────────────────────────────────────────────────────┐
│ Wave │ Work                                                                 │
├──────┼──────────────────────────────────────────────────────────────────────┤
│ 0A   │ 00a; then 00t. P13 prerequisite remains binding.                     │
│ 0B   │ 01a, 02, 12a independent pure work, 14p.                             │
│ 0C   │ 01b; 04a; remaining 12a. Then 03a after 01b.                         │
│ 0D   │ 00b; then 00c and all current generated data.                        │
│ 1A   │ SWITCH; 05a; then 05b.                                              │
│ 1B   │ 06a; then 05c and 03b; then 06b,03c,06c.                            │
│ 1C   │ 09a → 04b. No broad phase consumer starts before this handoff.       │
│ 1D   │ 07 Clean; 08 conditional Outage; 09b Healing; 11 Finality.           │
│ 1E   │ 10 WC; 12b simulation; 13v tests/inhabitation; remaining family work.│
│ 1F   │ 15 assembly; 16 final data; joint FULL; atomic landing.              │
│ 2    │ 13 saved head; 14a; 14b only after its separate derisk.               │
└──────┴──────────────────────────────────────────────────────────────────────┘
```

At four active writers, the data owner waits for a slot. Serialize all writes to generated data and facades.

Named synchronization points:

```text
┌────────┬──────────────────────────────────────────────────────────────────────┐
│ Point  │ Action                                                               │
├────────┼──────────────────────────────────────────────────────────────────────┤
│ M0     │ Verify checked P13 main; close P13 history; establish the port base. │
│ M1     │ Merge latest main after Stage 0; run FULL; capture pre-SWITCH basis. │
│ M2     │ Merge latest main after Shared and phase-helper closure.            │
│ M3     │ Merge latest main after family targets, simulation and fixtures.    │
│ M4     │ Merge latest main before final data generation and FULL.            │
│ M5     │ Gate the exact landing commit on both machines, then land atomically.│
└────────┴──────────────────────────────────────────────────────────────────────┘
```

At M2–M4, record conflicts and rerun every affected target. Renew affected reviews at the new fixed commit. Do not reuse invalidated evidence. After S0 history is recorded, use merges rather than rebases.

Verify that the NUC HOLD has been released before any gate starts. Retain lane locks, memory scopes, and slot limits. Do not infer current gate permission from the stale state snapshot.

**STOP checkpoints**

```text
┌──────────────────────┬────────────────────────────────────────────────────────┐
│ Checkpoint           │ STOP condition                                         │
├──────────────────────┼────────────────────────────────────────────────────────┤
│ Base and ownership   │ P13 is unchecked/open; a file lacks an owner; a package │
│                      │ has an unresolved backward dependency.                 │
│ Stage 0              │ Active behavior changes, or a new-reader import cycle   │
│                      │ appears.                                               │
│ SWITCH               │ A run proof still targets the old protocol, or a frame │
│                      │ consumer retains an unguarded inference.               │
│ Resolution           │ Ambiguity changes; correspondence claims unrestricted   │
│                      │ list, fast-set, or arbitrary-target equality.          │
│ Score/carry          │ F_dst ⪯ N is unavailable, or retention comes only from │
│                      │ candidate geometry or the score conclusion.            │
│ Phase                │ RXing/top retention is unavailable; F ⪯ W is missing; │
│                      │ a charge count or timing bound increases.              │
│ Combined suppliers   │ cpCompat loses its universal conclusion, or outage     │
│                      │ continuation needs a new slashing premise.             │
│ Claims               │ A new premise, weaker conclusion, larger bound, changed│
│                      │ read scope, equal-F assumption, or restored inactive    │
│                      │ contribution is required.                              │
│ Correspondence       │ Only honest inputs are embedded; root order changes;   │
│                      │ refusal/order fails; regimes or matched cuts differ.   │
│ PC-SA                │ Source, behavior, imported signatures, or compiled     │
│                      │ statement dependencies change.                         │
│ Freeze/data          │ A digest, fingerprint, name or data row is unexplained;│
│                      │ an S0 change is missing; a checker must be weakened.   │
│ Review/evidence      │ A main merge invalidates evidence without a recheck;   │
│                      │ pending data is presented as a FULL pass.              │
│ Saved head/clamp     │ Writes depend on emission or committee membership;     │
│                      │ sleeping nodes write; safety uses finality alone.      │
│ WP14b                │ The fallback derisk does not close every promised read.│
└──────────────────────┴────────────────────────────────────────────────────────┘
```

A STOP report gives the declaration, exact premises, failed obligation or counterexample, affected callers, and commit. The writer must preserve the failed evidence. A STOP does not authorize a contract change.

# Port plan r2 — lead rulings (addendum; binding for every port writer and reviewer)
Plan: codex/reports/reviews/plan-fgsa-port-r2-sol.md. Opus delta check: /Users/francesco/.claude/jobs/22f59f85/tmp/rev-portplan-opus-r2.md (GO-WITH-CHANGES). Rulings 2026-10-09 (fg-sa-manager, user asleep; revisable):
A. Frame target = option (a): the FrameNext declarations become the final frame surface. At SWITCH the aggregate's `frame` field and `FGFoundation.frame` point to them. RFrameExact/RFrame keep their text and become legacy (census class B, attributed). Record in advance the deep-digest exceptions FrameNext entries need at SWITCH.
B. S0-C: the spec frame correspondence relates only to `FGSA.Next` readers and to model parts unchanged by SWITCH; it must not unfold canonical controls, fullTree, liveRoot, headVote, proposerSupport.
C. `F/Model/Legacy/Frame.lean` must not import canonical `Model/Frame.lean`; it copies the complete legacy reader chain; a test checks `Legacy.X = X` on main before SWITCH.
D. S0-D regenerates `docs/GEN-API.md` (append-only). `docs/ARCHITECTURE.md` has ONE owner: the data owner (WP16 role). S0-D may start before P13 lands.
E. No fast service tier, ever (plan text that says otherwise is overridden). Standard effort.
F. There is no NUC hold (state.md has none); lane rules: GATE_LANE=1 full tier, GATE_LANE=2 merge tier; never set LEAN_THROTTLE_HELD; never lake update.
G. Writers never start reviews/agents/codex/claude processes, never push, never rebase landed commits; minimal diff, no reflow; commit trailer "Claude-Session: https://claude.ai/code/session_013Q1uFdsDSzNEnWtuKSn4fc".
