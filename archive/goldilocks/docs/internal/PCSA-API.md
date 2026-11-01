# PC-SA API manifest

_STALE-UNPORTED: last PC-SA snapshot from main `b3d56790`. See
`scripts/unported-libraries.txt`. Compiled checks resume after the sleep port._

_Statement manifest of the PC-SA claim surface (roadmap item 7). Not frozen._

This file lists every public declaration under the Statements prefixes of
`AvailableChainPCSA`, `AvailableChainPCSARun` and `AvailableChainPCSAClaims`,
under `AvailableChainPCSAClaims.Claims`, and in the claim facade
`AvailableChainPCSAClaims.PCSAClaims` (`PCSAClaims`, `PCSAStageTwoClaims`),
by fully qualified name and grouped by library and module. It uses the
FG-SA manifest rules (`docs/FGSA-API.md`). PC-SA has no anchor rule.

## Update rule

The PC-SA claim surface is not frozen. A commit that adds, changes or removes
a declaration in this scope must write this doc again in the same commit, so
that the diff of this doc shows each statement change. The check fails when
this doc and the code differ. A freeze copies this doc to
`docs/PCSA-API-frozen.md` and records its SHA-256 in
`scripts/pcsa-manifest-frozen.sha256`. Then the FG-SA append-only rule
applies, with allow lines in `scripts/pcsa-manifest-allow.txt`.

## How to check

`scripts/V2Manifest.lean` generates and checks this list.

- `lake env lean --run scripts/V2Manifest.lean --scope pcsa --list` prints
the module blocks from the environment, in source order, with hashes.
- `lake env lean --run scripts/V2Manifest.lean --scope pcsa --write` writes this doc.
- `lake env lean --run scripts/V2Manifest.lean --scope pcsa --check` checks
the names, modules, kinds, hashes and completeness (D15). A failed check
exits 1. A missing doc exits 2.
- `bash scripts/check-pcsa-manifest.sh` runs the check, then (when `NEG` is
not 0) checks that `--write` gives the same entry sections and runs negative
controls.

Each entry hash uses the shared hash rules in `scripts/V2Manifest.lean`:
types and definition values, generated or private helpers in the closure,
type binder names and infos, reducibility, and instance status. Theorem
proofs do not affect the hash. Public `_def` theorems are entries. Each public
structure projection is a separate `field` entry beside the structure entry.

## `AvailableChainPCSA`

### `AvailableChainPCSA.Statements.FinalityView`

```text
def AvailableChain.PCSA.pcsa_finalityView c01f372237d33806
theorem AvailableChain.PCSA.pcsa_finalityView_def 5d20d1e0acaabb9d
```

### `AvailableChainPCSA.Statements.Invariants`

```text
inductive AvailableChain.PCSA.Reachable af356bf7f6a1d262
ctor AvailableChain.PCSA.Reachable.init a3c2813df14b40f2
ctor AvailableChain.PCSA.Reachable.tick b6a319a258048c94
ctor AvailableChain.PCSA.Reachable.deliver 1296ff703ba47d71
def AvailableChain.PCSA.NestOK d708664fc34eabde
def AvailableChain.PCSA.SACompat 4f43bf9b0207fecc
def AvailableChain.PCSA.PCDom 8bb48ed23e881265
structure AvailableChain.PCSA.CStoreInv 808dfd06c752f585
ctor AvailableChain.PCSA.CStoreInv.mk 6452b6124fa836e8
field AvailableChain.PCSA.CStoreInv.fg dfc8739b2e7140e5
field AvailableChain.PCSA.CStoreInv.rootInj ff2021c78b527646
field AvailableChain.PCSA.CStoreInv.baseTree 327960899552375b
field AvailableChain.PCSA.CStoreInv.saCompat 01ff31166ee72d32
field AvailableChain.PCSA.CStoreInv.Smem 0329094e397d5dc5
field AvailableChain.PCSA.CStoreInv.pcDom 0f08f27e7092311f
field AvailableChain.PCSA.CStoreInv.genuineKeys a22842dffeac0ff0
field AvailableChain.PCSA.CStoreInv.leaseKeys ed518f1c0a4ebf2c
def AvailableChain.PCSA.Inv0 0612345acbb19759
structure AvailableChain.PCSA.MetaInv 74f4927a69f08577
ctor AvailableChain.PCSA.MetaInv.mk 81098b3248a4a689
field AvailableChain.PCSA.MetaInv.wireTree a1796182b9dad34b
field AvailableChain.PCSA.MetaInv.treeWire c15019098aa996f1
field AvailableChain.PCSA.MetaInv.proposalsNodup 2f07a8d43b99a1bc
field AvailableChain.PCSA.MetaInv.stampKeys 834f1dc18850b14a
field AvailableChain.PCSA.MetaInv.blocksNodup 1006d521e5cd1ae3
field AvailableChain.PCSA.MetaInv.poolDecodes bed8c0a3b8870ce0
field AvailableChain.PCSA.MetaInv.poolNodup 60dfafb190cc668b
field AvailableChain.PCSA.MetaInv.noGenesisWire 1e02754e690cbcab
def AvailableChain.PCSA.ContentAgree ea54863b55654d84
```

### `AvailableChainPCSA.Statements.Store`

```text
def AvailableChain.PCSA.OutputNestingStored 42001b993212ca9e
def AvailableChain.PCSA.StoreInvariant 226a020e89a6fcdb
structure AvailableChain.PCSA.StoreBundle 1d1888462a4e7edf
ctor AvailableChain.PCSA.StoreBundle.mk 73715ce87c8c1c10
field AvailableChain.PCSA.StoreBundle.cstore b9c6a434a622d025
field AvailableChain.PCSA.StoreBundle.meta cf751df8beea1bb0
field AvailableChain.PCSA.StoreBundle.nest 2af7deb17c541419
def AvailableChain.PCSA.pcsa_StoreBundleInvariant c82c8c451482c575
theorem AvailableChain.PCSA.pcsa_StoreBundleInvariant_def ee4dca3a4b8f3996
def AvailableChain.PCSA.FMonotone d47de7f5c541d454
def AvailableChain.PCSA.MetadataInvariant e853f17a63ecab6e
```

### `AvailableChainPCSA.Statements.WindowCertificate`

```text
def AvailableChain.PCSA.Window.pcsa_projectFinality edc9983017d851be
theorem AvailableChain.PCSA.Window.pcsa_projectFinality_def d4a95a399cfe491f
def AvailableChain.PCSA.Window.pcsa_projectCertEntry 8ff668202f2c16aa
theorem AvailableChain.PCSA.Window.pcsa_projectCertEntry_def 36a0d49ffc09f9fc
def AvailableChain.PCSA.Window.pcsa_certificateHeight ad358e9f68fe1967
theorem AvailableChain.PCSA.Window.pcsa_certificateHeight_def 70ed419d80128127
def AvailableChain.PCSA.Window.pcsa_certificateFinality 2aa2f7ada930169c
theorem AvailableChain.PCSA.Window.pcsa_certificateFinality_def 33fa24b6a1e58df3
def AvailableChain.PCSA.Window.pcsa_certificateFolded 1e2979e9cfd7547b
theorem AvailableChain.PCSA.Window.pcsa_certificateFolded_def 3994641567ac13fb
def AvailableChain.PCSA.Window.pcsa_certificateSelection efeb2dfef85e93e0
theorem AvailableChain.PCSA.Window.pcsa_certificateSelection_def 97f1cb7b489b66a4
def AvailableChain.PCSA.Window.pcsa_EntryOriginAt 1214349fbc241778
theorem AvailableChain.PCSA.Window.pcsa_EntryOriginAt_def 598c7b4d366edb3b
```

## `AvailableChainPCSARun`

### `AvailableChainPCSARun.Statements.Interface`

```text
def AvailableChain.PCSA.Run.pcsaInterface f6c4dfd26d9aceee
def AvailableChain.PCSA.Run.pcsaFinalizedOut be0eea944970074a
theorem AvailableChain.PCSA.Run.pcsaFinalizedOut_def 26c05d8dfecbae3a
```

### `AvailableChainPCSARun.Statements.Roots`

```text
def AvailableChain.PCSA.Run.DirectNamedProposalInRun cb40c573f7b81e2f
def AvailableChain.PCSA.Run.NamedProposalInRun 22677e4736e963a2
structure AvailableChain.PCSA.Run.NamedRootCollisionFree 861dba6558139987
ctor AvailableChain.PCSA.Run.NamedRootCollisionFree.mk e64f62a4f7b39086
field AvailableChain.PCSA.Run.NamedRootCollisionFree.root_injective c1db6aad4ed4379b
def AvailableChain.PCSA.Run.DirectRootBlockInRun 34435a972f0f0b2b
def AvailableChain.PCSA.Run.RootBlockInRun 15d38cca0b4c22d2
```

## `AvailableChainPCSAClaims`

### `AvailableChainPCSAClaims.Claims.AcFrame`

```text
def AvailableChain.PCSA.Run.AcOnlyFrameClaim ff695e1ce973d49c
theorem AvailableChain.PCSA.Run.AcOnlyFrameClaim_def 14c1c9c9ff4ed334
```

### `AvailableChainPCSAClaims.Claims.Clean`

```text
def AvailableChain.PCSA.Run.PCSnapshotStampClaim 732330527a02f73e
theorem AvailableChain.PCSA.Run.PCSnapshotStampClaim_def 33aae28c534e2a68
structure AvailableChain.PCSA.Run.CleanInvariantAt 66d0b47c4eecaef2
ctor AvailableChain.PCSA.Run.CleanInvariantAt.mk 29a4e6ca0f7ca932
field AvailableChain.PCSA.Run.CleanInvariantAt.resultsChain 56d5af38137e74fe
field AvailableChain.PCSA.Run.CleanInvariantAt.headsAbove db4606aaaf4b5f07
field AvailableChain.PCSA.Run.CleanInvariantAt.headsEqual 2a060cad46ef4fa1
field AvailableChain.PCSA.Run.CleanInvariantAt.pcAck 3a2e3588376cf4dd
field AvailableChain.PCSA.Run.CleanInvariantAt.pcChain ba1cb0160ffa6d99
field AvailableChain.PCSA.Run.CleanInvariantAt.pcResults e789b182ef7581cb
field AvailableChain.PCSA.Run.CleanInvariantAt.leaseBelowResult b85535255ee89737
field AvailableChain.PCSA.Run.CleanInvariantAt.leaseCompatible 23b48b96e52c3ea4
field AvailableChain.PCSA.Run.CleanInvariantAt.lockWriteAll 00ee0422953f71be
field AvailableChain.PCSA.Run.CleanInvariantAt.lockKeep aebeba7c314e8f43
field AvailableChain.PCSA.Run.CleanInvariantAt.recordOrigin 4d60b108335e2ea3
field AvailableChain.PCSA.Run.CleanInvariantAt.recordMono 59238bb202d2ad5f
field AvailableChain.PCSA.Run.CleanInvariantAt.recordCompatible 3d496b311f81d505
field AvailableChain.PCSA.Run.CleanInvariantAt.roots 1fbbecc6deddb192
def AvailableChain.PCSA.Run.FormationConcl cb8cdb500acbcc71
theorem AvailableChain.PCSA.Run.FormationConcl_def b6da8480e3fa5ba7
def AvailableChain.PCSA.Run.CleanInvariantClaim 0a2ea45e4cddb170
theorem AvailableChain.PCSA.Run.CleanInvariantClaim_def f0c03c4d96af0af2
def AvailableChain.PCSA.Run.FormationClaim eab377bc3d5cb264
theorem AvailableChain.PCSA.Run.FormationClaim_def 08e936e360d82d99
def AvailableChain.PCSA.Run.CleanDisseminationClaim 9a1ea3c5c6484697
theorem AvailableChain.PCSA.Run.CleanDisseminationClaim_def 4bb242aef0b0bf23
def AvailableChain.PCSA.Run.PCSACleanSafetyClaim e3934a3f05f0ec0e
theorem AvailableChain.PCSA.Run.PCSACleanSafetyClaim_def c50fe34b8a130e95
def AvailableChain.PCSA.Run.PCSACleanInclusionClaim 4069ee5460286b1a
theorem AvailableChain.PCSA.Run.PCSACleanInclusionClaim_def 39d8b678ae6f3039
def AvailableChain.PCSA.Run.StrongIncludedClaim 390afc56c4c23f34
theorem AvailableChain.PCSA.Run.StrongIncludedClaim_def 87827fe228b6d984
def AvailableChain.PCSA.Run.CleanResultsNonemptyClaim 0a3612b39473aed4
theorem AvailableChain.PCSA.Run.CleanResultsNonemptyClaim_def 3778269113aa1f1d
def AvailableChain.PCSA.Run.CleanResultsChainPendingClaim 306f9ce0f29ba746
theorem AvailableChain.PCSA.Run.CleanResultsChainPendingClaim_def 0d90537b89b5ea6a
def AvailableChain.PCSA.Run.CleanDisseminationPendingClaim 65dab35403a93ee2
theorem AvailableChain.PCSA.Run.CleanDisseminationPendingClaim_def 679a14dddb81c495
def AvailableChain.PCSA.Run.CleanBlockReceiptClaim fcc6c53e56d2abbb
theorem AvailableChain.PCSA.Run.CleanBlockReceiptClaim_def 3a310d3a15393af9
```

### `AvailableChainPCSAClaims.Claims.Finality`

```text
def AvailableChain.PCSA.Run.FormationSourceClaim 32a560a2c2190e3b
theorem AvailableChain.PCSA.Run.FormationSourceClaim_def 6c247bb3a0f31bfc
def AvailableChain.PCSA.Run.CleanSourceTransferClaim eb9e61ec971a7b3e
theorem AvailableChain.PCSA.Run.CleanSourceTransferClaim_def 9f0b5dddf26469d1
def AvailableChain.PCSA.Run.HealedSourceTransferClaim 6674f78be2444486
theorem AvailableChain.PCSA.Run.HealedSourceTransferClaim_def 5d41368959ae155b
def AvailableChain.PCSA.Run.Q0PCSelectionClaim dd33a60e32ca8bd4
theorem AvailableChain.PCSA.Run.Q0PCSelectionClaim_def d0f759fa700d8ca7
def AvailableChain.PCSA.Run.Q0PCClaim bae13b6f616c6cf7
theorem AvailableChain.PCSA.Run.Q0PCClaim_def 2892e97cfe8d346c
def AvailableChain.PCSA.Run.PCSAPureAccountableClaim a2dce5e6f103f48e
theorem AvailableChain.PCSA.Run.PCSAPureAccountableClaim_def 79792689c5e5beb9
def AvailableChain.PCSA.Run.PCSAPureAgreementClaim 8d7cdb518f0a4418
theorem AvailableChain.PCSA.Run.PCSAPureAgreementClaim_def 76014b66d16c18f6
def AvailableChain.PCSA.Run.PCSAWholeRunAccountableClaim c29649bc56864c50
theorem AvailableChain.PCSA.Run.PCSAWholeRunAccountableClaim_def ffa70776e8731537
def AvailableChain.PCSA.Run.PCSAWholeRunAgreementClaim 593f97ecd4c779c8
theorem AvailableChain.PCSA.Run.PCSAWholeRunAgreementClaim_def a158805f7f298342
def AvailableChain.PCSA.Run.PCSAEventPrefixAgreementClaim cc561b16dba7bfe7
theorem AvailableChain.PCSA.Run.PCSAEventPrefixAgreementClaim_def 2b9acc3ee12eebd8
def AvailableChain.PCSA.Run.PCSAFinalizedMonotoneClaim 2c2f37cb348b511f
theorem AvailableChain.PCSA.Run.PCSAFinalizedMonotoneClaim_def 1d773bb19942130b
def AvailableChain.PCSA.Run.PCSAFaultCountSlashableBoundClaim 886cbe4ad10c174d
theorem AvailableChain.PCSA.Run.PCSAFaultCountSlashableBoundClaim_def 92b33561f3a71169
def AvailableChain.PCSA.Run.PCSAHonestNeverSlashedClaim 80f68fed3ef20ace
theorem AvailableChain.PCSA.Run.PCSAHonestNeverSlashedClaim_def c0574cf1f30ace50
structure AvailableChain.PCSA.Run.PCSAFinalitySafetyClaims a156318428bef940
ctor AvailableChain.PCSA.Run.PCSAFinalitySafetyClaims.mk 7ec738539342ddc9
field AvailableChain.PCSA.Run.PCSAFinalitySafetyClaims.accountable f2bd5ffa19e6c036
field AvailableChain.PCSA.Run.PCSAFinalitySafetyClaims.agreement a89544798f584cd9
field AvailableChain.PCSA.Run.PCSAFinalitySafetyClaims.runAccountable 12bd7ff3a67ee116
field AvailableChain.PCSA.Run.PCSAFinalitySafetyClaims.runAgreement 8d9c82fa6458cbb4
field AvailableChain.PCSA.Run.PCSAFinalitySafetyClaims.eventPrefixAgreement 49de1c5988428691
field AvailableChain.PCSA.Run.PCSAFinalitySafetyClaims.finalizedMonotone c3c1a508ad41d33e
field AvailableChain.PCSA.Run.PCSAFinalitySafetyClaims.faultCountSlashableBound 2fe6194bb755c193
field AvailableChain.PCSA.Run.PCSAFinalitySafetyClaims.honestNeverSlashed 8667493b81b61ed0
```

### `AvailableChainPCSAClaims.Claims.Outage`

```text
def AvailableChain.PCSA.Run.ArmPersistenceClaim 7d47456e13b57be2
theorem AvailableChain.PCSA.Run.ArmPersistenceClaim_def d5b03ded00201788
def AvailableChain.PCSA.Run.ArmHealthyClaim 992ec3dcc79e6c09
theorem AvailableChain.PCSA.Run.ArmHealthyClaim_def 1728e6d6bf22dc1e
def AvailableChain.PCSA.Run.PCSASlowP1Claim 3189d3bbae545725
theorem AvailableChain.PCSA.Run.PCSASlowP1Claim_def 3667a119ef890b01
```

### `AvailableChainPCSAClaims.Claims.PC`

```text
def AvailableChain.PCSA.Run.PCUniquenessClaim 209e8175aaea19fd
theorem AvailableChain.PCSA.Run.PCUniquenessClaim_def 22de6449a6209104
def AvailableChain.PCSA.Run.OneAckPerSlotClaim 1ab08e9df8941327
theorem AvailableChain.PCSA.Run.OneAckPerSlotClaim_def 618255dd06b29489
def AvailableChain.PCSA.Run.PCDisseminationClaim 09bc5edd3d3fce89
theorem AvailableChain.PCSA.Run.PCDisseminationClaim_def f45509656636f453
def AvailableChain.PCSA.Run.OutputNestingClaim a389c2a1fadfd6b0
theorem AvailableChain.PCSA.Run.OutputNestingClaim_def d1f6e3f89f4678d0
def AvailableChain.PCSA.Run.AvailableMonotoneClaim 3ccf989433e54d4b
theorem AvailableChain.PCSA.Run.AvailableMonotoneClaim_def 8f83fe17b9c2e7c6
def AvailableChain.PCSA.Run.LeaseBelowRecordClaim da75a73e5ec25a7e
theorem AvailableChain.PCSA.Run.LeaseBelowRecordClaim_def 34a16d746b55e10d
structure AvailableChain.PCSA.Run.PCSAPCClaims 9a642f6c1d7f608a
ctor AvailableChain.PCSA.Run.PCSAPCClaims.mk 342b2d3278cd2cfd
field AvailableChain.PCSA.Run.PCSAPCClaims.pcUnique a1d6cef9abd08c59
field AvailableChain.PCSA.Run.PCSAPCClaims.oneAck b7f92b679353c671
field AvailableChain.PCSA.Run.PCSAPCClaims.dissemination 5188dbb2e6e6a2ed
field AvailableChain.PCSA.Run.PCSAPCClaims.outputNesting f52224bd63923249
field AvailableChain.PCSA.Run.PCSAPCClaims.availableMonotone 2edc221b18f666dc
field AvailableChain.PCSA.Run.PCSAPCClaims.leaseBelowRecord f26bd6bd6df08fd0
```

### `AvailableChainPCSAClaims.Claims.Recovery`

```text
def AvailableChain.PCSA.Run.HealedFrom 823cd36ca0a98002
theorem AvailableChain.PCSA.Run.HealedFrom_def 3d5ef20bbc75a5ba
structure AvailableChain.PCSA.Run.ShortBreakPrem 72251b865d8072e9
ctor AvailableChain.PCSA.Run.ShortBreakPrem.mk 29ff87d70379944c
field AvailableChain.PCSA.Run.ShortBreakPrem.recovery 85d49d14c5827186
field AvailableChain.PCSA.Run.ShortBreakPrem.frame 754a684459370a41
field AvailableChain.PCSA.Run.ShortBreakPrem.anchorPos 69e541ba0117360a
field AvailableChain.PCSA.Run.ShortBreakPrem.anchorProposer 16e11d38cac9f236
field AvailableChain.PCSA.Run.ShortBreakPrem.anchorClean f14da246041b5fd8
field AvailableChain.PCSA.Run.ShortBreakPrem.anchorPart 2a2e685da4d6e8cb
field AvailableChain.PCSA.Run.ShortBreakPrem.firstProposer f3ba78e72a7e70f2
field AvailableChain.PCSA.Run.ShortBreakPrem.firstAfterGST 57dc64b346b3be92
field AvailableChain.PCSA.Run.ShortBreakPrem.firstMin 0f1bda41dafa11a3
field AvailableChain.PCSA.Run.ShortBreakPrem.order 93052044d06a74f8
field AvailableChain.PCSA.Run.ShortBreakPrem.window 6ff53ce9e0aef4df
field AvailableChain.PCSA.Run.ShortBreakPrem.horizon a0ad9450d734bd7f
def AvailableChain.PCSA.Run.FastRecoveredClaim b0a61e869ba7fc33
theorem AvailableChain.PCSA.Run.FastRecoveredClaim_def f2ffc90aecaf339a
def AvailableChain.PCSA.Run.LongBreakRecoveredClaim b1ba2e17e858d8b9
theorem AvailableChain.PCSA.Run.LongBreakRecoveredClaim_def 920cc83fb8585f9c
```

### `AvailableChainPCSAClaims.Claims.StageTwo`

```text
def AvailableChain.PCSA.Run.JStable 9fec9bd99766a939
theorem AvailableChain.PCSA.Run.JStable_def 8e3b9d71c3d2066d
def AvailableChain.PCSA.Run.ArmPersistenceJStableClaim d2405bed01874469
theorem AvailableChain.PCSA.Run.ArmPersistenceJStableClaim_def 9ee97d9d9d4e91e8
def AvailableChain.PCSA.Run.ArmHealthyStageTwoClaim 4194de4a33646ba3
theorem AvailableChain.PCSA.Run.ArmHealthyStageTwoClaim_def 0ee88469092e3c27
def AvailableChain.PCSA.Run.StrongIncludedStageTwoClaim c31017fc1ae91476
theorem AvailableChain.PCSA.Run.StrongIncludedStageTwoClaim_def 1f7ca394ee92a9ab
```

### `AvailableChainPCSAClaims.PCSAClaims`

```text
structure AvailableChain.PCSA.Run.PCSAClaims a517e0d7e97e7e8d
field AvailableChain.PCSA.Run.PCSAClaims.toPCSAPCClaims e8587242edd52e8f
ctor AvailableChain.PCSA.Run.PCSAClaims.mk f2907a633860bb57
field AvailableChain.PCSA.Run.PCSAClaims.acOnlyFrame 8472fc3f76e03bf6
field AvailableChain.PCSA.Run.PCSAClaims.snapshotStamp 20be37da448f968f
field AvailableChain.PCSA.Run.PCSAClaims.cleanInvariant 034eec91d406e4dd
field AvailableChain.PCSA.Run.PCSAClaims.formation 81c05f964b1fac5f
field AvailableChain.PCSA.Run.PCSAClaims.cleanDissemination d2ce22e7e0d5e6bf
field AvailableChain.PCSA.Run.PCSAClaims.cleanSafety 83a43f0beed1e82c
field AvailableChain.PCSA.Run.PCSAClaims.cleanInclusion ebd9d5a84e23225d
field AvailableChain.PCSA.Run.PCSAClaims.strongIncluded 2ad2bf09af83ee32
field AvailableChain.PCSA.Run.PCSAClaims.armPersistence 1f6911a8f9466406
field AvailableChain.PCSA.Run.PCSAClaims.armHealthy 0955b72b4aad848e
field AvailableChain.PCSA.Run.PCSAClaims.slowP1 30524e0412e4bdbe
field AvailableChain.PCSA.Run.PCSAClaims.fastRecovered 1b54d610c10dd303
field AvailableChain.PCSA.Run.PCSAClaims.longBreakRecovered c888d5af872c58c1
field AvailableChain.PCSA.Run.PCSAClaims.formationSource 1fb278eb184c6997
field AvailableChain.PCSA.Run.PCSAClaims.cleanSourceTransfer 95686a35978a5e12
field AvailableChain.PCSA.Run.PCSAClaims.healedSourceTransfer a239062ba7bf489a
field AvailableChain.PCSA.Run.PCSAClaims.q0PCSelection 9c00cf686200c776
field AvailableChain.PCSA.Run.PCSAClaims.q0PC 01338a48f3cbad12
field AvailableChain.PCSA.Run.PCSAClaims.finality 85b521ce0abd7569
structure AvailableChain.PCSA.Run.PCSAStageTwoClaims 111b28ccfdfbbe4f
ctor AvailableChain.PCSA.Run.PCSAStageTwoClaims.mk 75286a61cf74598b
field AvailableChain.PCSA.Run.PCSAStageTwoClaims.armPersistence 5c1ce586e50ea7d6
field AvailableChain.PCSA.Run.PCSAStageTwoClaims.armHealthy a8fd9e704a12d890
field AvailableChain.PCSA.Run.PCSAStageTwoClaims.strongIncluded dcce841ddd1efc48
```

### `AvailableChainPCSAClaims.Statements.FinalityApi`

```text
def AvailableChain.PCSA.Run.PCFinalizedAt 52803cf4cb13dc07
theorem AvailableChain.PCSA.Run.pcsa_PCFinalizedAt_def d02381a3008d5fc9
def AvailableChain.PCSA.Run.PCFinalityBlock 67ff9d0da3eefeef
theorem AvailableChain.PCSA.Run.pcsa_PCFinalityBlock_def b0f10a09fd32e666
def AvailableChain.PCSA.Run.pcFinalityRows 76f22b3f8ce5be48
theorem AvailableChain.PCSA.Run.pcsa_pcFinalityRows_def 15fda4e4bf3689d2
def AvailableChain.PCSA.Run.PCFinalitySlashableBound 00de6a83b43e31b5
theorem AvailableChain.PCSA.Run.pcsa_PCFinalitySlashableBound_def 35c0ebe532f06a28
def AvailableChain.PCSA.Run.PCFinalityExecution 0194aec18a69ce5a
theorem AvailableChain.PCSA.Run.pcsa_PCFinalityExecution_def 0efb65b82de25262
def AvailableChain.PCSA.Run.PCWholeRunAccountable 8de64352410ecdd4
theorem AvailableChain.PCSA.Run.pcsa_PCWholeRunAccountable_def 0edd7af6a9240530
def AvailableChain.PCSA.Run.PCWholeRunAgreement d95420c97c4ed7fe
theorem AvailableChain.PCSA.Run.pcsa_PCWholeRunAgreement_def 4c41700490880428
```

### `AvailableChainPCSAClaims.Statements.LaneReads`

```text
def AvailableChain.PCSA.Run.storeBefore 13341049873c8236
theorem AvailableChain.PCSA.Run.pcsa_storeBefore_def b871172daf99454b
def AvailableChain.PCSA.Run.voteHeadAt 2e9390063c67294a
theorem AvailableChain.PCSA.Run.pcsa_voteHeadAt_def b88db629928a4ffd
def AvailableChain.PCSA.Run.viewAt 8678e57675dff61c
theorem AvailableChain.PCSA.Run.pcsa_viewAt_def 0bbff01c7816098a
def AvailableChain.PCSA.Run.liveRootAt ccfb7ad11a2906e6
theorem AvailableChain.PCSA.Run.pcsa_liveRootAt_def 79bf2f3d54ef5d7b
def AvailableChain.PCSA.Run.nTargetAt 72bf89d285a05ae6
theorem AvailableChain.PCSA.Run.pcsa_nTargetAt_def 038b5af87d786ad0
def AvailableChain.PCSA.Run.ackAt 0145fd7b41e82892
theorem AvailableChain.PCSA.Run.pcsa_ackAt_def 867ab6b6206bbee1
def AvailableChain.PCSA.Run.HonestAckAt eefbf1a199450a86
theorem AvailableChain.PCSA.Run.pcsa_HonestAckAt_def 031d6309eb952e6e
def AvailableChain.PCSA.Run.HonestHeadAt 80266c3a91d8525a
theorem AvailableChain.PCSA.Run.pcsa_HonestHeadAt_def ed42373767b500f3
def AvailableChain.PCSA.Run.gateInAt 181d7c0b7eedf33f
theorem AvailableChain.PCSA.Run.pcsa_gateInAt_def 4a28f053b92da85d
def AvailableChain.PCSA.Run.gateResultAt e5107ba56c58491e
theorem AvailableChain.PCSA.Run.pcsa_gateResultAt_def d25403a06136a276
def AvailableChain.PCSA.Run.PCStampedBefore 1b35e07942f97cea
theorem AvailableChain.PCSA.Run.pcsa_PCStampedBefore_def d74a8be62087a637
def AvailableChain.PCSA.Run.actionSourceAt 0ae7c6a1462e0b5c
theorem AvailableChain.PCSA.Run.pcsa_actionSourceAt_def e95e76794e7e53eb
def AvailableChain.PCSA.Run.HonestStatesFrom e850c44944f65943
theorem AvailableChain.PCSA.Run.pcsa_HonestStatesFrom_def e9b754ba6e38b5f0
def AvailableChain.PCSA.Run.HonestStatesThrough daa600f003c66475
theorem AvailableChain.PCSA.Run.pcsa_HonestStatesThrough_def 0f25f515ce231880
def AvailableChain.PCSA.Run.HeldJustification 3aa22f36ffa64801
theorem AvailableChain.PCSA.Run.pcsa_HeldJustification_def d1b5dc196a2f48aa
def AvailableChain.PCSA.LiveLease ad088f160da401a8
theorem AvailableChain.PCSA.pcsa_LiveLease_def e03984ff72f6fcf3
```

### `AvailableChainPCSAClaims.Statements.OutageItems`

```text
def AvailableChain.PCSA.LockRow d1624a7c94a59ccd
theorem AvailableChain.PCSA.LockRow_def fd9ee0ff8a00a84c
def AvailableChain.PCSA.Run.CleanHeldPCRelay f486819be3935e2c
theorem AvailableChain.PCSA.Run.CleanHeldPCRelay_def 9a512cf41d452de1
def AvailableChain.PCSA.Run.CleanArmAcks edbf0c14d4c9e165
theorem AvailableChain.PCSA.Run.CleanArmAcks_def 625e99bb11bc128a
def AvailableChain.PCSA.Run.CleanArmItems 014134844516c064
theorem AvailableChain.PCSA.Run.CleanArmItems_def a017af64c66664c9
def AvailableChain.PCSA.Run.CleanRelayItems 437aa1b7229b5905
theorem AvailableChain.PCSA.Run.CleanRelayItems_def ccfe860da7adbe84
structure AvailableChain.PCSA.Run.CleanSlowBoundary 633f6c7e8c1261f9
ctor AvailableChain.PCSA.Run.CleanSlowBoundary.mk 8ba21a2f78bcd9b3
field AvailableChain.PCSA.Run.CleanSlowBoundary.pending 0ddc0e87d866c6cb
field AvailableChain.PCSA.Run.CleanSlowBoundary.first 564d02d31770ffa7
field AvailableChain.PCSA.Run.CleanSlowBoundary.window 6469688111be05fc
field AvailableChain.PCSA.Run.CleanSlowBoundary.stable 909af95b9e7c3482
field AvailableChain.PCSA.Run.CleanSlowBoundary.locks 24c4976f1589431a
field AvailableChain.PCSA.Run.CleanSlowBoundary.tree 415ad01595b9e9c1
field AvailableChain.PCSA.Run.CleanSlowBoundary.saved fb12899c6e265194
field AvailableChain.PCSA.Run.CleanSlowBoundary.result 48bfc9a213dba983
field AvailableChain.PCSA.Run.CleanSlowBoundary.acks e4cc2b086b322e87
field AvailableChain.PCSA.Run.CleanSlowBoundary.heads dca0ea586384686f
field AvailableChain.PCSA.Run.CleanSlowBoundary.pendingHeads 9554b0f9bfe98181
def AvailableChain.PCSA.Run.CleanSlowItems 534229c226ba3542
theorem AvailableChain.PCSA.Run.CleanSlowItems_def 3f7bc9ccc35d7944
```

### `AvailableChainPCSAClaims.Statements.Premises`

```text
def AvailableChain.PCSA.Run.IsNonRow 5ff6adcc713fe9ff
theorem AvailableChain.PCSA.Run.pcsa_IsNonRow_def 12e59365c6a7ac23
def AvailableChain.PCSA.Run.HonestNamedProposal 44d0249ad2543248
theorem AvailableChain.PCSA.Run.pcsa_HonestNamedProposal_def 6ee3cbed8a46bb15
def AvailableChain.PCSA.Run.FormationRootReachable 103fcb157ae2235c
structure AvailableChain.PCSA.Run.FormationPrem 0ec792f1dbf3c8b5
ctor AvailableChain.PCSA.Run.FormationPrem.mk 4bc7d664bd9f84e8
field AvailableChain.PCSA.Run.FormationPrem.base 7c4b092dc163f877
field AvailableChain.PCSA.Run.FormationPrem.quarterCap a0ad8dde404f1fac
field AvailableChain.PCSA.Run.FormationPrem.frame 2798151296e9a5f2
field AvailableChain.PCSA.Run.FormationPrem.slotPos f8f59f79f9c7d9a4
field AvailableChain.PCSA.Run.FormationPrem.horizon 8a67e989b332121b
field AvailableChain.PCSA.Run.FormationPrem.deltaF 28175081cf6fa7cd
field AvailableChain.PCSA.Run.FormationPrem.proposal 6896451a097bb02b
field AvailableChain.PCSA.Run.FormationPrem.delivery 13c3204d03eab0ac
field AvailableChain.PCSA.Run.FormationPrem.participation b83dcec527d26041
field AvailableChain.PCSA.Run.FormationPrem.commonView b129da707229c82e
field AvailableChain.PCSA.Run.FormationPrem.proposerRootReachable e18687e9743d0f5d
field AvailableChain.PCSA.Run.FormationPrem.leases af68f1f26801003a
structure AvailableChain.PCSA.Run.Arm c25c25b4c80c3403
ctor AvailableChain.PCSA.Run.Arm.mk 7cf8bc62c933abeb
field AvailableChain.PCSA.Run.Arm.stamped c2bc75d374dc2c83
field AvailableChain.PCSA.Run.Arm.acks 43ff30a2faf74d02
def AvailableChain.PCSA.Run.ArmConcl 25133e5d10e3f406
theorem AvailableChain.PCSA.Run.pcsa_ArmConcl_def 34f51a7c5dd99c66
def AvailableChain.PCSA.Run.Q0PCConcl bd592be2c9f6c136
theorem AvailableChain.PCSA.Run.pcsa_Q0PCConcl_def 346f73094b63d906
structure AvailableChain.PCSA.Run.Q0PCPackage 6c63588a8a5fbedb
ctor AvailableChain.PCSA.Run.Q0PCPackage.mk 255ab60cc43b6209
field AvailableChain.PCSA.Run.Q0PCPackage.proposal 200a1253d5c40efb
field AvailableChain.PCSA.Run.Q0PCPackage.afterReset ca81f73ccf577d18
field AvailableChain.PCSA.Run.Q0PCPackage.lift c4dcc4b0ff94f86c
field AvailableChain.PCSA.Run.Q0PCPackage.high 54086fd659f8c93a
field AvailableChain.PCSA.Run.Q0PCPackage.liftHeld ec74b1db855ca04f
field AvailableChain.PCSA.Run.Q0PCPackage.window c96eb245d0e58bfd
field AvailableChain.PCSA.Run.Q0PCPackage.horizon c272c32d19360188
field AvailableChain.PCSA.Run.Q0PCPackage.healing 7440303c4e9c22a7
field AvailableChain.PCSA.Run.Q0PCPackage.h2' be8d2537abeb333d
field AvailableChain.PCSA.Run.Q0PCPackage.fCover df5d1d70d1f4034b
field AvailableChain.PCSA.Run.Q0PCPackage.cap b1da191baf3355be
field AvailableChain.PCSA.Run.Q0PCPackage.muBound 0e343f294a60783e
field AvailableChain.PCSA.Run.Q0PCPackage.ff2 b0772b113c36bf37
field AvailableChain.PCSA.Run.Q0PCPackage.ff2C 62d5bdf53fd41af8
field AvailableChain.PCSA.Run.Q0PCPackage.transfer a71f72c7320d203b
structure AvailableChain.PCSA.Run.HealedSourcePrem ff245e66f5d306aa
ctor AvailableChain.PCSA.Run.HealedSourcePrem.mk 1d0ea387642ac128
field AvailableChain.PCSA.Run.HealedSourcePrem.recovery d6210b0e514d60c9
field AvailableChain.PCSA.Run.HealedSourcePrem.proposal e3f7b7bc65783005
field AvailableChain.PCSA.Run.HealedSourcePrem.horizon 2db39c23597f3063
field AvailableChain.PCSA.Run.HealedSourcePrem.afterGST f9e41eef0f6efa04
field AvailableChain.PCSA.Run.HealedSourcePrem.participation 14a96d7f223aeb30
field AvailableChain.PCSA.Run.HealedSourcePrem.commonView ce7ed766aab039ef
field AvailableChain.PCSA.Run.HealedSourcePrem.proposerRootReachable 6c2bff4b45d798b5
field AvailableChain.PCSA.Run.HealedSourcePrem.locks 1b9c76031c8c0420
field AvailableChain.PCSA.Run.HealedSourcePrem.equalFrames 52f1bc7847916901
field AvailableChain.PCSA.Run.HealedSourcePrem.fCompat f731545f8995cf77
field AvailableChain.PCSA.Run.HealedSourcePrem.frameActive 9b6746e0f37feb15
```

### `AvailableChainPCSAClaims.Statements.Reads`

```text
def AvailableChain.PCSA.Run.cutPred 4dd4a051b928d445
def AvailableChain.PCSA.Run.afterTicksIdx 260a9b23ba0adfb6
def AvailableChain.PCSA.Run.afterTicks 9aee93c8f02d21b6
def AvailableChain.PCSA.Run.pcsa_preTick 4dfb93b680469037
theorem AvailableChain.PCSA.Run.pcsa_preTick_def bed338a0d904fc93
def AvailableChain.PCSA.Run.pcsa_postClock 175f1e78dcec0ed8
theorem AvailableChain.PCSA.Run.pcsa_postClock_def 45c1a7439705c865
def AvailableChain.PCSA.Run.storeAt a35f5f08fadf1711
theorem AvailableChain.PCSA.Run.storeAt_def 97fe24d90a49311b
def AvailableChain.PCSA.Run.storeAfterTicks 37bef5a4cfab6417
theorem AvailableChain.PCSA.Run.storeAfterTicks_def 8a777ccdae87fac0
def AvailableChain.PCSA.Run.ackObj 6c5ecde36e91b23f
theorem AvailableChain.PCSA.Run.ackObj_def fd36b87e5d85f1c9
```

### `AvailableChainPCSAClaims.Statements.Regimes`

```text
structure AvailableChain.PCSA.Run.Base₂ 069c4736b8218725
ctor AvailableChain.PCSA.Run.Base₂.mk c11115576d5c3c24
field AvailableChain.PCSA.Run.Base₂.valid 8c06d89525e79a8c
field AvailableChain.PCSA.Run.Base₂.linked ab83d2f1fe01516a
field AvailableChain.PCSA.Run.Base₂.cstar 010dc8f3df9f0a89
field AvailableChain.PCSA.Run.Base₂.noRestart 04fbc85ce684be68
field AvailableChain.PCSA.Run.Base₂.delta e233fb4ad919c08e
field AvailableChain.PCSA.Run.Base₂.idealization 4855eea45b7f14f8
def AvailableChain.PCSA.Run.pcsaDelay 67c799b7e6e9adc3
theorem AvailableChain.PCSA.Run.pcsaDelay_def aa5c278eab6d7de4
def AvailableChain.PCSA.Run.FaultsBelowQA 828dc0d6daa1aa21
theorem AvailableChain.PCSA.Run.FaultsBelowQA_def 6e32bb6c4493d987
def AvailableChain.PCSA.Run.FGSafetyBound 6bf9819b6a228fb9
theorem AvailableChain.PCSA.Run.FGSafetyBound_def 1f4b533a566d9e99
def AvailableChain.PCSA.Run.awakeHonestLabel 7e42553833a223e6
theorem AvailableChain.PCSA.Run.pcsa_awakeHonestLabel_def d15bfd4703ca8b26
structure AvailableChain.PCSA.Run.Clean₂ 8db526fc7ed523dd
ctor AvailableChain.PCSA.Run.Clean₂.mk aff3834cfebacec5
field AvailableChain.PCSA.Run.Clean₂.base f1b4de1843fdcecd
field AvailableChain.PCSA.Run.Clean₂.cut 376c9e2e25eb9e6c
field AvailableChain.PCSA.Run.Clean₂.healthy 6bcd4d398f8a4fff
field AvailableChain.PCSA.Run.Clean₂.deltaF 16eb1c5419776f43
field AvailableChain.PCSA.Run.Clean₂.labels d5361e05366a15e8
def AvailableChain.PCSA.Run.QuarterCap 1cd7c2835c528126
theorem AvailableChain.PCSA.Run.QuarterCap_def 9a4fd0410badd8ec
def AvailableChain.PCSA.Run.FrameVacuous fafc02f0eccac01a
theorem AvailableChain.PCSA.Run.FrameVacuous_def 326529721f0301d4
def AvailableChain.PCSA.Run.StageOneFrame 4be9295f5c1d4364
theorem AvailableChain.PCSA.Run.StageOneFrame_def 8b4f793b6acf9d7e
def AvailableChain.PCSA.Run.pcsaL 9cbd736d8c53fdfc
theorem AvailableChain.PCSA.Run.pcsaL_def 1fefffa0bc209419
structure AvailableChain.PCSA.Run.Outage₂ f42c743d0c4c15a2
ctor AvailableChain.PCSA.Run.Outage₂.mk d8df43d2dec2bc50
field AvailableChain.PCSA.Run.Outage₂.pre ce35e25fa9a2b9b6
field AvailableChain.PCSA.Run.Outage₂.order a8b0a6ee3f7fb9d9
field AvailableChain.PCSA.Run.Outage₂.lag b3a15c73d316c4ac
field AvailableChain.PCSA.Run.Outage₂.budget e8f42d75dbd803f6
structure AvailableChain.PCSA.Run.Recovery₂ f68a713e48b281cd
ctor AvailableChain.PCSA.Run.Recovery₂.mk f3e5544f0f36b202
field AvailableChain.PCSA.Run.Recovery₂.base 3841f1bf87cce2e4
field AvailableChain.PCSA.Run.Recovery₂.sync f4ea523c6d76534d
field AvailableChain.PCSA.Run.Recovery₂.deltaF c6ac238275978547
field AvailableChain.PCSA.Run.Recovery₂.awake bc215fad11d97edd
field AvailableChain.PCSA.Run.Recovery₂.gap b91e466b4df4f996
field AvailableChain.PCSA.Run.Recovery₂.quarterCap e1ea0330db61834a
field AvailableChain.PCSA.Run.Recovery₂.gapPos b242ad280f84d677
```

### `AvailableChainPCSAClaims.Statements.Slashing`

```text
def AvailableChain.PCSA.Run.pcsaSlashing 4cd74f997ca3fa6d
theorem AvailableChain.PCSA.Run.pcsa_pcsaSlashing_slashes_def 780c27c71f7dcf55
def AvailableChain.PCSA.Run.PCEmitsRow 4ff0296b48a7ee27
theorem AvailableChain.PCSA.Run.pcsa_PCEmitsRow_def 150b9fb0900cd47d
def AvailableChain.PCSA.Run.PCEmittedRowsNoSlash 56d07245e8f8310c
theorem AvailableChain.PCSA.Run.pcsa_PCEmittedRowsNoSlash_def ddcdde0801d450b8
def AvailableChain.PCSA.Run.PCRowSigner 1c1b157a29bd73de
theorem AvailableChain.PCSA.Run.pcsa_PCRowSigner_def eb5d2432a2bcdad0
def AvailableChain.PCSA.Run.PCHonestRowAt cfeed68093abda04
theorem AvailableChain.PCSA.Run.pcsa_PCHonestRowAt_def 09aba26fd42bf10a
def AvailableChain.PCSA.Run.PCFinalityRowCarriage 2d6ac48426e81657
theorem AvailableChain.PCSA.Run.pcsa_PCFinalityRowCarriage_def f557aa00645c3593
```
