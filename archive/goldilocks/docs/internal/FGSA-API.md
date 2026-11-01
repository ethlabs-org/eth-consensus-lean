# FG-SA API manifest

_Current compiled snapshot. Policy: 2026-10-09._

Run the writer after a source change and review the complete diff.
The check requires all current names, modules, kinds and hashes.
Theorem proof values are excluded. Snapshot updates do not approve claims.

Entries: 1358; modules: 59.

`lake env lean --run scripts/V2Manifest.lean --scope fgsa --write` updates this file; `--check` checks it.

## `AvailableChainFGSA`

### `AvailableChainFGSA.Statements.FinalityView`

```text
def AvailableChain.FGSA.finalityView f86cac6f46832901
theorem AvailableChain.FGSA.finalityView_def 1defbcb125e22963
```

### `AvailableChainFGSA.Statements.Invariants`

```text
inductive AvailableChain.FGSA.Reachable 5ae06f33c332bd63
ctor AvailableChain.FGSA.Reachable.init e177eeae31e29317
ctor AvailableChain.FGSA.Reachable.restart 8c028a1346dcdfe8
ctor AvailableChain.FGSA.Reachable.tick c229d16ced622964
ctor AvailableChain.FGSA.Reachable.deliver 3797884c11c03eb2
def AvailableChain.FGSA.NestOK 33ad573c238f8a2f
def AvailableChain.FGSA.SACompat c4047629eda6178e
def AvailableChain.FGSA.LeaseBelowOutputStore 5a26063b06ffa2b3
theorem AvailableChain.FGSA.LeaseBelowOutputStore_def eb04df6daba0bcc7
def AvailableChain.FGSA.FastOrigin a060b278304561e6
structure AvailableChain.FGSA.CStoreInv cb980d5cc624cc81
ctor AvailableChain.FGSA.CStoreInv.mk 7dbdcf83111fdc21
field AvailableChain.FGSA.CStoreInv.fg c1deb7786fb3d7eb
field AvailableChain.FGSA.CStoreInv.rootInj bb704c9e61292aff
field AvailableChain.FGSA.CStoreInv.baseTree 03a6ba0feaea5526
field AvailableChain.FGSA.CStoreInv.saCompat bb90981a09bbbfcf
field AvailableChain.FGSA.CStoreInv.Smem 36136e441223d8d5
field AvailableChain.FGSA.CStoreInv.fastOrigin 1c55ea1227a90e90
field AvailableChain.FGSA.CStoreInv.fastDom 06f389d97cd62401
field AvailableChain.FGSA.CStoreInv.genuineKeys 710fd01d0cfd5c00
field AvailableChain.FGSA.CStoreInv.leaseKeys 07eb8bd41ac0489c
def AvailableChain.FGSA.Inv0 ff334c1483718cab
structure AvailableChain.FGSA.MetaInv f45d5aef38f40570
ctor AvailableChain.FGSA.MetaInv.mk 53dc0ab2c18cda32
field AvailableChain.FGSA.MetaInv.wireTree 504b601c11f0758a
field AvailableChain.FGSA.MetaInv.treeWire 8f520c74259a4688
field AvailableChain.FGSA.MetaInv.proposalsNodup f11e7a262bfecc18
field AvailableChain.FGSA.MetaInv.stampKeys 91b08b3725ff1b75
field AvailableChain.FGSA.MetaInv.blocksNodup 1ee4473d396dce9d
field AvailableChain.FGSA.MetaInv.poolDecodes fb10c17a18b86c58
field AvailableChain.FGSA.MetaInv.poolNodup 17f1d74196004c20
field AvailableChain.FGSA.MetaInv.noGenesisWire 642062fc8864b40a
def AvailableChain.FGSA.ContentAgree f5ead200f3526dd2
```

### `AvailableChainFGSA.Statements.Store`

```text
def AvailableChain.FGSA.OutputNestingStored 9928c3fb7a325dfc
def AvailableChain.FGSA.StoreInvariant 8d2ce0d1e1d346cd
structure AvailableChain.FGSA.StoreBundle 867f0e9c7427b71f
ctor AvailableChain.FGSA.StoreBundle.mk 8f25d5f3d68a092c
field AvailableChain.FGSA.StoreBundle.cstore f854db2e029ec633
field AvailableChain.FGSA.StoreBundle.meta fb08046851103ce5
field AvailableChain.FGSA.StoreBundle.nest 359244bfc55aca26
field AvailableChain.FGSA.StoreBundle.lease 7f394be9d8c9c17f
def AvailableChain.FGSA.StoreBundleInvariant 1e40298d4ab8d8ee
theorem AvailableChain.FGSA.StoreBundleInvariant_def f55152b45d0ae4fa
def AvailableChain.FGSA.FMonotone 9da9a6923c07ec6c
def AvailableChain.FGSA.MetadataInvariant b64ff58ac0c1d3c4
```

### `AvailableChainFGSA.Statements.WindowCertificate`

```text
def AvailableChain.FGSA.Window.projectFinality ba05ae418852b5ca
theorem AvailableChain.FGSA.Window.projectFinality_def 73cc801dfe20c6b2
def AvailableChain.FGSA.Window.projectCertEntry e041d7ad22bd1ba7
theorem AvailableChain.FGSA.Window.projectCertEntry_def 25fe0f85797c49a3
def AvailableChain.FGSA.Window.certificateHeight a0b51be547ad4981
theorem AvailableChain.FGSA.Window.certificateHeight_def 9f9b71d4b7a068b3
def AvailableChain.FGSA.Window.certificateFinality d481ba15c7e37159
theorem AvailableChain.FGSA.Window.certificateFinality_def b35d5f5b3742c183
def AvailableChain.FGSA.Window.certificateFolded 2cb5c528dc514dbf
theorem AvailableChain.FGSA.Window.certificateFolded_def 9856dc7b2679dd2d
def AvailableChain.FGSA.Window.certificateSelection 359fd279864172e9
theorem AvailableChain.FGSA.Window.certificateSelection_def 7cdac046ad446ad9
def AvailableChain.FGSA.Window.EntryOriginAt fadb800486589259
theorem AvailableChain.FGSA.Window.EntryOriginAt_def 926282b6e22ab42b
```

### `AvailableChainFGSA.Statements.WindowEntries`

```text
def AvailableChain.FGSA.Window.RetainedW f3a4f0de9eb685b1
theorem AvailableChain.FGSA.Window.RetainedW_def 89b861dd733f7560
def AvailableChain.FGSA.Window.CoveredW 139f69bec2cd2ab8
theorem AvailableChain.FGSA.Window.CoveredW_def a1289877806b338c
def AvailableChain.FGSA.Window.EntryBitW cde8ada231b23ffa
theorem AvailableChain.FGSA.Window.EntryBitW_def 474b336873be8e87
```

### `AvailableChainFGSA.Statements.WindowHeight`

```text
```

## `AvailableChainFGSARun`

### `AvailableChainFGSARun.Statements.AC`

```text
def AvailableChain.FGSA.Run.fgsaAC c4705a70406ae02c
```

### `AvailableChainFGSARun.Statements.Acceptance`

```text
def AvailableChain.FGSA.Run.fgsaAdmissionTime bedfcddab6bbb51e
def AvailableChain.FGSA.Run.fgsaTimely 5044aee82cfb94ef
def AvailableChain.FGSA.Run.fgsaAcceptanceInv ba55a152bf76f1d0
def AvailableChain.FGSA.Run.fgsaTrigger 95dbabbfa2ab768f
```

### `AvailableChainFGSARun.Statements.Client`

```text
def AvailableChain.FGSA.Run.EmitsRow 76e3f085634c083d
def AvailableChain.FGSA.Run.EmittedRowsNoSlash 82ec7d5817acb5b7
def AvailableChain.FGSA.Run.decodeRowObject 35e2c252c32a9ecd
def AvailableChain.FGSA.Run.fgClientEvent 053226d04e7627d2
def AvailableChain.FGSA.Run.fgClientEvents 2e157e2622d71588
```

### `AvailableChainFGSARun.Statements.Emission`

```text
def AvailableChain.FGSA.Run.EmissionRowsValid 4d0f72aeedade33f
def AvailableChain.FGSA.Run.decode c06272443aaec6cb
def AvailableChain.FGSA.Run.HonestEmissionWellFormed 469cf26857259cff
def AvailableChain.FGSA.Run.HonestProposalDecodes 3e6c7f10b14a93ba
def AvailableChain.FGSA.Run.HeadTargetAtEmission 324a2e95d9a9de13
```

### `AvailableChainFGSARun.Statements.Excludes`

```text
inductive AvailableChain.FGSA.Run.EpochStep d603204da3b8e817
ctor AvailableChain.FGSA.Run.EpochStep.deliver 0ae1eec3d834d931
ctor AvailableChain.FGSA.Run.EpochStep.clock 3cdcaac6bff96ff3
def AvailableChain.FGSA.Run.Epoch 27b04f5eb36f7dd1
def AvailableChain.FGSA.Run.excludesFixed d078abd01e68b82e
```

### `AvailableChainFGSARun.Statements.Interface`

```text
def AvailableChain.FGSA.Run.isRowObject 32e8f31ea396b155
theorem AvailableChain.FGSA.Run.isRowObject_def 58e7750cdba35442
def AvailableChain.FGSA.Run.fgsaDelay 00fcdbeb68f38c80
theorem AvailableChain.FGSA.Run.fgsaDelay_def 79c81256b4dd243e
def AvailableChain.FGSA.Run.fgsaInterface eee603739178f6fa
def AvailableChain.FGSA.Run.fgsaOutputs b2a190dc8996df4c
def AvailableChain.FGSA.Run.finalizedOut 24ed8491960825ab
```

### `AvailableChainFGSARun.Statements.ReceiptCoverage`

```text
structure AvailableChain.FGSA.Run.ReceiptCoveragePremises cfd49e432bf86212
ctor AvailableChain.FGSA.Run.ReceiptCoveragePremises.mk cf1115757024458a
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.within c1d114c4e9c08799
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.slotWindow 0db74c8df66ed697
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.compat 27b3785a286becfd
field AvailableChain.FGSA.Run.ReceiptCoveragePremises.deadline b8f6f154509275a1
structure AvailableChain.FGSA.Run.ReceiptCoverageSleepPremises 5371cdfaca65d835
ctor AvailableChain.FGSA.Run.ReceiptCoverageSleepPremises.mk 7f2297498095bc35
field AvailableChain.FGSA.Run.ReceiptCoverageSleepPremises.within 9cf1fb279b2325ce
field AvailableChain.FGSA.Run.ReceiptCoverageSleepPremises.slotWindow d3e43e8db0abb51d
field AvailableChain.FGSA.Run.ReceiptCoverageSleepPremises.compat 943b60457b7319ec
field AvailableChain.FGSA.Run.ReceiptCoverageSleepPremises.deadline 2c8e3299cb797d4f
def AvailableChain.FGSA.Run.ReceiptCoverageSleepStatement a1c68279ba13528f
theorem AvailableChain.FGSA.Run.ReceiptCoverageSleepStatement_def 210107c82d65bde0
```

### `AvailableChainFGSARun.Statements.Receipts`

```text
def AvailableChain.FGSA.Run.blockOf? 1eb10aaed544fcb1
```

### `AvailableChainFGSARun.Statements.Roots`

```text
def AvailableChain.FGSA.Run.DirectNamedProposalInRun c7381c14e04d231a
def AvailableChain.FGSA.Run.NamedProposalInRun a5e87ca507d4e620
structure AvailableChain.FGSA.Run.NamedRootCollisionFree 08a90e35f7a00542
ctor AvailableChain.FGSA.Run.NamedRootCollisionFree.mk fe7fbd76894fc6f4
field AvailableChain.FGSA.Run.NamedRootCollisionFree.root_injective a8d5ebd9dc66f7f0
def AvailableChain.FGSA.Run.NamedProposalReceiptScope a8e059c3ec4ed67e
def AvailableChain.FGSA.Run.NamedReceiptRootCollisionFree 3883f6977b16529c
def AvailableChain.FGSA.Run.DirectRootBlockInRun fa58f9496f4efc91
def AvailableChain.FGSA.Run.RootBlockInRun 56dac6937ef2d663
```

### `AvailableChainFGSARun.Statements.Slashing`

```text
def AvailableChain.FGSA.Run.fgsaEvidence 1b9808a1a59c7fca
def AvailableChain.FGSA.Run.fgsaSlashing 6965dab6c03a7f80
```

## `AvailableChainFGSAClaims`

### `AvailableChainFGSAClaims.Claims.Clean`

```text
def AvailableChain.FGSA.Run.CleanHistoryAt 313f2283cbb5494d
def AvailableChain.FGSA.Run.CleanGateAt 772474d874c887ff
def AvailableChain.FGSA.Run.CleanTruncAt a1b7db12958759a5
def AvailableChain.FGSA.Run.CleanSafetyAt c02484e5a5b420c1
def AvailableChain.FGSA.Run.CleanCutClaim 666c1bbb4fa6abe9
def AvailableChain.FGSA.Run.CleanCutZeroClaim a1b4ec08f86263c2
def AvailableChain.FGSA.Run.CleanHistoryClaim 416f231485f95845
def AvailableChain.FGSA.Run.CleanPrefixTruncationClaim cef1fc6bc322d176
def AvailableChain.FGSA.Run.CleanSafetyClaim 144849c3866889e7
def AvailableChain.FGSA.Run.CleanCutPosClaim 355e7f7d52053ca1
```

### `AvailableChainFGSAClaims.Claims.Finality`

```text
def AvailableChain.FGSA.Run.FinalityKernelClaim_W 4cabf75ae9a09fa4
def AvailableChain.FGSA.Run.KernelACSideClaim_W 9c6c45d58e455ad7
def AvailableChain.FGSA.Run.FinalityKernelJoinedClaim_W 4c2a2fd1eca41632
def AvailableChain.FGSA.Run.TailKernelClaim_W 3d7d3d97ef7aa80b
def AvailableChain.FGSA.Run.FinalityLivenessConcl_W b5d236205c8e03c3
def AvailableChain.FGSA.Run.FirstFinalityConcl_W 68047533f8a7da38
def AvailableChain.FGSA.Run.ProposalFinalConcl_W a27990dc46d217a5
def AvailableChain.FGSA.Run.AboveFrontierConcl_W 4d7dac098b5cfb99
def AvailableChain.FGSA.Run.FirstFinalityRecFEClaim_W ce5d13195e4fa51b
def AvailableChain.FGSA.Run.FirstFinalityRecF4Claim_W 210f6bc070865e84
def AvailableChain.FGSA.Run.FinalityLivenessRecFEClaim_W 59f46b270e7a5406
def AvailableChain.FGSA.Run.FinalityLivenessRecF4Claim_W 4783d4f65f17308d
def AvailableChain.FGSA.Run.ProposalFinalRecFEClaim_W bf27c3f344f54050
def AvailableChain.FGSA.Run.ProposalFinalRecF4Claim_W 121c0e6b3a205b61
def AvailableChain.FGSA.Run.AboveFrontierRecFEClaim_W 1e61758acf27c5ad
def AvailableChain.FGSA.Run.AboveFrontierRecF4Claim_W ab818ac01f54e705
def AvailableChain.FGSA.Run.FinalityLivenessGSTClaim_W 9004385bc42fb985
def AvailableChain.FGSA.Run.ProposalFinalGSTClaim_W 8bc5891e4eea1e96
def AvailableChain.FGSA.Run.AboveFrontierGSTClaim_W ab73819f55008ebc
```

### `AvailableChainFGSAClaims.Claims.Foundations`

```text
def AvailableChain.FGSA.Run.ClientSafeAll 3f6588feebce6e86
def AvailableChain.FGSA.Run.ClientSafetyClaim c7a06815411bed08
def AvailableChain.FGSA.Run.ClientSafetyBaseClaim 65452670b5e0518d
def AvailableChain.FGSA.Run.FGFoundationClaim cda755d2b8f9dba3
def AvailableChain.FGSA.Run.SrcFrameAboveClaim 6590c3056f9f8828
def AvailableChain.FGSA.Run.RunFGBlock c68befd8b44516b4
def AvailableChain.FGSA.Run.CarrierAt 6dcf4626561b23ac
def AvailableChain.FGSA.Run.StoreAt dc374396ac285557
def AvailableChain.FGSA.Run.ActiveViewAt 6f2e6daa5bfbd95a
def AvailableChain.FGSA.Run.LeaseOriginsAt 98495bd3ff04ddcf
def AvailableChain.FGSA.Run.SourceDisciplineBaseAt 71263600932d411a
def AvailableChain.FGSA.Run.SourceDisciplineAt 0b9e01220e35a8f2
def AvailableChain.FGSA.Run.CarrierClaim c3ea7579b3009e22
def AvailableChain.FGSA.Run.ChainCertificatesAt 59816f613ead5cc9
def AvailableChain.FGSA.Run.ChainCertificatesClaim 0fe420685fd6ae74
def AvailableChain.FGSA.Run.StoreClaim c67888bc0285f6df
def AvailableChain.FGSA.Run.ActiveViewClaim b5a0de45a721d6c4
def AvailableChain.FGSA.Run.LeaseOriginsClaim e7c3b3d44842994a
def AvailableChain.FGSA.Run.ReconcileAt 8f6c68e49e8bc75b
def AvailableChain.FGSA.Run.ReconcileClaim 31722e34e1850dce
def AvailableChain.FGSA.Run.OutputNestingAt 173c3650fe4faae3
def AvailableChain.FGSA.Run.OutputNestingClaim fdd22cb5e178bdb5
def AvailableChain.FGSA.Run.FrameAt 981a7ade498712f1
def AvailableChain.FGSA.Run.FrameClaim f0715c361a511d02
def AvailableChain.FGSA.Run.SourceDisciplineBaseClaim 62faaa5621b0dce9
def AvailableChain.FGSA.Run.SourceDisciplineClaim f360701011a1faa8
def AvailableChain.FGSA.Run.RowServiceBaseClaim ea7b79d55ffeefac
def AvailableChain.FGSA.Run.RowServiceClaim 1eae721cb2588cfa
def AvailableChain.FGSA.Run.PureAccountableClaim c8647a5737a4db34
def AvailableChain.FGSA.Run.PureAgreementClaim 18c8a1db5132d365
def AvailableChain.FGSA.Run.WholeRunAccountableClaim 59ce7b6177c2256b
def AvailableChain.FGSA.Run.WholeRunAgreementClaim 4d23887c5cfd7a4c
def AvailableChain.FGSA.Run.EventPrefixAgreementClaim c00863088c7a44d9
def AvailableChain.FGSA.Run.FaultCountSlashableBoundClaim 7dadb325f0ddba4a
def AvailableChain.FGSA.Run.FinalizedMonotonicityClaim 3d10a83dff154ce8
def AvailableChain.FGSA.Run.HonestNeverSlashedClaim f86eebfdaa03b9d4
def AvailableChain.FGSA.Run.FinalizedSafetyConcl 952a509d7f0c660c
def AvailableChain.FGSA.Run.FinalizedSafetyClaim 3557094dd36b9c45
def AvailableChain.FGSA.Run.FinalLockClaim 2359969841f06849
def AvailableChain.FGSA.Run.FinalizedMonotonicityRestartClaim 763fccca16b8d137
```

### `AvailableChainFGSAClaims.Claims.FrameNext`

```text
def AvailableChain.FGSA.Run.FGFoundationClaimNext 2563cdd0ca206c38
def AvailableChain.FGSA.Run.FrameClaimNext 04b6d8313f71d555
```

### `AvailableChainFGSAClaims.Claims.Healing`

```text
def AvailableChain.FGSA.Run.RowPermissionAt fd668652dc5be121
def AvailableChain.FGSA.Run.RowPermissionClaim c1d205837df4d84f
def AvailableChain.FGSA.Run.HealingInputClaim 299996f93e58c72f
def AvailableChain.FGSA.Run.HTimeConcl 6ce43c7e8c548d4d
def AvailableChain.FGSA.Run.HTimeClaim bd44a91e474d3a3d
def AvailableChain.FGSA.Run.ResetArrivalConcl 8a3ffd710e8ff267
def AvailableChain.FGSA.Run.ResetArrivalClaim c767e4818cbcece1
def AvailableChain.FGSA.Run.RenewedPromotionConcl 46aa4989ce76d164
def AvailableChain.FGSA.Run.RenewedPromotionClaim c93a79b68fff8eb3
def AvailableChain.FGSA.Run.HTimeBestClaim 35a141dba5939378
def AvailableChain.FGSA.Run.HTimeSearchClaim 74e265b8f4b7658c
```

### `AvailableChainFGSAClaims.Claims.Outage`

```text
def AvailableChain.FGSA.Run.ExactProposalAt e41e377fdc92a0e1
def AvailableChain.FGSA.Run.ExactProposalClaim 7359f47edf3da78c
def AvailableChain.FGSA.Run.InclusionPostGateAt 1b205b4800ef2314
def AvailableChain.FGSA.Run.InclusionAt 36d34ad487711470
def AvailableChain.FGSA.Run.CleanInclusionPostGateClaim 62b5682fe423864b
def AvailableChain.FGSA.Run.CleanInclusionClaim 615008f5eb9615bb
def AvailableChain.FGSA.Run.DutiesExtendOn 4a68c54a7673ecae
def AvailableChain.FGSA.Run.FCompatBefore 0e813116cc83c396
def AvailableChain.FGSA.Run.P1Concl 9df77fe63e76c75e
def AvailableChain.FGSA.Run.LeaseOrFFrom 8e9f579ba0892821
def AvailableChain.FGSA.Run.OutageCompatAt 914ac13cab44d3e8
def AvailableChain.FGSA.Run.OutageCompatClaim 75c88960110cd009
def AvailableChain.FGSA.Run.FastP1Claim 399cdb6afa7cddcf
def AvailableChain.FGSA.Run.SlowP1Claim b6e4677a7031d0ca
def AvailableChain.FGSA.Run.AvailableFromConcl 248a6c22e7c99029
def AvailableChain.FGSA.Run.AvailableGrowthConcl 087e24156b98767c
def AvailableChain.FGSA.Run.AvailableGSTClaim e2298320bfe69e0a
def AvailableChain.FGSA.Run.AvailableGrowthGSTClaim d0aeb463a9d32e6e
def AvailableChain.FGSA.Run.CleanGrowthClaim 09242e8e226c2014
```

### `AvailableChainFGSAClaims.Claims.OutageContinuation`

```text
def AvailableChain.FGSA.Run.OutageContinuationClaim 4f0bb8e1be4ad379
```

### `AvailableChainFGSAClaims.Claims.Shared`

```text
def AvailableChain.FGSA.Run.SameLabelAt 0f35cb5c602a8382
def AvailableChain.FGSA.Run.SameLabelClaim e4b2c8958c31db05
def AvailableChain.FGSA.Run.HeadReachesLoAt cb7ed7d1a16e1810
def AvailableChain.FGSA.Run.HeadReachesLoClaim ac50f5fd967084e5
def AvailableChain.FGSA.Run.ReleaseStoreAt 285defc3d4981499
def AvailableChain.FGSA.Run.ReleaseStoreClaim 25351981b7e88ffa
def AvailableChain.FGSA.Run.ReleaseAt 7d366d1fa8992fa5
def AvailableChain.FGSA.Run.ReleaseClaim d94bac3b208a8dbc
```

### `AvailableChainFGSAClaims.Claims.WeakContinuation`

```text
def AvailableChain.FGSA.Run.WeakContinuationClaim a57e684a19286678
def AvailableChain.FGSA.Run.WeakContinuationLiveClaim 635bfd1e2ffd0efe
```

### `AvailableChainFGSAClaims.Claims.WeakContinuationGrowth`

```text
def AvailableChain.FGSA.Run.WeakContinuationGrowthClaim 65c9c601528b3193
```

### `AvailableChainFGSAClaims.FGSAClaims`

```text
structure AvailableChain.FGSA.Run.FGSASafetyClaims 2f93e0c4c60f7146
ctor AvailableChain.FGSA.Run.FGSASafetyClaims.mk 59dab344427bdf76
field AvailableChain.FGSA.Run.FGSASafetyClaims.carrier c7e3d09b8aeb9ad5
field AvailableChain.FGSA.Run.FGSASafetyClaims.chainCertificates 18f48f891ab1f84c
field AvailableChain.FGSA.Run.FGSASafetyClaims.store 0870f1df2b8ed771
field AvailableChain.FGSA.Run.FGSASafetyClaims.activeView e1611f167c1a346a
field AvailableChain.FGSA.Run.FGSASafetyClaims.leaseOrigins 35c8555c46be4d3b
field AvailableChain.FGSA.Run.FGSASafetyClaims.reconcile 00560184c7bbc1c7
field AvailableChain.FGSA.Run.FGSASafetyClaims.outputNesting 789667bc4471aba4
field AvailableChain.FGSA.Run.FGSASafetyClaims.frame 718d3fe6bd22ba0a
field AvailableChain.FGSA.Run.FGSASafetyClaims.clientSafety dbd3b957e3c085cf
field AvailableChain.FGSA.Run.FGSASafetyClaims.clientSafetyBase 86898e8de3f37d2a
field AvailableChain.FGSA.Run.FGSASafetyClaims.sourceDisciplineBase 49d9266bece2fa2e
field AvailableChain.FGSA.Run.FGSASafetyClaims.sourceDiscipline 97b70f197f2ab704
field AvailableChain.FGSA.Run.FGSASafetyClaims.sameLabel 8860f7e8927fd2c6
field AvailableChain.FGSA.Run.FGSASafetyClaims.releaseStore 273eaae4ddbf58d1
field AvailableChain.FGSA.Run.FGSASafetyClaims.release 3883a8c41633e0f4
field AvailableChain.FGSA.Run.FGSASafetyClaims.headReachesLo 386f925efc29b10c
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanCut 46c31da8b5acd4c2
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanHistory 31431df88af1b795
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanPrefixTruncation 49a7ea77a6472865
field AvailableChain.FGSA.Run.FGSASafetyClaims.cleanSafety d0eef167bc9021af
structure AvailableChain.FGSA.Run.FGSASafetyInterfaces 87fe75c34f4d5e29
ctor AvailableChain.FGSA.Run.FGSASafetyInterfaces.mk 5da70806a91cbff0
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.fgFoundation 4def58a4313ab0a8
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.srcFrameAbove b7b1b54314c964f9
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.cpPrefix 32e3a46e014b772b
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.cpCompat 314f990358b6cb30
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.tSrc b8987b4a897e777c
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.labelBound 3fdceda40ac4ff98
field AvailableChain.FGSA.Run.FGSASafetyInterfaces.timingContract 67c5feb185521297
structure AvailableChain.FGSA.Run.FGSAFinalityClaims 8be63fa8f5741ff4
ctor AvailableChain.FGSA.Run.FGSAFinalityClaims.mk 207274c0bcbe8bc0
field AvailableChain.FGSA.Run.FGSAFinalityClaims.accountable ce3e5f9c2bccd89c
field AvailableChain.FGSA.Run.FGSAFinalityClaims.agreement 4fb66583cbde3017
field AvailableChain.FGSA.Run.FGSAFinalityClaims.runAccountable db8431b4386b88ac
field AvailableChain.FGSA.Run.FGSAFinalityClaims.runAgreement a9a3848ac5c9bb05
field AvailableChain.FGSA.Run.FGSAFinalityClaims.eventPrefixAgreement d149a075a194a841
field AvailableChain.FGSA.Run.FGSAFinalityClaims.faultCountSlashableBound ae5547b613063114
field AvailableChain.FGSA.Run.FGSAFinalityClaims.finalizedMonotone f05ab0a82965eeb4
field AvailableChain.FGSA.Run.FGSAFinalityClaims.honestNeverSlashed 5abc1a0ddb277e6d
structure AvailableChain.FGSA.Run.FGSAClaims 6e021da21514fd75
field AvailableChain.FGSA.Run.FGSAClaims.toFGSASafetyClaims b4e5a6acec547a7c
ctor AvailableChain.FGSA.Run.FGSAClaims.mk dd1f1ed8aa3d159c
field AvailableChain.FGSA.Run.FGSAClaims.finality 604d76e41873d890
field AvailableChain.FGSA.Run.FGSAClaims.finalizedSafety 7290f923981fb639
field AvailableChain.FGSA.Run.FGSAClaims.finalLock 683a7cbb582e4100
field AvailableChain.FGSA.Run.FGSAClaims.outageCompat 69e8f1e196885f10
field AvailableChain.FGSA.Run.FGSAClaims.fastP1 3ae1f7dabeb29310
field AvailableChain.FGSA.Run.FGSAClaims.slowP1 81bedc9695d254d7
field AvailableChain.FGSA.Run.FGSAClaims.exactProposal d9481175461688cb
field AvailableChain.FGSA.Run.FGSAClaims.cleanInclusionPostGate 707fed99677cfb28
field AvailableChain.FGSA.Run.FGSAClaims.cleanInclusion 6a46410ff33da80b
field AvailableChain.FGSA.Run.FGSAClaims.firstFinalityRecFE 4062ececd82c22a7
field AvailableChain.FGSA.Run.FGSAClaims.firstFinalityRecF4 56cf3791cd84db88
field AvailableChain.FGSA.Run.FGSAClaims.finalityLivenessGSTRecFE bc330d5077f1594f
field AvailableChain.FGSA.Run.FGSAClaims.finalityLivenessGSTRecF4 562f49ef5bf980bd
field AvailableChain.FGSA.Run.FGSAClaims.proposalFinalGSTRecFE 5ae309745da66586
field AvailableChain.FGSA.Run.FGSAClaims.proposalFinalGSTRecF4 c34fb1079d2a77b9
field AvailableChain.FGSA.Run.FGSAClaims.aboveFrontierGSTRecFE 2873035b6aab20ad
field AvailableChain.FGSA.Run.FGSAClaims.aboveFrontierGSTRecF4 2a951a2dc94077c9
field AvailableChain.FGSA.Run.FGSAClaims.availableGST 70a756cf87a30473
field AvailableChain.FGSA.Run.FGSAClaims.availableGrowthGST 633f61c0308e0e1f
field AvailableChain.FGSA.Run.FGSAClaims.cleanGrowth 2495b86d8d552bec
field AvailableChain.FGSA.Run.FGSAClaims.weakContinuationLive 52f3b4f9cd673d11
```

### `AvailableChainFGSAClaims.Statements.Bounds`

```text
def AvailableChain.FGSA.Run.L 8d4e932a42cf7b48
def AvailableChain.FGSA.Run.P f47871c3f7f4e6ab
def AvailableChain.FGSA.Run.Γ 548fe9969771212f
def AvailableChain.FGSA.Run.ρΓ e28f4f6a1e9f2b3b
def AvailableChain.FGSA.Run.ρ₁ 9022e67716777304
def AvailableChain.FGSA.Run.ρ 9cfc682cff55879f
def AvailableChain.FGSA.Run.E_g 655c22c6b0b26d2e
def AvailableChain.FGSA.Run.E_j c875c1583c2122b0
def AvailableChain.FGSA.Run.B_c 8370be549cfde2a9
def AvailableChain.FGSA.Run.D_c 63ef7ccc088b1d3a
def AvailableChain.FGSA.Run.B_reset 6f3cf78da4b1a20f
def AvailableChain.FGSA.Run.B 7fe30c11b48773f6
def AvailableChain.FGSA.Run.B_H2 3a2f311cd4245aa1
def AvailableChain.FGSA.Run.B_H1 4f3822b9e41b1443
def AvailableChain.FGSA.Run.B_H eebbb104be63948b
def AvailableChain.FGSA.Run.W_F d6cc6ebee1684526
def AvailableChain.FGSA.Run.B_F ad04a713598ea2f7
def AvailableChain.FGSA.Run.B_heal 5c1726465beadb54
def AvailableChain.FGSA.Run.B_best 6f92fac690aedf28
def AvailableChain.FGSA.Run.carrierTime2 fcf77c71390b7fee
def AvailableChain.FGSA.Run.kernelDeadline c14a31b66db5f07e
def AvailableChain.FGSA.Run.ActionDeliveryBounds ff4cca06e8d066c0
def AvailableChain.FGSA.Run.KernelBeforeNextAction 2e7642e148d854d6
def AvailableChain.FGSA.Run.VoteBeforeAction 8fd853db14856b97
def AvailableChain.FGSA.Run.GateAfterCarrier2 cc2a283cea1a2479
def AvailableChain.FGSA.Run.GateActionOrder 3591a84fddb52054
def AvailableChain.FGSA.Run.FourteenBeforeTwoRounds ff90f4dcf8415a1b
```

### `AvailableChainFGSAClaims.Statements.BoundsW`

```text
def AvailableChain.FGSA.Run.kappaF 6371313005b273e9
def AvailableChain.FGSA.Run.betaF e4d2aedc4cde665f
def AvailableChain.FGSA.Run.epsF 5ab7054c134be9ef
def AvailableChain.FGSA.Run.carrierTimeW c488dec9df90298f
def AvailableChain.FGSA.Run.kernelDeadlineW 54745f3905c6f92b
def AvailableChain.FGSA.Run.W_W 279bf1ae475f6868
def AvailableChain.FGSA.Run.E_gF 17dd82d9bc11cfaa
def AvailableChain.FGSA.Run.E_jF fd6e9996cf068a97
def AvailableChain.FGSA.Run.B_cF 4b6c14f5460230d3
def AvailableChain.FGSA.Run.D_cF 2b808c0dc7e16ca5
def AvailableChain.FGSA.Run.B_resetF c294cb223d30623f
def AvailableChain.FGSA.Run.BF e373703c25aa133c
def AvailableChain.FGSA.Run.B_H2F aa9b46c752f0d574
def AvailableChain.FGSA.Run.B_H1F 6fdcb4ef645c6017
def AvailableChain.FGSA.Run.B_HF 05073841effcea16
def AvailableChain.FGSA.Run.B'_resetF f2027477445bc4bd
def AvailableChain.FGSA.Run.B_bestF be84b53201b78f15
def AvailableChain.FGSA.Run.ActionDeliveryBoundsW 02e3698eb5609617
def AvailableChain.FGSA.Run.KernelBeforeNextActionW 4b349af3e0c9f776
structure AvailableChain.FGSA.Run.LivenessBoundW add6843622665972
ctor AvailableChain.FGSA.Run.LivenessBoundW.mk f3f84757bb6d5cb4
field AvailableChain.FGSA.Run.LivenessBoundW.kappa_le_R de51cf339cd35edf
def AvailableChain.FGSA.Run.FE_W a0c2f0e811b5b21a
def AvailableChain.FGSA.Run.F4_W 420d214e499c6aae
def AvailableChain.FGSA.Run.FGoodE_Wp d5de884b95205234
def AvailableChain.FGSA.Run.FGood4_Wp 4b7ff8450f774337
def AvailableChain.FGSA.Run.Tail_Wp e568443262ba9390
def AvailableChain.FGSA.Run.B_FW 191aeaa5a607d5a9
theorem AvailableChain.FGSA.Run.kappaF_def fef901c039d62410
theorem AvailableChain.FGSA.Run.betaF_def 166167f826d5cb48
theorem AvailableChain.FGSA.Run.epsF_def 4438023ec2765319
theorem AvailableChain.FGSA.Run.carrierTimeW_def 2c9ef5e4eb73f0ef
theorem AvailableChain.FGSA.Run.kernelDeadlineW_def 4ad3c17af5511fb5
theorem AvailableChain.FGSA.Run.W_W_def 38b7a5a5044fed7d
theorem AvailableChain.FGSA.Run.E_gF_def 769dbd5fbebe2867
theorem AvailableChain.FGSA.Run.E_jF_def 5c42de4200fe33a1
theorem AvailableChain.FGSA.Run.B_cF_def ab6d669d29d267e7
theorem AvailableChain.FGSA.Run.D_cF_def df333c137aa19c83
theorem AvailableChain.FGSA.Run.B_resetF_def fe4f48a7e6f4e54e
theorem AvailableChain.FGSA.Run.BF_def f469038bc44d01a8
theorem AvailableChain.FGSA.Run.B_H2F_def f424a92b7f97c935
theorem AvailableChain.FGSA.Run.B_H1F_def 1ab795f6987d8ed1
theorem AvailableChain.FGSA.Run.B_HF_def 4ec142c9de6daf1e
theorem AvailableChain.FGSA.Run.B'_resetF_def ffd7344c460472e6
theorem AvailableChain.FGSA.Run.B_bestF_def a56741daed1285e5
theorem AvailableChain.FGSA.Run.ActionDeliveryBoundsW_def 9afe336447a0417c
theorem AvailableChain.FGSA.Run.KernelBeforeNextActionW_def f86f12fe200a6474
theorem AvailableChain.FGSA.Run.FE_W_def 426a7f82308dc80c
theorem AvailableChain.FGSA.Run.F4_W_def b4bb5b3dda93721a
theorem AvailableChain.FGSA.Run.FGoodE_Wp_def 1939eb5083c4b78b
theorem AvailableChain.FGSA.Run.FGood4_Wp_def ed2611e4dfaad59f
theorem AvailableChain.FGSA.Run.Tail_Wp_def f39b312bcb078ed3
theorem AvailableChain.FGSA.Run.B_FW_def 6ff7a073be682df8
```

### `AvailableChainFGSAClaims.Statements.ChannelProps`

```text
def AvailableChain.FGSA.Run.RCarrierView 0533730d50ba4dfc
theorem AvailableChain.FGSA.Run.RCarrierView_def af7532eb4b87b7d5
def AvailableChain.FGSA.Run.RStore 31b875a53827b272
theorem AvailableChain.FGSA.Run.RStore_def cb72115c4211b76d
def AvailableChain.FGSA.Run.RActive 83c274add3297946
theorem AvailableChain.FGSA.Run.RActive_def 5f7c58813dd1e40b
def AvailableChain.FGSA.Run.RStoreCumul b24156aeef695c95
theorem AvailableChain.FGSA.Run.RStoreCumul_def 2f4fee1fc8f58388
def AvailableChain.FGSA.Run.RMono 8ba6ebe39dede045
theorem AvailableChain.FGSA.Run.RMono_def a92ff997546b89a7
def AvailableChain.FGSA.Run.RFrameExact 59f9b668387a1401
theorem AvailableChain.FGSA.Run.RFrameExact_def b0e17aab6d2d1d91
def AvailableChain.FGSA.Run.RFrame 3ff7298284744cc6
theorem AvailableChain.FGSA.Run.RFrame_def 582109c9ed46ea77
def AvailableChain.FGSA.Run.RGeo 6ec609af4dd50b6b
theorem AvailableChain.FGSA.Run.RGeo_def 7d2edbfd2d711a88
def AvailableChain.FGSA.Run.RCert 57ed5abe51f57bb1
theorem AvailableChain.FGSA.Run.RCert_def 14c4c6a379429c77
def AvailableChain.FGSA.Run.RRec 3e37c5cd8c78507e
theorem AvailableChain.FGSA.Run.RRec_def e8953a2ea2f89456
def AvailableChain.FGSA.Run.TSrc ebca772659208bf1
theorem AvailableChain.FGSA.Run.TSrc_def ae05fd7596bca209
def AvailableChain.FGSA.Run.LabelBound a771b085de52c3f0
theorem AvailableChain.FGSA.Run.LabelBound_def af0e94f3ec44aa5b
def AvailableChain.FGSA.Run.TChain 780c65d202e2ba04
theorem AvailableChain.FGSA.Run.TChain_def 0b178af751d82633
def AvailableChain.FGSA.Run.TCompat 1fe8273816bbd105
theorem AvailableChain.FGSA.Run.TCompat_def fb8488c260261b05
structure AvailableChain.FGSA.Run.AncestorClosed a82d5e35de829ed2
ctor AvailableChain.FGSA.Run.AncestorClosed.mk fa2827ea0465c6d5
field AvailableChain.FGSA.Run.AncestorClosed.down 6a9b1aab4f3ebb3e
def AvailableChain.FGSA.Run.FrameBelow d170caf7c923ca81
theorem AvailableChain.FGSA.Run.FrameBelow_def b261817e5cd74fb3
def AvailableChain.FGSA.Run.RStrat 1b64318baef03544
theorem AvailableChain.FGSA.Run.RStrat_def b9cf2186833dfd36
def AvailableChain.FGSA.Run.RQCOrigin 766dea3354024b45
theorem AvailableChain.FGSA.Run.RQCOrigin_def e796b915dd1df662
def AvailableChain.FGSA.Run.SrcFrameAbove 9edac07c7aa3bb15
theorem AvailableChain.FGSA.Run.SrcFrameAbove_def db5abe531e95a31d
def AvailableChain.FGSA.Run.SrcFrame 7c1fb653547a1f07
def AvailableChain.FGSA.Run.SrcFrameAboveStmt da9443620b2bacc7
theorem AvailableChain.FGSA.Run.SrcFrameAboveStmt_def f63c735e140beea9
def AvailableChain.FGSA.Run.CPPrefix bd8124fa9bef9b77
theorem AvailableChain.FGSA.Run.CPPrefix_def c9bf1bc13dc178cb
def AvailableChain.FGSA.Run.CPCompat 7fc1b70970e16108
theorem AvailableChain.FGSA.Run.CPCompat_def 24066922845e9ba7
def AvailableChain.FGSA.Run.RXing 14c9ca8c734c9bdf
def AvailableChain.FGSA.Run.RCap 5abdd9553bd7f4bf
def AvailableChain.FGSA.Run.THigh 29d9e01f3cbaa9d2
def AvailableChain.FGSA.Run.TCarrier fc36996876602c57
def AvailableChain.FGSA.Run.TRowsSelect c99e0ed7d5ac8017
def AvailableChain.FGSA.Run.TRowsSync ec235cd4a31b1b32
def AvailableChain.FGSA.Run.TRowsReceipt bf921e80bf3a5119
theorem AvailableChain.FGSA.Run.TRowsReceipt_def 65a2f315cba919fd
structure AvailableChain.FGSA.Run.TRows 44fbe30184933358
ctor AvailableChain.FGSA.Run.TRows.mk 576229dbc5d5056d
field AvailableChain.FGSA.Run.TRows.select d6e97ee926db7c05
field AvailableChain.FGSA.Run.TRows.sync de856ec93f35547d
field AvailableChain.FGSA.Run.TRows.receipt 404b8145202d01f6
def AvailableChain.FGSA.Run.SourceBefore 3eb4798238ccb425
def AvailableChain.FGSA.Run.Kept ed92f5f8880b5581
def AvailableChain.FGSA.Run.KeepOrCause 166011ad2d7d013a
def AvailableChain.FGSA.Run.RExcl b4655726711a6ad3
def AvailableChain.FGSA.Run.RKeep 426f897f28cd937d
def AvailableChain.FGSA.Run.RFProv aebe599b91be4170
def AvailableChain.FGSA.Run.TDel 9f3fe05ef8297719
def AvailableChain.FGSA.Run.TDelReset 68478584c811758e
def AvailableChain.FGSA.Run.TGeom 1414e61a74606c75
def AvailableChain.FGSA.Run.ExactService 99e4a2d7f17d35fb
def AvailableChain.FGSA.Run.PhaseInterval afef75f997db3a4d
def AvailableChain.FGSA.Run.Transfers 896fc06cd181465c
def AvailableChain.FGSA.Run.PhaseBody f03d85d9cad33cf0
def AvailableChain.FGSA.Run.TPerm 7107e0c92bc6f203
def AvailableChain.FGSA.Run.ProposalGap 19e914ffe8dc8c61
def AvailableChain.FGSA.Run.RepairAfter 15111b685565f209
def AvailableChain.FGSA.Run.TRepair aa05dd16fc9cf562
def AvailableChain.FGSA.Run.OpeningCovered 76cb4c0a27f856b2
def AvailableChain.FGSA.Run.OpeningEntry 525af493a96ad9e1
def AvailableChain.FGSA.Run.TCommon 44717970edca5fc2
def AvailableChain.FGSA.Run.TFrontier da4929d474147fe1
def AvailableChain.FGSA.Run.FinalityRowCarriage ef0b0b17011f546d
theorem AvailableChain.FGSA.Run.FinalityRowCarriage_def 108856d5d6440223
def AvailableChain.FGSA.Run.RMonoAll 270dd641905f5a39
theorem AvailableChain.FGSA.Run.RMonoAll_def 30e45fb8e7066ccd
def AvailableChain.FGSA.Run.RStoreDurable cdad8a0889fcdb69
theorem AvailableChain.FGSA.Run.RStoreDurable_def c99b8e86b7664a07
def AvailableChain.FGSA.Run.RStoreEpoch 2f46ce9dbb2aed26
theorem AvailableChain.FGSA.Run.RStoreEpoch_def b4a039806c3b8896
```

### `AvailableChainFGSAClaims.Statements.Channels`

```text
def AvailableChain.FGSA.Run.certified 80e4a3693bf2d89c
theorem AvailableChain.FGSA.Run.certified_def a5d675c89a272887
def AvailableChain.FGSA.Run.treeT 2b69ec7b0e57e60e
def AvailableChain.FGSA.Run.treeErased b78204b44e3c46cd
def AvailableChain.FGSA.Run.frameR 395107f87e1057e7
def AvailableChain.FGSA.Run.domainR 4161e11ed74ec34d
def AvailableChain.FGSA.Run.finR aac46ba18b4700c2
def AvailableChain.FGSA.Run.FAdvance 295788c25e134f22
def AvailableChain.FGSA.Run.sourceCandidates ea2b20c12ea3f181
def AvailableChain.FGSA.Run.jointSource 0c24947a4c7a783b
def AvailableChain.FGSA.Run.proposerHead b9b8415a6df36962
def AvailableChain.FGSA.Run.outputS 1d0f4a9dbb766c1e
theorem AvailableChain.FGSA.Run.outputS_def 78e519431fcc26cb
theorem AvailableChain.FGSA.Run.frameR_def 46870ba5dac194b2
theorem AvailableChain.FGSA.Run.jointSource_def 884a9f045b72de73
theorem AvailableChain.FGSA.Run.sourceCandidates_def 7cd6a98c9f1d7d5a
theorem AvailableChain.FGSA.Run.domainR_def 729fb9eaa24e05a3
theorem AvailableChain.FGSA.Run.treeT_def 3acc17fc60e79846
theorem AvailableChain.FGSA.Run.proposerHead_def 23840b24f59e59b6
theorem AvailableChain.FGSA.Run.FAdvance_def 910b82c4a0274160
def AvailableChain.FGSA.Run.R_at 125864c7e0b887ef
def AvailableChain.FGSA.Run.D_at df8061f98414c68f
def AvailableChain.FGSA.Run.FAdvanceAt 387d4f385e459cb1
def AvailableChain.FGSA.Run.candidatesAt 37a1523639a3b911
def AvailableChain.FGSA.Run.proposalHeadAt c961406441f42731
def AvailableChain.FGSA.Run.actionHead 3ea9e13efed4869a
def AvailableChain.FGSA.Run.actionTriple fee23b7a13d995fa
def AvailableChain.FGSA.Run.namedEntry a50c73e0c7ee36db
def AvailableChain.FGSA.Run.EntryBelow 70f4e667e4654e34
def AvailableChain.FGSA.Run.RowSigner 72fb6945bb42aebd
def AvailableChain.FGSA.Run.HonestRowAt bbb52057aef5437f
def AvailableChain.FGSA.Run.HonestRowBefore 9f8a0178fe3d81f2
theorem AvailableChain.FGSA.Run.HonestRowBefore_def 671c0e58319a2236
def AvailableChain.FGSA.Run.RowComplete 375ab20310c6a991
def AvailableChain.FGSA.Run.HonestCarrier 8bf0258c272ab462
def AvailableChain.FGSA.Run.HeldAt 3d2fad79a4428f65
def AvailableChain.FGSA.Run.BlockInRunBefore 056954b929fe1eb3
theorem AvailableChain.FGSA.Run.RowSigner_def d251e7b6477d81c6
theorem AvailableChain.FGSA.Run.HonestRowAt_def c5b57462175ebf30
def AvailableChain.FGSA.Run.rowHeld b4f2f67df3ca81ea
def AvailableChain.FGSA.Run.proposalStateAt 7d39985dcc37155f
def AvailableChain.FGSA.Run.heldAtProposal 45092c1e8bef6a4f
def AvailableChain.FGSA.Run.onParentChain da3fec5ef178f898
def AvailableChain.FGSA.Run.HeldBefore 16240418035226f2
def AvailableChain.FGSA.Run.ValidForParent c201d2f10be82e22
theorem AvailableChain.FGSA.Run.ValidForParent_def eddf7fcc645c7b5b
def AvailableChain.FGSA.Run.HeightMatch 65f180d7a2ed3624
theorem AvailableChain.FGSA.Run.HeightMatch_def 948c5bd77efca9c0
def AvailableChain.FGSA.Run.headAtLabel 24662322d1f7f9ea
theorem AvailableChain.FGSA.Run.RowComplete_def 568194e519e28cb1
theorem AvailableChain.FGSA.Run.HonestCarrier_def ee2197616722e30e
theorem AvailableChain.FGSA.Run.HeldAt_def cad99396bf08c6c5
theorem AvailableChain.FGSA.Run.namedEntry_def f3827e3bef137733
```

### `AvailableChainFGSAClaims.Statements.ComposeNext`

```text
structure AvailableChain.FGSA.Run.FGFoundationNext 964f5200c7aad77c
ctor AvailableChain.FGSA.Run.FGFoundationNext.mk d29f9ca35dd7e4a1
field AvailableChain.FGSA.Run.FGFoundationNext.store 5987ec6a726c43e6
field AvailableChain.FGSA.Run.FGFoundationNext.cumul baba5417257dc7fa
field AvailableChain.FGSA.Run.FGFoundationNext.mono 149e36e23b359b1f
field AvailableChain.FGSA.Run.FGFoundationNext.frame 40ce73d2ac61ec18
field AvailableChain.FGSA.Run.FGFoundationNext.geo 06dbe1c985401d8e
field AvailableChain.FGSA.Run.FGFoundationNext.strat 31133cd42dbe1198
field AvailableChain.FGSA.Run.FGFoundationNext.reconcile 005a1b133f5f5626
```

### `AvailableChainFGSAClaims.Statements.ComposeStmt`

```text
def AvailableChain.FGSA.Run.windowIdx 268714a0c685435e
structure AvailableChain.FGSA.Run.TimingContract d72ebd2b29f8270d
ctor AvailableChain.FGSA.Run.TimingContract.mk 073f6058d0c1a1a6
field AvailableChain.FGSA.Run.TimingContract.rowLag 36f4eb10eaf5c7e5
field AvailableChain.FGSA.Run.TimingContract.certLag 6028f69801952ca8
field AvailableChain.FGSA.Run.TimingContract.label ec65aa9819ba5ac4
field AvailableChain.FGSA.Run.TimingContract.atomic 8f45493496f39e4c
field AvailableChain.FGSA.Run.TimingContract.tickFG cb3085627933efce
structure AvailableChain.FGSA.Run.FGFoundation 1ec5df08b9836ace
ctor AvailableChain.FGSA.Run.FGFoundation.mk defad9f20a46f3ab
field AvailableChain.FGSA.Run.FGFoundation.store 0606a6c58daa50c7
field AvailableChain.FGSA.Run.FGFoundation.cumul 850914f667fa4e67
field AvailableChain.FGSA.Run.FGFoundation.mono 281564f0dac3a930
field AvailableChain.FGSA.Run.FGFoundation.frame 2085d3e462a291ba
field AvailableChain.FGSA.Run.FGFoundation.geo a718e16594b0fd8f
field AvailableChain.FGSA.Run.FGFoundation.strat 38ecd3d8098ab364
field AvailableChain.FGSA.Run.FGFoundation.reconcile f5dd6cc7d64b41a9
def AvailableChain.FGSA.Run.TStart 6a7ea9ddee457d45
def AvailableChain.FGSA.Run.FullVoteService 6018a805f8657bf8
def AvailableChain.FGSA.Run.TVote 18e73e7f4cf4b011
def AvailableChain.FGSA.Run.WalkBatch d9946d7dfef37750
def AvailableChain.FGSA.Run.TWalk 6ab6442dec1f6d5c
structure AvailableChain.FGSA.Run.CoreServices 8fa614ffbb4dbaf7
ctor AvailableChain.FGSA.Run.CoreServices.mk 2f2f3ca4059eab02
field AvailableChain.FGSA.Run.CoreServices.start 437345b711d62c1b
field AvailableChain.FGSA.Run.CoreServices.vote e0011f54635cc257
field AvailableChain.FGSA.Run.CoreServices.walk 005abc467f5157a7
inductive AvailableChain.FGSA.Run.PhaseKind c1b8ad8e15380e60
ctor AvailableChain.FGSA.Run.PhaseKind.gap 5e88dc1d014a063a
ctor AvailableChain.FGSA.Run.PhaseKind.topJ ef3517c6daf975b3
ctor AvailableChain.FGSA.Run.PhaseKind.contest 09d7f16d016aa074
inductive AvailableChain.FGSA.Run.AttemptTask 90defab1dcdb57a7
ctor AvailableChain.FGSA.Run.AttemptTask.raise fe31883cbb822cf7
ctor AvailableChain.FGSA.Run.AttemptTask.firstRow 6412d6399a447594
structure AvailableChain.FGSA.Run.AttemptKey ab5f1b1e8d1673ae
ctor AvailableChain.FGSA.Run.AttemptKey.mk 1752ea276d7f0293
field AvailableChain.FGSA.Run.AttemptKey.start 2fde4ea3fa941fa2
field AvailableChain.FGSA.Run.AttemptKey.frontier dee085abe8607002
field AvailableChain.FGSA.Run.AttemptKey.phase 84195c8f48291dfb
field AvailableChain.FGSA.Run.AttemptKey.task 6a4993e3f16b51cb
field AvailableChain.FGSA.Run.AttemptKey.served 36c55bac0872d02c
def AvailableChain.FGSA.Run.ResetArrivalStatement 9f655ca293622db3
theorem AvailableChain.FGSA.Run.ResetArrivalStatement_def a7549810bc7507a7
def AvailableChain.FGSA.Run.ResetArrivalFullStatement 3ce18d85c267ac5e
theorem AvailableChain.FGSA.Run.ResetArrivalFullStatement_def 8637df07c077175d
structure AvailableChain.FGSA.Run.KernelPt 9235f1fbc5c48477
ctor AvailableChain.FGSA.Run.KernelPt.mk 32c96b623cc6f691
field AvailableChain.FGSA.Run.KernelPt.w 6cbd0d7075070f20
field AvailableChain.FGSA.Run.KernelPt.r e581c6d88b7635d7
def AvailableChain.FGSA.Run.kernelStart 2096e8da282ae310
def AvailableChain.FGSA.Run.OpeningCarrier_W 91f657c89dd43dc5
theorem AvailableChain.FGSA.Run.OpeningCarrier_W_def 5b8cf6e81a430a9d
def AvailableChain.FGSA.Run.KernelConclusion_W 6551e3cd0c71fbdd
theorem AvailableChain.FGSA.Run.KernelConclusion_W_def 136eb83ab27eb1d1
structure AvailableChain.FGSA.Run.KernelPrem_W 34dc4fdcf948a902
ctor AvailableChain.FGSA.Run.KernelPrem_W.mk 31561256e608f8df
field AvailableChain.FGSA.Run.KernelPrem_W.set 19272a384fd0abb6
field AvailableChain.FGSA.Run.KernelPrem_W.bound fc4fb999c8ee31d4
field AvailableChain.FGSA.Run.KernelPrem_W.window 176cb0e654ad550d
field AvailableChain.FGSA.Run.KernelPrem_W.start 54a8db4912c53a09
field AvailableChain.FGSA.Run.KernelPrem_W.hhor c17f163ca1724886
field AvailableChain.FGSA.Run.KernelPrem_W.input d335115444fd5eca
field AvailableChain.FGSA.Run.KernelPrem_W.services d4bb3618469d0e46
structure AvailableChain.FGSA.Run.TailKernelPt b330d4900d1ca7d6
ctor AvailableChain.FGSA.Run.TailKernelPt.mk 41cdd6cb6261ae64
field AvailableChain.FGSA.Run.TailKernelPt.w b55caf984a16e648
field AvailableChain.FGSA.Run.TailKernelPt.r 4006ca4b73b3c4a7
field AvailableChain.FGSA.Run.TailKernelPt.carrier 62ca7b0096b16566
field AvailableChain.FGSA.Run.TailKernelPt.U 5b648aaa4a87357a
structure AvailableChain.FGSA.Run.TailKernelPrem_W 84ce963f30356a98
ctor AvailableChain.FGSA.Run.TailKernelPrem_W.mk caa64e13b48e0cbc
field AvailableChain.FGSA.Run.TailKernelPrem_W.set 9eed80fa893e3366
field AvailableChain.FGSA.Run.TailKernelPrem_W.bound 54cbc80c2603436e
field AvailableChain.FGSA.Run.TailKernelPrem_W.input 25cef8b6a03ce335
field AvailableChain.FGSA.Run.TailKernelPrem_W.start f2750ca67f84ef5d
field AvailableChain.FGSA.Run.TailKernelPrem_W.window bbb492833d015018
field AvailableChain.FGSA.Run.TailKernelPrem_W.carrier 9f5d14addb8d7cc5
field AvailableChain.FGSA.Run.TailKernelPrem_W.high 1a6e123aa07ef60c
field AvailableChain.FGSA.Run.TailKernelPrem_W.cover 24f529bb0881b891
field AvailableChain.FGSA.Run.TailKernelPrem_W.hhor 09c6e13716da3e02
structure AvailableChain.FGSA.Run.HealTContract 046d977504f28a1d
ctor AvailableChain.FGSA.Run.HealTContract.mk 0428407ab375b3e2
field AvailableChain.FGSA.Run.HealTContract.del 622ab465d1fdb8e7
field AvailableChain.FGSA.Run.HealTContract.delReset fea7c1de135ba3be
field AvailableChain.FGSA.Run.HealTContract.perm 82afb346466e187e
field AvailableChain.FGSA.Run.HealTContract.repair d1ca4226db9f885c
field AvailableChain.FGSA.Run.HealTContract.common 32bda0f5adb1beb8
field AvailableChain.FGSA.Run.HealTContract.frontier 26ef0b58b66547d1
field AvailableChain.FGSA.Run.HealTContract.geom 71662de42c202a9d
def AvailableChain.FGSA.Run.frontierAtIdx 4260f8fca0263421
def AvailableChain.FGSA.Run.TopEvidence 9edef6ccbd395a7c
def AvailableChain.FGSA.Run.ContestEvidence e90af4eb42250929
def AvailableChain.FGSA.Run.EffectiveEvent 2ade77b79f4b314e
def AvailableChain.FGSA.Run.AttemptPhaseAt 295a1769785cb806
def AvailableChain.FGSA.Run.ServedFrontier 90b44c6d2fdaf84a
def AvailableChain.FGSA.Run.AttemptValid 9b0c39ffb66acfc8
def AvailableChain.FGSA.Run.attemptBudget b92a1475dc2a8a8b
def AvailableChain.FGSA.Run.AttemptEndsBy b5160401477a33c9
def AvailableChain.FGSA.Run.SettledPhaseFrame 362bcbb7ba51ca7e
theorem AvailableChain.FGSA.Run.SettledPhaseFrame_def 2350c57f4b2aabd0
def AvailableChain.FGSA.Run.RPhase b7a024f03a877f9f
theorem AvailableChain.FGSA.Run.RPhase_def 66f9483da363379d
structure AvailableChain.FGSA.Run.HealRContract e740d2046862fe23
ctor AvailableChain.FGSA.Run.HealRContract.mk f5f36294f3aa4b4f
field AvailableChain.FGSA.Run.HealRContract.xing c3b0802ec0b78a25
field AvailableChain.FGSA.Run.HealRContract.cap 30a838d25f7e48d9
field AvailableChain.FGSA.Run.HealRContract.phase d771feb4a0adf01d
field AvailableChain.FGSA.Run.HealRContract.excl d7c78423417e7753
field AvailableChain.FGSA.Run.HealRContract.keep 0c7017c3531ba0fc
field AvailableChain.FGSA.Run.HealRContract.fprov ebf919fa30e2ff85
def AvailableChain.FGSA.Run.ProgressAttemptStatement 402b56a70f8e0c90
theorem AvailableChain.FGSA.Run.ProgressAttemptStatement_def 0688c6b1f2c39b37
```

### `AvailableChainFGSAClaims.Statements.Counts`

```text
def AvailableChain.FGSA.Run.awakeHonestIn 54415ad59f9cd90a
def AvailableChain.FGSA.Run.HonestProposal ae9f4b671ef57b39
```

### `AvailableChainFGSAClaims.Statements.FinalityApi`

```text
def AvailableChain.FGSA.Run.FinalityFinalizedAt 07c61af64b2952e5
theorem AvailableChain.FGSA.Run.FinalityFinalizedAt_def 5d19c2698c4c9d8e
def AvailableChain.FGSA.Run.FinalityBlock 4d754f3fcd9ff659
theorem AvailableChain.FGSA.Run.FinalityBlock_def 5c59d00a9469bdc9
def AvailableChain.FGSA.Run.finalityRows 0095a1b4bd82114d
theorem AvailableChain.FGSA.Run.finalityRows_def 33877122b770dbb3
def AvailableChain.FGSA.Run.FinalitySlashableBound a44d46e1c6e816de
theorem AvailableChain.FGSA.Run.FinalitySlashableBound_def f865b31462841df8
def AvailableChain.FGSA.Run.FinalityExecution 0d9b51c976729c2c
theorem AvailableChain.FGSA.Run.FinalityExecution_def 2ea56130d0c142e9
def AvailableChain.FGSA.Run.WholeRunAccountable df93edcc003bd56b
theorem AvailableChain.FGSA.Run.WholeRunAccountable_def a05793f2dd53e86f
def AvailableChain.FGSA.Run.WholeRunAgreement 06c333a38b514591
theorem AvailableChain.FGSA.Run.WholeRunAgreement_def 8c7254a06273917f
```

### `AvailableChainFGSAClaims.Statements.Fold`

```text
inductive AvailableChain.FGSA.Run.RowKind da2d1119c2ef39fc
ctor AvailableChain.FGSA.Run.RowKind.target a127adc0838fa2e4
ctor AvailableChain.FGSA.Run.RowKind.progress e22f9613e6edb955
def AvailableChain.FGSA.Run.RowNames c882dc72ac13848c
def AvailableChain.FGSA.Run.SlotChain 026b8cab17d0c00f
def AvailableChain.FGSA.Run.EntryAt 6a182d85dcf4ffba
def AvailableChain.FGSA.Run.JustifiedCross 4220b788bb017546
def AvailableChain.FGSA.Run.MixedCross 1c0f9778f6d9b446
def AvailableChain.FGSA.Run.NoMixedOnPath 3e473ddff4cc55e1
def AvailableChain.FGSA.Run.SeatCovers 0d72d8b768d2a82c
def AvailableChain.FGSA.Run.CoveredByChild c5e54547daf9eb39
def AvailableChain.FGSA.Run.foldTrichotomy 3f91adf7d9eba691
def AvailableChain.FGSA.Run.StoredProgressConsume bcb8f879ae014395
def AvailableChain.FGSA.Run.NoMixedMaturity f968c4f72940f18d
def AvailableChain.FGSA.Run.NamesEntry 4157bcc504c0ab7f
def AvailableChain.FGSA.Run.rowHeight 8e2499ef46ddafdd
def AvailableChain.FGSA.Run.eventTime 4bdaaa69edcc1980
def AvailableChain.FGSA.Run.honestSeats 937b930bab78c4b6
theorem AvailableChain.FGSA.Run.rowHeight_def 770f0d6454ee9f76
theorem AvailableChain.FGSA.Run.eventTime_def 58ef7b966e9699ec
theorem AvailableChain.FGSA.Run.honestSeats_def a40e17e9b3a6f1b1
def AvailableChain.FGSA.Run.ChainRowsBefore 1b346f5d4dff3f85
structure AvailableChain.FGSA.Run.PreBatchPrem 16ba43e434f2d697
ctor AvailableChain.FGSA.Run.PreBatchPrem.mk ff94976925b77dd2
field AvailableChain.FGSA.Run.PreBatchPrem.base 2b7f13287c50e79e
field AvailableChain.FGSA.Run.PreBatchPrem.faultQ 090ad2c6104c1ccd
field AvailableChain.FGSA.Run.PreBatchPrem.entry a3e2e2fac603edf2
field AvailableChain.FGSA.Run.PreBatchPrem.path 21c93a9c9f47bbbf
field AvailableChain.FGSA.Run.PreBatchPrem.cut 9f36405dc35693d1
field AvailableChain.FGSA.Run.PreBatchPrem.early 148a4a80b362c992
field AvailableChain.FGSA.Run.PreBatchPrem.rows d3995e41ccc8a464
field AvailableChain.FGSA.Run.PreBatchPrem.noRow 69abcf4fd708a7f3
def AvailableChain.FGSA.Run.NoMixedPreBatchParent e74df4294f9b0bb6
structure AvailableChain.FGSA.Run.BatchPrem ca036f7fd0a3dea1
ctor AvailableChain.FGSA.Run.BatchPrem.mk afa9b28e71ce4fdc
field AvailableChain.FGSA.Run.BatchPrem.base a5cc64e0855b3ecb
field AvailableChain.FGSA.Run.BatchPrem.faultQ e53ee62ce7a77361
field AvailableChain.FGSA.Run.BatchPrem.deltaF 535c77b795bd6b4b
field AvailableChain.FGSA.Run.BatchPrem.rowsReceipt 3eceebe238a0b9f3
field AvailableChain.FGSA.Run.BatchPrem.horizon 7e0ab3d5fa7d2fc2
field AvailableChain.FGSA.Run.BatchPrem.carrier d22ff1cca7654784
field AvailableChain.FGSA.Run.BatchPrem.after ac1554458f33f42a
field AvailableChain.FGSA.Run.BatchPrem.valid 413f8cfec62f4b34
field AvailableChain.FGSA.Run.BatchPrem.entry 875aed6f908fc4e5
field AvailableChain.FGSA.Run.BatchPrem.path bd0d302c21355fba
field AvailableChain.FGSA.Run.BatchPrem.above 8fb712cdc99f4469
def AvailableChain.FGSA.Run.BatchCoverage 3cd25b19c665d389
theorem AvailableChain.FGSA.Run.JustifiedCross_def df81b827b773af75
theorem AvailableChain.FGSA.Run.MixedCross_def 9bb1a7e85401f709
theorem AvailableChain.FGSA.Run.foldTrichotomy_def 132834b174b22f9b
theorem AvailableChain.FGSA.Run.StoredProgressConsume_def 36cd5ccc9859c367
def AvailableChain.FGSA.Run.FinRowNames 94adce64d3029936
def AvailableChain.FGSA.Run.FinalityCoveredByChild_W 643922320c84f168
def AvailableChain.FGSA.Run.FinalityNames 6502008fb69955a7
structure AvailableChain.FGSA.Run.FinalityBatchPrem_W 98c635cdeaa3351f
ctor AvailableChain.FGSA.Run.FinalityBatchPrem_W.mk 1ee6f6e7e8e8eed9
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.base ebfcfc3e14eb7eb5
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.faultQ ab2f7ca819600237
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.deltaF 54bf147bcd42bb9f
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.rowsReceipt 5cc5aa455d45d03e
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.carrier 8014b8c3c5186fbb
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.after 8418785f135d0f00
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.horizon 25aad21117fb05f3
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.parent a24dcad3c803d38c
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.birth c921f1616937f075
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.retainedOrCovered 6adaa1bcd86c8617
field AvailableChain.FGSA.Run.FinalityBatchPrem_W.batch 3b32774ccaeab24a
def AvailableChain.FGSA.Run.FinalityBatchCoverage_W c340d983a7e4dbb3
structure AvailableChain.FGSA.Run.PendingFold_W 5f973f39dc1fdc9c
ctor AvailableChain.FGSA.Run.PendingFold_W.mk 05cc06274674b236
field AvailableChain.FGSA.Run.PendingFold_W.child 8966d5943b8bb5c5
field AvailableChain.FGSA.Run.PendingFold_W.cover 9f4386d5fd82c86d
theorem AvailableChain.FGSA.Run.FinalityCoveredByChild_W_def b949f1a305ead8fa
theorem AvailableChain.FGSA.Run.FinRowNames_def ed158b1dc934a188
theorem AvailableChain.FGSA.Run.FinalityNames_def 008a06cf02c71175
theorem AvailableChain.FGSA.Run.FinalityBatchCoverage_W_def d49af754fb7fb26c
```

### `AvailableChainFGSAClaims.Statements.FrameNext`

```text
def AvailableChain.FGSA.Run.frameRNext 33b7c1ef71276d31
theorem AvailableChain.FGSA.Run.frameRNext_def 649e816c96f958ce
def AvailableChain.FGSA.Run.domainRNext 214f5b1a1f9887f2
theorem AvailableChain.FGSA.Run.domainRNext_def 3a2c2f087ea67909
def AvailableChain.FGSA.Run.RFrameExactNext 20538506b0b8c025
theorem AvailableChain.FGSA.Run.RFrameExactNext_def a77c2f3c3d9250e5
def AvailableChain.FGSA.Run.RFrameNext 01fcc16bc1139a1c
theorem AvailableChain.FGSA.Run.RFrameNext_def 1af9547fcc16c6a8
def AvailableChain.FGSA.Run.TStartNext 3e726b352788b587
def AvailableChain.FGSA.Run.WalkBatchNext 4060da2514e01eb4
def AvailableChain.FGSA.Run.TWalkNext 2cbfd79b34ead0fc
def AvailableChain.FGSA.Run.SettledPhaseFrameNext 63c3a6c59e1b286f
theorem AvailableChain.FGSA.Run.SettledPhaseFrameNext_def c5096ec9c41a3e33
def AvailableChain.FGSA.Run.TGeomNext bc7a5e607c99c83b
def AvailableChain.FGSA.Run.OpeningCoveredNext 7f67f925c0a566b6
def AvailableChain.FGSA.Run.FrameAtNext 0712a93cb431fc70
def AvailableChain.FGSA.Run.RFrameNextEpoch d7f8656d2c25d784
theorem AvailableChain.FGSA.Run.RFrameNextEpoch_def 02297ec641fc3f00
```

### `AvailableChainFGSAClaims.Statements.Healed`

```text
def AvailableChain.FGSA.Run.healStart f6480b01bf246b0e
def AvailableChain.FGSA.Run.HealSuffix ae00fba281759cd2
def AvailableChain.FGSA.Run.Healed 6dc6ac818f0b10e4
def AvailableChain.FGSA.Run.H2A bd3bc2cdb383cfb5
def AvailableChain.FGSA.Run.H2Prime 37851a9a02794f71
def AvailableChain.FGSA.Run.H3 6b836bf82539f889
def AvailableChain.FGSA.Run.H4 24b6e258058841f4
def AvailableChain.FGSA.Run.H5RawTransfer e9cb8e437d744287
def AvailableChain.FGSA.Run.H6GateService f8bb019a4ca1af9c
structure AvailableChain.FGSA.Run.HealT 15acd71b6e85788d
ctor AvailableChain.FGSA.Run.HealT.mk 6d6ab7eee43ee327
field AvailableChain.FGSA.Run.HealT.h1 d84d6dd1cc931fc2
field AvailableChain.FGSA.Run.HealT.h2 c1f0ba57c5a4a756
field AvailableChain.FGSA.Run.HealT.rows 88b7ee71bdd16655
structure AvailableChain.FGSA.Run.HealAC d6ddd1b8a35ff5b6
ctor AvailableChain.FGSA.Run.HealAC.mk 18d13295b4663a19
field AvailableChain.FGSA.Run.HealAC.h2A b664dd45c299dbbd
field AvailableChain.FGSA.Run.HealAC.h2' 7a708d9685489640
field AvailableChain.FGSA.Run.HealAC.h3 01cf68a9f557101d
field AvailableChain.FGSA.Run.HealAC.h4 fa39823148fd4f78
field AvailableChain.FGSA.Run.HealAC.h5 8001741381517f6e
field AvailableChain.FGSA.Run.HealAC.h6 00e15120f7eaccb3
structure AvailableChain.FGSA.Run.HealingInput 32780bd541071dee
ctor AvailableChain.FGSA.Run.HealingInput.mk 8f97db1991f1a24f
field AvailableChain.FGSA.Run.HealingInput.healed a2eeadc8991e253e
field AvailableChain.FGSA.Run.HealingInput.wit b77c128112f55119
field AvailableChain.FGSA.Run.HealingInput.t b94d95c0219ec028
field AvailableChain.FGSA.Run.HealingInput.ac 0c93d433a7964afd
def AvailableChain.FGSA.Run.HTimeStatement 1b11b0af791acdd5
theorem AvailableChain.FGSA.Run.HTimeStatement_def 443015d09dde4de8
theorem AvailableChain.FGSA.Run.HealSuffix_def cd16c5329656c090
theorem AvailableChain.FGSA.Run.healStart_def 258cbf12e812cf49
```

### `AvailableChainFGSAClaims.Statements.HealedBest`

```text
def AvailableChain.FGSA.Run.HTimeBestConcl 8f6c3f8316c557f0
theorem AvailableChain.FGSA.Run.HTimeBestConcl_def 3a552e73dcb7aadd
```

### `AvailableChainFGSAClaims.Statements.Join`

```text
def AvailableChain.FGSA.Run.slotStartZ 73d5d2251c2a66ad
def AvailableChain.FGSA.Run.voteZ 0c27eeb3ac9a683b
def AvailableChain.FGSA.Run.slotAt 51d57281df64e3ec
def AvailableChain.FGSA.Run.AwakeClosed 1fa42676af0a84e3
def AvailableChain.FGSA.Run.RestartFreeTime 32854feb7b5c727f
def AvailableChain.FGSA.Run.joinedAt 4de866f7954997f8
def AvailableChain.FGSA.Run.joinedDuty ab4369bc5987a225
def AvailableChain.FGSA.Run.enabledGateAt 934f31bfb248203e
def AvailableChain.FGSA.Run.gatePassedAt 703387bcf5f4ec09
def AvailableChain.FGSA.Run.caughtUpAtIdx c96b2d2e17bcc332
def AvailableChain.FGSA.Run.caughtUpAt 4c74101a897b1e10
def AvailableChain.FGSA.Run.confirmedReaderAtIdx 159b93fc3b36e976
def AvailableChain.FGSA.Run.confirmedReader e42e8626ac78401f
def AvailableChain.FGSA.Run.headReader 7d4727ecac3d9ff9
def AvailableChain.FGSA.Run.ScopedCompat 5fabc314d35614b8
def AvailableChain.FGSA.Run.ScopedMono 685881e678dbe31d
def AvailableChain.FGSA.Run.ScopedServed 35d3bc3d0ed1cf23
def AvailableChain.FGSA.Run.prefixTime 8c835dcc04a5906d
def AvailableChain.FGSA.Run.WakesAppliedAtIdx a3d765f7343fea85
def AvailableChain.FGSA.Run.confirmedReaderIdx ccfdc522c8f49cab
def AvailableChain.FGSA.Run.joinedHonest e75c46dc1de0aeb2
def AvailableChain.FGSA.Run.sleepyBad d02da28b56c75d47
def AvailableChain.FGSA.Run.firstUpdateLabel 12e6a4e14b32999f
def AvailableChain.FGSA.Run.tauC 765f1712a05f6613
def AvailableChain.FGSA.Run.recoveryStart 5423120bd1a9c25b
def AvailableChain.FGSA.Run.recoveryDelay 691f8f72a30651cd
def AvailableChain.FGSA.Run.B_HF_sleep 3e210b3510860459
def AvailableChain.FGSA.Run.B_resetF_sleep 72a13e2e12c9b6b6
def AvailableChain.FGSA.Run.B_FW_sleep 384a264acc762a1a
def AvailableChain.FGSA.Run.coverLabel d0c1413c8201de47
def AvailableChain.FGSA.Run.coverDeadline 326eb2b63b59a3d2
def AvailableChain.FGSA.Run.slowCoveredSchedule b239c45e03ab4ebd
def AvailableChain.FGSA.Run.fastCoveredSchedule 1a553e7cbe5ba63b
def AvailableChain.FGSA.Run.coveredNodes c0cc2cecc1aaa405
def AvailableChain.FGSA.Run.outageH 9c9bd6a66622ca2d
def AvailableChain.FGSA.Run.OutageVoteMember 52d02dd5f16c4068
def AvailableChain.FGSA.Run.outageW 86b31d4801e25430
def AvailableChain.FGSA.Run.ReceiptObjectAt 6efe46d566df6bb5
def AvailableChain.FGSA.Run.BatchReceiptAt 56506320f92d7633
def AvailableChain.FGSA.Run.OutagePrefixReceipt 8ec6aa41fc9ea79c
def AvailableChain.FGSA.Run.restoredLabel 5cb38f3349327b62
def AvailableChain.FGSA.Run.FirstRestored 3f25cacc48137f23
def AvailableChain.FGSA.Run.OutageContinuationReceipt c1529c7ccdb6ad97
def AvailableChain.FGSA.Run.OutageE fdb3065d1bec382e
def AvailableChain.FGSA.Run.OutageE1 efca814ddc99f7d8
def AvailableChain.FGSA.Run.OutageEnd 74ec34f2f7da6bd4
def AvailableChain.FGSA.Run.outageHeadReader f6f8f60f2efc9d4c
def AvailableChain.FGSA.Run.outageConfirmedReader 4c756cfe029b8de8
def AvailableChain.FGSA.Run.DutiesExtendScoped 3a54a7543692cc40
```

### `AvailableChainFGSAClaims.Statements.LiveDC`

```text
def AvailableChain.FGSA.Run.liveDCDeadline_W 98bb35b3a856b670
theorem AvailableChain.FGSA.Run.liveDCDeadline_W_def 69c7b1824c4488b2
def AvailableChain.FGSA.Run.LiveDCConcl_W 309449776e78866c
theorem AvailableChain.FGSA.Run.LiveDCConcl_W_def 174b64120ec9d10f
def AvailableChain.FGSA.Run.LiveDCFromWindowsStatement 735300f9ae3a344a
theorem AvailableChain.FGSA.Run.LiveDCFromWindowsStatement_def eb1006cb9311c283
```

### `AvailableChainFGSAClaims.Statements.OutageContinuation`

```text
def AvailableChain.FGSA.Run.OutageLengthV df9f8cdb53ebe336
theorem AvailableChain.FGSA.Run.OutageLengthV_def a5143e0190facb37
structure AvailableChain.FGSA.Run.OutageContinuationPrem d16cf4d943149b8a
ctor AvailableChain.FGSA.Run.OutageContinuationPrem.mk 193873576286b423
field AvailableChain.FGSA.Run.OutageContinuationPrem.pre 20d916adb425c6a3
field AvailableChain.FGSA.Run.OutageContinuationPrem.sleepy 9545927371e7ae4b
field AvailableChain.FGSA.Run.OutageContinuationPrem.order 16d226d654b180de
field AvailableChain.FGSA.Run.OutageContinuationPrem.lag 5e66ddfda3ff1c59
field AvailableChain.FGSA.Run.OutageContinuationPrem.lengthV e0dd6e2438bd83e1
field AvailableChain.FGSA.Run.OutageContinuationPrem.fastPart 0982ef0b00a78c7e
field AvailableChain.FGSA.Run.OutageContinuationPrem.sync 62eb85c98519bd0b
field AvailableChain.FGSA.Run.OutageContinuationPrem.gst 0873886185da4f5a
field AvailableChain.FGSA.Run.OutageContinuationPrem.partAfter 5d424be44ad9f881
def AvailableChain.FGSA.Run.OutageRepairReady f50983792c00ad02
def AvailableChain.FGSA.Run.OutageContinuationConcl 7d400cefdc047217
structure AvailableChain.FGSA.Run.OutageContinuationSleepPrem 3f9e888257f5e977
field AvailableChain.FGSA.Run.OutageContinuationSleepPrem.toOutageContinuationPrem b18c4fb91c11164e
ctor AvailableChain.FGSA.Run.OutageContinuationSleepPrem.mk 78b9391b6bcd8334
field AvailableChain.FGSA.Run.OutageContinuationSleepPrem.sleepPre 808b55d893234c8f
field AvailableChain.FGSA.Run.OutageContinuationSleepPrem.joinedSleepy 761b5f489c28b76f
field AvailableChain.FGSA.Run.OutageContinuationSleepPrem.joinedFastPart cca3143142fa6077
field AvailableChain.FGSA.Run.OutageContinuationSleepPrem.protection 87567c3e58b36aa0
field AvailableChain.FGSA.Run.OutageContinuationSleepPrem.joinedPartAfter fcef54d9e50a35ec
field AvailableChain.FGSA.Run.OutageContinuationSleepPrem.sleepyAfter 1f33c160b1350c48
```

### `AvailableChainFGSAClaims.Statements.OutageSleep`

```text
def AvailableChain.FGSA.Run.OutagePrefixReceiptDerivedClaim 3537aa8e6b06093b
def AvailableChain.FGSA.Run.OutageContinuationReceiptDerivedClaim 81b26b9300ef2360
def AvailableChain.FGSA.Run.OutageE1DerivedClaim 0bbcc4801b268f0f
```

### `AvailableChainFGSAClaims.Statements.OutputReads`

```text
def AvailableChain.FGSA.Run.ServedFromGateAt 94e76e9e705f41fc
theorem AvailableChain.FGSA.Run.ServedFromGateAt_def ae7f6a4e74ab3629
def AvailableChain.FGSA.Run.JointGrowthAt 53baa948ff61048f
theorem AvailableChain.FGSA.Run.JointGrowthAt_def 34475b4aba3d5a7f
```

### `AvailableChainFGSAClaims.Statements.Packages.Finality`

```text
inductive AvailableChain.FGSA.Run.FinFormW e65aa35faec5d780
ctor AvailableChain.FGSA.Run.FinFormW.recFE f5bdcad089b74a37
ctor AvailableChain.FGSA.Run.FinFormW.recF4 9740b2983363dec5
def AvailableChain.FGSA.Run.FinFormW.holdsW 4649365580aa48ae
theorem AvailableChain.FGSA.Run.FinFormW.holdsW_def 0c25c65a15eb1f5b
structure AvailableChain.FGSA.Run.FinalitySet_W 66616e5da3b241f9
ctor AvailableChain.FGSA.Run.FinalitySet_W.mk 5546f1823993a8a9
field AvailableChain.FGSA.Run.FinalitySet_W.core 4abdfd71def516bd
field AvailableChain.FGSA.Run.FinalitySet_W.bound eeaeb3b78de10b23
field AvailableChain.FGSA.Run.FinalitySet_W.recur cad7527b729e913f
def AvailableChain.FGSA.Run.finalityWindow_W 257edaf1d0233a74
theorem AvailableChain.FGSA.Run.finalityWindow_W_def 7713675ab497d5a2
structure AvailableChain.FGSA.Run.FirstFinalityPrem_W 883902a991ea14bf
ctor AvailableChain.FGSA.Run.FirstFinalityPrem_W.mk cfc658dddb680ddf
field AvailableChain.FGSA.Run.FirstFinalityPrem_W.set 2d71d8e3b1b03f1a
field AvailableChain.FGSA.Run.FirstFinalityPrem_W.hhor 8b5a53ba325ec894
structure AvailableChain.FGSA.Run.FinalityLivenessPrem_W 7738db13c7d4113d
ctor AvailableChain.FGSA.Run.FinalityLivenessPrem_W.mk 53751b13eac74c56
field AvailableChain.FGSA.Run.FinalityLivenessPrem_W.set 9812371b3d6064a4
field AvailableChain.FGSA.Run.FinalityLivenessPrem_W.input 6b83cb720e51ab73
field AvailableChain.FGSA.Run.FinalityLivenessPrem_W.start 1037035a15294b92
field AvailableChain.FGSA.Run.FinalityLivenessPrem_W.hhor a812e7633817d28b
structure AvailableChain.FGSA.Run.ProposalFinalPrem_W 36d46dc46fc301e2
ctor AvailableChain.FGSA.Run.ProposalFinalPrem_W.mk 28e7acffa94082eb
field AvailableChain.FGSA.Run.ProposalFinalPrem_W.set 289f4fa02cb02cde
field AvailableChain.FGSA.Run.ProposalFinalPrem_W.input 0d9bae7c36078e1d
field AvailableChain.FGSA.Run.ProposalFinalPrem_W.prop 19f091adf4f3c477
field AvailableChain.FGSA.Run.ProposalFinalPrem_W.start 07df22499e84acc0
field AvailableChain.FGSA.Run.ProposalFinalPrem_W.hhor 3846438e5765da19
structure AvailableChain.FGSA.Run.AboveFrontierPrem_W 85da67367dce5747
ctor AvailableChain.FGSA.Run.AboveFrontierPrem_W.mk e5b48df3b143a222
field AvailableChain.FGSA.Run.AboveFrontierPrem_W.set e7affdd23c35b3b5
field AvailableChain.FGSA.Run.AboveFrontierPrem_W.input 08ffef2463a1b3c9
field AvailableChain.FGSA.Run.AboveFrontierPrem_W.start 2a93f0c5653f73ea
field AvailableChain.FGSA.Run.AboveFrontierPrem_W.firstHorizon ad1817de05fb9c3d
field AvailableChain.FGSA.Run.AboveFrontierPrem_W.hhor 49910ddffb8625c7
```

### `AvailableChainFGSAClaims.Statements.Packages.FinalityGST`

```text
structure AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W 1cb807d623156701
ctor AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.mk 64953c2d6b2fb700
field AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.set 0821670fb4bd165d
field AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.late 2b29110aef092447
field AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.hhor e53ae53cf955b74e
structure AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W 2e4b3bd140065643
ctor AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.mk e343da0538247b38
field AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.set c7331074161e94b1
field AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.prop 71827169dcbafa19
field AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.late c85a9bec7ded68f0
field AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.hhor 9aa0f850133f420f
structure AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W a645bb855c2aa61b
ctor AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.mk ca16462b6e68f48c
field AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.set dcb1bfc9a049ae82
field AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.late 1cc0953fad8e252b
field AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.hhor 326d558954714d43
```

### `AvailableChainFGSAClaims.Statements.Packages.Healing`

```text
structure AvailableChain.FGSA.Run.PtU cdac5d36b3aeedbe
ctor AvailableChain.FGSA.Run.PtU.mk 625fb9a6fbf8a302
field AvailableChain.FGSA.Run.PtU.u 40df3815e8005f72
structure AvailableChain.FGSA.Run.PtW eb1adc0bd9b6b352
ctor AvailableChain.FGSA.Run.PtW.mk 711d02cd9776871a
field AvailableChain.FGSA.Run.PtW.w cf526e58be9745f5
structure AvailableChain.FGSA.Run.PtM 059377273aab57dc
ctor AvailableChain.FGSA.Run.PtM.mk e29feda302f8ab79
field AvailableChain.FGSA.Run.PtM.m 4751e98c84b7e6b1
structure AvailableChain.FGSA.Run.PtR 3dd0516b2fc1a7b0
ctor AvailableChain.FGSA.Run.PtR.mk 6f9192a830d167ad
field AvailableChain.FGSA.Run.PtR.r 4752d821807cec4c
structure AvailableChain.FGSA.Run.PtK cf42500a5cf0ea56
ctor AvailableChain.FGSA.Run.PtK.mk 8ef059b2f2ea090a
field AvailableChain.FGSA.Run.PtK.k d4dcaa4e26dd6859
structure AvailableChain.FGSA.Run.HealingPrem a497e49e219a7b93
ctor AvailableChain.FGSA.Run.HealingPrem.mk 1de86cd4009652d8
field AvailableChain.FGSA.Run.HealingPrem.set 7a2dd4d0affc8d4b
field AvailableChain.FGSA.Run.HealingPrem.bound 6216cf68bebdd750
structure AvailableChain.FGSA.Run.HealingWitnessPrem bfa818d1a79a8cb6
field AvailableChain.FGSA.Run.HealingWitnessPrem.toHealingPrem 282944f19f2d2c86
ctor AvailableChain.FGSA.Run.HealingWitnessPrem.mk ec4cca3645799e89
field AvailableChain.FGSA.Run.HealingWitnessPrem.h0 6ce903e9e3051f8c
structure AvailableChain.FGSA.Run.HealingTimePrem 9769ce6f33d4d111
field AvailableChain.FGSA.Run.HealingTimePrem.toHealingPrem f2b16c1d908de350
ctor AvailableChain.FGSA.Run.HealingTimePrem.mk c7b5f609d2045686
field AvailableChain.FGSA.Run.HealingTimePrem.hhor 07e1d9eff80ac0c1
structure AvailableChain.FGSA.Run.ResetArrivalPrem 6a50d2a6947eb97c
field AvailableChain.FGSA.Run.ResetArrivalPrem.toHealingPrem e795e5ae1d3a745d
ctor AvailableChain.FGSA.Run.ResetArrivalPrem.mk cfe63cda1de18761
field AvailableChain.FGSA.Run.ResetArrivalPrem.hhor becf6655806e083b
structure AvailableChain.FGSA.Run.ResetArrivalFullPrem 17ad7ef5b7119c7f
field AvailableChain.FGSA.Run.ResetArrivalFullPrem.toHealingPrem 58d6fb2e978ec4d4
ctor AvailableChain.FGSA.Run.ResetArrivalFullPrem.mk 8efc20efd56fdcd0
field AvailableChain.FGSA.Run.ResetArrivalFullPrem.hhor b37b5ecc66f604f6
structure AvailableChain.FGSA.Run.KernelJoinedPrem 40b90a48eecbfd7c
ctor AvailableChain.FGSA.Run.KernelJoinedPrem.mk 84b67fa3853e950e
field AvailableChain.FGSA.Run.KernelJoinedPrem.set 0fa435edb112a475
field AvailableChain.FGSA.Run.KernelJoinedPrem.bound 3503d6d7b09a0198
field AvailableChain.FGSA.Run.KernelJoinedPrem.window 1e748b0ef6bd98c8
field AvailableChain.FGSA.Run.KernelJoinedPrem.start 59cc95fbdf92d22b
field AvailableChain.FGSA.Run.KernelJoinedPrem.hhor ecafdaba5ff9e99a
structure AvailableChain.FGSA.Run.HealingAttemptPrem e6dce82675eb5650
field AvailableChain.FGSA.Run.HealingAttemptPrem.toHealingPrem b7d337fddfee4389
ctor AvailableChain.FGSA.Run.HealingAttemptPrem.mk 1614ea9551a6a91d
field AvailableChain.FGSA.Run.HealingAttemptPrem.valid afb65e3546cf242b
field AvailableChain.FGSA.Run.HealingAttemptPrem.hhor d0f8076ac3ba3559
structure AvailableChain.FGSA.Run.HealingInputPrem b7732c5d9651f919
field AvailableChain.FGSA.Run.HealingInputPrem.toHealingWitnessPrem 8dd0b5eb9ab0519f
ctor AvailableChain.FGSA.Run.HealingInputPrem.mk be891ad164d20bfa
field AvailableChain.FGSA.Run.HealingInputPrem.hhor 36da131eec8d8861
structure AvailableChain.FGSA.Run.RenewedPromotionPrem 094fd0c0d145f52e
field AvailableChain.FGSA.Run.RenewedPromotionPrem.toHealingPrem dbab31fd916055b3
ctor AvailableChain.FGSA.Run.RenewedPromotionPrem.mk d91daf44c2b1828f
field AvailableChain.FGSA.Run.RenewedPromotionPrem.hhor 4b3d03507d559778
```

### `AvailableChainFGSAClaims.Statements.Packages.Inclusion`

```text
structure AvailableChain.FGSA.Run.CleanInclusionPrem 94afd59a51cfeddf
ctor AvailableChain.FGSA.Run.CleanInclusionPrem.mk 67acdbbb84c244cc
field AvailableChain.FGSA.Run.CleanInclusionPrem.set cb34da561379cabf
field AvailableChain.FGSA.Run.CleanInclusionPrem.prop 27482f5b450b61fd
field AvailableChain.FGSA.Run.CleanInclusionPrem.hhor 22dff59253f5c220
structure AvailableChain.FGSA.Run.ExactProposalPrem a08576cab214bcad
ctor AvailableChain.FGSA.Run.ExactProposalPrem.mk 4c71d0a0cd54b4c6
field AvailableChain.FGSA.Run.ExactProposalPrem.set 6ba5e88bdf35a90b
field AvailableChain.FGSA.Run.ExactProposalPrem.prop 7ccee9bc96bda509
field AvailableChain.FGSA.Run.ExactProposalPrem.hhor 0b2b5937f11f2298
```

### `AvailableChainFGSAClaims.Statements.Packages.Outage`

```text
structure AvailableChain.FGSA.Run.OutagePrem 6fdf289aee19ba96
ctor AvailableChain.FGSA.Run.OutagePrem.mk 9b03ca00632e321e
field AvailableChain.FGSA.Run.OutagePrem.set 2416f091d5b22c29
```

### `AvailableChainFGSAClaims.Statements.Packages.Safety`

```text
structure AvailableChain.FGSA.Run.PtS 3ddf285bec98b83f
ctor AvailableChain.FGSA.Run.PtS.mk e720a461b1a5424f
field AvailableChain.FGSA.Run.PtS.s 5bb84050690af37e
structure AvailableChain.FGSA.Run.PtSP fc8097886eb4d267
ctor AvailableChain.FGSA.Run.PtSP.mk 4958d7d8e28fc3d5
field AvailableChain.FGSA.Run.PtSP.s cf868e7b2f18c993
field AvailableChain.FGSA.Run.PtSP.P a52da557be0edaf9
structure AvailableChain.FGSA.Run.PtSX 24cf4f0edad717bf
ctor AvailableChain.FGSA.Run.PtSX.mk e83b82d3cde3d0fa
field AvailableChain.FGSA.Run.PtSX.s 70175b03c2a302e4
field AvailableChain.FGSA.Run.PtSX.X e89f8f1bdf903974
structure AvailableChain.FGSA.Run.BasePrem db87c2ec0e2c32f1
ctor AvailableChain.FGSA.Run.BasePrem.mk 088ab7edd752d7e7
field AvailableChain.FGSA.Run.BasePrem.set 779cd8c196fdcb3b
structure AvailableChain.FGSA.Run.SameLabelPrem df7c71569aafa4a0
ctor AvailableChain.FGSA.Run.SameLabelPrem.mk 04d7804870b52ffa
field AvailableChain.FGSA.Run.SameLabelPrem.set 533b1e1f75152201
field AvailableChain.FGSA.Run.SameLabelPrem.sync 5b00384eecafce86
structure AvailableChain.FGSA.Run.SourceDisciplinePrem 640b6d4cec57c146
ctor AvailableChain.FGSA.Run.SourceDisciplinePrem.mk a19a1505e6af437c
field AvailableChain.FGSA.Run.SourceDisciplinePrem.set a43287ae64e9773d
field AvailableChain.FGSA.Run.SourceDisciplinePrem.quorum 06ae7edb14e7b774
structure AvailableChain.FGSA.Run.FinalizedSafetyPrem 7f268747e74e8cb0
ctor AvailableChain.FGSA.Run.FinalizedSafetyPrem.mk 1c072af38153a396
field AvailableChain.FGSA.Run.FinalizedSafetyPrem.set d8b2d30422ae621f
field AvailableChain.FGSA.Run.FinalizedSafetyPrem.fault 8604b1420e0537c7
structure AvailableChain.FGSA.Run.CleanPrem 5666118343bb5989
ctor AvailableChain.FGSA.Run.CleanPrem.mk da5fe613cc0d2e56
field AvailableChain.FGSA.Run.CleanPrem.set c0935ea381864037
structure AvailableChain.FGSA.Run.CleanPrefixPrem 4dc6a1058d8f5044
ctor AvailableChain.FGSA.Run.CleanPrefixPrem.mk 2d7439d25a83e3f2
field AvailableChain.FGSA.Run.CleanPrefixPrem.set 07df60cb737abce4
structure AvailableChain.FGSA.Run.CleanCutPrem a72110dff7114939
ctor AvailableChain.FGSA.Run.CleanCutPrem.mk 57727982c8ac7239
field AvailableChain.FGSA.Run.CleanCutPrem.set 5a5ba9c453da1b53
structure AvailableChain.FGSA.Run.ReleasePrem 4e1dc90fee2baba9
ctor AvailableChain.FGSA.Run.ReleasePrem.mk b50ee400a4e4c108
field AvailableChain.FGSA.Run.ReleasePrem.set 5431d56187ae0114
field AvailableChain.FGSA.Run.ReleasePrem.lt 7675014a8cd3be40
```

### `AvailableChainFGSAClaims.Statements.Phases`

```text
def AvailableChain.FGSA.Run.finHeight 45ca642905486866
structure AvailableChain.FGSA.Run.FreshPrem 201ed420b6857ac2
ctor AvailableChain.FGSA.Run.FreshPrem.mk 4d63465a1ab5116d
field AvailableChain.FGSA.Run.FreshPrem.base 66f9c64a230a11c3
field AvailableChain.FGSA.Run.FreshPrem.faultQ 0323fc8e3f9b7499
field AvailableChain.FGSA.Run.FreshPrem.cut e2b1249aaeac0861
field AvailableChain.FGSA.Run.FreshPrem.early 4a60e44181c35259
field AvailableChain.FGSA.Run.FreshPrem.rows c0d59ec04e961283
field AvailableChain.FGSA.Run.FreshPrem.noNextRow ab8077397d2e7219
field AvailableChain.FGSA.Run.FreshPrem.noFinRow d956b583fd93e0f2
def AvailableChain.FGSA.Run.JustifyAt 4f632ffc688bc358
def AvailableChain.FGSA.Run.JustifyFresh_W 0fd1ea3922df30a4
def AvailableChain.FGSA.Run.Ready_W 57ec56e889164ceb
def AvailableChain.FGSA.Run.receiptInsert_W 64c4e34d9291ae89
structure AvailableChain.FGSA.Run.ReceiptWitness_W 96480f7d786199e2
ctor AvailableChain.FGSA.Run.ReceiptWitness_W.mk 1c433d7a0bb74541
field AvailableChain.FGSA.Run.ReceiptWitness_W.index d94469eb94339260
field AvailableChain.FGSA.Run.ReceiptWitness_W.time 4a999c5986ac6c0a
structure AvailableChain.FGSA.Run.BlockDelivery_W e3a322c36b218d0c
ctor AvailableChain.FGSA.Run.BlockDelivery_W.mk 4d1e06f5d83f4e4c
field AvailableChain.FGSA.Run.BlockDelivery_W.selected 5d024607f1bbe8b1
field AvailableChain.FGSA.Run.BlockDelivery_W.witness 30cc372b11576197
structure AvailableChain.FGSA.Run.AcceptGuards_W 3e7c872056114bc3
ctor AvailableChain.FGSA.Run.AcceptGuards_W.mk 6b184c9562e37973
field AvailableChain.FGSA.Run.AcceptGuards_W.finCmp d2b6be4536bbbf8c
field AvailableChain.FGSA.Run.AcceptGuards_W.jPath 7b0d51efcc204b4c
field AvailableChain.FGSA.Run.AcceptGuards_W.cap 37c9072fa1343ca3
structure AvailableChain.FGSA.Run.AcceptPrem_W eb2a83d7a31e7621
ctor AvailableChain.FGSA.Run.AcceptPrem_W.mk eddc1b8b2926ec82
field AvailableChain.FGSA.Run.AcceptPrem_W.base d1bcf59e4d47b47c
field AvailableChain.FGSA.Run.AcceptPrem_W.faultBound a10c2af96d70a50d
field AvailableChain.FGSA.Run.AcceptPrem_W.finalized 9813d599bbbb736e
field AvailableChain.FGSA.Run.AcceptPrem_W.deliver 3f8ec8c760e0ed9a
field AvailableChain.FGSA.Run.AcceptPrem_W.guards 01b6f66f40ac2664
field AvailableChain.FGSA.Run.AcceptPrem_W.horizon 366bd6ec3b983105
def AvailableChain.FGSA.Run.AcceptBefore_W d8e89b087aad8da6
structure AvailableChain.FGSA.Run.FinalizePrem_W 4edf75b52b3675fc
ctor AvailableChain.FGSA.Run.FinalizePrem_W.mk daea720afba08732
field AvailableChain.FGSA.Run.FinalizePrem_W.fold d873dedd2469dbac
field AvailableChain.FGSA.Run.FinalizePrem_W.base cc8540ceaa8f1f3d
field AvailableChain.FGSA.Run.FinalizePrem_W.faultBound 60f2c594a6b70cf2
field AvailableChain.FGSA.Run.FinalizePrem_W.deliver 21628c83cc6a4731
field AvailableChain.FGSA.Run.FinalizePrem_W.guards c5bb8d14ff8c3440
field AvailableChain.FGSA.Run.FinalizePrem_W.horizon eb3c0cb876a75b8c
def AvailableChain.FGSA.Run.FinalizePending_W 984dbc1bdc65e90c
theorem AvailableChain.FGSA.Run.JustifyAt_def cb9916438df18f33
theorem AvailableChain.FGSA.Run.JustifyFresh_W_def 0d814cd982e426d8
theorem AvailableChain.FGSA.Run.Ready_W_def 24f755994f80e005
theorem AvailableChain.FGSA.Run.receiptInsert_W_def 4b9634e27d0b9dac
theorem AvailableChain.FGSA.Run.AcceptBefore_W_def 6f2fd191594b732f
theorem AvailableChain.FGSA.Run.FinalizePending_W_def 1f65bb85b6005369
def AvailableChain.FGSA.Run.FreshFinalityRows_W e1b0bbd36fbc7623
structure AvailableChain.FGSA.Run.TerminalCarriagePrem_W 79bf32ba52359340
ctor AvailableChain.FGSA.Run.TerminalCarriagePrem_W.mk 400aac04cdecc7a8
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.base 311d4f03038388bb
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.faultQ 853302a5f85357f8
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.deltaF df4fa3c787f1ffe9
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.carrier 61bf4d7a1863af4c
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.parent b41d13e5d9b1d7a5
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.path c1b37b300837ecf7
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.freshHeight f9f9138ff6f6971b
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.retainedOrCovered 27a24ca83c2a48d4
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.horizon 4be4ecfb636def40
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.seats 43075e16ccea65c1
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.rows 22c1e736f5d69dd3
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.fresh df8cbc613845e815
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.heightEntry 22ea5a5addbff9b1
field AvailableChain.FGSA.Run.TerminalCarriagePrem_W.receipt 296da6fdaa468285
def AvailableChain.FGSA.Run.TerminalCarriage_W aaad1a0938bdd5c3
theorem AvailableChain.FGSA.Run.FreshFinalityRows_W_def fd7626c43cf1632b
theorem AvailableChain.FGSA.Run.TerminalCarriage_W_def 24a6ab8474ba9dbc
theorem AvailableChain.FGSA.Run.finHeight_def 9b7a4c751f560d6e
```

### `AvailableChainFGSAClaims.Statements.Reads`

```text
def AvailableChain.FGSA.Run.cutPred 3c25f45ea3dd1e64
def AvailableChain.FGSA.Run.afterTicksIdx fa2bf1c57bf37a45
def AvailableChain.FGSA.Run.SuffixIdx c99ac279f60dfd73
def AvailableChain.FGSA.Run.timeIdx 95f9d6305e8acf84
def AvailableChain.FGSA.Run.afterTicks 471393c48a52aa8a
def AvailableChain.FGSA.Run.preTick 214a3db929c139fc
theorem AvailableChain.FGSA.Run.preTick_def 4e0b8b76fc8422d2
def AvailableChain.FGSA.Run.postClock fa10da1ff3118dc7
theorem AvailableChain.FGSA.Run.postClock_def 72ce1732777b08e9
def AvailableChain.FGSA.Run.postTick 4b0ae333cc158bb0
def AvailableChain.FGSA.Run.storeAt 9d695017dcd7df2b
def AvailableChain.FGSA.Run.S_at b0e45bf38f3f9726
def AvailableChain.FGSA.Run.F_at 4c2aa1259065e285
def AvailableChain.FGSA.Run.J_at c81ca94e24894738
def AvailableChain.FGSA.Run.gateIn 7917e784915075fb
theorem AvailableChain.FGSA.Run.gateIn_def b00f95a421606f1d
def AvailableChain.FGSA.Run.gateResult 2972947bc66a6b92
theorem AvailableChain.FGSA.Run.gateResult_def 3805713ef8908464
def AvailableChain.FGSA.Run.isGateTime de71406ad46da144
theorem AvailableChain.FGSA.Run.isGateTime_def a991674f5c9d52f5
def AvailableChain.FGSA.Run.IsGateTick 07c83f92da67adb9
def AvailableChain.FGSA.Run.gateResultAt d9ca5a731e1f4218
def AvailableChain.FGSA.Run.fastAt a0b175a140143670
def AvailableChain.FGSA.Run.headAtIdx 64c0f9f5ca179b9d
def AvailableChain.FGSA.Run.vHead 6bb013f757f686de
theorem AvailableChain.FGSA.Run.vHead_def 4869b1c39f81b5ff
def AvailableChain.FGSA.Run.actionSourceFG 777a51685eb9b07a
theorem AvailableChain.FGSA.Run.actionSourceFG_def 0898a481435365fd
def AvailableChain.FGSA.Run.actionSource 7dbe35edbcfe919b
def AvailableChain.FGSA.Run.labelBoundAt cde9d49f0eeea8d5
def AvailableChain.FGSA.Run.DeliveredAt 509e97dce026ceca
def AvailableChain.FGSA.Run.HandlesRowAt 322d4dc49308546d
def AvailableChain.FGSA.Run.AcceptsFinalBefore 3a8243e82924854a
def AvailableChain.FGSA.Run.cleanResults a1b0267154f49024
def AvailableChain.FGSA.Run.BelowLabel b6bad33315c20dab
theorem AvailableChain.FGSA.Run.S_at_def 1bbbc22f8b010c73
def AvailableChain.FGSA.Run.diagnosticGateResult 7a01a7862b4a5d59
```

### `AvailableChainFGSAClaims.Statements.Recurrence`

```text
```

### `AvailableChainFGSAClaims.Statements.Regimes`

```text
structure AvailableChain.FGSA.Run.Base₂ 61af3fdedad7a9e0
ctor AvailableChain.FGSA.Run.Base₂.mk 50171d4783db1115
field AvailableChain.FGSA.Run.Base₂.valid 2b8fef5e3a91c1f4
field AvailableChain.FGSA.Run.Base₂.linked 4cc7e197d40ee15e
field AvailableChain.FGSA.Run.Base₂.cstar 61bab511f621259c
field AvailableChain.FGSA.Run.Base₂.restartsAtWakes f86eee8de202dbac
field AvailableChain.FGSA.Run.Base₂.delta 77aaa0e6bf669320
field AvailableChain.FGSA.Run.Base₂.receiptIdealization d524d57a523285f7
theorem AvailableChain.FGSA.Run.Base₂.idealization 5158f7cba1651505
structure AvailableChain.FGSA.Run.HealthyPrefix₂ eaefc571c2b92a42
ctor AvailableChain.FGSA.Run.HealthyPrefix₂.mk aa17e0fc01af6d3c
field AvailableChain.FGSA.Run.HealthyPrefix₂.base 8c97fee05ca99754
field AvailableChain.FGSA.Run.HealthyPrefix₂.cut d22c2ebd0af31650
field AvailableChain.FGSA.Run.HealthyPrefix₂.healthy 411e289aa005d909
field AvailableChain.FGSA.Run.HealthyPrefix₂.deltaF 08f70c6527716029
field AvailableChain.FGSA.Run.HealthyPrefix₂.partBefore cfa0a3ca378afbb4
structure AvailableChain.FGSA.Run.CleanPrefix₂ fc94450d46008f33
field AvailableChain.FGSA.Run.CleanPrefix₂.toHealthyPrefix₂ 7dd2e9e9b8dbf979
ctor AvailableChain.FGSA.Run.CleanPrefix₂.mk a22ac060ba45596d
field AvailableChain.FGSA.Run.CleanPrefix₂.partAt 3fb065be557c6b87
def AvailableChain.FGSA.Run.CleanCut₂ 9b6a07e7461332ba
structure AvailableChain.FGSA.Run.Clean₂ b1f4d64b74a54f90
ctor AvailableChain.FGSA.Run.Clean₂.mk 2d2181cee99a0516
field AvailableChain.FGSA.Run.Clean₂.pre 28958f337e687c36
field AvailableChain.FGSA.Run.Clean₂.gst 05c4aa60bead61d6
structure AvailableChain.FGSA.Run.Recovery₂ 1ab6cbcf152bdddb
ctor AvailableChain.FGSA.Run.Recovery₂.mk 111929291a643d71
field AvailableChain.FGSA.Run.Recovery₂.sync 6d884b388f7d20b2
field AvailableChain.FGSA.Run.Recovery₂.deltaF 84fb5389da5d42b6
field AvailableChain.FGSA.Run.Recovery₂.gap 2a70f53700bdefc8
field AvailableChain.FGSA.Run.Recovery₂.base 88e64dce9df2c15d
field AvailableChain.FGSA.Run.Recovery₂.fault a22260c7d5948e0d
field AvailableChain.FGSA.Run.Recovery₂.awake 09b49bd72d92d770
field AvailableChain.FGSA.Run.Recovery₂.gapPos b9bf33e70ac4d51c
structure AvailableChain.FGSA.Run.HealthyPrefixSleep₂ 752139cf62be504d
field AvailableChain.FGSA.Run.HealthyPrefixSleep₂.toHealthyPrefix₂ 22e7912e4b1a64a5
ctor AvailableChain.FGSA.Run.HealthyPrefixSleep₂.mk 1a737a0aa475cd04
field AvailableChain.FGSA.Run.HealthyPrefixSleep₂.joinedPartBefore 90514942043d356d
structure AvailableChain.FGSA.Run.CleanPrefixSleep₂ c43e2b480e6653c5
field AvailableChain.FGSA.Run.CleanPrefixSleep₂.toCleanPrefix₂ 23d3597fce3562d8
ctor AvailableChain.FGSA.Run.CleanPrefixSleep₂.mk 0250686108c91e2e
field AvailableChain.FGSA.Run.CleanPrefixSleep₂.sleepPre 3040740cd660f112
field AvailableChain.FGSA.Run.CleanPrefixSleep₂.joinedPartAt 6f5f16cf32c5f083
structure AvailableChain.FGSA.Run.CleanSleep₂ 5eac2f39042fad2c
field AvailableChain.FGSA.Run.CleanSleep₂.toClean₂ d57488f3dc6b6cc2
ctor AvailableChain.FGSA.Run.CleanSleep₂.mk 2c91a05f6b73c756
field AvailableChain.FGSA.Run.CleanSleep₂.sleepPre 96b3051ee1f32066
def AvailableChain.FGSA.Run.BaseSet ee6da9bafbfa022f
def AvailableChain.FGSA.Run.CleanSet 61e839ae2dd1a8b1
def AvailableChain.FGSA.Run.CleanCutSet dc0c59523fbb36b7
def AvailableChain.FGSA.Run.CleanPrefixSet b49c4854d30d3616
def AvailableChain.FGSA.Run.AwakeProposerRecurrenceFrom bb68b0744902d34f
structure AvailableChain.FGSA.Run.RecoverySleep₂ 4328411887e15307
field AvailableChain.FGSA.Run.RecoverySleep₂.toRecovery₂ 599617edeb2a25b6
ctor AvailableChain.FGSA.Run.RecoverySleep₂.mk 9362a46103385335
field AvailableChain.FGSA.Run.RecoverySleep₂.suffixNoRestart ab9f3f8daa8aba86
field AvailableChain.FGSA.Run.RecoverySleep₂.joinedGap 4848f4f164072b74
def AvailableChain.FGSA.Run.RecoveryReadinessClaim dcfcec94ead2b878
def AvailableChain.FGSA.Run.HealingSet 1f9d32a8b29446e9
structure AvailableChain.FGSA.Run.Outage₂ e53c4aff73527b56
ctor AvailableChain.FGSA.Run.Outage₂.mk 7695555e2bf39688
field AvailableChain.FGSA.Run.Outage₂.pre bd5b248258c20dd5
field AvailableChain.FGSA.Run.Outage₂.sleepy 437d243e89f5fd0d
field AvailableChain.FGSA.Run.Outage₂.order d39bef584abc6dd3
field AvailableChain.FGSA.Run.Outage₂.lag b1671083e2fdbf1f
field AvailableChain.FGSA.Run.Outage₂.budget fefbf9c566300281
field AvailableChain.FGSA.Run.Outage₂.fastPart 56bc4ff72dbda71c
structure AvailableChain.FGSA.Run.OutageSleep₂ 43b531cbb04a3e66
field AvailableChain.FGSA.Run.OutageSleep₂.toOutage₂ 654b469bdb3857ef
ctor AvailableChain.FGSA.Run.OutageSleep₂.mk c5083d391c4335a8
field AvailableChain.FGSA.Run.OutageSleep₂.sleepPre 68fffb62db5076ed
field AvailableChain.FGSA.Run.OutageSleep₂.joinedSleepy 1fcb1f5e76a9e16a
field AvailableChain.FGSA.Run.OutageSleep₂.joinedFastPart 642c77920e033d19
field AvailableChain.FGSA.Run.OutageSleep₂.protection 93176468b5668c8a
def AvailableChain.FGSA.Run.OutageSet ba7ae72eec7c3668
```

### `AvailableChainFGSAClaims.Statements.WeakContinuation`

```text
structure AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂ 376df87232208773
field AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂.toRecoverySleep₂ 937333eccf8551fa
ctor AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂.mk 7a6dddfbd38c7ab8
field AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂.liveness 18aa5bcad5d2c104
field AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂.endpoint 105cd0f72be14caf
structure AvailableChain.FGSA.Run.AgreesThrough₂ 9b8d9c1e29604dfe
ctor AvailableChain.FGSA.Run.AgreesThrough₂.mk 4a21efd46cc432f8
field AvailableChain.FGSA.Run.AgreesThrough₂.honest ffd8f1f88bff039c
field AvailableChain.FGSA.Run.AgreesThrough₂.gst 71719461b9bc92d8
field AvailableChain.FGSA.Run.AgreesThrough₂.delta de9e8411e4b646fe
field AvailableChain.FGSA.Run.AgreesThrough₂.seats 003944bf02a6274d
field AvailableChain.FGSA.Run.AgreesThrough₂.inputs beb1cf86244be102
field AvailableChain.FGSA.Run.AgreesThrough₂.awake 59ba556dfe8daaed
field AvailableChain.FGSA.Run.AgreesThrough₂.events 339e27a2e5e03d75
field AvailableChain.FGSA.Run.AgreesThrough₂.suffixTime e9f9f10023969281
structure AvailableChain.FGSA.Run.CleanContinuation₂ 51d0713212598d32
ctor AvailableChain.FGSA.Run.CleanContinuation₂.mk 5cdee9dc73247c0e
field AvailableChain.FGSA.Run.CleanContinuation₂.base 938e4906340a734b
field AvailableChain.FGSA.Run.CleanContinuation₂.agrees 14b58c266971dee2
field AvailableChain.FGSA.Run.CleanContinuation₂.covered 90f52e2a8a51817a
field AvailableChain.FGSA.Run.CleanContinuation₂.sync 6997de26001d8f59
field AvailableChain.FGSA.Run.CleanContinuation₂.deltaF 568161412d9032ac
field AvailableChain.FGSA.Run.CleanContinuation₂.participation 108540fed97fd7c7
structure AvailableChain.FGSA.Run.BoundedHealingCut₂ 61809e466a8c4ad8
ctor AvailableChain.FGSA.Run.BoundedHealingCut₂.mk 14033eada009c106
field AvailableChain.FGSA.Run.BoundedHealingCut₂.afterGST 7a44bcc48928e513
field AvailableChain.FGSA.Run.BoundedHealingCut₂.beforeEnd 4bb18cd4cea127d1
field AvailableChain.FGSA.Run.BoundedHealingCut₂.cut ed1c569d43d46bea
field AvailableChain.FGSA.Run.BoundedHealingCut₂.actualProposal 28912ec7e84aa3df
field AvailableChain.FGSA.Run.BoundedHealingCut₂.refreshed 476ce8eb591e0755
structure AvailableChain.FGSA.Run.SSafeFromCut₂ cb081ae298d64dd0
ctor AvailableChain.FGSA.Run.SSafeFromCut₂.mk 8aa638409f5b02e7
field AvailableChain.FGSA.Run.SSafeFromCut₂.compatible e216f549b6dffe03
field AvailableChain.FGSA.Run.SSafeFromCut₂.monotone 825a889220c36328
field AvailableChain.FGSA.Run.SSafeFromCut₂.seed a7a2c5426288bdfd
field AvailableChain.FGSA.Run.SSafeFromCut₂.finalBelow d0eb7e094c7e28cf
field AvailableChain.FGSA.Run.SSafeFromCut₂.outputs bf63fc3ef05b1d74
structure AvailableChain.FGSA.Run.CleanContinuationSleep₂ 3ee5d050b2afe814
field AvailableChain.FGSA.Run.CleanContinuationSleep₂.toCleanContinuation₂ 69b800208752f847
ctor AvailableChain.FGSA.Run.CleanContinuationSleep₂.mk ae25c360b8644184
field AvailableChain.FGSA.Run.CleanContinuationSleep₂.joinedParticipation d0707e627baf6733
def AvailableChain.FGSA.Run.BoundedSafetyRecovery₂ e65fe62ad4623052
```

### `AvailableChainFGSAClaims.Statements.WeakContinuationGrowth`

```text
structure AvailableChain.FGSA.Run.RetainedAgreesThrough₂ 383eb0ccf2e81b95
ctor AvailableChain.FGSA.Run.RetainedAgreesThrough₂.mk 6f5c992e5a7d35d0
field AvailableChain.FGSA.Run.RetainedAgreesThrough₂.honest edb2f1f8b21b8386
field AvailableChain.FGSA.Run.RetainedAgreesThrough₂.gst 38822a6b6bc4c514
field AvailableChain.FGSA.Run.RetainedAgreesThrough₂.delta 92e1b0c623363192
field AvailableChain.FGSA.Run.RetainedAgreesThrough₂.seats fc8bca70783a869a
field AvailableChain.FGSA.Run.RetainedAgreesThrough₂.inputs 8549ca94669e0175
field AvailableChain.FGSA.Run.RetainedAgreesThrough₂.awake 40ea41b7585d1e4c
field AvailableChain.FGSA.Run.RetainedAgreesThrough₂.events 37d051495bcab949
def AvailableChain.FGSA.Run.SourcePendingReceipt 3fbab56a610ca9aa
structure AvailableChain.FGSA.Run.PendingSourceDelivery₂ d1a88fc9919b1b1e
ctor AvailableChain.FGSA.Run.PendingSourceDelivery₂.mk cb49c94237c402b2
field AvailableChain.FGSA.Run.PendingSourceDelivery₂.sourceBroadcast 0287d4d028262019
field AvailableChain.FGSA.Run.PendingSourceDelivery₂.sourceRelay c5bc2be0a6e543a6
structure AvailableChain.FGSA.Run.CleanGrowthContinuation₂ c05416aca7c431bb
ctor AvailableChain.FGSA.Run.CleanGrowthContinuation₂.mk bb07d67fb71f599e
field AvailableChain.FGSA.Run.CleanGrowthContinuation₂.base 97668fef67bfe5f7
field AvailableChain.FGSA.Run.CleanGrowthContinuation₂.agrees ab3899bd33e88ae0
field AvailableChain.FGSA.Run.CleanGrowthContinuation₂.covered 18b353da42c01bb9
field AvailableChain.FGSA.Run.CleanGrowthContinuation₂.sync 119c3f43873a8fa2
field AvailableChain.FGSA.Run.CleanGrowthContinuation₂.pending 89a24842f552192e
field AvailableChain.FGSA.Run.CleanGrowthContinuation₂.deltaF 3e939f3dc14830e5
field AvailableChain.FGSA.Run.CleanGrowthContinuation₂.accountable 773fbb988c8fc912
field AvailableChain.FGSA.Run.CleanGrowthContinuation₂.participation 2246b59e2d60a923
structure AvailableChain.FGSA.Run.CleanGrowthContinuationSleep₂ bd86b48458657706
field AvailableChain.FGSA.Run.CleanGrowthContinuationSleep₂.toCleanGrowthContinuation₂ cb5041fe45ceb893
ctor AvailableChain.FGSA.Run.CleanGrowthContinuationSleep₂.mk 2e148a131950f909
field AvailableChain.FGSA.Run.CleanGrowthContinuationSleep₂.joinedParticipation bdfb54cd6372a4b4
def AvailableChain.FGSA.Run.BoundedGrowthRecovery₂ aecf6de0f6ed84ce
theorem AvailableChain.FGSA.Run.BoundedGrowthRecovery₂_def 47867ee603545c7e
```

### `AvailableChainFGSAClaims.Statements.WeakContinuationLive`

```text
structure AvailableChain.FGSA.Run.WeakContinuationLiveAt₂ 3fea0b544ad883be
ctor AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.mk 25ef8a2121655783
field AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.safety 873c591b978ab464
field AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.inclusion 0efdbe0e6c0fab80
field AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.growth c30f1f362ff26d2d
def AvailableChain.FGSA.Run.BoundedSafetyLivenessRecovery₂ 63db9036737fb7b8
theorem AvailableChain.FGSA.Run.BoundedSafetyLivenessRecovery₂_def 716e2890c6a9d045
```

### `AvailableChainFGSAClaims.Statements.Windows`

```text
def AvailableChain.FGSA.Run.WinSpec 9b356bb7862cc020
structure AvailableChain.FGSA.Run.PtB₀ 1c361d6c128ea00c
ctor AvailableChain.FGSA.Run.PtB₀.mk aa2a197a9df55eeb
field AvailableChain.FGSA.Run.PtB₀.b₀ 7e217271b019a6fe
structure AvailableChain.FGSA.Run.PtT f95204a9e0d403e6
ctor AvailableChain.FGSA.Run.PtT.mk 8dab17e0e2809d52
field AvailableChain.FGSA.Run.PtT.t c32afb93eb197b78
structure AvailableChain.FGSA.Run.PtOut ead6c93e9ea77c06
ctor AvailableChain.FGSA.Run.PtOut.mk f30bb183780a0d12
field AvailableChain.FGSA.Run.PtOut.T 001b9946784cc15c
field AvailableChain.FGSA.Run.PtOut.b₀ fbbe596c7589671a
field AvailableChain.FGSA.Run.PtOut.b₁ 112b2b150c9e3c48
def AvailableChain.FGSA.Run.cleanWinAt fe0f87696e6f3437
def AvailableChain.FGSA.Run.cleanWin 1c62e684de0bc96b
def AvailableChain.FGSA.Run.cleanPrefixWin 7fe582dbc463f7a8
def AvailableChain.FGSA.Run.cleanLabelWin 36e8cfcda8ffc18d
def AvailableChain.FGSA.Run.gapWinReady ac7d78f0d42869cd
def AvailableChain.FGSA.Run.formWinAtReady bd0d420703178b1b
def AvailableChain.FGSA.Run.kernelWin 967d465a5d13ec2f
def AvailableChain.FGSA.Run.trigWin 07350ea3ec5ff184
def AvailableChain.FGSA.Run.outWin 10c5a70a99896a67
def AvailableChain.FGSA.Run.TerminalRetention_W fcae20d56cabc8a1
theorem AvailableChain.FGSA.Run.TerminalRetention_W_def 23f17c485239de66
```

### `AvailableChainFGSAClaims.Statements.Witness`

```text
structure AvailableChain.FGSA.Run.HealingWitness 98857114d31fca1b
ctor AvailableChain.FGSA.Run.HealingWitness.mk 533a1ca9d6d6e71f
field AvailableChain.FGSA.Run.HealingWitness.rG 24abf3bc4016a096
field AvailableChain.FGSA.Run.HealingWitness.u₀ a69f530f1425b734
field AvailableChain.FGSA.Run.HealingWitness.M 931bea3059c247b7
field AvailableChain.FGSA.Run.HealingWitness.rStar 4b76ab1c2e507188
field AvailableChain.FGSA.Run.HealingWitness.sStar 2d11909925076825
field AvailableChain.FGSA.Run.HealingWitness.CStar a6650ab30193da26
field AvailableChain.FGSA.Run.HealingWitness.u 53e15c872782e203
field AvailableChain.FGSA.Run.HealingWitness.QStar c0854bdbccdf113f
def AvailableChain.FGSA.Run.tstar 337454ec3bb362a4
theorem AvailableChain.FGSA.Run.tstar_def 3389582619b0d6ee
def AvailableChain.FGSA.Run.oldRowHeights 245ab1c1df1e88d7
def AvailableChain.FGSA.Run.muOf a8fe9b621382c174
def AvailableChain.FGSA.Run.high ca2be6cd67aaf5eb
def AvailableChain.FGSA.Run.honestFrontier 71435f999916598b
def AvailableChain.FGSA.Run.HeightRow e5e23a3383fcf6ac
structure AvailableChain.FGSA.Run.H0Reset 550fd66fef364409
ctor AvailableChain.FGSA.Run.H0Reset.mk eb6fb45e5d652230
field AvailableChain.FGSA.Run.H0Reset.rG_after fef37f83ec66a385
field AvailableChain.FGSA.Run.H0Reset.rG_first 06e84421d5bf480d
field AvailableChain.FGSA.Run.H0Reset.cut c7db884ad700d3f5
field AvailableChain.FGSA.Run.H0Reset.frontier 68f158e821fce8f2
field AvailableChain.FGSA.Run.H0Reset.rowCap 6e96e4c81440a748
field AvailableChain.FGSA.Run.H0Reset.mu_le aba9f41c27bb9ace
field AvailableChain.FGSA.Run.H0Reset.cut_lower 9ab7cfaf67ad4c54
field AvailableChain.FGSA.Run.H0Reset.cut_upper 506dc689712b079e
field AvailableChain.FGSA.Run.H0Reset.reset_row 2ed52e7190b3b35e
field AvailableChain.FGSA.Run.H0Reset.reset_first 4edbbb339995f98a
field AvailableChain.FGSA.Run.H0Reset.label 6d0c01b436707a59
field AvailableChain.FGSA.Run.H0Reset.fresh a9d432cee07c7662
field AvailableChain.FGSA.Run.H0Reset.synchronous d272f25cdce4457e
structure AvailableChain.FGSA.Run.H0 7f1a3e80973a12a9
field AvailableChain.FGSA.Run.H0.toH0Reset b10cfd65d150c5f3
ctor AvailableChain.FGSA.Run.H0.mk 2eb4c97e0959cf20
field AvailableChain.FGSA.Run.H0.proposal_lower b9b1ea2d8a280e0e
field AvailableChain.FGSA.Run.H0.proposal 2c188bb9126eaaad
field AvailableChain.FGSA.Run.H0.proposal_first b82784f9a7eb9602
field AvailableChain.FGSA.Run.H0.after_gst 64feab98cea47ee6
field AvailableChain.FGSA.Run.H0.source_prefix d532d4ab1aeb480b
def AvailableChain.FGSA.Run.tstarOf 9e931a4959884078
theorem AvailableChain.FGSA.Run.muOf_def fa4229924c9572d1
theorem AvailableChain.FGSA.Run.high_def 943f4315935708a9
```
