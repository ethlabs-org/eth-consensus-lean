module
-- shake keep reason: #print axioms targets
public import AvailableChainFGSAClaims.Statements.WeakContinuationGrowth -- shake: keep
public import AvailableChainFGSAClaims.Statements.OutageSleep -- shake: keep (#print axioms targets)
public import AvailableChainFGSAClaims.Statements.FinalityApi -- shake: keep (S4.5b axiom audit)
public import AvailableChainFGSAClaims.Statements.Packages.Inclusion -- shake: keep (S4.5b axiom audit)
public import AvailableChainFGSAClaims.Claims.Outage -- shake: keep (S4.5b axiom audit)
public import AvailableChainFGSAClaims.Claims.Finality -- shake: keep (S4.3b axiom audit)
public import AvailableChainFGSAClaims.Claims.WeakContinuation -- shake: keep (axiom audit commands)
public import AvailableChainFGSAClaims.Statements.BoundsW -- shake: keep (S4.1 axiom audit)
public import AvailableChainFGSAClaims.Statements.Phases -- shake: keep (07-H audit)
public import AvailableChainFGSAClaims.Claims.Healing -- shake: keep (07-H audit)
public import AvailableChainFGSAClaims.Statements.Packages.Finality -- shake: keep (public aliases or axiom audit commands)
public import AvailableChainFGSAClaims.Statements.Packages.Healing -- shake: keep (public aliases or axiom audit commands)
public import AvailableChainFGSAClaims.Claims.Foundations -- shake: keep (axiom audit commands)
public import AvailableChainFGSAClaims.Claims.Shared -- shake: keep (axiom audit commands)
public import AvailableChainFGSAClaims.Claims.Clean -- shake: keep (axiom audit commands)
public import AvailableChainFGSAClaims.Statements.Packages.Outage -- shake: keep (axiom audit commands)

public import AvailableChainFGSAClaims.Claims.FrameNext -- shake: keep (axiom audit)

/-! Axiom audit. Add one `#print axioms` for each new public theorem.
The guard scans all compiled constants. -/

#print axioms AvailableChain.FGSA.Run.L
#print axioms AvailableChain.FGSA.Run.P
#print axioms AvailableChain.FGSA.Run.Γ
#print axioms AvailableChain.FGSA.Run.ρΓ
#print axioms AvailableChain.FGSA.Run.ρ₁
#print axioms AvailableChain.FGSA.Run.ρ
#print axioms AvailableChain.FGSA.Run.E_g
#print axioms AvailableChain.FGSA.Run.E_j
#print axioms AvailableChain.FGSA.Run.B_c
#print axioms AvailableChain.FGSA.Run.D_c
#print axioms AvailableChain.FGSA.Run.B_reset
#print axioms AvailableChain.FGSA.Run.B
#print axioms AvailableChain.FGSA.Run.B_H2
#print axioms AvailableChain.FGSA.Run.B_H1
#print axioms AvailableChain.FGSA.Run.B_H
#print axioms AvailableChain.FGSA.Run.W_F
#print axioms AvailableChain.FGSA.Run.B_F
#print axioms AvailableChain.FGSA.Run.B_heal
#print axioms AvailableChain.FGSA.Run.B_best
#print axioms AvailableChain.FGSA.Run.carrierTime2
#print axioms AvailableChain.FGSA.Run.kernelDeadline
#print axioms AvailableChain.FGSA.Run.ActionDeliveryBounds
#print axioms AvailableChain.FGSA.Run.KernelBeforeNextAction
#print axioms AvailableChain.FGSA.Run.VoteBeforeAction
#print axioms AvailableChain.FGSA.Run.GateAfterCarrier2
#print axioms AvailableChain.FGSA.Run.GateActionOrder
#print axioms AvailableChain.FGSA.Run.FourteenBeforeTwoRounds

#print axioms AvailableChain.FGSA.Run.storeAt
#print axioms AvailableChain.FGSA.Run.S_at
#print axioms AvailableChain.FGSA.Run.F_at
#print axioms AvailableChain.FGSA.Run.J_at
#print axioms AvailableChain.FGSA.Run.gateIn
#print axioms AvailableChain.FGSA.Run.gateResult
#print axioms AvailableChain.FGSA.Run.isGateTime
#print axioms AvailableChain.FGSA.Run.IsGateTick
#print axioms AvailableChain.FGSA.Run.gateResultAt
#print axioms AvailableChain.FGSA.Run.gatePassedAt
#print axioms AvailableChain.FGSA.Run.fastAt
#print axioms AvailableChain.FGSA.Run.headAtIdx
#print axioms AvailableChain.FGSA.Run.vHead
#print axioms AvailableChain.FGSA.Run.actionSourceFG
#print axioms AvailableChain.FGSA.Run.actionSource
#print axioms AvailableChain.FGSA.Run.labelBoundAt
#print axioms AvailableChain.FGSA.Run.DeliveredAt
#print axioms AvailableChain.FGSA.Run.HandlesRowAt
#print axioms AvailableChain.FGSA.Run.AcceptsFinalBefore
#print axioms AvailableChain.FGSA.Run.cleanResults
#print axioms AvailableChain.FGSA.Run.BelowLabel

#print axioms AvailableChain.FGSA.Run.preTick_def
#print axioms AvailableChain.FGSA.Run.postClock_def
#print axioms AvailableChain.FGSA.Run.gateIn_def
#print axioms AvailableChain.FGSA.Run.gateResult_def
#print axioms AvailableChain.FGSA.Run.isGateTime_def
#print axioms AvailableChain.FGSA.Run.vHead_def
#print axioms AvailableChain.FGSA.Run.actionSourceFG_def

#print axioms AvailableChain.FGSA.Run.awakeHonestIn
#print axioms AvailableChain.FGSA.Run.HonestProposal
#print axioms AvailableChain.FGSA.Run.Base₂
#print axioms AvailableChain.FGSA.Run.Base₂.idealization
#print axioms AvailableChain.FGSA.Run.HealthyPrefix₂
#print axioms AvailableChain.FGSA.Run.CleanPrefix₂
#print axioms AvailableChain.FGSA.Run.CleanCut₂
#print axioms AvailableChain.FGSA.Run.Clean₂
#print axioms AvailableChain.FGSA.Run.Recovery₂
#print axioms AvailableChain.FGSA.Run.BaseSet
#print axioms AvailableChain.FGSA.Run.CleanSet
#print axioms AvailableChain.FGSA.Run.CleanCutSet
#print axioms AvailableChain.FGSA.Run.CleanPrefixSet
#print axioms AvailableChain.FGSA.Run.HealingSet
#print axioms AvailableChain.FGSA.Run.WinSpec
#print axioms AvailableChain.FGSA.Run.PtB₀
#print axioms AvailableChain.FGSA.Run.PtT
#print axioms AvailableChain.FGSA.Run.PtOut
#print axioms AvailableChain.FGSA.Run.cleanWinAt
#print axioms AvailableChain.FGSA.Run.cleanWin
#print axioms AvailableChain.FGSA.Run.cleanPrefixWin
#print axioms AvailableChain.FGSA.Run.cleanLabelWin
#print axioms AvailableChain.FGSA.Run.gapWinReady
#print axioms AvailableChain.FGSA.Run.formWinAtReady
#print axioms AvailableChain.FGSA.Run.kernelWin
#print axioms AvailableChain.FGSA.Run.trigWin
#print axioms AvailableChain.FGSA.Run.PtS
#print axioms AvailableChain.FGSA.Run.PtSP
#print axioms AvailableChain.FGSA.Run.PtSX
#print axioms AvailableChain.FGSA.Run.BasePrem
#print axioms AvailableChain.FGSA.Run.SameLabelPrem
#print axioms AvailableChain.FGSA.Run.SourceDisciplinePrem
#print axioms AvailableChain.FGSA.Run.FinalizedSafetyPrem
#print axioms AvailableChain.FGSA.Run.CleanPrem
#print axioms AvailableChain.FGSA.Run.CleanPrefixPrem
#print axioms AvailableChain.FGSA.Run.CleanCutPrem

#print axioms AvailableChain.FGSA.Run.Outage₂
#print axioms AvailableChain.FGSA.Run.OutageSet
#print axioms AvailableChain.FGSA.Run.outWin
#print axioms AvailableChain.FGSA.Run.OutagePrem
#print axioms AvailableChain.FGSA.Run.treeT
#print axioms AvailableChain.FGSA.Run.treeErased
#print axioms AvailableChain.FGSA.Run.frameR
#print axioms AvailableChain.FGSA.Run.domainR
#print axioms AvailableChain.FGSA.Run.finR
#print axioms AvailableChain.FGSA.Run.FAdvance
#print axioms AvailableChain.FGSA.Run.sourceCandidates
#print axioms AvailableChain.FGSA.Run.jointSource
#print axioms AvailableChain.FGSA.Run.proposerHead
#print axioms AvailableChain.FGSA.Run.outputS
#print axioms AvailableChain.FGSA.Run.frameR_def
#print axioms AvailableChain.FGSA.Run.jointSource_def
#print axioms AvailableChain.FGSA.Run.sourceCandidates_def
#print axioms AvailableChain.FGSA.Run.domainR_def
#print axioms AvailableChain.FGSA.Run.treeT_def
#print axioms AvailableChain.FGSA.Run.proposerHead_def
#print axioms AvailableChain.FGSA.Run.FAdvance_def
#print axioms AvailableChain.FGSA.Run.R_at
#print axioms AvailableChain.FGSA.Run.D_at
#print axioms AvailableChain.FGSA.Run.FAdvanceAt
#print axioms AvailableChain.FGSA.Run.candidatesAt
#print axioms AvailableChain.FGSA.Run.proposalHeadAt
#print axioms AvailableChain.FGSA.Run.actionHead
#print axioms AvailableChain.FGSA.Run.actionTriple
#print axioms AvailableChain.FGSA.Run.namedEntry
#print axioms AvailableChain.FGSA.Run.EntryBelow
#print axioms AvailableChain.FGSA.Run.RowSigner
#print axioms AvailableChain.FGSA.Run.HonestRowAt
#print axioms AvailableChain.FGSA.Run.HonestRowBefore
#print axioms AvailableChain.FGSA.Run.RowComplete
#print axioms AvailableChain.FGSA.Run.HonestCarrier
#print axioms AvailableChain.FGSA.Run.HeldAt
#print axioms AvailableChain.FGSA.Run.BlockInRunBefore
#print axioms AvailableChain.FGSA.Run.RowSigner_def
#print axioms AvailableChain.FGSA.Run.HonestRowAt_def
#print axioms AvailableChain.FGSA.Run.RowComplete_def
#print axioms AvailableChain.FGSA.Run.HonestCarrier_def
#print axioms AvailableChain.FGSA.Run.HeldAt_def
#print axioms AvailableChain.FGSA.Run.namedEntry_def
#print axioms AvailableChain.FGSA.Run.rowHeight_def
#print axioms AvailableChain.FGSA.Run.eventTime_def
#print axioms AvailableChain.FGSA.Run.honestSeats_def
#print axioms AvailableChain.FGSA.Run.muOf_def
#print axioms AvailableChain.FGSA.Run.high_def
#print axioms AvailableChain.FGSA.Run.RStore
#print axioms AvailableChain.FGSA.Run.RStoreCumul
#print axioms AvailableChain.FGSA.Run.RMono
#print axioms AvailableChain.FGSA.Run.RFrameExact
#print axioms AvailableChain.FGSA.Run.RGeo
#print axioms AvailableChain.FGSA.Run.RRec
#print axioms AvailableChain.FGSA.Run.TSrc
#print axioms AvailableChain.FGSA.Run.LabelBound
#print axioms AvailableChain.FGSA.Run.TChain
#print axioms AvailableChain.FGSA.Run.TCompat
#print axioms AvailableChain.FGSA.Run.AncestorClosed
#print axioms AvailableChain.FGSA.Run.windowIdx

#print axioms AvailableChain.FGSA.Run.ClientSafeAll
#print axioms AvailableChain.FGSA.Run.ClientSafetyClaim
#print axioms AvailableChain.FGSA.Run.ClientSafetyBaseClaim
#print axioms AvailableChain.FGSA.Run.SameLabelAt
#print axioms AvailableChain.FGSA.Run.SameLabelClaim
#print axioms AvailableChain.FGSA.Run.HeadReachesLoAt
#print axioms AvailableChain.FGSA.Run.HeadReachesLoClaim
#print axioms AvailableChain.FGSA.Run.CleanHistoryAt
#print axioms AvailableChain.FGSA.Run.CleanGateAt
#print axioms AvailableChain.FGSA.Run.CleanTruncAt
#print axioms AvailableChain.FGSA.Run.CleanSafetyAt
#print axioms AvailableChain.FGSA.Run.CleanCutClaim
#print axioms AvailableChain.FGSA.Run.CleanCutZeroClaim
#print axioms AvailableChain.FGSA.Run.CleanHistoryClaim
#print axioms AvailableChain.FGSA.Run.CleanPrefixTruncationClaim
#print axioms AvailableChain.FGSA.Run.CleanSafetyClaim
#print axioms AvailableChain.FGSA.Run.certified
#print axioms AvailableChain.FGSA.Run.FrameBelow
#print axioms AvailableChain.FGSA.Run.RStrat
#print axioms AvailableChain.FGSA.Run.SrcFrameAbove
#print axioms AvailableChain.FGSA.Run.SrcFrame
#print axioms AvailableChain.FGSA.Run.SrcFrameAboveStmt
#print axioms AvailableChain.FGSA.Run.CPPrefix
#print axioms AvailableChain.FGSA.Run.CPCompat
#print axioms AvailableChain.FGSA.Run.TimingContract
#print axioms AvailableChain.FGSA.Run.FGFoundation
#print axioms AvailableChain.FGSA.Run.certified_def
#print axioms AvailableChain.FGSA.Run.HonestRowBefore_def
#print axioms AvailableChain.FGSA.Run.RStore_def
#print axioms AvailableChain.FGSA.Run.RStoreCumul_def
#print axioms AvailableChain.FGSA.Run.RMono_def
#print axioms AvailableChain.FGSA.Run.RFrameExact_def
#print axioms AvailableChain.FGSA.Run.RGeo_def
#print axioms AvailableChain.FGSA.Run.RRec_def
#print axioms AvailableChain.FGSA.Run.TSrc_def
#print axioms AvailableChain.FGSA.Run.LabelBound_def
#print axioms AvailableChain.FGSA.Run.TChain_def
#print axioms AvailableChain.FGSA.Run.TCompat_def
#print axioms AvailableChain.FGSA.Run.FrameBelow_def
#print axioms AvailableChain.FGSA.Run.RStrat_def
#print axioms AvailableChain.FGSA.Run.SrcFrameAbove_def
#print axioms AvailableChain.FGSA.Run.SrcFrameAboveStmt_def
#print axioms AvailableChain.FGSA.Run.CPPrefix_def
#print axioms AvailableChain.FGSA.Run.CPCompat_def

-- F0.6a part 2.
#print axioms AvailableChain.FGSA.Run.CleanCutPosClaim
#print axioms AvailableChain.FGSA.Run.FGFoundationClaim
#print axioms AvailableChain.FGSA.Run.SrcFrameAboveClaim
#print axioms AvailableChain.FGSA.Run.RunFGBlock
#print axioms AvailableChain.FGSA.Run.CarrierAt
#print axioms AvailableChain.FGSA.Run.StoreAt
#print axioms AvailableChain.FGSA.Run.ActiveViewAt
#print axioms AvailableChain.FGSA.Run.LeaseOriginsAt
#print axioms AvailableChain.FGSA.Run.SourceDisciplineBaseAt
#print axioms AvailableChain.FGSA.Run.SourceDisciplineAt
#print axioms AvailableChain.FGSA.Run.CarrierClaim
#print axioms AvailableChain.FGSA.Run.ChainCertificatesClaim
#print axioms AvailableChain.FGSA.Run.StoreClaim
#print axioms AvailableChain.FGSA.Run.ActiveViewClaim
#print axioms AvailableChain.FGSA.Run.LeaseOriginsClaim
#print axioms AvailableChain.FGSA.Run.ReconcileClaim
#print axioms AvailableChain.FGSA.Run.FrameClaim
#print axioms AvailableChain.FGSA.Run.SourceDisciplineBaseClaim
#print axioms AvailableChain.FGSA.Run.SourceDisciplineClaim
#print axioms AvailableChain.FGSA.Run.ReleaseStoreAt
#print axioms AvailableChain.FGSA.Run.ReleaseStoreClaim
#print axioms AvailableChain.FGSA.Run.ReleaseAt
#print axioms AvailableChain.FGSA.Run.ReleaseClaim
#print axioms AvailableChain.FGSA.Run.ReleasePrem
#print axioms AvailableChain.FGSA.Run.ReconcileAt
#print axioms AvailableChain.FGSA.Run.OutputNestingAt
#print axioms AvailableChain.FGSA.Run.OutputNestingClaim

-- FGSASafetyClaims is audited by the compiled EXPECTED check through the Claims root.
-- FGSASafetyInterfaces is audited by the same compiled EXPECTED check through the Claims root.
-- This test does not import the facade (P3 §4.8).

#print axioms AvailableChain.FGSA.Run.RActive
#print axioms AvailableChain.FGSA.Run.RActive_def
#print axioms AvailableChain.FGSA.Run.RCert
#print axioms AvailableChain.FGSA.Run.RCert_def
#print axioms AvailableChain.FGSA.Run.ChainCertificatesAt

#print axioms AvailableChain.FGSA.Run.RCarrierView
#print axioms AvailableChain.FGSA.Run.RCarrierView_def
#print axioms AvailableChain.FGSA.Run.RFrame
#print axioms AvailableChain.FGSA.Run.RFrame_def
#print axioms AvailableChain.FGSA.Run.RQCOrigin
#print axioms AvailableChain.FGSA.Run.RQCOrigin_def
#print axioms AvailableChain.FGSA.Run.FrameAt

-- F0.8b: new public declarations.
#print axioms AvailableChain.FGSA.Run.H2A
#print axioms AvailableChain.FGSA.Run.H2Prime
#print axioms AvailableChain.FGSA.Run.H3
#print axioms AvailableChain.FGSA.Run.H4
#print axioms AvailableChain.FGSA.Run.H5RawTransfer
#print axioms AvailableChain.FGSA.Run.H6GateService
#print axioms AvailableChain.FGSA.Run.HealT
#print axioms AvailableChain.FGSA.Run.HealAC
#print axioms AvailableChain.FGSA.Run.HealingInput
#print axioms AvailableChain.FGSA.Run.HTimeStatement
#print axioms AvailableChain.FGSA.Run.HTimeStatement_def
#print axioms AvailableChain.FGSA.Run.TStart
#print axioms AvailableChain.FGSA.Run.FullVoteService
#print axioms AvailableChain.FGSA.Run.TVote
#print axioms AvailableChain.FGSA.Run.WalkBatch
#print axioms AvailableChain.FGSA.Run.TWalk
#print axioms AvailableChain.FGSA.Run.CoreServices
#print axioms AvailableChain.FGSA.Run.PhaseKind
#print axioms AvailableChain.FGSA.Run.AttemptTask
#print axioms AvailableChain.FGSA.Run.AttemptKey
#print axioms AvailableChain.FGSA.Run.ResetArrivalStatement
#print axioms AvailableChain.FGSA.Run.ResetArrivalStatement_def
#print axioms AvailableChain.FGSA.Run.ResetArrivalFullStatement
#print axioms AvailableChain.FGSA.Run.ResetArrivalFullStatement_def
#print axioms AvailableChain.FGSA.Run.KernelPt
#print axioms AvailableChain.FGSA.Run.kernelStart
#print axioms AvailableChain.FGSA.Run.HealTContract
#print axioms AvailableChain.FGSA.Run.frontierAtIdx
#print axioms AvailableChain.FGSA.Run.TopEvidence
#print axioms AvailableChain.FGSA.Run.ContestEvidence
#print axioms AvailableChain.FGSA.Run.EffectiveEvent
#print axioms AvailableChain.FGSA.Run.AttemptPhaseAt
#print axioms AvailableChain.FGSA.Run.ServedFrontier
#print axioms AvailableChain.FGSA.Run.AttemptValid
#print axioms AvailableChain.FGSA.Run.attemptBudget
#print axioms AvailableChain.FGSA.Run.AttemptEndsBy
#print axioms AvailableChain.FGSA.Run.rowHeld
#print axioms AvailableChain.FGSA.Run.proposalStateAt
#print axioms AvailableChain.FGSA.Run.heldAtProposal
#print axioms AvailableChain.FGSA.Run.onParentChain
#print axioms AvailableChain.FGSA.Run.HeldBefore
#print axioms AvailableChain.FGSA.Run.ValidForParent
#print axioms AvailableChain.FGSA.Run.ValidForParent_def
#print axioms AvailableChain.FGSA.Run.headAtLabel
#print axioms AvailableChain.FGSA.Run.RXing
#print axioms AvailableChain.FGSA.Run.RCap
#print axioms AvailableChain.FGSA.Run.THigh
#print axioms AvailableChain.FGSA.Run.TCarrier
#print axioms AvailableChain.FGSA.Run.TRowsSelect
#print axioms AvailableChain.FGSA.Run.TRowsSync
#print axioms AvailableChain.FGSA.Run.TRows
#print axioms AvailableChain.FGSA.Run.SourceBefore
#print axioms AvailableChain.FGSA.Run.Kept
#print axioms AvailableChain.FGSA.Run.KeepOrCause
#print axioms AvailableChain.FGSA.Run.RExcl
#print axioms AvailableChain.FGSA.Run.RKeep
#print axioms AvailableChain.FGSA.Run.RFProv
#print axioms AvailableChain.FGSA.Run.TDel
#print axioms AvailableChain.FGSA.Run.TDelReset
#print axioms AvailableChain.FGSA.Run.TGeom
#print axioms AvailableChain.FGSA.Run.ExactService
#print axioms AvailableChain.FGSA.Run.PhaseInterval
#print axioms AvailableChain.FGSA.Run.Transfers
#print axioms AvailableChain.FGSA.Run.PhaseBody
#print axioms AvailableChain.FGSA.Run.TPerm
#print axioms AvailableChain.FGSA.Run.ProposalGap
#print axioms AvailableChain.FGSA.Run.RepairAfter
#print axioms AvailableChain.FGSA.Run.TRepair
#print axioms AvailableChain.FGSA.Run.OpeningEntry
#print axioms AvailableChain.FGSA.Run.TCommon
#print axioms AvailableChain.FGSA.Run.TFrontier
#print axioms AvailableChain.FGSA.Run.oldRowHeights
#print axioms AvailableChain.FGSA.Run.muOf
#print axioms AvailableChain.FGSA.Run.high
#print axioms AvailableChain.FGSA.Run.honestFrontier
#print axioms AvailableChain.FGSA.Run.HeightRow
#print axioms AvailableChain.FGSA.Run.H0Reset
#print axioms AvailableChain.FGSA.Run.H0
#print axioms AvailableChain.FGSA.Run.tstarOf
#print axioms AvailableChain.FGSA.Run.PtU
#print axioms AvailableChain.FGSA.Run.PtW
#print axioms AvailableChain.FGSA.Run.PtM
#print axioms AvailableChain.FGSA.Run.PtR
#print axioms AvailableChain.FGSA.Run.PtK
#print axioms AvailableChain.FGSA.Run.HealingPrem
#print axioms AvailableChain.FGSA.Run.HealingWitnessPrem
#print axioms AvailableChain.FGSA.Run.HealingTimePrem
#print axioms AvailableChain.FGSA.Run.ResetArrivalPrem
#print axioms AvailableChain.FGSA.Run.ResetArrivalFullPrem
#print axioms AvailableChain.FGSA.Run.KernelJoinedPrem
#print axioms AvailableChain.FGSA.Run.HealingAttemptPrem

-- fg-noround/07-H additions.
#print axioms AvailableChain.FGSA.Run.RowServiceBaseClaim
#print axioms AvailableChain.FGSA.Run.TRowsReceipt
#print axioms AvailableChain.FGSA.Run.TRowsReceipt_def
#print axioms AvailableChain.FGSA.Run.OpeningCovered
#print axioms AvailableChain.FGSA.Run.FinalityRowCarriage
#print axioms AvailableChain.FGSA.Run.FinalityRowCarriage_def
#print axioms AvailableChain.FGSA.Run.HeightMatch
#print axioms AvailableChain.FGSA.Run.HeightMatch_def
#print axioms AvailableChain.FGSA.Run.SettledPhaseFrame
#print axioms AvailableChain.FGSA.Run.SettledPhaseFrame_def
#print axioms AvailableChain.FGSA.Run.RPhase
#print axioms AvailableChain.FGSA.Run.RPhase_def
#print axioms AvailableChain.FGSA.Run.HealRContract
#print axioms AvailableChain.FGSA.Run.ProgressAttemptStatement
#print axioms AvailableChain.FGSA.Run.ProgressAttemptStatement_def
#print axioms AvailableChain.FGSA.Run.HealingInputPrem
#print axioms AvailableChain.FGSA.Run.RenewedPromotionPrem
#print axioms AvailableChain.FGSA.Run.RowPermissionAt
#print axioms AvailableChain.FGSA.Run.RowPermissionClaim
#print axioms AvailableChain.FGSA.Run.RowServiceClaim
#print axioms AvailableChain.FGSA.Run.HealingInputClaim
#print axioms AvailableChain.FGSA.Run.HTimeConcl
#print axioms AvailableChain.FGSA.Run.HTimeClaim
#print axioms AvailableChain.FGSA.Run.HTimeBestConcl
#print axioms AvailableChain.FGSA.Run.HTimeBestConcl_def
#print axioms AvailableChain.FGSA.Run.HTimeBestClaim
#print axioms AvailableChain.FGSA.Run.HTimeSearchClaim
#print axioms AvailableChain.FGSA.Run.ResetArrivalConcl
#print axioms AvailableChain.FGSA.Run.ResetArrivalClaim
#print axioms AvailableChain.FGSA.Run.RenewedPromotionConcl
#print axioms AvailableChain.FGSA.Run.RenewedPromotionClaim
#print axioms AvailableChain.FGSA.Run.RowKind
#print axioms AvailableChain.FGSA.Run.RowNames
#print axioms AvailableChain.FGSA.Run.SlotChain
#print axioms AvailableChain.FGSA.Run.EntryAt
#print axioms AvailableChain.FGSA.Run.JustifiedCross
#print axioms AvailableChain.FGSA.Run.MixedCross
#print axioms AvailableChain.FGSA.Run.NoMixedOnPath
#print axioms AvailableChain.FGSA.Run.SeatCovers
#print axioms AvailableChain.FGSA.Run.CoveredByChild
#print axioms AvailableChain.FGSA.Run.foldTrichotomy
#print axioms AvailableChain.FGSA.Run.StoredProgressConsume
#print axioms AvailableChain.FGSA.Run.NoMixedMaturity
#print axioms AvailableChain.FGSA.Run.NamesEntry
#print axioms AvailableChain.FGSA.Run.rowHeight
#print axioms AvailableChain.FGSA.Run.eventTime
#print axioms AvailableChain.FGSA.Run.honestSeats
#print axioms AvailableChain.FGSA.Run.ChainRowsBefore
#print axioms AvailableChain.FGSA.Run.PreBatchPrem
#print axioms AvailableChain.FGSA.Run.NoMixedPreBatchParent
#print axioms AvailableChain.FGSA.Run.BatchPrem
#print axioms AvailableChain.FGSA.Run.BatchCoverage
#print axioms AvailableChain.FGSA.Run.finHeight
#print axioms AvailableChain.FGSA.Run.FreshPrem

#print axioms AvailableChain.FGSA.Run.kappaF
#print axioms AvailableChain.FGSA.Run.betaF
#print axioms AvailableChain.FGSA.Run.epsF
#print axioms AvailableChain.FGSA.Run.carrierTimeW
#print axioms AvailableChain.FGSA.Run.kernelDeadlineW
#print axioms AvailableChain.FGSA.Run.W_W
#print axioms AvailableChain.FGSA.Run.E_gF
#print axioms AvailableChain.FGSA.Run.E_jF
#print axioms AvailableChain.FGSA.Run.B_cF
#print axioms AvailableChain.FGSA.Run.D_cF
#print axioms AvailableChain.FGSA.Run.B_resetF
#print axioms AvailableChain.FGSA.Run.BF
#print axioms AvailableChain.FGSA.Run.B_H2F
#print axioms AvailableChain.FGSA.Run.B_H1F
#print axioms AvailableChain.FGSA.Run.B_HF
#print axioms AvailableChain.FGSA.Run.B'_resetF
#print axioms AvailableChain.FGSA.Run.B_bestF
#print axioms AvailableChain.FGSA.Run.ActionDeliveryBoundsW
#print axioms AvailableChain.FGSA.Run.KernelBeforeNextActionW
#print axioms AvailableChain.FGSA.Run.LivenessBoundW
#print axioms AvailableChain.FGSA.Run.kappaF_def
#print axioms AvailableChain.FGSA.Run.betaF_def
#print axioms AvailableChain.FGSA.Run.epsF_def
#print axioms AvailableChain.FGSA.Run.carrierTimeW_def
#print axioms AvailableChain.FGSA.Run.kernelDeadlineW_def
#print axioms AvailableChain.FGSA.Run.W_W_def
#print axioms AvailableChain.FGSA.Run.E_gF_def
#print axioms AvailableChain.FGSA.Run.E_jF_def
#print axioms AvailableChain.FGSA.Run.B_cF_def
#print axioms AvailableChain.FGSA.Run.D_cF_def
#print axioms AvailableChain.FGSA.Run.B_resetF_def
#print axioms AvailableChain.FGSA.Run.BF_def
#print axioms AvailableChain.FGSA.Run.B_H2F_def
#print axioms AvailableChain.FGSA.Run.B_H1F_def
#print axioms AvailableChain.FGSA.Run.B_HF_def
#print axioms AvailableChain.FGSA.Run.B'_resetF_def
#print axioms AvailableChain.FGSA.Run.B_bestF_def
#print axioms AvailableChain.FGSA.Run.ActionDeliveryBoundsW_def
#print axioms AvailableChain.FGSA.Run.KernelBeforeNextActionW_def

#print axioms AvailableChain.FGSA.Run.StrongRecoverySearchPrefix₂
#print axioms AvailableChain.FGSA.Run.AgreesThrough₂
#print axioms AvailableChain.FGSA.Run.CleanContinuation₂
#print axioms AvailableChain.FGSA.Run.BoundedHealingCut₂
#print axioms AvailableChain.FGSA.Run.SSafeFromCut₂
#print axioms AvailableChain.FGSA.Run.BoundedSafetyRecovery₂
#print axioms AvailableChain.FGSA.Run.WeakContinuationClaim
-- S4.4a: row-delay liveness binding and actual-event finite horizon.
#print axioms AvailableChain.FGSA.Run.HealingPrem.bound
#print axioms AvailableChain.FGSA.Run.KernelJoinedPrem.bound
#print axioms AvailableChain.FGSA.Run.HealingAttemptPrem.hhor
#print axioms AvailableChain.FGSA.Run.FE_W
#print axioms AvailableChain.FGSA.Run.F4_W
#print axioms AvailableChain.FGSA.Run.FGoodE_Wp
#print axioms AvailableChain.FGSA.Run.FGood4_Wp
#print axioms AvailableChain.FGSA.Run.Tail_Wp
#print axioms AvailableChain.FGSA.Run.B_FW
#print axioms AvailableChain.FGSA.Run.FE_W_def
#print axioms AvailableChain.FGSA.Run.F4_W_def
#print axioms AvailableChain.FGSA.Run.FGoodE_Wp_def
#print axioms AvailableChain.FGSA.Run.FGood4_Wp_def
#print axioms AvailableChain.FGSA.Run.Tail_Wp_def
#print axioms AvailableChain.FGSA.Run.B_FW_def

-- S4.2b: terminal retention contract.
#print axioms AvailableChain.FGSA.Run.TerminalRetention_W
#print axioms AvailableChain.FGSA.Run.TerminalRetention_W_def
-- S4.3: W contracts, equations, constructors, fields, and pure adapters.
#print axioms AvailableChain.FGSA.Run.FinalityCoveredByChild_W
#print axioms AvailableChain.FGSA.Run.FinRowNames
#print axioms AvailableChain.FGSA.Run.FinalityNames
#print axioms AvailableChain.FGSA.Run.FinalityBatchPrem_W
#print axioms AvailableChain.FGSA.Run.FinalityBatchPrem_W.mk
#print axioms AvailableChain.FGSA.Run.FinalityBatchPrem_W.base
#print axioms AvailableChain.FGSA.Run.FinalityBatchPrem_W.faultQ
#print axioms AvailableChain.FGSA.Run.FinalityBatchPrem_W.deltaF
#print axioms AvailableChain.FGSA.Run.FinalityBatchPrem_W.rowsReceipt
#print axioms AvailableChain.FGSA.Run.FinalityBatchPrem_W.carrier
#print axioms AvailableChain.FGSA.Run.FinalityBatchPrem_W.after
#print axioms AvailableChain.FGSA.Run.FinalityBatchPrem_W.horizon
#print axioms AvailableChain.FGSA.Run.FinalityBatchPrem_W.parent
#print axioms AvailableChain.FGSA.Run.FinalityBatchPrem_W.birth
#print axioms AvailableChain.FGSA.Run.FinalityBatchPrem_W.retainedOrCovered
#print axioms AvailableChain.FGSA.Run.FinalityBatchPrem_W.batch
#print axioms AvailableChain.FGSA.Run.FinalityBatchCoverage_W
#print axioms AvailableChain.FGSA.Run.PendingFold_W
#print axioms AvailableChain.FGSA.Run.PendingFold_W.mk
#print axioms AvailableChain.FGSA.Run.PendingFold_W.child
#print axioms AvailableChain.FGSA.Run.PendingFold_W.cover
#print axioms AvailableChain.FGSA.Run.FinalityCoveredByChild_W_def
#print axioms AvailableChain.FGSA.Run.FinRowNames_def
#print axioms AvailableChain.FGSA.Run.FinalityNames_def
#print axioms AvailableChain.FGSA.Run.FinalityBatchCoverage_W_def
#print axioms AvailableChain.FGSA.Run.FreshFinalityRows_W
#print axioms AvailableChain.FGSA.Run.TerminalCarriagePrem_W
#print axioms AvailableChain.FGSA.Run.TerminalCarriagePrem_W.mk
#print axioms AvailableChain.FGSA.Run.TerminalCarriagePrem_W.base
#print axioms AvailableChain.FGSA.Run.TerminalCarriagePrem_W.faultQ
#print axioms AvailableChain.FGSA.Run.TerminalCarriagePrem_W.deltaF
#print axioms AvailableChain.FGSA.Run.TerminalCarriagePrem_W.carrier
#print axioms AvailableChain.FGSA.Run.TerminalCarriagePrem_W.parent
#print axioms AvailableChain.FGSA.Run.TerminalCarriagePrem_W.path
#print axioms AvailableChain.FGSA.Run.TerminalCarriagePrem_W.freshHeight
#print axioms AvailableChain.FGSA.Run.TerminalCarriagePrem_W.retainedOrCovered
#print axioms AvailableChain.FGSA.Run.TerminalCarriagePrem_W.horizon
#print axioms AvailableChain.FGSA.Run.TerminalCarriagePrem_W.seats
#print axioms AvailableChain.FGSA.Run.TerminalCarriagePrem_W.rows
#print axioms AvailableChain.FGSA.Run.TerminalCarriagePrem_W.fresh
#print axioms AvailableChain.FGSA.Run.TerminalCarriagePrem_W.heightEntry
#print axioms AvailableChain.FGSA.Run.TerminalCarriagePrem_W.receipt
#print axioms AvailableChain.FGSA.Run.TerminalCarriage_W
#print axioms AvailableChain.FGSA.Run.FreshFinalityRows_W_def
#print axioms AvailableChain.FGSA.Run.TerminalCarriage_W_def
#print axioms AvailableChain.FGSA.Run.JustifyAt
#print axioms AvailableChain.FGSA.Run.JustifyFresh_W
#print axioms AvailableChain.FGSA.Run.Ready_W
#print axioms AvailableChain.FGSA.Run.receiptInsert_W
#print axioms AvailableChain.FGSA.Run.ReceiptWitness_W
#print axioms AvailableChain.FGSA.Run.ReceiptWitness_W.mk
#print axioms AvailableChain.FGSA.Run.ReceiptWitness_W.index
#print axioms AvailableChain.FGSA.Run.ReceiptWitness_W.time
#print axioms AvailableChain.FGSA.Run.BlockDelivery_W
#print axioms AvailableChain.FGSA.Run.BlockDelivery_W.mk
#print axioms AvailableChain.FGSA.Run.BlockDelivery_W.selected
#print axioms AvailableChain.FGSA.Run.BlockDelivery_W.witness
#print axioms AvailableChain.FGSA.Run.AcceptGuards_W
#print axioms AvailableChain.FGSA.Run.AcceptGuards_W.mk
#print axioms AvailableChain.FGSA.Run.AcceptGuards_W.finCmp
#print axioms AvailableChain.FGSA.Run.AcceptGuards_W.jPath
#print axioms AvailableChain.FGSA.Run.AcceptGuards_W.cap
#print axioms AvailableChain.FGSA.Run.AcceptPrem_W
#print axioms AvailableChain.FGSA.Run.AcceptPrem_W.mk
#print axioms AvailableChain.FGSA.Run.AcceptPrem_W.base
#print axioms AvailableChain.FGSA.Run.AcceptPrem_W.faultBound
#print axioms AvailableChain.FGSA.Run.AcceptPrem_W.finalized
#print axioms AvailableChain.FGSA.Run.AcceptPrem_W.deliver
#print axioms AvailableChain.FGSA.Run.AcceptPrem_W.guards
#print axioms AvailableChain.FGSA.Run.AcceptPrem_W.horizon
#print axioms AvailableChain.FGSA.Run.AcceptBefore_W
#print axioms AvailableChain.FGSA.Run.FinalizePrem_W
#print axioms AvailableChain.FGSA.Run.FinalizePrem_W.mk
#print axioms AvailableChain.FGSA.Run.FinalizePrem_W.fold
#print axioms AvailableChain.FGSA.Run.FinalizePrem_W.base
#print axioms AvailableChain.FGSA.Run.FinalizePrem_W.faultBound
#print axioms AvailableChain.FGSA.Run.FinalizePrem_W.deliver
#print axioms AvailableChain.FGSA.Run.FinalizePrem_W.guards
#print axioms AvailableChain.FGSA.Run.FinalizePrem_W.horizon
#print axioms AvailableChain.FGSA.Run.FinalizePending_W
#print axioms AvailableChain.FGSA.Run.JustifyAt_def
#print axioms AvailableChain.FGSA.Run.JustifyFresh_W_def
#print axioms AvailableChain.FGSA.Run.Ready_W_def
#print axioms AvailableChain.FGSA.Run.receiptInsert_W_def
#print axioms AvailableChain.FGSA.Run.AcceptBefore_W_def
#print axioms AvailableChain.FGSA.Run.FinalizePending_W_def
#print axioms AvailableChain.FGSA.Run.JustifiedCross_def
#print axioms AvailableChain.FGSA.Run.MixedCross_def
#print axioms AvailableChain.FGSA.Run.foldTrichotomy_def
#print axioms AvailableChain.FGSA.Run.StoredProgressConsume_def

-- S4.3b: W kernels and FF5–FF7 public surface.
#print axioms AvailableChain.FGSA.Run.KernelJoinedPrem.window
#print axioms AvailableChain.FGSA.Run.FinFormW
#print axioms AvailableChain.FGSA.Run.FinFormW.recFE
#print axioms AvailableChain.FGSA.Run.FinFormW.recF4
#print axioms AvailableChain.FGSA.Run.FinFormW.rec
#print axioms AvailableChain.FGSA.Run.FinFormW.recOn
#print axioms AvailableChain.FGSA.Run.FinFormW.casesOn
#print axioms AvailableChain.FGSA.Run.FinFormW.holdsW
#print axioms AvailableChain.FGSA.Run.FinFormW.holdsW_def
#print axioms AvailableChain.FGSA.Run.FinalitySet_W
#print axioms AvailableChain.FGSA.Run.FinalitySet_W.mk
#print axioms AvailableChain.FGSA.Run.FinalitySet_W.core
#print axioms AvailableChain.FGSA.Run.FinalitySet_W.bound
#print axioms AvailableChain.FGSA.Run.FinalitySet_W.recur
#print axioms AvailableChain.FGSA.Run.OpeningCarrier_W
#print axioms AvailableChain.FGSA.Run.OpeningCarrier_W_def
#print axioms AvailableChain.FGSA.Run.KernelConclusion_W
#print axioms AvailableChain.FGSA.Run.KernelConclusion_W_def
#print axioms AvailableChain.FGSA.Run.KernelPrem_W
#print axioms AvailableChain.FGSA.Run.KernelPrem_W.mk
#print axioms AvailableChain.FGSA.Run.KernelPrem_W.set
#print axioms AvailableChain.FGSA.Run.KernelPrem_W.bound
#print axioms AvailableChain.FGSA.Run.KernelPrem_W.window
#print axioms AvailableChain.FGSA.Run.KernelPrem_W.start
#print axioms AvailableChain.FGSA.Run.KernelPrem_W.hhor
#print axioms AvailableChain.FGSA.Run.KernelPrem_W.input
#print axioms AvailableChain.FGSA.Run.KernelPrem_W.services
#print axioms AvailableChain.FGSA.Run.TailKernelPt
#print axioms AvailableChain.FGSA.Run.TailKernelPt.mk
#print axioms AvailableChain.FGSA.Run.TailKernelPt.w
#print axioms AvailableChain.FGSA.Run.TailKernelPt.r
#print axioms AvailableChain.FGSA.Run.TailKernelPt.carrier
#print axioms AvailableChain.FGSA.Run.TailKernelPt.U
#print axioms AvailableChain.FGSA.Run.TailKernelPrem_W
#print axioms AvailableChain.FGSA.Run.TailKernelPrem_W.mk
#print axioms AvailableChain.FGSA.Run.TailKernelPrem_W.set
#print axioms AvailableChain.FGSA.Run.TailKernelPrem_W.bound
#print axioms AvailableChain.FGSA.Run.TailKernelPrem_W.input
#print axioms AvailableChain.FGSA.Run.TailKernelPrem_W.start
#print axioms AvailableChain.FGSA.Run.TailKernelPrem_W.window
#print axioms AvailableChain.FGSA.Run.TailKernelPrem_W.carrier
#print axioms AvailableChain.FGSA.Run.TailKernelPrem_W.high
#print axioms AvailableChain.FGSA.Run.TailKernelPrem_W.cover
#print axioms AvailableChain.FGSA.Run.TailKernelPrem_W.hhor
#print axioms AvailableChain.FGSA.Run.finalityWindow_W
#print axioms AvailableChain.FGSA.Run.finalityWindow_W_def
#print axioms AvailableChain.FGSA.Run.FirstFinalityPrem_W
#print axioms AvailableChain.FGSA.Run.FirstFinalityPrem_W.mk
#print axioms AvailableChain.FGSA.Run.FirstFinalityPrem_W.set
#print axioms AvailableChain.FGSA.Run.FirstFinalityPrem_W.hhor
#print axioms AvailableChain.FGSA.Run.FinalityLivenessPrem_W
#print axioms AvailableChain.FGSA.Run.FinalityLivenessPrem_W.mk
#print axioms AvailableChain.FGSA.Run.FinalityLivenessPrem_W.set
#print axioms AvailableChain.FGSA.Run.FinalityLivenessPrem_W.input
#print axioms AvailableChain.FGSA.Run.FinalityLivenessPrem_W.start
#print axioms AvailableChain.FGSA.Run.FinalityLivenessPrem_W.hhor
#print axioms AvailableChain.FGSA.Run.ProposalFinalPrem_W
#print axioms AvailableChain.FGSA.Run.ProposalFinalPrem_W.mk
#print axioms AvailableChain.FGSA.Run.ProposalFinalPrem_W.set
#print axioms AvailableChain.FGSA.Run.ProposalFinalPrem_W.input
#print axioms AvailableChain.FGSA.Run.ProposalFinalPrem_W.prop
#print axioms AvailableChain.FGSA.Run.ProposalFinalPrem_W.start
#print axioms AvailableChain.FGSA.Run.ProposalFinalPrem_W.hhor
#print axioms AvailableChain.FGSA.Run.AboveFrontierPrem_W
#print axioms AvailableChain.FGSA.Run.AboveFrontierPrem_W.mk
#print axioms AvailableChain.FGSA.Run.AboveFrontierPrem_W.set
#print axioms AvailableChain.FGSA.Run.AboveFrontierPrem_W.input
#print axioms AvailableChain.FGSA.Run.AboveFrontierPrem_W.start
#print axioms AvailableChain.FGSA.Run.AboveFrontierPrem_W.firstHorizon
#print axioms AvailableChain.FGSA.Run.AboveFrontierPrem_W.hhor
#print axioms AvailableChain.FGSA.Run.FinalityKernelClaim_W
#print axioms AvailableChain.FGSA.Run.KernelACSideClaim_W
#print axioms AvailableChain.FGSA.Run.FinalityKernelJoinedClaim_W
#print axioms AvailableChain.FGSA.Run.TailKernelClaim_W
#print axioms AvailableChain.FGSA.Run.FinalityLivenessConcl_W
#print axioms AvailableChain.FGSA.Run.FirstFinalityConcl_W
#print axioms AvailableChain.FGSA.Run.ProposalFinalConcl_W
#print axioms AvailableChain.FGSA.Run.AboveFrontierConcl_W
#print axioms AvailableChain.FGSA.Run.FirstFinalityRecFEClaim_W
#print axioms AvailableChain.FGSA.Run.FirstFinalityRecF4Claim_W
#print axioms AvailableChain.FGSA.Run.FinalityLivenessRecFEClaim_W
#print axioms AvailableChain.FGSA.Run.FinalityLivenessRecF4Claim_W
#print axioms AvailableChain.FGSA.Run.ProposalFinalRecFEClaim_W
#print axioms AvailableChain.FGSA.Run.ProposalFinalRecF4Claim_W
#print axioms AvailableChain.FGSA.Run.AboveFrontierRecFEClaim_W
#print axioms AvailableChain.FGSA.Run.AboveFrontierRecF4Claim_W

-- Check the adapter with an explicit recovery supplier; public records stay fixed.
example (p : AvailableChain.FGSA.Params)
    (split : AvailableChain.FGSA.Run.FinalityKernelClaim_W p)
    (ac : AvailableChain.FGSA.Run.KernelACSideClaim_W p)
    (ready : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type}
      (c : AvailableChain.FGSA.Run.AppCodec In) (E : AvailableChain.Generic.Env V)
      (rho : AvailableChain.V2.D.Run V (AvailableChain.FGSA.Run.fgsa p c))
      (G ΔF : AvailableChain.Time),
      AvailableChain.FGSA.Run.Recovery₂ p c E rho G ΔF →
      AvailableChain.FGSA.Run.RecoverySleep₂ p c E rho G ΔF) :
    AvailableChain.FGSA.Run.FinalityKernelJoinedClaim_W p :=
by
  intro G ΔF hδ V _ _ In c E rho pt prem
  obtain ⟨w, input, start⟩ := prem.start
  exact split G ΔF hδ c E rho ⟨w, pt.r⟩
    ⟨prem.set, prem.bound, prem.window, start, prem.hhor, input,
      ac G ΔF hδ c E rho w (ready c E rho G ΔF prem.set) prem.bound input⟩

-- S4.5b: each new public contract, support equation, field, and adapter.
#print axioms AvailableChain.FGSA.Run.FinalityFinalizedAt
#print axioms AvailableChain.FGSA.Run.FinalityFinalizedAt_def
#print axioms AvailableChain.FGSA.Run.FinalityBlock
#print axioms AvailableChain.FGSA.Run.FinalityBlock_def
#print axioms AvailableChain.FGSA.Run.finalityRows
#print axioms AvailableChain.FGSA.Run.finalityRows_def
#print axioms AvailableChain.FGSA.Run.FinalitySlashableBound
#print axioms AvailableChain.FGSA.Run.FinalitySlashableBound_def
#print axioms AvailableChain.FGSA.Run.FinalityExecution
#print axioms AvailableChain.FGSA.Run.FinalityExecution_def
#print axioms AvailableChain.FGSA.Run.WholeRunAccountable
#print axioms AvailableChain.FGSA.Run.WholeRunAccountable_def
#print axioms AvailableChain.FGSA.Run.WholeRunAgreement
#print axioms AvailableChain.FGSA.Run.WholeRunAgreement_def
#print axioms AvailableChain.FGSA.Run.CleanInclusionPrem
#print axioms AvailableChain.FGSA.Run.CleanInclusionPrem.mk
#print axioms AvailableChain.FGSA.Run.CleanInclusionPrem.set
#print axioms AvailableChain.FGSA.Run.CleanInclusionPrem.prop
#print axioms AvailableChain.FGSA.Run.CleanInclusionPrem.hhor
#print axioms AvailableChain.FGSA.Run.ExactProposalPrem
#print axioms AvailableChain.FGSA.Run.ExactProposalPrem.mk
#print axioms AvailableChain.FGSA.Run.ExactProposalPrem.set
#print axioms AvailableChain.FGSA.Run.ExactProposalPrem.prop
#print axioms AvailableChain.FGSA.Run.ExactProposalPrem.hhor
#print axioms AvailableChain.FGSA.Run.PureAccountableClaim
#print axioms AvailableChain.FGSA.Run.PureAgreementClaim
#print axioms AvailableChain.FGSA.Run.WholeRunAccountableClaim
#print axioms AvailableChain.FGSA.Run.WholeRunAgreementClaim
#print axioms AvailableChain.FGSA.Run.EventPrefixAgreementClaim
#print axioms AvailableChain.FGSA.Run.FaultCountSlashableBoundClaim
#print axioms AvailableChain.FGSA.Run.FinalizedMonotonicityClaim
#print axioms AvailableChain.FGSA.Run.HonestNeverSlashedClaim
#print axioms AvailableChain.FGSA.Run.FinalizedSafetyConcl
#print axioms AvailableChain.FGSA.Run.FinalizedSafetyClaim
#print axioms AvailableChain.FGSA.Run.FinalLockClaim
#print axioms AvailableChain.FGSA.Run.ExactProposalAt
#print axioms AvailableChain.FGSA.Run.ExactProposalClaim
#print axioms AvailableChain.FGSA.Run.InclusionPostGateAt
#print axioms AvailableChain.FGSA.Run.InclusionAt
#print axioms AvailableChain.FGSA.Run.CleanInclusionPostGateClaim
#print axioms AvailableChain.FGSA.Run.CleanInclusionClaim
#print axioms AvailableChain.FGSA.Run.DutiesExtendOn
#print axioms AvailableChain.FGSA.Run.FCompatBefore
#print axioms AvailableChain.FGSA.Run.P1Concl
#print axioms AvailableChain.FGSA.Run.LeaseOrFFrom
#print axioms AvailableChain.FGSA.Run.OutageCompatAt
#print axioms AvailableChain.FGSA.Run.OutageCompatClaim
#print axioms AvailableChain.FGSA.Run.FastP1Claim
#print axioms AvailableChain.FGSA.Run.SlowP1Claim

-- S4.6b GST finality forms.
#print axioms AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W
#print axioms AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.mk
#print axioms AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.set
#print axioms AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.late
#print axioms AvailableChain.FGSA.Run.FinalityLivenessGSTPrem_W.hhor
#print axioms AvailableChain.FGSA.Run.FinalityLivenessGSTClaim_W
#print axioms AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W
#print axioms AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.mk
#print axioms AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.set
#print axioms AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.prop
#print axioms AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.late
#print axioms AvailableChain.FGSA.Run.ProposalFinalGSTPrem_W.hhor
#print axioms AvailableChain.FGSA.Run.ProposalFinalGSTClaim_W
#print axioms AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W
#print axioms AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.mk
#print axioms AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.set
#print axioms AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.late
#print axioms AvailableChain.FGSA.Run.AboveFrontierGSTPrem_W.hhor
#print axioms AvailableChain.FGSA.Run.AboveFrontierGSTClaim_W

#print axioms AvailableChain.FGSA.Run.AvailableFromConcl
#print axioms AvailableChain.FGSA.Run.AvailableGrowthConcl
#print axioms AvailableChain.FGSA.Run.AvailableGSTClaim
#print axioms AvailableChain.FGSA.Run.AvailableGrowthGSTClaim
#print axioms AvailableChain.FGSA.Run.AwakeProposerRecurrenceFrom
#print axioms AvailableChain.FGSA.Run.CleanGrowthClaim
#print axioms AvailableChain.FGSA.Run.finHeight_def
#print axioms AvailableChain.FGSA.Run.HealSuffix_def
#print axioms AvailableChain.FGSA.Run.healStart_def
#print axioms AvailableChain.FGSA.Run.tstar_def
#print axioms AvailableChain.FGSA.Run.S_at_def
#print axioms AvailableChain.FGSA.Run.outputS_def

namespace AvailableChain.FGSA.Run.Tests.HealedBest

variable (p : Params) {In V : Type} [DecidableEq V] [Fintype V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (G ΔF : Time) (g : Nat)

-- Apply only the stated premises. These tests do not prove the claims.
example (h : HTimeBestClaim p) (hδ : p.δt = 2 * p.R)
    (hs : HealingSet p c E rho G ΔF) (hb : LivenessBoundW p ΔF)
    (hr : Gen.Pure.FinForm.recS.holds (Gen.V2.Duty.HonestSlot rho (fgsaInterface p c))
      p.R (P p) p.Δ (recoveryStart p E) rho.horizon g)
    (hh : recoveryStart p E + B_bestF p ΔF G g ≤ rho.horizon) :
    HTimeBestConcl p c E rho G ΔF g :=
  h G ΔF g hδ c E rho hs hb hr hh

example (h : HTimeSearchClaim p) (hδ : p.δt = 2 * p.R) (hg : 1 ≤ g)
    (hs : HealingSet p c E rho G ΔF) (hb : LivenessBoundW p ΔF)
    (hq : Gen.Pure.QualSearch (Gen.V2.Duty.HonestSlot rho (fgsaInterface p c))
      p.R (P p) p.Δ (recoveryStart p E) rho.horizon g)
    (hh : recoveryStart p E + B_bestF p ΔF G g ≤ rho.horizon) :
    HTimeBestConcl p c E rho G ΔF g :=
  h G ΔF g hδ c E rho hg hs hb hq hh

end AvailableChain.FGSA.Run.Tests.HealedBest
-- B33 WC-LIVE additive statements and test controls.
#print axioms AvailableChain.FGSA.Run.ServedFromGateAt
#print axioms AvailableChain.FGSA.Run.ServedFromGateAt_def
#print axioms AvailableChain.FGSA.Run.JointGrowthAt
#print axioms AvailableChain.FGSA.Run.JointGrowthAt_def
#print axioms AvailableChain.FGSA.Run.WeakContinuationLiveAt₂
#print axioms AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.mk
#print axioms AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.safety
#print axioms AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.inclusion
#print axioms AvailableChain.FGSA.Run.WeakContinuationLiveAt₂.growth
#print axioms AvailableChain.FGSA.Run.BoundedSafetyLivenessRecovery₂
#print axioms AvailableChain.FGSA.Run.BoundedSafetyLivenessRecovery₂_def
#print axioms AvailableChain.FGSA.Run.WeakContinuationLiveClaim

public section

namespace AvailableChain.FGSA.Run.Tests.WeakContinuationLive

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V] [Fintype V]

-- Intended universal claim projection; this does not prove the live claim.
example (G : Time) : WeakContinuationLiveClaim p G → WeakContinuationClaim p G := by
  intro h V _ _ In c ΔF hδ E source hs
  obtain ⟨u, Q, iStar, cut, live⟩ := h c ΔF hδ E source hs
  refine ⟨u, Q, iStar, cut, ?_⟩
  intro E' rho continuation
  exact (live E' rho continuation).safety (cut.beforeEnd.le.trans continuation.covered)

end AvailableChain.FGSA.Run.Tests.WeakContinuationLive
end

-- LIVE-DC definitions and equation exports.
#print axioms AvailableChain.FGSA.Run.liveDCDeadline_W
#print axioms AvailableChain.FGSA.Run.liveDCDeadline_W_def
#print axioms AvailableChain.FGSA.Run.LiveDCConcl_W
#print axioms AvailableChain.FGSA.Run.LiveDCConcl_W_def
#print axioms AvailableChain.FGSA.Run.LiveDCFromWindowsStatement
#print axioms AvailableChain.FGSA.Run.LiveDCFromWindowsStatement_def

-- FrameNext and ComposeNext statement modules
#print axioms AvailableChain.FGSA.Run.frameRNext
#print axioms AvailableChain.FGSA.Run.frameRNext_def
#print axioms AvailableChain.FGSA.Run.domainRNext
#print axioms AvailableChain.FGSA.Run.domainRNext_def
#print axioms AvailableChain.FGSA.Run.RFrameExactNext
#print axioms AvailableChain.FGSA.Run.RFrameExactNext_def
#print axioms AvailableChain.FGSA.Run.RFrameNext
#print axioms AvailableChain.FGSA.Run.RFrameNext_def
#print axioms AvailableChain.FGSA.Run.FGFoundationNext
#print axioms AvailableChain.FGSA.Run.TStartNext
#print axioms AvailableChain.FGSA.Run.TWalkNext
#print axioms AvailableChain.FGSA.Run.WalkBatchNext
#print axioms AvailableChain.FGSA.Run.SettledPhaseFrameNext
#print axioms AvailableChain.FGSA.Run.SettledPhaseFrameNext_def
#print axioms AvailableChain.FGSA.Run.TGeomNext
#print axioms AvailableChain.FGSA.Run.OpeningCoveredNext
#print axioms AvailableChain.FGSA.Run.FGFoundationNext.mk
#print axioms AvailableChain.FGSA.Run.FGFoundationNext.store
#print axioms AvailableChain.FGSA.Run.FGFoundationNext.cumul
#print axioms AvailableChain.FGSA.Run.FGFoundationNext.mono
#print axioms AvailableChain.FGSA.Run.FGFoundationNext.frame
#print axioms AvailableChain.FGSA.Run.FGFoundationNext.geo
#print axioms AvailableChain.FGSA.Run.FGFoundationNext.strat
#print axioms AvailableChain.FGSA.Run.FGFoundationNext.reconcile

-- AvailableChainFGSAClaims/Claims/FrameNext.lean
#print axioms AvailableChain.FGSA.Run.FGFoundationClaimNext
#print axioms AvailableChain.FGSA.Run.FrameAtNext
#print axioms AvailableChain.FGSA.Run.FrameClaimNext
#print axioms AvailableChain.FGSA.Run.AwakeClosed
#print axioms AvailableChain.FGSA.Run.B_FW_sleep
#print axioms AvailableChain.FGSA.Run.B_HF_sleep
#print axioms AvailableChain.FGSA.Run.B_resetF_sleep
#print axioms AvailableChain.FGSA.Run.BatchReceiptAt
#print axioms AvailableChain.FGSA.Run.DutiesExtendScoped
#print axioms AvailableChain.FGSA.Run.FirstRestored
#print axioms AvailableChain.FGSA.Run.OutageContinuationReceipt
#print axioms AvailableChain.FGSA.Run.OutageE
#print axioms AvailableChain.FGSA.Run.OutageE1
#print axioms AvailableChain.FGSA.Run.OutageEnd
#print axioms AvailableChain.FGSA.Run.OutagePrefixReceipt
#print axioms AvailableChain.FGSA.Run.OutageVoteMember
#print axioms AvailableChain.FGSA.Run.ReceiptObjectAt
#print axioms AvailableChain.FGSA.Run.RestartFreeTime
#print axioms AvailableChain.FGSA.Run.ScopedCompat
#print axioms AvailableChain.FGSA.Run.ScopedMono
#print axioms AvailableChain.FGSA.Run.ScopedServed
#print axioms AvailableChain.FGSA.Run.WakesAppliedAtIdx
#print axioms AvailableChain.FGSA.Run.caughtUpAt
#print axioms AvailableChain.FGSA.Run.caughtUpAtIdx
#print axioms AvailableChain.FGSA.Run.confirmedReader
#print axioms AvailableChain.FGSA.Run.confirmedReaderAtIdx
#print axioms AvailableChain.FGSA.Run.confirmedReaderIdx
#print axioms AvailableChain.FGSA.Run.coverDeadline
#print axioms AvailableChain.FGSA.Run.coverLabel
#print axioms AvailableChain.FGSA.Run.coveredNodes
#print axioms AvailableChain.FGSA.Run.enabledGateAt
#print axioms AvailableChain.FGSA.Run.fastCoveredSchedule
#print axioms AvailableChain.FGSA.Run.firstUpdateLabel
#print axioms AvailableChain.FGSA.Run.headReader
#print axioms AvailableChain.FGSA.Run.joinedAt
#print axioms AvailableChain.FGSA.Run.joinedDuty
#print axioms AvailableChain.FGSA.Run.joinedHonest
#print axioms AvailableChain.FGSA.Run.outageConfirmedReader
#print axioms AvailableChain.FGSA.Run.outageH
#print axioms AvailableChain.FGSA.Run.outageHeadReader
#print axioms AvailableChain.FGSA.Run.outageW
#print axioms AvailableChain.FGSA.Run.prefixTime
#print axioms AvailableChain.FGSA.Run.recoveryDelay
#print axioms AvailableChain.FGSA.Run.recoveryStart
#print axioms AvailableChain.FGSA.Run.restoredLabel
#print axioms AvailableChain.FGSA.Run.sleepyBad
#print axioms AvailableChain.FGSA.Run.slotAt
#print axioms AvailableChain.FGSA.Run.slotStartZ
#print axioms AvailableChain.FGSA.Run.slowCoveredSchedule
#print axioms AvailableChain.FGSA.Run.tauC
#print axioms AvailableChain.FGSA.Run.voteZ
#print axioms AvailableChain.FGSA.Run.diagnosticGateResult
#print axioms AvailableChain.FGSA.Run.CleanPrefixSleep₂
#print axioms AvailableChain.FGSA.Run.CleanSleep₂
#print axioms AvailableChain.FGSA.Run.HealthyPrefixSleep₂
#print axioms AvailableChain.FGSA.Run.OutageSleep₂
#print axioms AvailableChain.FGSA.Run.RecoveryReadinessClaim
#print axioms AvailableChain.FGSA.Run.RecoverySleep₂
#print axioms AvailableChain.FGSA.Run.RMonoAll
#print axioms AvailableChain.FGSA.Run.RMonoAll_def
#print axioms AvailableChain.FGSA.Run.RStoreDurable
#print axioms AvailableChain.FGSA.Run.RStoreDurable_def
#print axioms AvailableChain.FGSA.Run.RStoreEpoch
#print axioms AvailableChain.FGSA.Run.RStoreEpoch_def
#print axioms AvailableChain.FGSA.Run.RFrameNextEpoch
#print axioms AvailableChain.FGSA.Run.RFrameNextEpoch_def
#print axioms AvailableChain.FGSA.Run.FinalizedMonotonicityRestartClaim
#print axioms AvailableChain.FGSA.Run.OutageRepairReady
#print axioms AvailableChain.FGSA.Run.OutageContinuationSleepPrem
#print axioms AvailableChain.FGSA.Run.CleanContinuationSleep₂
#print axioms AvailableChain.FGSA.Run.CleanGrowthContinuationSleep₂
#print axioms AvailableChain.FGSA.Run.SourcePendingReceipt
#print axioms AvailableChain.FGSA.Run.OutageContinuationReceiptDerivedClaim
#print axioms AvailableChain.FGSA.Run.OutageE1DerivedClaim
#print axioms AvailableChain.FGSA.Run.OutagePrefixReceiptDerivedClaim
