module
public import ConsensusLeanTest.Blocks
public import ConsensusLeanTest.Common
public import ConsensusLeanTest.Controls
public import ConsensusLeanTest.Gaps
public import ConsensusLeanTest.Goldilocks
public import ConsensusLeanTest.Good
public import ConsensusLeanTest.Leaks
public import ConsensusLeanTest.Lift
public import ConsensusLeanTest.Model
public import ConsensusLeanTest.Network
public import ConsensusLeanTest.Problem
public import ConsensusLeanTest.Realizable
public import ConsensusLeanTest.Regimes
public import ConsensusLeanTest.Shape
public import ConsensusLeanTest.Support
public import ConsensusLeanTest.Vacuity
public import ConsensusLean
public import Solution

/-! # Name index

Every name a reviewer or the README relies on, checked to exist by the build:
`example := ``X` is a resolved name literal, which fails unless `X` is a declaration
(`example := @X` would also accept a field projection of a constant, e.g. `@c.field`).
This checks **existence only**, not strength: what a test
proves is its own statement (compiled in the gate). The declaration check
(`scripts/check.sh`, EthLib check-decls) scans every declaration of every module.

Kept here: the endpoint theorems, every theorem of the rejecting-test files
(`Problem`, `Network`, `Regimes`, `Good`, `Leaks`, `Vacuity`), the names cited
by `Gaps` and the Goldilocks sheet, the former audit list, and every name cited by the docs that
check.sh step 12 checks against this file (`doc_name_files` in `scripts/boundaries.toml`). -/

/-! ## Endpoints -/

example := ``Consensus.Review.AcceptedGood
example := ``Consensus.Review.RegimesRealizable
example := ``Consensus.Review.LogFaithful
example := ``Consensus.Review.HeldIffServed
example := ``Consensus.Review.acceptedGood
example := ``Consensus.Review.regimesRealizable
example := ``Consensus.Review.logFaithful
example := ``Consensus.Review.heldIffServed
example := ``Consensus.Shape.Accepted.good
example := ``Consensus.Shape.Accepted.activeService
example := ``Consensus.Shape.refinement
example := ``Consensus.Shape.regimes_realizable
example := ``Consensus.Model.sysOf_adequate

/-! ## L0 (problem and facts) -/

example := ``Consensus.CommLog.Delivers.prefix
example := ``Consensus.CommLog.Delivers.reindex
example := ``Consensus.CommLog.EagerFrom.delivers
example := ``Consensus.CommLog.EagerFrom.psync
example := ``Consensus.CommLog.EagerFrom.syncUntil
example := ``Consensus.CommLog.PSync.mono
example := ``Consensus.CommLog.PSync.syncUntil_zero
example := ``Consensus.EnvPoint.EtaReadyAbove.awakeForm
example := ``Consensus.EnvPoint.EtaReadyAbove.mono
example := ``Consensus.EnvPoint.EtaReadyAbove.readyAbove
example := ``Consensus.EnvPoint.EtaSleepyOn.mono
example := ``Consensus.EnvPoint.EtaSleepyOn.sleepyOn
example := ``Consensus.EnvPoint.HealthyOn.awakeOfAll
example := ``Consensus.EnvPoint.HealthyOn.faultsBelow
example := ``Consensus.EnvPoint.etaReadyAbove_zero
example := ``Consensus.EnvPoint.etaSet_mono
example := ``Consensus.EnvPoint.etaSleepyOn_zero
example := ``Consensus.EnvPoint.readyAbove_iff_union
example := ``Consensus.EnvPoint.readyAt_subset_awakeAt
example := ``Consensus.Good.final_agree
example := ``Consensus.Good.final_safe_healthy
example := ``Consensus.Good.healedSafe_prefix
example := ``Consensus.Good.outage_prefix
example := ``Consensus.Good.persists_final_compatible
example := ``Consensus.Good.served
example := ``Consensus.Good.sleepySafe_prefix
example := ``Consensus.Params.standard_admissible
example := ``Consensus.System.Healthy.of_le
example := ``Consensus.System.Outage.of_le
example := ``Consensus.System.Sleepy.of_le
example := ``Consensus.System.outage_eta_zero
example := ``Consensus.System.cDur_of_catchUp
example := ``Consensus.System.agree_of_accountable
example := ``Consensus.Trace.PrefixOf.endCut_eq
example := ``Consensus.Trace.PrefixOf.protectedUpTo
example := ``Consensus.Trace.PrefixOf.readySafeUpTo
example := ``Consensus.Trace.TxLive.served

example := ``Consensus.System.Sleepy
example := ``Consensus.System.Healthy
example := ``Consensus.System.Outage
example := ``Consensus.System.cDur
example := ``Consensus.System.heal
example := ``Consensus.System.ready
example := ``Consensus.System.lat
example := ``Consensus.Behaviour.healthyLive
example := ``Consensus.Behaviour.finalAccountable
example := ``Consensus.Trace.ReadySafeUpTo
example := ``Consensus.CommLog.SendsFromZero

/-! ## L1 (model and proofs) -/
example := ``Consensus.Model.Run.mem_viewIdx_iff
example := ``Consensus.Model.Run.seen_source
example := ``Consensus.Model.Run.viewIdx_mono

example := ``Consensus.Model.Obj.Contains.trans
example := ``Consensus.Model.Run.SameTrace.log_eq
example := ``Consensus.Model.Run.candidates_signer
example := ``Consensus.Model.Run.credentials_of_causal
example := ``Consensus.Model.Run.held_iff_served
example := ``Consensus.Model.Run.honestNeverSlashed
example := ``Consensus.Model.Run.log_sendsFromZero
example := ``Consensus.Model.Run.not_hashCollision_of_injective
example := ``Consensus.Model.Run.not_slashable_of_causal
example := ``Consensus.Model.Run.rehash_trace
example := ``Consensus.Model.Run.selected_of_observed
example := ``Consensus.Model.Run.signed_seen_released
example := ``Consensus.Model.Run.truncate_prefix
example := ``Consensus.Model.Run.truncate_valid
example := ``Consensus.Model.Run.txHeld_mem_mempool
example := ``Consensus.Model.SelSpec.admits_exists
example := ``Consensus.Model.canonical_run_from
example := ``Consensus.Model.canonical_run_from_causal
example := ``Consensus.Model.holds_of_injective
example := ``Consensus.Model.mem_honestEvidence_iff
example := ``Consensus.Model.protects
example := ``Consensus.Model.protects_iff
example := ``Consensus.Model.releaseAll_eq_carried
example := ``Consensus.Model.releaseAll_noConflict
example := ``Consensus.Model.sysOf_delivers_iff
example := ``Consensus.Model.sysOf_eagerFrom
example := ``Consensus.Model.sysOf_laws
example := ``Consensus.Model.sysOf_log_faithful
example := ``Consensus.Model.sysOf_nonFraming

/-! ## Blocks -/

example := ``Consensus.Blocks.NotReadyOn.mono
example := ``Consensus.Blocks.NotReadyOn.of_card_le
example := ``Consensus.Blocks.NotReadyOn.readyAt_nonempty
example := ``Consensus.Blocks.NotReadyOn.shrink
example := ``Consensus.Blocks.Pattern.range
example := ``Consensus.Blocks.Pattern.span_le
example := ``Consensus.Blocks.Pattern.span_range
example := ``Consensus.Blocks.PatternRecurrence.exists_honest
example := ``Consensus.Blocks.PatternRecurrence.exists_inside
example := ``Consensus.Blocks.PatternRecurrence.mono
example := ``Consensus.Blocks.PatternRecurrence.reads_upTo
example := ``Consensus.Blocks.PatternRecurrence.shrink
example := ``Consensus.Blocks.PatternRecurrence.single_of_zero
example := ``Consensus.Blocks.ledgerOf_prefix
example := ``Consensus.Blocks.patternRecurrence_of_all
example := ``Consensus.Blocks.patternRecurrence_of_periodic
example := ``Consensus.Blocks.Recurrence.exists_bad_slot
example := ``Consensus.Blocks.Recurrence.pattern_good
example := ``Consensus.Blocks.Recurrence.BadSlotSlack

/-! ## L2 (shape) and test values -/

example := ``Consensus.Shape.Accepted.behaviour
example := ``Consensus.Shape.ProgressFits
example := ``Consensus.Shape.ProgressReq.Fits
example := ``Consensus.Shape.ProgressReq.Tolerates
example := ``Consensus.Shape.ProgressTolerant
example := ``Consensus.Shape.ProposalLive.ready
example := ``Consensus.Shape.ProposalLiveReady.of_noReady
example := ``Consensus.Shape.RealizableActive.toRealizable
example := ``Consensus.Shape.BadProposerEvery
example := ``Consensus.Shape.badSlotRole
example := ``Consensus.Shape.badSel
example := ``Consensus.Shape.badSel_admits
example := ``Consensus.Shape.badSel_bad
example := ``Consensus.Shape.badSel_good_mem
example := ``Consensus.Shape.bad_selection
example := ``Consensus.Shape.ShapeClaimsAt
example := ``Consensus.Shape.active_relay
example := ``Consensus.Shape.bftContract_admissible
example := ``Consensus.Shape.coverage
example := ``Consensus.Shape.etaReadyAbove_of_card
example := ``Consensus.Shape.gst_le_heal
example := ``Consensus.Shape.healthy_witness
example := ``Consensus.Shape.healthy_witness_sel
example := ``Consensus.Shape.real_run_sel
example := ``Consensus.Shape.honestProposal_payload
example := ``Consensus.Shape.ledgerTrace
example := ``Consensus.Shape.one_lt_beta_mul_card
example := ``Consensus.Shape.outage_witness
example := ``Consensus.Shape.proposalLive_txLive
example := ``Consensus.Shape.shapeProgress
example := ``Consensus.Shape.sleepyStress_witness
example := ``Consensus.Shape.sleepy_witness
example := ``Consensus.Shape.streamletContract_progressFits
example := ``Consensus.Shape.streamletContract_progressTolerant
example := ``Consensus.Shape.tendermintContract_progressFits
example := ``Consensus.Shape.tendermintContract_progressTolerant

/-! ## Goldilocks FG (milestone M₁) -/

example := ``Consensus.Goldilocks.FG.FGParams
example := ``Consensus.Goldilocks.FG.FGParams.q
example := ``Consensus.Goldilocks.FG.Att
example := ``Consensus.Goldilocks.FG.FGBlock
example := ``Consensus.Goldilocks.FG.ChainState
example := ``Consensus.Goldilocks.FG.ChainState.bound
example := ``Consensus.Goldilocks.FG.Att.WellFormed
example := ``Consensus.Goldilocks.FG.ChainState.validAtt
example := ``Consensus.Goldilocks.FG.ChainState.processAtt
example := ``Consensus.Goldilocks.FG.FGParams.heightEvents
example := ``Consensus.Goldilocks.FG.FGParams.stateTransition
example := ``Consensus.Goldilocks.FG.FGParams.chainState
example := ``Consensus.Goldilocks.FG.Record
example := ``Consensus.Goldilocks.FG.Record.createAtt
example := ``Consensus.Goldilocks.FG.Record.run
example := ``Consensus.Goldilocks.FG.slashable
example := ``Consensus.Goldilocks.FG.QuorumIntersection
example := ``Consensus.Goldilocks.FG.ChainInvariants
example := ``Consensus.Goldilocks.FG.HeightStep
example := ``Consensus.Goldilocks.FG.GatedConsumption
example := ``Consensus.Goldilocks.FG.FinalityBeforeGate
example := ``Consensus.Goldilocks.FG.Retention
example := ``Consensus.Goldilocks.FG.RetentionThroughAppend
example := ``Consensus.Goldilocks.FG.Aggregation
example := ``Consensus.Goldilocks.FG.ClientSafety
example := ``Consensus.Goldilocks.FG.AccountableSafety
example := ``Consensus.Goldilocks.FG.FGSafety

/-! ## Goldilocks Common and Frame -/

example := ``Consensus.Goldilocks.Anc
example := ``Consensus.Goldilocks.AncAntisymm
example := ``Consensus.Goldilocks.AncTotal
example := ``Consensus.Goldilocks.Block
example := ``Consensus.Goldilocks.Block.RootOk
example := ``Consensus.Goldilocks.Coherent
example := ``Consensus.Goldilocks.CommonStatements
example := ``Consensus.Goldilocks.Compatible
example := ``Consensus.Goldilocks.DeepestCommonAncestor
example := ``Consensus.Goldilocks.Digest
example := ``Consensus.Goldilocks.DigestDeterminesBlock
example := ``Consensus.Goldilocks.FrameEntersOnce
example := ``Consensus.Goldilocks.Frame
example := ``Consensus.Goldilocks.Frame.IsViableAncestor
example := ``Consensus.Goldilocks.Frame.Rooted
example := ``Consensus.Goldilocks.Frame.viableAncestor
example := ``Consensus.Goldilocks.Frame.viableTree
example := ``Consensus.Goldilocks.FrameEvol
example := ``Consensus.Goldilocks.FrameOK
example := ``Consensus.Goldilocks.FrameSeq
example := ``Consensus.Goldilocks.FrameSeqIn
example := ``Consensus.Goldilocks.FrameStatements
example := ``Consensus.Goldilocks.FrameStep
example := ``Consensus.Goldilocks.FrameNeverReturns
example := ``Consensus.Goldilocks.Params
example := ``Consensus.Goldilocks.Params.IsPublic
example := ``Consensus.Goldilocks.Params.q
example := ``Consensus.Goldilocks.Params.slotOf
example := ``Consensus.Goldilocks.FrameParentClosed
example := ``Consensus.Goldilocks.ParentIn
example := ``Consensus.Goldilocks.FrameRetention
example := ``Consensus.Goldilocks.SlotOfSpec
example := ``Consensus.Goldilocks.FrameStepAddsBlock
example := ``Consensus.Goldilocks.ViableAncestorExists
example := ``Consensus.Goldilocks.ViableAncestorSelf
example := ``Consensus.Goldilocks.ViableTreeAncestorClosed

/-! ## Goldilocks FGStore (a milestone PR appends here only) -/

example := ``Consensus.Goldilocks.Block.fgView
example := ``Consensus.Goldilocks.NodeBlock
example := ``Consensus.Goldilocks.Params.fg
example := ``Consensus.Goldilocks.Params.genesisBlock
example := ``Consensus.Goldilocks.Store
example := ``Consensus.Goldilocks.Store.AcceptIsFrameStep
example := ``Consensus.Goldilocks.Store.AcceptedTree
example := ``Consensus.Goldilocks.Store.Anc
example := ``Consensus.Goldilocks.Store.CacheInvariants
example := ``Consensus.Goldilocks.Store.ChainStateOfChain
example := ``Consensus.Goldilocks.Store.Contest
example := ``Consensus.Goldilocks.Store.FGStoreLocal
example := ``Consensus.Goldilocks.Store.FGStoreLocalAt
example := ``Consensus.Goldilocks.Store.FinalizedMonotone
example := ``Consensus.Goldilocks.Store.FrameRealization
example := ``Consensus.Goldilocks.Store.EntryStateOfSource
example := ``Consensus.Goldilocks.FGLabel.Step
example := ``Consensus.Goldilocks.FGLabel.processed
example := ``Consensus.Goldilocks.FGLocalRun
example := ``Consensus.Goldilocks.FGState
example := ``Consensus.Goldilocks.FGTrace
example := ``Consensus.Goldilocks.FGTrace.AcceptAt
example := ``Consensus.Goldilocks.FGTrace.ProcessAt
example := ``Consensus.Goldilocks.FGTrace.SignAt
example := ``Consensus.Goldilocks.Store.FGStoreTrace
example := ``Consensus.Goldilocks.Store.FGStoreTraceAt
example := ``Consensus.Goldilocks.Store.FinalizedSafety
example := ``Consensus.Goldilocks.Store.QuorumFreeEntries
example := ``Consensus.Goldilocks.Store.namers
example := ``Consensus.Goldilocks.Store.HasViableDescendant
example := ``Consensus.Goldilocks.Store.IsViable
example := ``Consensus.Goldilocks.Store.LexLt
example := ``Consensus.Goldilocks.Store.LinkedFromGenesis
example := ``Consensus.Goldilocks.Store.OnChain
example := ``Consensus.Goldilocks.Store.Reachable
example := ``Consensus.Goldilocks.Store.Step
example := ``Consensus.Goldilocks.Store.TreeGrows
example := ``Consensus.Goldilocks.Store.addAtts
example := ``Consensus.Goldilocks.Store.attest
example := ``Consensus.Goldilocks.Store.fcRoot
example := ``Consensus.Goldilocks.Store.headHeightFloor
example := ``Consensus.Goldilocks.Store.init
example := ``Consensus.Goldilocks.Store.onAttestation
example := ``Consensus.Goldilocks.Store.onBlock
example := ``Consensus.Goldilocks.Store.proposalAttestations
example := ``Consensus.Goldilocks.Store.toFrame
example := ``Consensus.Goldilocks.Store.tree
example := ``Consensus.Goldilocks.Store.updateFinality

/-! ## Goldilocks ACBase (a milestone PR appends here only) -/

example := ``Consensus.Goldilocks.ACInterface
example := ``Consensus.Goldilocks.ACInterface.AtReachable
example := ``Consensus.Goldilocks.ACInterface.Call
example := ``Consensus.Goldilocks.ACInterface.CallOK
example := ``Consensus.Goldilocks.ACInterface.CallStep
example := ``Consensus.Goldilocks.ACInterface.FrameIn
example := ``Consensus.Goldilocks.ACInterface.HeadOK
example := ``Consensus.Goldilocks.ACInterface.InitialFrame
example := ``Consensus.Goldilocks.ACInterface.Reachable
example := ``Consensus.Goldilocks.ACInterface.ReachableAt
example := ``Consensus.Goldilocks.ACInterface.ReqHeads
example := ``Consensus.Goldilocks.ACInterface.ReqOutputs
example := ``Consensus.Goldilocks.ACInterface.ReqParent
example := ``Consensus.Goldilocks.ACInterface.ReqPayload
example := ``Consensus.Goldilocks.ACInterface.ReqSource
example := ``Consensus.Goldilocks.ACInterface.Requirements
example := ``Consensus.Goldilocks.ACInterface.step
example := ``Consensus.Goldilocks.ACLabel
example := ``Consensus.Goldilocks.ACLocalRun
example := ``Consensus.Goldilocks.ACTrace
example := ``Consensus.Goldilocks.ACTrace.deadline
example := ``Consensus.Goldilocks.ACTrace.lastWake
example := ``Consensus.Goldilocks.DutyHead
example := ``Consensus.Goldilocks.Emission
example := ``Consensus.Goldilocks.LocalRunReachable
example := ``Consensus.Goldilocks.SA.ACBase
example := ``Consensus.Goldilocks.SA.AdmissionSlots
example := ``Consensus.Goldilocks.SA.CandidatesChain
example := ``Consensus.Goldilocks.SA.CarriedVotes
example := ``Consensus.Goldilocks.SA.Carry
example := ``Consensus.Goldilocks.SA.CarryAt
example := ``Consensus.Goldilocks.SA.ETime
example := ``Consensus.Goldilocks.SA.FaultBound
example := ``Consensus.Goldilocks.SA.InTree
example := ``Consensus.Goldilocks.SA.InterfaceRequirements
example := ``Consensus.Goldilocks.SA.JoinedAt
example := ``Consensus.Goldilocks.SA.JoinedAwake
example := ``Consensus.Goldilocks.SA.JoinedFrom
example := ``Consensus.Goldilocks.SA.JoinedKeepsVotes
example := ``Consensus.Goldilocks.SA.LiveLocksChain
example := ``Consensus.Goldilocks.SA.Lock
example := ``Consensus.Goldilocks.SA.LockExpiry
example := ``Consensus.Goldilocks.SA.LockToTip
example := ``Consensus.Goldilocks.SA.LocksMoveBack
example := ``Consensus.Goldilocks.SA.MajorityChain
example := ``Consensus.Goldilocks.SA.MergedOpponents
example := ``Consensus.Goldilocks.SA.MovesBack
example := ``Consensus.Goldilocks.SA.OneVotePerSlot
example := ``Consensus.Goldilocks.SA.OpponentsMonotone
example := ``Consensus.Goldilocks.SA.OptimisticChain
example := ``Consensus.Goldilocks.SA.Payload
example := ``Consensus.Goldilocks.SA.ReplayOrder
example := ``Consensus.Goldilocks.SA.PoolCap
example := ``Consensus.Goldilocks.SA.ProposalPayloadValid
example := ``Consensus.Goldilocks.SA.ResolutionStable
example := ``Consensus.Goldilocks.SA.RestartState
example := ``Consensus.Goldilocks.SA.SAParams
example := ``Consensus.Goldilocks.SA.SAParams.ts
example := ``Consensus.Goldilocks.SA.SAState
example := ``Consensus.Goldilocks.SA.SAState.initial
example := ``Consensus.Goldilocks.SA.SATrace
example := ``Consensus.Goldilocks.SA.SlotArithmetic
example := ``Consensus.Goldilocks.SA.StampParent
example := ``Consensus.Goldilocks.SA.StampStable
example := ``Consensus.Goldilocks.SA.SupportInTree
example := ``Consensus.Goldilocks.SA.SupportersAntitone
example := ``Consensus.Goldilocks.SA.UnlockIdempotent
example := ``Consensus.Goldilocks.SA.UnlockNoFallback
example := ``Consensus.Goldilocks.SA.Vote
example := ``Consensus.Goldilocks.SA.acConfirmed
example := ``Consensus.Goldilocks.SA.acHead
example := ``Consensus.Goldilocks.SA.acOnBlock
example := ``Consensus.Goldilocks.SA.acOnMessage
example := ``Consensus.Goldilocks.SA.acOnTick
example := ``Consensus.Goldilocks.SA.acProposal
example := ``Consensus.Goldilocks.SA.acRestart
example := ``Consensus.Goldilocks.SA.acToFG
example := ``Consensus.Goldilocks.SA.addLocks
example := ``Consensus.Goldilocks.SA.admitVote
example := ``Consensus.Goldilocks.SA.conflictsWithLock
example := ``Consensus.Goldilocks.SA.deepest
example := ``Consensus.Goldilocks.SA.equivocators
example := ``Consensus.Goldilocks.SA.getAnchor
example := ``Consensus.Goldilocks.SA.getHead
example := ``Consensus.Goldilocks.SA.ghost
example := ``Consensus.Goldilocks.SA.goldfishScore
example := ``Consensus.Goldilocks.SA.goldilocksSA
example := ``Consensus.Goldilocks.SA.joined
example := ``Consensus.Goldilocks.SA.latestView
example := ``Consensus.Goldilocks.SA.liveLocks
example := ``Consensus.Goldilocks.SA.lookup
example := ``Consensus.Goldilocks.SA.mergedVoteView
example := ``Consensus.Goldilocks.SA.opponents
example := ``Consensus.Goldilocks.SA.optimisticConfirmation
example := ``Consensus.Goldilocks.SA.resolutionTime
example := ``Consensus.Goldilocks.SA.supporters
example := ``Consensus.Goldilocks.SA.tryVote
example := ``Consensus.Goldilocks.SA.unlock
example := ``Consensus.Goldilocks.SA.updateConfirmation
example := ``Consensus.Goldilocks.SA.validPayload
example := ``Consensus.Goldilocks.SA.voteView
example := ``Consensus.Goldilocks.SA.voterBlockTree
example := ``Consensus.Goldilocks.SyncAC
example := ``Consensus.Goldilocks.Trace
example := ``Consensus.Goldilocks.Trace.CallAt
example := ``Consensus.Goldilocks.Trace.state

/-! ## Goldilocks ACSteps (a milestone PR appends here only) -/

example := ``Consensus.Goldilocks.SA.ACRun
example := ``Consensus.Goldilocks.SA.ACSteps
example := ``Consensus.Goldilocks.SA.ACStepsAt
example := ``Consensus.Goldilocks.SA.CastAt
example := ``Consensus.Goldilocks.SA.EarlierVotesExtend
example := ``Consensus.Goldilocks.SA.FastLockAt
example := ``Consensus.Goldilocks.SA.FastTest
example := ``Consensus.Goldilocks.SA.FastUpdateAt
example := ``Consensus.Goldilocks.SA.FirstTransfer
example := ``Consensus.Goldilocks.SA.HonestObjects
example := ``Consensus.Goldilocks.SA.NextTransfer
example := ``Consensus.Goldilocks.SA.OptimisticLockAt
example := ``Consensus.Goldilocks.SA.OptimisticNextUpdate
example := ``Consensus.Goldilocks.SA.OptimisticPoint
example := ``Consensus.Goldilocks.SA.OptimisticTransfer
example := ``Consensus.Goldilocks.SA.ProposalAt
example := ``Consensus.Goldilocks.SA.ProposerVotersAgree
example := ``Consensus.Goldilocks.SA.ResultAt
example := ``Consensus.Goldilocks.SA.ResultTransfer
example := ``Consensus.Goldilocks.SA.SourceAge
example := ``Consensus.Goldilocks.SA.SourceCompatible
example := ``Consensus.Goldilocks.SA.ToFGAt
example := ``Consensus.Goldilocks.SA.UpdateAt
example := ``Consensus.Goldilocks.SA.ViableAtVote
example := ``Consensus.Goldilocks.SA.VoteExtends
example := ``Consensus.Goldilocks.SA.blockReceipt
example := ``Consensus.Goldilocks.SA.confirmationPath
example := ``Consensus.Goldilocks.SA.fastCounted
example := ``Consensus.Goldilocks.SA.fastSelect
example := ``Consensus.Goldilocks.SA.optimisticSelect

/-! ## Goldilocks Compose/AnyAC (a milestone PR appends here only) -/

example := ``Consensus.Goldilocks.NodeAC
example := ``Consensus.Goldilocks.NodeState
example := ``Consensus.Goldilocks.Node.init
example := ``Consensus.Goldilocks.Node.frame
example := ``Consensus.Goldilocks.FGLabel
example := ``Consensus.Goldilocks.Cut
example := ``Consensus.Goldilocks.Node.acCall
example := ``Consensus.Goldilocks.Node.acProposal
example := ``Consensus.Goldilocks.Node.acToFG
example := ``Consensus.Goldilocks.Node.onBlock
example := ``Consensus.Goldilocks.Node.onMessage
example := ``Consensus.Goldilocks.Node.onAttestation
example := ``Consensus.Goldilocks.Node.restart
example := ``Consensus.Goldilocks.Node.mkBlock
example := ``Consensus.Goldilocks.Node.proposeBlock
example := ``Consensus.Goldilocks.Node.attest
example := ``Consensus.Goldilocks.Node.TickStep
example := ``Consensus.Goldilocks.Node.tickSteps
example := ``Consensus.Goldilocks.Node.Proposes
example := ``Consensus.Goldilocks.Node.tickStep
example := ``Consensus.Goldilocks.Node.runSteps
example := ``Consensus.Goldilocks.Node.onTick
example := ``Consensus.Goldilocks.Node.Event
example := ``Consensus.Goldilocks.Node.exec
example := ``Consensus.Goldilocks.Node.WireOK
example := ``Consensus.Goldilocks.Node.Phase
example := ``Consensus.Goldilocks.Node.Phase.at
example := ``Consensus.Goldilocks.Node.Config
example := ``Consensus.Goldilocks.Node.Config.init
example := ``Consensus.Goldilocks.Node.EventOK
example := ``Consensus.Goldilocks.Node.Event.phaseAfter
example := ``Consensus.Goldilocks.Node.Step
example := ``Consensus.Goldilocks.Node.Reaches
example := ``Consensus.Goldilocks.Node.Reachable
example := ``Consensus.Goldilocks.Node.CutStep
example := ``Consensus.Goldilocks.Node.CutChain
example := ``Consensus.Goldilocks.Compose.TipsNested
example := ``Consensus.Goldilocks.Compose.ProposalParentHeld
example := ``Consensus.Goldilocks.Compose.SourceHeld
example := ``Consensus.Goldilocks.Compose.DutyHeadsHeld
example := ``Consensus.Goldilocks.Compose.InterfaceStatements
example := ``Consensus.Goldilocks.Compose.ComposeInterfaceStatements
example := ``Consensus.Goldilocks.Compose.ThreeTips
example := ``Consensus.Goldilocks.Compose.FinalizedMonotone
example := ``Consensus.Goldilocks.Compose.RestartKeepsFG
example := ``Consensus.Goldilocks.Compose.NoCollOn
example := ``Consensus.Goldilocks.Compose.HonestBlockAccepted
example := ``Consensus.Goldilocks.Compose.ProposalCuts
example := ``Consensus.Goldilocks.Compose.UpdateCuts
example := ``Consensus.Goldilocks.Compose.TickShape
example := ``Consensus.Goldilocks.Compose.TickOrder
example := ``Consensus.Goldilocks.Compose.SignedOnlyInTicks
example := ``Consensus.Goldilocks.Compose.ExecIsCutChain
example := ``Consensus.Goldilocks.Compose.ACStatesReachable
example := ``Consensus.Goldilocks.Compose.FGStatesReachable
example := ``Consensus.Goldilocks.Compose.RecordIsClientRun
example := ``Consensus.Goldilocks.Compose.SourcesHeld
example := ``Consensus.Goldilocks.Compose.NodeStatements
example := ``Consensus.Goldilocks.Compose.ComposeNodeStatements

/-! ## Goldilocks Persist (a milestone PR appends here only) -/

/-! ## Goldilocks Service (a milestone PR appends here only) -/

/-! ## Goldilocks Healing (a milestone PR appends here only) -/

/-! ## Goldilocks Regimes (a milestone PR appends here only) -/

/-! ## Goldilocks Refinement (a milestone PR appends here only) -/

/-! ## Goldilocks (values and sheet) -/

example := ``Consensus.Shape.goldilocksSchema
example := ``Consensus.Shape.goldilocksGrid
example := ``Consensus.Shape.goldilocksSkeleton
example := ``Consensus.Shape.FGSAParams
example := ``Consensus.Shape.GoldilocksBindings
example := ``Consensus.Shape.GoldilocksTarget
example := ``Consensus.EnvPoint.two_mul_card_faulty_union_lt
example := ``Consensus.Shape.GoldilocksExtraAt
example := ``Consensus.Shape.GoldilocksExtraAt.crossNest
example := ``Consensus.Shape.GoldilocksExtraAt.finalFirst
example := ``Consensus.Shape.GoldilocksExtraAt.finalRecur
example := ``Consensus.Shape.GoldilocksExtraAt.growHealed
example := ``Consensus.Shape.GoldilocksExtraAt.growSleepy
example := ``Consensus.Shape.GoldilocksExtraAt.includeHealed
example := ``Consensus.Shape.GoldilocksExtraAt.includeSleepy
example := ``Consensus.Shape.GoldilocksExtraAt.liveDC
example := ``Consensus.Shape.GoldilocksExtraAt.outageWindow
example := ``Consensus.Shape.GoldilocksExtraAt.weakCrossNest
example := ``Consensus.Shape.GoldilocksExtraAt.weakGrow
example := ``Consensus.Shape.GoldilocksExtraAt.weakInclude
example := ``Consensus.Shape.GoldilocksExtraAt.weakSafe
example := ``Consensus.Shape.GoldilocksTarget.confirmed_persists
example := ``Consensus.Shape.GoldilocksTarget.confirmed_safe_healed
example := ``Consensus.Shape.GoldilocksTarget.confirmed_safe_healed_prefix
example := ``Consensus.Shape.GoldilocksTarget.confirmed_safe_sleepy
example := ``Consensus.Shape.GoldilocksTarget.confirmed_safe_sleepy_prefix
example := ``Consensus.Shape.GoldilocksTarget.confirmed_txLive_healed
example := ``Consensus.Shape.GoldilocksTarget.confirmed_txLive_sleepy
example := ``Consensus.Shape.GoldilocksTarget.finalized_accountable
example := ``Consensus.Shape.GoldilocksTarget.finalized_monotone
example := ``Consensus.Shape.GoldilocksTarget.finalized_safe_below_third
example := ``Consensus.Shape.GoldilocksTarget.finalized_txLive
example := ``Consensus.Shape.GoldilocksTarget.goldilocks_good
example := ``Consensus.Shape.GoldilocksTarget.nested
example := ``Consensus.Shape.GoldilocksTarget.nonFraming
example := ``Consensus.Shape.GoldilocksTarget.outage_final_compatible
example := ``Consensus.Shape.budget_implies_V
example := ``Consensus.Shape.finRec_span
example := ``Consensus.Shape.finalCut
example := ``Consensus.Shape.finalRecur_delay_vs_window
example := ``Consensus.Shape.final_heal_covers_window
example := ``Consensus.Shape.final_latency_covers_window
example := ``Consensus.Shape.gHealFin_eq
example := ``Consensus.Shape.gHeal_eq
example := ``Consensus.Shape.gReady_eq
example := ``Consensus.Shape.gc_eq
example := ``Consensus.Shape.goldilocksContract
example := ``Consensus.Shape.goldilocks_admissible
example := ``Consensus.Shape.goldilocks_progressFits
example := ``Consensus.Shape.goldilocks_progressTolerant
example := ``Consensus.Shape.range_head
example := ``Consensus.Shape.reference_bounds

/-! ## Tests: Blocks -/

example := ``Consensus.Shape.Tests.Blocks.recurrence_has_teeth
example := ``Consensus.Shape.Tests.Blocks.span_guard

/-! ## Tests: Controls -/

example := ``Consensus.Shape.Tests.Controls.ctrlK_progressTolerant
example := ``Consensus.Shape.Tests.Controls.ctrl_realizable
example := ``Consensus.Shape.Tests.Controls.outage_control
example := ``Consensus.Shape.Tests.Controls.positive_controls

/-! ## Tests: Goldilocks -/

example := ``Consensus.Shape.Tests.Goldilocks.collapse_prefix_only
example := ``Consensus.Shape.Tests.Goldilocks.outageWindow_prefix_only
example := ``Consensus.Shape.Tests.Goldilocks.pp223_numbers
example := ``Consensus.Shape.Tests.Goldilocks.stable_is_confirmed
example := ``Consensus.Shape.Tests.Goldilocks.weakPremise_inhabited

/-! ## Tests: Good -/

example := ``Consensus.Shape.Tests.Good.briefPoint_faulty
example := ``Consensus.Shape.Tests.Good.briefPoint_readyAt
example := ``Consensus.Shape.Tests.Good.censoring_progress_rejected
example := ``Consensus.Shape.Tests.Good.empty_valid_not_adequate
example := ``Consensus.Shape.Tests.Good.empty_valid_not_good
example := ``Consensus.Shape.Tests.Good.eta_sleepy_counts_brief
example := ``Consensus.Shape.Tests.Good.eta_sleepy_history_sensitive
example := ``Consensus.Shape.Tests.Good.eta_sleepy_startup
example := ``Consensus.Shape.Tests.Good.excuse_true_not_good
example := ``Consensus.Shape.Tests.Good.false_progress_not_good
example := ``Consensus.Shape.Tests.Good.healthy_rotating_sleeper
example := ``Consensus.Shape.Tests.Good.no_admissible_not_adequate
example := ``Consensus.Shape.Tests.Good.no_admissible_not_good
example := ``Consensus.Shape.Tests.Good.prefixPoint_faulty
example := ``Consensus.Shape.Tests.Good.prefixPoint_readyAt
example := ``Consensus.Shape.Tests.Good.prefix_sync_then_async
example := ``Consensus.Shape.Tests.Good.rotPoint_awake_card
example := ``Consensus.Shape.Tests.Good.rotPoint_faulty
example := ``Consensus.Shape.Tests.Good.stable_alias_final_sleepy_live
example := ``Consensus.Shape.Tests.Good.startPoint_awakeIn
example := ``Consensus.Shape.Tests.Good.startPoint_faulty
example := ``Consensus.Shape.Tests.Good.startPoint_readyAt

/-! ## Tests: Leaks -/

example := ``Consensus.Shape.Tests.Leaks.conflictsTrue_silent
example := ``Consensus.Shape.Tests.Leaks.env_ready
example := ``Consensus.Shape.Tests.Leaks.fabricated
example := ``Consensus.Shape.Tests.Leaks.familyC_mono
example := ``Consensus.Shape.Tests.Leaks.familyC_state
example := ``Consensus.Shape.Tests.Leaks.goodHash_injective
example := ``Consensus.Shape.Tests.Leaks.proposeButGenesis
example := ``Consensus.Shape.Tests.Leaks.recorder_live
example := ``Consensus.Shape.Tests.Leaks.recorder_live_testK
example := ``Consensus.Shape.Tests.Leaks.recorder_live_testK_healed
example := ``Consensus.Shape.Tests.Leaks.refuted_of_empty
example := ``Consensus.Shape.Tests.Leaks.releaseAll_mono
example := ``Consensus.Shape.Tests.Leaks.releaseAll_record
example := ``Consensus.Shape.Tests.Leaks.releaseAll_state
example := ``Consensus.Shape.Tests.Leaks.schema_daCore
example := ``Consensus.Shape.Tests.Leaks.silent
example := ``Consensus.Shape.Tests.Leaks.testK_progressTolerant
example := ``Consensus.Shape.Tests.Leaks.testSel_admits

/-! ## Tests: Model -/

example := ``Consensus.Shape.Tests.Model.conflictsTrue_releases_unsigned_only
example := ``Consensus.Shape.Tests.Model.forged_role_invalid
example := ``Consensus.Shape.Tests.Model.held_at_deadline
example := ``Consensus.Shape.Tests.Model.not_held_before_relay
example := ``Consensus.Shape.Tests.Model.unit_ticks

/-! ## Tests: Network -/

example := ``Consensus.Shape.Tests.Network.agreesUpTo_empty_messages
example := ``Consensus.Shape.Tests.Network.waker_within_bound
example := ``Consensus.Shape.Tests.Network.waker_within_bound_silent
example := ``Consensus.Shape.Tests.Network.waker_not_instant
example := ``Consensus.Shape.Tests.Network.faithful_receipt
example := ``Consensus.Shape.Tests.Network.faithful_relayedRun
example := ``Consensus.Shape.Tests.Network.held0
example := ``Consensus.Shape.Tests.Network.held1
example := ``Consensus.Shape.Tests.Network.held_all
example := ``Consensus.Shape.Tests.Network.held_restart
example := ``Consensus.Shape.Tests.Network.negative_send_covered
example := ``Consensus.Shape.Tests.Network.receipt_at_deadline
example := ``Consensus.Shape.Tests.Network.silent_not_psync
example := ``Consensus.Shape.Tests.Network.silent_run_valid
example := ``Consensus.Shape.Tests.Network.tickedRun_valid
example := ``Consensus.Shape.Tests.Network.truncate_relayedRun

/-! ## Tests: Problem -/

example := ``Consensus.Shape.Tests.Problem.finalized_stable_not_nested
example := ``Consensus.Shape.Tests.Problem.inCuts_zero
example := ``Consensus.Shape.Tests.Problem.incompatible_laws
example := ``Consensus.Shape.Tests.Problem.incompatible_not_agree
example := ``Consensus.Shape.Tests.Problem.init_rollback_not_monotone
example := ``Consensus.Shape.Tests.Problem.local_accountability_teeth
example := ``Consensus.Shape.Tests.Problem.omitted_laws
example := ``Consensus.Shape.Tests.Problem.omitted_not_txLive
example := ``Consensus.Shape.Tests.Problem.oneSource_submitted
example := ``Consensus.Shape.Tests.Problem.other_node_no_submission
example := ``Consensus.Shape.Tests.Problem.rollback_laws
example := ``Consensus.Shape.Tests.Problem.rollback_not_monotone
example := ``Consensus.Shape.Tests.Problem.shortHistory_not_awake_delta
example := ``Consensus.Shape.Tests.Problem.shortHistory_ready
example := ``Consensus.Shape.Tests.Problem.sleeping_source_not_submitted
example := ``Consensus.Shape.Tests.Problem.stable_confirmed_nested

/-! ## Tests: Realizable -/

example := ``Consensus.Shape.Tests.Realizable.allProposers_no_witness
example := ``Consensus.Shape.Tests.Realizable.coverage_keeps_selection
example := ``Consensus.Shape.Tests.Realizable.healed_witness_late
example := ``Consensus.Shape.Tests.Realizable.healed_witness_late_control
example := ``Consensus.Shape.Tests.Realizable.outage_witness_late
example := ``Consensus.Shape.Tests.Realizable.outage_witness_late_control
example := ``Consensus.Shape.Tests.Realizable.rotating_notReadyOn_false
example := ``Consensus.Shape.Tests.Realizable.rotating_notReadyOn_trivial
example := ``Consensus.Shape.Tests.Realizable.rotating_proposalLive_vacuous
example := ``Consensus.Shape.Tests.Realizable.tendermint_largeIdx_prog

/-! ## Tests: Regimes -/

example := ``Consensus.Shape.Tests.Regimes.faulty_third_not_healthy
example := ``Consensus.Shape.Tests.Regimes.healthy_needs_full_participation
example := ``Consensus.Shape.Tests.Regimes.healthy_wake_at_gst
example := ``Consensus.Shape.Tests.Regimes.logA_held
example := ``Consensus.Shape.Tests.Regimes.outage_async_log
example := ``Consensus.Shape.Tests.Regimes.outage_times_teeth
example := ``Consensus.Shape.Tests.Regimes.psync_lost_message
example := ``Consensus.Shape.Tests.Regimes.ptL_no_wake
example := ``Consensus.Shape.Tests.Regimes.ptS_faulty
example := ``Consensus.Shape.Tests.Regimes.ptS_readyAbove
example := ``Consensus.Shape.Tests.Regimes.ptS_readyAt
example := ``Consensus.Shape.Tests.Regimes.silentLog_delivers
example := ``Consensus.Shape.Tests.Regimes.sleepy_with_sleeper

/-! ## Tests: Shapes -/

example := ``Consensus.Shape.Tests.Shapes.poll_disabled_forged
example := ``Consensus.Shape.Tests.Shapes.poll_duty_every_tick
example := ``Consensus.Shape.Tests.Shapes.poll_proposal_local_height

/-! ## Tests: Vacuity -/

example := ``Consensus.Shape.Tests.Vacuity.admissibility_rejections
example := ``Consensus.Shape.Tests.Vacuity.allProposers_unfit
example := ``Consensus.Shape.Tests.Vacuity.credential_forgery_excluded
example := ``Consensus.Shape.Tests.Vacuity.forgedProposal_invalid
example := ``Consensus.Shape.Tests.Vacuity.noProgressFit_contract
example := ``Consensus.Shape.Tests.Vacuity.noService_not_accepted
example := ``Consensus.Shape.Tests.Vacuity.notReadyAtMost_fits
example := ``Consensus.Shape.Tests.Vacuity.recur_noSlack_not_tolerant
example := ``Consensus.Shape.Tests.Vacuity.recur_single_one_not_tolerant
example := ``Consensus.Shape.Tests.Vacuity.recur_single_one_bad_slots
example := ``Consensus.Shape.Tests.Vacuity.notReadyAtMost_one_not_realizable
example := ``Consensus.Shape.Tests.Vacuity.notReadyAtMost_below_not_realizable
example := ``Consensus.Shape.Tests.Vacuity.notReadyAtMost_one_not_tolerant
example := ``Consensus.Shape.Tests.Vacuity.reject_alpha
example := ``Consensus.Shape.Tests.Vacuity.reject_alpha_any
example := ``Consensus.Shape.Tests.Vacuity.reject_budget
example := ``Consensus.Shape.Tests.Vacuity.reject_catchUp
example := ``Consensus.Shape.Tests.Vacuity.reject_cover
example := ``Consensus.Shape.Tests.Vacuity.reject_beta
example := ``Consensus.Shape.Tests.Vacuity.reject_theta
example := ``Consensus.Shape.Tests.Vacuity.standard_admissible
