module
public import AvailableChainFGSAClaims.Claims.Foundations
public import AvailableChainFGSAClaims.Claims.Shared
public import AvailableChainFGSAClaims.Claims.Clean
public import AvailableChainFGSAClaims.Claims.Outage
public import AvailableChainFGSAClaims.Claims.Finality
public import AvailableChainFGSAClaims.Claims.WeakContinuation
public import AvailableChainFGSAClaims.Claims.FrameNext

@[expose] public section

/-! P3 §4.8: the exported safety claims. Only the Claims root and the exact
Proofs.Assembly.Root import this module (SYN L58).
G-F0b: FGSAClaims and FGSAFinalityClaims collect the exported claims (G-F0a safety, finality
safety, Clean and GST outputs; DC Consensus shape). Healing, H-time, local kernel and local
FF5–FF7 forms stay Claims-module interfaces.
The zero and positive Clean lane Props are not exported claims. The receipt
and suffix-walk rows cite their existing statements in their claim homes. -/

namespace AvailableChain.FGSA.Run

/-- The complete exported safety-claim aggregate, frozen at G-F0a. -/
structure FGSASafetyClaims (p : FGSA.Params) : Prop where
  carrier : CarrierClaim p
  chainCertificates : ChainCertificatesClaim p
  store : StoreClaim p
  activeView : ActiveViewClaim p
  leaseOrigins : LeaseOriginsClaim p
  reconcile : ReconcileClaim p
  outputNesting : OutputNestingClaim p
  frame : FrameClaimNext p
  clientSafety : ClientSafetyClaim p
  clientSafetyBase : ClientSafetyBaseClaim p
  sourceDisciplineBase : SourceDisciplineBaseClaim p
  sourceDiscipline : SourceDisciplineClaim p
  sameLabel : SameLabelClaim p
  releaseStore : ReleaseStoreClaim p
  release : ReleaseClaim p
  headReachesLo : HeadReachesLoClaim p
  cleanCut : CleanCutClaim p
  cleanHistory : CleanHistoryClaim p
  cleanPrefixTruncation : CleanPrefixTruncationClaim p
  cleanSafety : CleanSafetyClaim p

/-- The complete safety interface aggregate (L48, IF1), frozen whole at G-F0a (R5-64). -/
structure FGSASafetyInterfaces (p : FGSA.Params) : Prop where
  -- consumer: F2 positive Clean, Assembly/Clean; producer: F1.1–F1.5 (P3 :7820–7836)
  -- strat is filled by the same RStrat producer as timingContract.certLag.
  fgFoundation : FGFoundationClaimNext p
  -- consumer: F2/F3/F4/F5 lane proofs, Assembly/<Claim>; producer: F1.5 (P3 :7858–7870)
  srcFrameAbove : SrcFrameAboveClaim p
  -- consumer: Clean (F2), inclusion/proposal/suffix/gate;
  -- producer: F2.2 (Shared/Channels) (P3 :7311–7330)
  cpPrefix : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
    SourceDisciplinePrem p c E rho pt → CPPrefix p c E rho
  -- consumer: P1 (F3); producer: F2.2 (Shared/Channels) (P3 :7331–7341)
  cpCompat : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
    SourceDisciplinePrem p c E rho pt → CPCompat p c E rho
  -- consumer: 02 §5.4, 03 §8, 21 H.11, 22 kernel; producer: F1.5 (a) (P3 :7423–7438)
  -- Same Prop as SourceDisciplineBaseAt's first conjunct.
  tSrc : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
    BasePrem p c E rho pt → TSrc p c E rho
  -- consumer: TimingContract.label, BelowLabel; producer: F1.5 (d) (P3 :7439–7444)
  -- Same Prop as SourceDisciplineBaseAt's second conjunct.
  labelBound : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
    BasePrem p c E rho pt → LabelBound p c E rho
  -- consumer: every AG instance; producer: F1 (F1.5 (b–d) + the T7.5/clock facts
  -- for atomic/tickFG) (P3 :7203–7229; IF1)
  -- certLag and fgFoundation.strat are the same Prop RStrat;
  -- both are filled by the ONE RStrat producer lemma (F1.5); no second proof.
  timingContract : ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
    SourceDisciplinePrem p c E rho pt → TimingContract p c E rho

/-- The finality safety output claims for G-F0b. -/
structure FGSAFinalityClaims (p : FGSA.Params) : Prop where
  accountable : PureAccountableClaim p
  agreement : PureAgreementClaim p
  runAccountable : WholeRunAccountableClaim p
  runAgreement : WholeRunAgreementClaim p
  eventPrefixAgreement : EventPrefixAgreementClaim p
  faultCountSlashableBound : FaultCountSlashableBoundClaim p
  finalizedMonotone : FinalizedMonotonicityRestartClaim p
  honestNeverSlashed : HonestNeverSlashedClaim p

/-- The G-F0b output contract. Recovery is a premise; healing witnesses are outputs.
The local healing and finality lane interfaces stay in their Claims modules. -/
structure FGSAClaims (p : FGSA.Params) : Prop extends FGSASafetyClaims p where
  finality : FGSAFinalityClaims p
  finalizedSafety : FinalizedSafetyClaim p
  finalLock : FinalLockClaim p
  outageCompat : OutageCompatClaim p
  fastP1 : FastP1Claim p
  slowP1 : SlowP1Claim p
  exactProposal : ExactProposalClaim p
  cleanInclusionPostGate : CleanInclusionPostGateClaim p
  cleanInclusion : CleanInclusionClaim p
  firstFinalityRecFE : FirstFinalityRecFEClaim_W p
  firstFinalityRecF4 : FirstFinalityRecF4Claim_W p
  finalityLivenessGSTRecFE : FinalityLivenessGSTClaim_W p .recFE
  finalityLivenessGSTRecF4 : FinalityLivenessGSTClaim_W p .recF4
  proposalFinalGSTRecFE : ProposalFinalGSTClaim_W p .recFE
  proposalFinalGSTRecF4 : ProposalFinalGSTClaim_W p .recF4
  aboveFrontierGSTRecFE : AboveFrontierGSTClaim_W p .recFE
  aboveFrontierGSTRecF4 : AboveFrontierGSTClaim_W p .recF4
  availableGST : AvailableGSTClaim p
  availableGrowthGST : AvailableGrowthGSTClaim p
  cleanGrowth : CleanGrowthClaim p
  /-- WC plan §8 Job 4 and r2.1; DC one source cut for weak safety and liveness. -/
  weakContinuationLive : ∀ G : Time, WeakContinuationLiveClaim p G

end AvailableChain.FGSA.Run
end
