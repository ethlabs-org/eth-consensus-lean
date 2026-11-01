module
public import AvailableChainPCSAClaims.Claims.PC
public import AvailableChainPCSAClaims.Claims.Clean
public import AvailableChainPCSAClaims.Claims.Outage
public import AvailableChainPCSAClaims.Claims.Recovery
public import AvailableChainPCSAClaims.Claims.Finality
public import AvailableChainPCSAClaims.Claims.StageTwo
public import AvailableChainPCSAClaims.Claims.AcFrame

@[expose] public section

/-! [PC-SA claims, W0; pcsa-proof-plan §1, §3] The exported PC-SA claim
records. `PCSAClaims` is the stage-1 milestone: the PC path (C1–C5,
`PCSAPCClaims`) and the Clean, Outage, Recovery and Finality lanes (C6–C14).
`PCSAStageTwoClaims` holds the stage-2 shapes (C15); it is never mixed into
the stage-1 record. This module imports Claims modules only (FG-SA
FGSAClaims.lean shape).

Protocol instances: the stage-1 claims quantify over the FG mode
`m` (`pcsaWith m p c`) and take `StageOneFrame` as their only frame premise.
The AC-only instance is `m = .idle` (`pcsaAC`), where `AcOnlyFrameClaim`
discharges `StageOneFrame`. The stage-2 claims are over `pcsa p c`
(`m = .on`). -/

namespace AvailableChain.PCSA.Run

/-- [PC-SA claims, W0; plan §1 record] The stage-1 claims of PC-SA, for every
FG mode, and the frame claim of the AC-only instance. -/
structure PCSAClaims (p : Params) : Prop extends PCSAPCClaims p where
  -- AC-only frame (r4.3 5.0 stage 1; the `StageOneFrame` producer for `pcsaAC`)
  acOnlyFrame : AcOnlyFrameClaim p
  -- Clean lane (C6, C7, C9, C14; r4.3 5.2, 5.3)
  snapshotStamp : PCSnapshotStampClaim p
  cleanInvariant : CleanInvariantClaim p
  formation : FormationClaim p
  cleanDissemination : CleanDisseminationClaim p
  cleanSafety : PCSACleanSafetyClaim p
  cleanInclusion : PCSACleanInclusionClaim p
  strongIncluded : StrongIncludedClaim p
  -- Outage lane (C8, C10; r4.3 5.4, 5.5)
  armPersistence : ArmPersistenceClaim p
  armHealthy : ArmHealthyClaim p
  slowP1 : PCSASlowP1Claim p
  -- Recovery lane (C11; r4.3 5.6.1, 5.6.3 under the L*′ lock rule of the model)
  fastRecovered : FastRecoveredClaim p
  longBreakRecovered : LongBreakRecoveredClaim p
  -- Finality lane (C12, C13; r4.3 5.7, 5.8)
  formationSource : FormationSourceClaim p
  cleanSourceTransfer : CleanSourceTransferClaim p
  healedSourceTransfer : HealedSourceTransferClaim p
  q0PCSelection : Q0PCSelectionClaim p
  q0PC : Q0PCClaim p
  finality : PCSAFinalitySafetyClaims p

/-- [PC-SA claims, W0; plan C15] The stage-2 shapes (no proof in M1). -/
structure PCSAStageTwoClaims (p : Params) : Prop where
  armPersistence : ArmPersistenceJStableClaim p
  armHealthy : ArmHealthyStageTwoClaim p
  strongIncluded : StrongIncludedStageTwoClaim p

end AvailableChain.PCSA.Run

end
