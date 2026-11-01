module
public import AvailableChainFGCompose.Proofs.Finality.Middle -- shake: keep (kernel middle API)
public import AvailableChainFGCompose.Proofs.Finality.RecordInv -- shake: keep (client record laws)

public import AvailableChainFGCompose.Proofs.Population.RowsRecords

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable {R : FGCoreReads P n Base Proposal Wire} {S : FGSafetyReads P n Wire}
variable {O : FGObservationReads R} {T : FGTiming}
variable {E : Generic.Env V} {rho : V2.D.Run V P} {I : V2.D.Interface P}
variable {D : FGHistoryWireReads S} {Ef : Electorate (Fin n)}

/-- Event times at the exact action rounds imply the earlier-row height cap. -/
theorem rowsPrem_earlier_height (L : FGTimingLaws T) (q y : Nat)
    (hcut : ∀ j x r a h t, HonestRowAt S E rho T j x r a →
      historyRowHeight S D a = some h → y ≤ h → eventTime rho j = some t →
      T.action q ≤ t) :
    ∀ j x r a h, r < q → HonestRowAt S E rho T j x r a →
      historyRowHeight S D a = some h → h < y := by
  exact rowsPrem_earlier_height_core L q y hcut

variable {decodeProposal : P.Object → Option (Slot × Body)}
variable {bodyErase : Body → Block} {bodyRows : Body → List Wire}
variable {blockWireRows : P.State → List Wire}
variable {parentFG : P.State → Block → Option (FGBlock (Fin n))}
variable {parentHeight : P.State → Slot → FGBlock (Fin n) → Height × BlockId}
variable {validFor : P.State → Slot → FGBlock (Fin n) → Wire → Bool}
variable {makeFG : FGBlock (Fin n) → Block → List Wire → FGBlock (Fin n)}
variable {valid : Wire → Bool} {ac : FGACServiceReads V}
variable {cfg : FGConfig} {K : Nat} {ΔF : Time} {sp : FGServicePoint} {pt : KernelPt} {A : Block}
variable (m : KernelMiddleWitness_W R S O T E rho I D Ef decodeProposal bodyErase bodyRows
  blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A)

private def popc_record_middle_holder :
    KernelMiddleWitnessFG_W R S O T E rho I D Ef decodeProposal bodyErase bodyRows
      blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A := {
    A₀ := m.A₀
    B := m.B
    U := m.U
    X_D := m.X_D
    cD := m.cD
    d := m.d
    opening := m.opening
    eraseA := m.eraseA
    carrierA := m.carrierA
    carrierB := m.carrierB
    carrierD := m.carrierD
    honestB := m.honestB
    honestD := m.honestD
    slotA := m.slotA
    slotB := m.slotB
    slotD := m.slotD
    earlySlot := m.earlySlot
    heightA := m.heightA
    highA := m.highA
    heightB := m.heightB
    entryB := m.entryB
    freshEntry := m.freshEntry
    strictAU := m.strictAU
    pathUB := m.pathUB
    freshSlot := m.freshSlot
    parentAB := m.parentAB
    parentBD := m.parentBD
    sourceA := m.sourceA
    sourceB := m.sourceB
    serviceD := m.serviceD
    heightD := m.heightD
    justifiedD := m.justifiedD
    justifiedHeightD := m.justifiedHeightD
    pendingD := m.pendingD
    retainedD := m.retainedD
    noFirstHeight := m.noFirstHeight
    noSecondHeight := m.noSecondHeight
    noEarlyFinality := m.noEarlyFinality
    chainA := m.chainA
    chainB := m.chainB
    chainD := m.chainD
    freshD := m.freshD
    noMixedD := m.noMixedD
    batchB := m.batchB
    batchD := m.batchD
    targetsB := fun _ hi => m.targetsB _ hi
    actionsInRun := m.actionsInRun
    capThroughBAction := m.capThroughBAction
    capThroughFinalAction := m.capThroughFinalAction
    finalityThroughFinalAction := m.finalityThroughFinalAction
    heldDAtFinalAction := m.heldDAtFinalAction
    heldAAtEnd := m.heldAAtEnd
  }

/-- The published record producer supplies all seven guards at the same middle action. -/
theorem rowsPrem_action_record
    (hh : ∀ horizon, FGHistoricalHighChain R O T E rho sp horizon)
    (cert : FGCertificateLaws Ef O.height O.finality)
    (reflect : ∀ A B, Block.Preceq (R.erase A) (R.erase B) → FGBlock.Preceq A B)
    {storedCarrier : P.State → FGBlock (Fin n) → Wire → Prop}
    {SourceService : V → Nat → FGBlock (Fin n) → Prop}
    (hqc : RQCOrigin R S E rho O T storedCarrier SourceService Ef)
    (head : HighRecordHead R S O E rho) (client : FGSafetyClientLaws S Ef cfg)
    (emission : HighRecordEmission S T E rho Ef cfg)
    (own : HighRecordOwnOrigin S T E rho) (names : HighRecordNames R S O T E rho D)
    (L : FGTimingLaws T) (hs : V2.D.ScheduleWellFormed E rho) :
    ∀ x nd, x ∈ rho.honest → postClock E rho x (T.action (pt.r + 2)) = some nd →
      HighRecordGuard_W (S.record nd) (m.d + 1) m.U ∧
        HighRecordFresh (m.d + 2) (S.record nd) := by
  exact rowsPrem_action_record_holder (popc_record_middle_holder m) hh cert reflect hqc head
    client emission own names L hs

end AvailableChain.FGCompose
end
