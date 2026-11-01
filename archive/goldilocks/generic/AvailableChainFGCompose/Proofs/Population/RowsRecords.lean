module
public import AvailableChainFGCompose.Statements.Population.FinalityKernel
public import AvailableChainFGCompose.Proofs.Population.HolderBaseRowsRecords

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable {R : FGCoreReads P n Base Proposal Wire} {S : FGSafetyReads P n Wire}
variable {O : FGObservationReads R} {T : FGTiming}
variable {E : Generic.Env V} {rho : V2.D.Run V P} {I : V2.D.Interface P}
variable {D : FGHistoryWireReads S} {Ef : Electorate (Fin n)}

variable {decodeProposal : P.Object → Option (Slot × Body)}
variable {bodyErase : Body → Block} {bodyRows : Body → List Wire}
variable {blockWireRows : P.State → List Wire}
variable {parentFG : P.State → Block → Option (FGBlock (Fin n))}
variable {parentHeight : P.State → Slot → FGBlock (Fin n) → Height × BlockId}
variable {validFor : P.State → Slot → FGBlock (Fin n) → Wire → Bool}
variable {makeFG : FGBlock (Fin n) → Block → List Wire → FGBlock (Fin n)}
variable {valid : Wire → Bool} {ac : FGACServiceReads V}
variable {cfg : FGConfig} {K : Nat} {ΔF : Time} {sp : FGServicePoint} {pt : KernelPt} {A : Block}
variable (m : KernelMiddleWitnessFG_W R S O T E rho I D Ef decodeProposal bodyErase bodyRows
  blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A)

/-- The published record producer supplies all seven guards at the same middle action. -/
theorem rowsPrem_action_record_holder
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
  intro x nd hx hnd
  have result := high_record_guards_and_fresh_at_action hh cert reflect hqc head client
    emission own names L hs x (pt.r + 1) m.B hx (m.sourceB x hx)
    (m.d + 1) m.heightB (by have high := m.highA; omega) (pt.r + 2) x hx
    (fun j r a h hr ha ht => by
      simpa only [Nat.add_assoc] using
        rowsPrem_earlier_height_core L (pt.r + 2) (m.d + 2) m.noSecondHeight j x r a h hr ha ht)
    nd hnd
  simpa only [m.entryB, Nat.add_assoc] using result

end AvailableChain.FGCompose
end
