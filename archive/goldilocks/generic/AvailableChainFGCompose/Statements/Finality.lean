module
public import AvailableChainFGCompose.Statements.Service -- shake: keep (re-export)
public import AvailableChainFGCompose.Statements.Bounds
public import AvailableChainGeneric.Statements.Pure.ScheduleW

@[expose] public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In}
variable [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire)
variable (S : FGSafetyReads P n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V P)
variable (O : FGObservationReads R) (T : FGTiming) (I : V2.D.Interface P)
variable (entry : Wire → Option (Height × BlockId))
variable (carrier : P.Object → Slot → Block → List Wire → Prop)
variable (chainWireRows : P.State → Block → List Wire)
variable (blockWireRows : P.State → List Wire)
variable (parentFG : P.State → Block → Option (FGBlock (Fin n)))
variable (validFor : P.State → Slot → (FGBlock (Fin n)) → Wire → Bool)

structure KernelPt where
  r : Nat

structure KernelPrem_W (T : FGTiming) (deltaF horizon : Time)
    (sp : FGServicePoint) (pt : KernelPt) (honestSlot : Slot → Prop)
    (fgQuorum fgHonestWeight timeoutSlots capacity : Nat) : Prop where
  bound : LivenessBoundW T deltaF
  window : Gen.Pure.FGoodE_W honestSlot T.roundSlots (kappaF T deltaF) pt.r
  start : sp.serviceStart ≤ (pt.r : Time) * FGCompose.P T
  hhor : kernelDeadlineW T deltaF (pt.r + 2) ≤ horizon
  honest_quorum : fgQuorum ≤ fgHonestWeight
  timeout_eq : timeoutSlots = 2 * T.roundSlots
  capacity_ge : 2 ≤ capacity

-- The c1 carrier read and these exact full-content reads are explicit parameters.
-- decodeProposal : P.Object → Option (Slot × Body)
-- bodyErase : Body → Block; bodyRows : Body → List Wire
-- makeFG : (FGBlock (Fin n)) → Block → List Wire → (FGBlock (Fin n))
-- parentFG : P.State → Block → Option (FGBlock (Fin n))
-- I is the actual proposer interface.
def OpeningCarrier_W {Body : Type}
    (decodeProposal : P.Object → Option (Slot × Body))
    (bodyErase : Body → Block) (bodyRows : Body → List Wire)
    (parentFG : P.State → Block → Option (FGBlock (Fin n)))
    (makeFG : (FGBlock (Fin n)) → Block → List Wire → (FGBlock (Fin n)))
    (E : Generic.Env V) (rho : V2.D.Run V P) (I : V2.D.Interface P)
    (s : Slot) (A : Block) (Afg : (FGBlock (Fin n))) : Prop :=
  ∃ o N nd Par,
    V2.D.Run.emits E rho (V2.D.proposerOf rho I s) o (V2.D.proposalTime I s) ∧
    bodyErase N = A ∧ decodeProposal o = some (s, N) ∧
    proposalStateAt E rho I s = some nd ∧ parentFG nd A = some Par ∧
    makeFG Par A (bodyRows N) = Afg

def AcceptsFinalBefore (x : V) (X : (FGBlock (Fin n))) (d : Time) : Prop :=
  Gen.V2.Duty.HoldsBefore E rho (fun nd => FGBlock.Preceq X (R.core nd).fg.F) d x

def KernelConclusion_W {Body : Type}
    (decodeProposal : P.Object → Option (Slot × Body))
    (bodyErase : Body → Block) (bodyRows : Body → List Wire)
    (parentFG : P.State → Block → Option (FGBlock (Fin n)))
    (makeFG : (FGBlock (Fin n)) → Block → List Wire → (FGBlock (Fin n)))
    (deltaF : Time) (r : Nat) : Prop := ∀ A,
  HonestProposal E rho I (r * T.roundSlots) A →
  ∃ Afg : (FGBlock (Fin n)), R.erase Afg = A ∧
    OpeningCarrier_W decodeProposal bodyErase bodyRows parentFG makeFG E rho I
      (r * T.roundSlots) A Afg ∧
    (∀ x ∈ rho.honest, Afg ∈ (R.core (V2.D.Run.stateBefore E rho rho.events.length x)).fg.TF) ∧
    ∃ U : (FGBlock (Fin n)), FGBlock.Preceq Afg U ∧ Afg ≠ U ∧
      (O.height U).h = (O.height Afg).h + 1 ∧
      ∀ x ∈ rho.honest,
        AcceptsFinalBefore R E rho x U (kernelDeadlineW T deltaF (r + 2))

/-! P0d7b-b: exporter statements. The joined premise names one service point; the forward
witness and the local conclusion keep the kernel's opening and fresh extension. -/

/-- The local finality window: g + 2 periods, the carrier offset and one delay. -/
def W_W (T : FGTiming) (deltaF : Time) (g : Nat) : Time :=
  ((g : Time) + 2) * FGCompose.P T + betaF T deltaF + T.delta

/-- The W recurrence of good windows from an explicit recurrence start. -/
def FE_W (T : FGTiming) (deltaF : Time) (honestSlot : Slot → Prop)
    (start horizon : Time) (g : Nat) : Prop :=
  Gen.Pure.RecFE_W honestSlot T.roundSlots (kappaF T deltaF) (FGCompose.P T) T.delta
    (betaF T deltaF) start horizon g

/-- The joined kernel premise: one service point supplies the service facts and the start.
The independent FG quorum, the timeout and the capacity stay explicit. -/
structure KernelJoinedPrem (T : FGTiming) (deltaF horizon : Time) (r : Nat)
    (honestSlot : Slot → Prop) (fgQuorum fgHonestWeight timeoutSlots capacity : Nat)
    (Service : FGServicePoint → Prop) : Prop where
  bound : LivenessBoundW T deltaF
  window : Gen.Pure.FGoodE_W honestSlot T.roundSlots (kappaF T deltaF) r
  start : ∃ sp, Service sp ∧ sp.serviceStart ≤ (r : Time) * FGCompose.P T
  hhor : kernelDeadlineW T deltaF (r + 2) ≤ horizon
  honest_quorum : fgQuorum ≤ fgHonestWeight
  timeout_eq : timeoutSlots = 2 * T.roundSlots
  capacity_ge : 2 ≤ capacity

/-- The forward witness: an aligned round in the window, its honest opening, the same
carrier and fresh extension as the kernel, and strict acceptance before the deadline. -/
def ForwardWitness_W {Body : Type}
    (decodeProposal : P.Object → Option (Slot × Body))
    (bodyErase : Body → Block) (bodyRows : Body → List Wire)
    (parentFG : P.State → Block → Option (FGBlock (Fin n)))
    (makeFG : (FGBlock (Fin n)) → Block → List Wire → (FGBlock (Fin n)))
    (honestSlot : Slot → Prop) (deltaF : Time) (g : Nat) (sp : FGServicePoint)
    (t : Time) : Prop :=
  ∃ (q r : Nat) (A : Block) (Afg U : FGBlock (Fin n)) (d : Nat) (D : Time),
    t ≤ (q : Time) * FGCompose.P T ∧ (q : Time) * FGCompose.P T < t + FGCompose.P T ∧
    Gen.Pure.InWindow q g r ∧
    Gen.Pure.FGoodE_W honestSlot T.roundSlots (kappaF T deltaF) r ∧
    t ≤ (r : Time) * FGCompose.P T ∧ HonestProposal E rho I (r * T.roundSlots) A ∧
    R.erase Afg = A ∧
    OpeningCarrier_W decodeProposal bodyErase bodyRows parentFG makeFG E rho I
      (r * T.roundSlots) A Afg ∧
    (O.height Afg).h = d ∧ sp.reset.M + 1 ≤ d ∧
    FGBlock.Preceq Afg U ∧ Afg ≠ U ∧ (O.height U).h = d + 1 ∧
    D = kernelDeadlineW T deltaF (r + 2) ∧ D < t + W_W T deltaF g ∧ D ≤ rho.horizon ∧
    ∀ x ∈ rho.honest, AcceptsFinalBefore R E rho x U D

/-- Local finality liveness at time t: one block strictly above the supplied output read
and above every stored finality certificate, accepted strictly before d. -/
def FinalityLivenessConcl_W (output : P.State → Block) (t d : Time) : Prop :=
  ∃ U : FGBlock (Fin n),
    (∀ x ∈ rho.honest, Block.Prec (output (V2.D.Run.readAt E rho t x)) (R.erase U)) ∧
    (∀ x ∈ rho.honest, ∀ K ∈ (R.core (V2.D.Run.readAt E rho t x)).fg.TF,
      (O.finality K).F = (R.core (V2.D.Run.readAt E rho t x)).fg.F →
      (O.finality K).h_F < (O.height U).h) ∧
    ∀ x ∈ rho.honest, AcceptsFinalBefore R E rho x U d

end AvailableChain.FGCompose
end
