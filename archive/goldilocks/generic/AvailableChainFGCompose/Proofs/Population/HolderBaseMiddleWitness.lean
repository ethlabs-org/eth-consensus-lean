module
public import AvailableChainFGCompose.Proofs.Finality.MiddleSupport
public import AvailableChainFGCompose.Statements.Population.FinalityKernel

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
def kernel_middle_to_holder_core (m : KernelMiddleWitness_W R S O T E rho I D Ef
      decodeProposal bodyErase bodyRows
      blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A) :
    KernelMiddleWitnessFG_W R S O T E rho I D Ef
      decodeProposal bodyErase bodyRows
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

def kernel_middle_to_node_core (m : KernelMiddleWitnessFG_W R S O T E rho I D Ef
      decodeProposal bodyErase bodyRows
      blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A)
    (targets : ∀ x ∈ rho.honest, ∃ j a,
      HonestRowAt S E rho T j x (pt.r + 1) a ∧ RowComplete S rho D.signer valid x a ∧
      NamesEntry (pair := D.heightPair) .target a (m.d + 1) m.U) :
    KernelMiddleWitness_W R S O T E rho I D Ef
      decodeProposal bodyErase bodyRows
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
    targetsB := targets
    actionsInRun := m.actionsInRun
    capThroughBAction := m.capThroughBAction
    capThroughFinalAction := m.capThroughFinalAction
    finalityThroughFinalAction := m.finalityThroughFinalAction
    heldDAtFinalAction := m.heldDAtFinalAction
    heldAAtEnd := m.heldAAtEnd
  }

/-- Recover the all-node target field from the unchanged all-node row supplier. -/
theorem kernel_middle_targets_of_service_core
    (m : KernelMiddleWitnessFG_W R S O T E rho I D Ef
      decodeProposal bodyErase bodyRows
      blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A)
    (L : FGTimingLaws T)
    (cover : ∀ x ∈ rho.honest, ∀ r C,
      actionSourceFG R E rho T x r = some (some C) → sp.reset.M + 1 ≤ (O.height C).h →
      E.awake x (T.action r) = true →
      ∃ j rSent a, rSent ≤ r ∧ HonestRowAt S E rho T j x rSent a ∧
        RowComplete S rho D.signer valid x a ∧
        D.heightPair a = .vote (O.height C).h (O.height C).T_h.root false)
    (awake : ∀ x ∈ rho.honest, E.awake x (T.action (pt.r + 1)) = true) :
    ∀ x ∈ rho.honest, ∃ j a,
      HonestRowAt S E rho T j x (pt.r + 1) a ∧ RowComplete S rho D.signer valid x a ∧
      NamesEntry (pair := D.heightPair) .target a (m.d + 1) m.U := by
  intro x hx
  obtain ⟨j, rS, a, hle, ha, hc, hp⟩ := cover x hx (pt.r + 1) m.B (m.sourceB x hx)
    (by rw [m.heightB]; exact m.highA.trans (Nat.le_succ _)) (awake x hx)
  have hrS : rS = pt.r + 1 := by
    by_contra hne
    have hlt : rS < pt.r + 1 := lt_of_le_of_ne hle hne
    have hh : historyRowHeight S D a = some (m.d + 1) := by
      change (match D.heightPair a with | .empty => none | .vote h _ _ => some h) = _
      rw [hp, m.heightB]
    have hlate := m.noFirstHeight j x rS a _ _ ha hh le_rfl (kmid_event_time S T E rho ha)
    exact absurd ((kmid_action_strictMono T L).lt_iff_lt.mpr hlt) (not_lt.mpr hlate)
  subst hrS
  refine ⟨j, a, ha, hc, ?_⟩
  change D.heightPair a = .vote _ _ false
  rw [hp, m.heightB, m.entryB]

/-- The forward restriction preserves all selected blocks, slots, and heights. -/
theorem kernel_middle_to_holder_selected_core
    (m : KernelMiddleWitness_W R S O T E rho I D Ef decodeProposal bodyErase bodyRows
      blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A) :
    let h := kernel_middle_to_holder_core m
    h.A₀ = m.A₀ ∧ h.B = m.B ∧ h.U = m.U ∧ h.X_D = m.X_D ∧ h.cD = m.cD ∧ h.d = m.d := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The reconstructed node witness supplies the same selected holder action. -/
theorem kernel_middle_action_to_holder_core
    (m : KernelMiddleWitnessFG_W R S O T E rho I D Ef decodeProposal bodyErase bodyRows
      blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A)
    (targets : ∀ x ∈ rho.honest, ∃ j a,
      HonestRowAt S E rho T j x (pt.r + 1) a ∧ RowComplete S rho D.signer valid x a ∧
      NamesEntry (pair := D.heightPair) .target a (m.d + 1) m.U)
    (a : KernelActionSupply_W R S O T E rho I D Ef (kernel_middle_to_node_core m targets)) :
    KernelActionSupplyFG_W R S O T E rho I D Ef m := by
  exact ⟨a.read, a.service, a.head, a.walk⟩

end AvailableChain.FGCompose
end
