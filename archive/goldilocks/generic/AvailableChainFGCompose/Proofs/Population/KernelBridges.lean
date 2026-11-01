module
public import AvailableChainFGCompose.Statements.Population.FinalityKernel

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (O : FGObservationReads R) (T : FGTiming)
variable (E : Generic.Env V) (rho : V2.D.Run V P) (I : V2.D.Interface P)
variable (D : FGHistoryWireReads S) (Ef : Electorate (Fin n))

variable (decodeProposal : P.Object → Option (Slot × Body))
variable (bodyErase : Body → Block) (bodyRows : Body → List Wire)

variable (blockWireRows : P.State → List Wire)
variable (parentFG : P.State → Block → Option (FGBlock (Fin n)))
variable (parentHeight : P.State → Slot → FGBlock (Fin n) → Height × BlockId)
variable (validFor : P.State → Slot → FGBlock (Fin n) → Wire → Bool)

variable (makeFG : FGBlock (Fin n) → Block → List Wire → FGBlock (Fin n))
variable (valid : Wire → Bool) (ac : FGACServiceReads V)

variable (cfg : FGConfig) (K : Nat) (ΔF : Time) (sp : FGServicePoint) (pt : KernelPt)
variable (A : Block)

/-- Full holder coverage preserves every selected field of both middle records.
The reverse conversion uses the same rows, event indices and wire bytes. -/
theorem kernel_middle_holder_frozen_iff
    (e : Fin n ≃ V) (he : ∀ i, safetyHolder S rho i = e i) :
    (Nonempty (KernelMiddleWitness_W R S O T E rho I D Ef decodeProposal bodyErase bodyRows
      blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A) ↔
      Nonempty (KernelMiddleWitnessFG_W R S O T E rho I D Ef decodeProposal bodyErase bodyRows
      blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A)) ∧
    (∀ m : KernelMiddleWitness_W R S O T E rho I D Ef decodeProposal bodyErase bodyRows
      blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A,
      ∃ h : KernelMiddleWitnessFG_W R S O T E rho I D Ef decodeProposal bodyErase bodyRows
      blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A,
      m.A₀ = h.A₀ ∧ m.B = h.B ∧ m.U = h.U ∧
      m.X_D = h.X_D ∧ m.cD = h.cD ∧ m.d = h.d) ∧
    (∀ h : KernelMiddleWitnessFG_W R S O T E rho I D Ef decodeProposal bodyErase bodyRows
      blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A,
      ∃ m : KernelMiddleWitness_W R S O T E rho I D Ef decodeProposal bodyErase bodyRows
      blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A,
      m.A₀ = h.A₀ ∧ m.B = h.B ∧ m.U = h.U ∧
      m.X_D = h.X_D ∧ m.cD = h.cD ∧ m.d = h.d) := by
  let toHolder (m : KernelMiddleWitness_W R S O T E rho I D Ef decodeProposal bodyErase bodyRows
      blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A) :
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
    targetsB := fun i hi => m.targetsB _ hi
    actionsInRun := m.actionsInRun
    capThroughBAction := m.capThroughBAction
    capThroughFinalAction := m.capThroughFinalAction
    finalityThroughFinalAction := m.finalityThroughFinalAction
    heldDAtFinalAction := m.heldDAtFinalAction
    heldAAtEnd := m.heldAAtEnd
  }
  let toNode (h : KernelMiddleWitnessFG_W R S O T E rho I D Ef decodeProposal bodyErase bodyRows
      blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A) :
      KernelMiddleWitness_W R S O T E rho I D Ef decodeProposal bodyErase bodyRows
      blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A := {
    A₀ := h.A₀
    B := h.B
    U := h.U
    X_D := h.X_D
    cD := h.cD
    d := h.d
    opening := h.opening
    eraseA := h.eraseA
    carrierA := h.carrierA
    carrierB := h.carrierB
    carrierD := h.carrierD
    honestB := h.honestB
    honestD := h.honestD
    slotA := h.slotA
    slotB := h.slotB
    slotD := h.slotD
    earlySlot := h.earlySlot
    heightA := h.heightA
    highA := h.highA
    heightB := h.heightB
    entryB := h.entryB
    freshEntry := h.freshEntry
    strictAU := h.strictAU
    pathUB := h.pathUB
    freshSlot := h.freshSlot
    parentAB := h.parentAB
    parentBD := h.parentBD
    sourceA := h.sourceA
    sourceB := h.sourceB
    serviceD := h.serviceD
    heightD := h.heightD
    justifiedD := h.justifiedD
    justifiedHeightD := h.justifiedHeightD
    pendingD := h.pendingD
    retainedD := h.retainedD
    noFirstHeight := h.noFirstHeight
    noSecondHeight := h.noSecondHeight
    noEarlyFinality := h.noEarlyFinality
    chainA := h.chainA
    chainB := h.chainB
    chainD := h.chainD
    freshD := h.freshD
    noMixedD := h.noMixedD
    batchB := h.batchB
    batchD := h.batchD
    targetsB := by
      intro x hx
      have hh : safetyHolder S rho (e.symm x) = x :=
        (he (e.symm x)).trans (e.apply_symm_apply x)
      simpa only [hh] using h.targetsB (e.symm x) (hh.symm ▸ hx)
    actionsInRun := h.actionsInRun
    capThroughBAction := h.capThroughBAction
    capThroughFinalAction := h.capThroughFinalAction
    finalityThroughFinalAction := h.finalityThroughFinalAction
    heldDAtFinalAction := h.heldDAtFinalAction
    heldAAtEnd := h.heldAAtEnd
  }
  exact ⟨⟨fun ⟨m⟩ => ⟨toHolder m⟩, fun ⟨h⟩ => ⟨toNode h⟩⟩,
    (fun m => ⟨toHolder m, rfl, rfl, rfl, rfl, rfl, rfl⟩),
    (fun h => ⟨toNode h, rfl, rfl, rfl, rfl, rfl, rfl⟩)⟩

/-- Action supplies are equivalent for the paired, field-preserving witnesses. -/
theorem kernel_action_holder_frozen_iff
    (m : KernelMiddleWitness_W R S O T E rho I D Ef decodeProposal bodyErase bodyRows
      blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A)
    (h : KernelMiddleWitnessFG_W R S O T E rho I D Ef decodeProposal bodyErase bodyRows
      blockWireRows parentFG parentHeight validFor makeFG valid ac cfg K ΔF sp pt A)
    (selected : m.A₀ = h.A₀ ∧ m.B = h.B ∧ m.U = h.U ∧
      m.X_D = h.X_D ∧ m.cD = h.cD ∧ m.d = h.d) :
    KernelActionSupply_W R S O T E rho I D Ef m ↔
      KernelActionSupplyFG_W R S O T E rho I D Ef h := by
  obtain ⟨_, _, _, hX, hcD, _⟩ := selected
  constructor
  · intro a
    refine ⟨a.read, ?_, a.head, ?_⟩
    · simpa only [← hX, ← hcD] using a.service
    · simpa only [← hX] using a.walk
  · intro a
    refine ⟨a.read, ?_, a.head, ?_⟩
    · simpa only [hX, hcD] using a.service
    · simpa only [hX] using a.walk

end AvailableChain.FGCompose
end
