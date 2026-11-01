module
public import AvailableChainFGCompose.Statements.Population.FrontierSearch
public import AvailableChainFGCompose.Proofs.Population.PromotionBridges

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot)
variable (O : FGObservationReads R) (T : FGTiming) (I : V2.D.Interface Prot)
variable (pair : Wire → NamedHeightPair) (Jst : Time) (leaseSlots deltaT : Nat)
variable (e : Fin n ≃ V) (he : ∀ i, safetyHolder S rho i = e i)

include e he

/-- Iff: frozen all-holder coverage reindexes only the opening rows. -/
theorem frontierLocalServiceFG_frozen_iff (q : Slot) (Q : Block) (Qfg : FGBlock (Fin n))
    (m : Nat) (v : Time) :
    FrontierLocalServiceFG R S E rho O T I pair q Q Qfg m v ↔
      FrontierLocalService R S E rho O T I pair q Q Qfg m v := by
  dsimp only [FrontierLocalService]
  simp only [FrontierLocalServiceFG_def,
    openingCoveredFG_frozen_iff R S E rho O.height T pair e he]

/-- Iff: preserve the selected seed witnesses and every all-node clause. -/
theorem strongServedFG_frozen_iff (m : Nat) (t : Time) :
    StrongServedFG R S E rho O T I pair Jst leaseSlots m t ↔
      StrongServed R S E rho O T I pair Jst leaseSlots m t := by
  simp only [StrongServedFG_def, StrongServed_def,
    frontierLocalServiceFG_frozen_iff R S E rho O T I pair e he]

/-- Iff: the first-stop and rise alternatives and served time bounds are unchanged. -/
theorem frontierHG3ResultFG_frozen_iff (i m : Nat) (start deadline : Time) :
    FrontierHG3ResultFG R S E rho O T I pair Jst leaseSlots i m start deadline ↔
      FrontierHG3Result R S E rho O T I pair Jst leaseSlots i m start deadline := by
  simp only [FrontierHG3ResultFG_def, FrontierHG3Result_def,
    strongServedFG_frozen_iff R S E rho O T I pair Jst leaseSlots e he]

/-- Iff: transport only the saved-seed alternative under the original repair guard. -/
theorem interruptedRepairStatementFG_frozen_iff (G ΔF ρbar : Time) :
    InterruptedRepairStatementFG R S E rho O T I pair Jst leaseSlots deltaT G ΔF ρbar ↔
      InterruptedRepairStatement R S E rho O T I pair Jst leaseSlots deltaT G ΔF ρbar := by
  dsimp only [InterruptedRepairStatement]
  simp only [InterruptedRepairStatementFG_def,
    strongServedFG_frozen_iff R S E rho O T I pair Jst leaseSlots e he]

/-- Iff: use the served equivalence contravariantly, preserving both independent horizons. -/
theorem frontierTailStatementFG_frozen_iff (G ΔF : Time) :
    FrontierTailStatementFG R S E rho O T I pair Jst leaseSlots deltaT G ΔF ↔
      FrontierTailStatement R S E rho O T I pair Jst leaseSlots deltaT G ΔF := by
  simp only [FrontierTailStatementFG_def, FrontierTailStatement_def,
    strongServedFG_frozen_iff R S E rho O T I pair Jst leaseSlots e he]

end AvailableChain.FGCompose
end
