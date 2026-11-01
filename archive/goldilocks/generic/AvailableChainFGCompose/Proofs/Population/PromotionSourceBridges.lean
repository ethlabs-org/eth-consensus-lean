module
public import AvailableChainFGCompose.Statements.FrontierMaturity
public import AvailableChainFGCompose.Statements.Population.FrontierMaturity
public import AvailableChainFGCompose.Statements.Population.Seats

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot)
variable (O : FGObservationReads R) (T : FGTiming) (I : V2.D.Interface Prot)
variable (D : FGHistoryWireReads S)

/-- The frozen all-holder source statement is equivalent at all honest seats. -/
theorem promotionSourceAtFG_frozen_iff (e : Fin n ≃ V)
    (he : ∀ i, safetyHolder S rho i = e i) (ΔF : Time) (r height : Nat)
    (U : FGBlock (Fin n)) (s : Slot) (X : FGBlock (Fin n)) :
    PromotionSourceAtFG R S E rho O T I D (FGHonestSeats S rho) ΔF r height U s X ↔
      PromotionSourceAt R S E rho O T I D ΔF r height U s X := by
  constructor
  · intro h
    refine ⟨h.entry, h.parentPath, h.proposal, h.slot, h.sync, h.carrier, h.age, h.horizon, ?_⟩
    intro x hx
    obtain ⟨i, hi⟩ := e.surjective x
    have hh : safetyHolder S rho i = x := (he i).trans hi
    have hm : i ∈ FGHonestSeats S rho := by
      simp only [FGHonestSeats_def, Finset.mem_filter, Finset.mem_univ, true_and, hh, hx]
    simpa only [hh] using h.rows i hm
  · intro h
    refine ⟨h.entry, h.parentPath, h.proposal, h.slot, h.sync, h.carrier, h.age, h.horizon, ?_⟩
    intro i hi
    have hh : safetyHolder S rho i ∈ rho.honest := by
      simpa only [FGHonestSeats_def, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    exact h.rows (safetyHolder S rho i) hh

end AvailableChain.FGCompose
end
