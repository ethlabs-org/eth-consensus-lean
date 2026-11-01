module
public import AvailableChainFGCompose.Statements.Population.Promotion
public import AvailableChainFGCompose.Statements.Population.Seats

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V P)
variable (H : FGHeightView (Fin n)) (T : FGTiming)
variable (pair : Wire → NamedHeightPair)

/-- Iff at all honest seats under the frozen all-holder equivalence. -/
theorem openingCoveredFG_frozen_iff (e : Fin n ≃ V)
    (he : ∀ i, safetyHolder S rho i = e i) (r : Nat) (Q : Block) :
    OpeningCoveredFG R S E rho H T pair (FGHonestSeats S rho) r Q ↔
      OpeningCovered R S E rho H T pair r Q := by
  constructor
  · intro hc x hx
    obtain ⟨i, hi⟩ := e.surjective x
    have hh : safetyHolder S rho i = x := (he i).trans hi
    have hm : i ∈ FGHonestSeats S rho := by
      simp only [FGHonestSeats_def, Finset.mem_filter, Finset.mem_univ, true_and, hh, hx]
    simpa only [hh] using hc i hm
  · intro hc i hi
    have hh : safetyHolder S rho i ∈ rho.honest := by
      simpa only [FGHonestSeats_def, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    exact hc (safetyHolder S rho i) hh

/-- Iff at all honest seats under the frozen all-holder equivalence. -/
theorem fixedRowsFG_frozen_iff (e : Fin n ≃ V)
    (he : ∀ i, safetyHolder S rho i = e i) (r height : Nat)
    (Q : Block) (U : FGBlock (Fin n)) :
    FixedRowsFG R S E rho H T pair (FGHonestSeats S rho) r height Q U ↔
      FixedRows R S E rho H T pair r height Q U := by
  constructor
  · intro hc x hx
    obtain ⟨i, hi⟩ := e.surjective x
    have hh : safetyHolder S rho i = x := (he i).trans hi
    have hm : i ∈ FGHonestSeats S rho := by
      simp only [FGHonestSeats_def, Finset.mem_filter, Finset.mem_univ, true_and, hh, hx]
    simpa only [hh] using hc i hm
  · intro hc i hi
    have hh : safetyHolder S rho i ∈ rho.honest := by
      simpa only [FGHonestSeats_def, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    exact hc (safetyHolder S rho i) hh

end AvailableChain.FGCompose
end
