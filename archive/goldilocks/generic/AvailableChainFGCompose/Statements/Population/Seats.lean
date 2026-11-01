module
public import AvailableChainFGCompose.Statements.SafetyReads

@[expose] public section

namespace AvailableChain.FGCompose
variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Wire : Type}

/-- Honest FG seats; honest runtime nodes without a seat contribute no vote. -/
noncomputable def FGHonestSeats (S : FGSafetyReads P n Wire) (rho : V2.D.Run V P) :
    Finset (Fin n) :=
  Finset.univ.filter (fun i => safetyHolder S rho i ∈ rho.honest)

theorem FGHonestSeats_def (S : FGSafetyReads P n Wire) (rho : V2.D.Run V P) :
    FGHonestSeats S rho =
      Finset.univ.filter (fun i => safetyHolder S rho i ∈ rho.honest) := rfl

end AvailableChain.FGCompose
end
