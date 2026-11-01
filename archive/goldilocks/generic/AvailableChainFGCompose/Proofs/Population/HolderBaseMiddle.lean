module
public import AvailableChainFGCompose.Proofs.Finality.MiddleSupport

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire Body : Type}
variable (R : FGCoreReads P n Base Proposal Wire) (S : FGSafetyReads P n Wire)
variable (O : FGObservationReads R) (T : FGTiming) (L : FGTimingLaws T)
variable (E : Generic.Env V) (rho : V2.D.Run V P) (I : V2.D.Interface P)
variable (D : FGHistoryWireReads S) (Ef : Electorate (Fin n))

include L in
/-- The actual reset source transfers before the opening, even before service starts. -/
theorem middle_reset_opening_height_core (sp : FGServicePoint) (horizon Jst : Time)
    (reset : H0Reset R S E rho O T (fun a => namedEntry (D.heightPair a)) Jst sp.reset)
    (history : FGHistoricalHighTransfer R O T E rho I sp horizon)
    (height : FGHeightLaws Ef O.height)
    (reflect : ∀ A B, Block.Preceq (R.erase A) (R.erase B) → FGBlock.Preceq A B)
    (parent : ∀ B, R.erase B.parent = (R.erase B).parent)
    (q : Nat) (A₀ : FGBlock (Fin n))
    (hA : HonestProposal E rho I (q * T.roundSlots) (R.erase A₀))
    (hprop : T.proposal (q * T.roundSlots) ≤ horizon)
    (hgap : sp.reset.sStar + 2 ≤ q * T.roundSlots) :
    sp.reset.M + 1 ≤ (O.height A₀).h := by
  obtain ⟨j, x, a, C, ha, _hname, hsource, _herase, hheight⟩ := reset.fresh
  have gap : sp.reset.rStar * T.roundSlots + 2 ≤ q * T.roundSlots := by
    rw [← reset.label]
    exact hgap
  have source_horizon : T.action sp.reset.rStar ≤ horizon := by
    have hslot := kmid_slot_scale_le T L gap
    rw [kmid_actionTime_eq T L]
    rw [L.proposal_eq] at hprop
    have hd := L.delta_pos
    push_cast at hslot hprop
    push_cast
    nlinarith
  have hp := history x sp.reset.rStar C ha.1 hsource (by rw [hheight]) source_horizon
    _ _ hA hprop gap
  rw [← parent] at hp
  have hh := (height.h_mono (reflect C A₀.parent hp)).trans
    (height.h_mono (kmid_parent_preceq A₀))
  rw [hheight] at hh
  exact hh

end AvailableChain.FGCompose
end
