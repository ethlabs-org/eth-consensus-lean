module
public import AvailableChainFGSAClaims.Statements.Packages.Safety
public import AvailableChainFGSAClaims.Statements.Healed

@[expose] public section

namespace AvailableChain.FGSA.Run
open Gen.Pure
variable (p : Params) {In V : Type} (c : AppCodec In) [DecidableEq V] [Fintype V]

/-- Plan §1.7. DC: INTENTIONAL W recurrence forms; no strong dispatch. -/
inductive FinFormW | recFE | recF4

/-- Blueprint 22:1371–1448. DC: INTENTIONAL full receipt guards. -/
def FinFormW.holdsW (form : FinFormW) (ΔF : Time) (H : Slot → Prop)
    (GST horizon : Time) (g : Nat) : Prop :=
  match form with
  | .recFE => FE_W p ΔF H GST horizon g
  | .recF4 => F4_W p ΔF H GST horizon g

theorem FinFormW.holdsW_def (form : FinFormW) (ΔF : Time) (H : Slot → Prop)
    (GST horizon : Time) (g : Nat) :
    FinFormW.holdsW p form ΔF H GST horizon g =
  (match form with
  | .recFE => FE_W p ΔF H GST horizon g
  | .recF4 => F4_W p ΔF H GST horizon g) := rfl

/-- Plan §1.7. DC: INTENTIONAL explicit ΔF, κ bound and W recurrence.
The existing Recovery₂ supplies validity, row delivery and finite proposer gap.
S4.6: the Regimes move needs an out-of-scope WeakContinuation import fix. -/
structure FinalitySet_W (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (G ΔF : Time) (form : FinFormW) (g : Nat) : Prop where
  core : RecoverySleep₂ p c E rho G ΔF
  bound : LivenessBoundW p ΔF
  recur : form.holdsW p ΔF (Gen.V2.Duty.HonestSlot rho (fgsaInterface p c))
    (recoveryStart p E) rho.horizon g

/-- Plan §1.7. DC: INTENTIONAL FE/F4 share W_W; no strong dispatch. -/
def finalityWindow_W (ΔF : Time) (_form : FinFormW) (g : Nat) : Time := W_W p ΔF g

theorem finalityWindow_W_def (ΔF : Time) (form : FinFormW) (g : Nat) :
    finalityWindow_W p ΔF form g = W_W p ΔF g := rfl

/-- FF5 GST composition (22:1382–1384). DC: INTENTIONAL H-time composition.
HTime supplies input and start. This package does not use best/search healing. -/
structure FirstFinalityPrem_W (G ΔF : Time) (form : FinFormW) (g : Nat)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (_pt : Unit) : Prop where
  set : FinalitySet_W p c E rho G ΔF form g
  hhor : recoveryStart p E + B_HF p ΔF G + W_W p ΔF g ≤ rho.horizon

/-- Local FF5 (22:1371–1380). DC: INTENTIONAL common input and receipt horizon.
The trigger is at or after t*, with no GST healing-bound restriction. -/
structure FinalityLivenessPrem_W (G ΔF : Time) (form : FinFormW) (g : Nat)
    (w : HealingWitness) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (pt : PtT) : Prop where
  set : FinalitySet_W p c E rho G ΔF form g
  input : HealingInput p c E rho w ΔF
  start : tstar p w ≤ pt.t
  hhor : pt.t + W_W p ΔF g ≤ rho.horizon

/-- Local FF6 (22:1421–1430). DC: INTENTIONAL common input; local proposal deadline. -/
structure ProposalFinalPrem_W (G ΔF : Time) (form : FinFormW) (g : Nat)
    (w : HealingWitness) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (pt : PtSX) : Prop where
  set : FinalitySet_W p c E rho G ΔF form g
  input : HealingInput p c E rho w ΔF
  prop : HonestProposal E rho (fgsaInterface p c) pt.s pt.X
  start : tstar p w ≤ V2.D.proposalTime (fgsaInterface p c) pt.s
  hhor : V2.D.proposalTime (fgsaInterface p c) pt.s + W_W p ΔF g ≤ rho.horizon

/-- Local FF7 (22:1434–1451). DC: INTENTIONAL two complete forward searches.
The first guard and the second guard include their carrier receipt tails. -/
structure AboveFrontierPrem_W (G ΔF : Time) (form : FinFormW) (g : Nat)
    (w : HealingWitness) (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (pt : PtT) : Prop where
  set : FinalitySet_W p c E rho G ΔF form g
  input : HealingInput p c E rho w ΔF
  start : tstar p w ≤ pt.t
  firstHorizon : pt.t + W_W p ΔF g ≤ rho.horizon
  hhor : pt.t + W_W p ΔF g + W_W p ΔF g ≤ rho.horizon

end AvailableChain.FGSA.Run
end
