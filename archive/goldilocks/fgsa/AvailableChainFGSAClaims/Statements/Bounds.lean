module
public import AvailableChainGeneric.Statements.Pure.Schedule -- shake: keep (Tests.Recurrence positive controls)
public import AvailableChainFGSA.Model.Objects

@[expose] public section

namespace AvailableChain.FGSA.Run

/-- Blueprint 00 §2.5 and 21 §1. All subtraction is in integer time. -/
def L (p : Params) : Time := (4 * (p.k : Time) - 1) * p.Δ
def P (p : Params) : Time := 4 * (p.R : Time) * p.Δ
def Γ (p : Params) (G : Time) : Time := 4 * p.Δ * ((G + 4 * p.Δ - 1) / (4 * p.Δ))
def ρΓ (p : Params) (G : Time) : Time := 2 * L p + Γ p G + 8 * p.Δ
def ρ₁ (p : Params) (G : Time) : Time := L p + Γ p G + 10 * p.Δ
def ρ (p : Params) (G : Time) : Time := 2 * L p + G + 8 * p.Δ

def E_g (p : Params) (G ρbar : Time) : Time := ρbar + 2 * P p + Γ p G - p.Δ
def E_j (p : Params) (G ρbar : Time) : Time :=
  max (ρbar + P p + Γ p G + 3 * p.Δ) (2 * P p + Γ p G - 4 * p.Δ)
def B_c (p : Params) (G ρbar : Time) : Time := ρbar + 2 * P p + Γ p G - 6 * p.Δ
def D_c (p : Params) (ρbar : Time) : Time := ρbar + P p - p.Δ
def B_reset (p : Params) (G ρbar : Time) : Time :=
  3 * P p + 2 * E_g p G ρbar + 2 * E_j p G ρbar + B_c p G ρbar + D_c p ρbar
/-- D25: use the sum form as the definition. -/
def B (p : Params) (G ρbar : Time) : Time := B_reset p G ρbar + Γ p G + 4 * p.Δ
def B_H2 (p : Params) (G : Time) : Time := B p G (ρΓ p G)
def B_H1 (p : Params) (G : Time) : Time := B p G (ρ₁ p G)
def B_H (p : Params) (G : Time) : Time :=
  if p.k ≤ 2 * p.R + 1 then min (B_H2 p G) (B_H1 p G) else B_H2 p G

def W_F (p : Params) (g : Nat) : Time := ((g : Time) + 2) * P p + 9 * p.Δ
def B_F (p : Params) (G : Time) (g : Nat) : Time := B_H p G + W_F p g
def B_heal (p : Params) (G : Time) (g : Nat) : Time :=
  6 * ρ p G + (23 + 13 * (g : Time)) * P p + G + 64 * p.Δ
def B_best (p : Params) (G : Time) (g : Nat) : Time := min (B_heal p G g) (B_H p G)
def carrierTime2 (p : Params) (r : Nat) : Time := (r : Time) * P p + 8 * p.Δ
def kernelDeadline (p : Params) (r : Nat) : Time := (r : Time) * P p + 9 * p.Δ

/-- P13: the action batch arrives before the +2 carrier and next opening. -/
def ActionDeliveryBounds (p : Params) (r : Nat) : Prop :=
  p.actionTime r + p.Δ = (r : Time) * P p + 7 * p.Δ ∧
  p.actionTime r + p.Δ < carrierTime2 p r ∧
  p.actionTime r + p.Δ < ((r : Time) + 1) * P p
/-- P13: the kernel deadline precedes the next action. -/
def KernelBeforeNextAction (p : Params) (r : Nat) : Prop :=
  kernelDeadline p r < p.actionTime (r + 1)
/-- P13: the label-(qR+1) vote precedes action q. -/
def VoteBeforeAction (p : Params) (q : Nat) : Prop :=
  SA.voteTime p.toParams (q * p.R + 1) < p.actionTime q
/-- P13: the label-(qR+1) gate follows the +2 carrier. -/
def GateAfterCarrier2 (p : Params) (q : Nat) : Prop :=
  carrierTime2 p q < SA.gateTime p.toParams (q * p.R + 1)
/-- P13: the gate order at z=(p+2)R, including the next label. -/
def GateActionOrder (p : Params) (r c : Nat) : Prop :=
  (c ≤ (r + 2) * p.R → SA.gateTime p.toParams c ≤ p.actionTime (r + 2)) ∧
  (c = (r + 2) * p.R + 1 → p.actionTime (r + 2) < SA.gateTime p.toParams c)
/-- P13: fourteen delay units fit in two rounds. -/
def FourteenBeforeTwoRounds (p : Params) (r : Nat) : Prop :=
  (r : Time) * P p + 14 * p.Δ < (r : Time) * P p + 2 * P p

end AvailableChain.FGSA.Run

end
