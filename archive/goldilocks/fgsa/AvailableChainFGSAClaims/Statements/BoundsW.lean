module
public import AvailableChainFGSAClaims.Statements.Bounds
public import AvailableChainGeneric.Statements.Pure.ScheduleW

@[expose] public section

namespace AvailableChain.FGSA.Run

/-! Spec 273–281, 509–539; blueprint 21:54–80. Integer-time W bounds.
The row delay is an explicit argument. The reset bound uses the D25 sum. -/

def kappaF (p : Params) (ΔF : Time) : Nat :=
  ((6 * p.Δ + ΔF + 4 * p.Δ - 1) / (4 * p.Δ)).toNat

def betaF (p : Params) (ΔF : Time) : Time :=
  4 * (kappaF p ΔF : Time) * p.Δ

def epsF (p : Params) (ΔF : Time) : Time :=
  betaF p ΔF - 8 * p.Δ

def carrierTimeW (p : Params) (ΔF : Time) (r : Nat) : Time :=
  (r : Time) * P p + betaF p ΔF

def kernelDeadlineW (p : Params) (ΔF : Time) (r : Nat) : Time :=
  (r : Time) * P p + betaF p ΔF + p.Δ

def W_W (p : Params) (ΔF : Time) (g : Nat) : Time :=
  ((g : Time) + 2) * P p + betaF p ΔF + p.Δ

def E_gF (p : Params) (ΔF G ρbar : Time) : Time :=
  ρbar + Γ p G + max (P p + 3 * p.Δ + epsF p ΔF) (2 * P p - p.Δ)

def E_jF (p : Params) (ΔF G ρbar : Time) : Time :=
  max (ρbar + P p + Γ p G + 3 * p.Δ + epsF p ΔF)
    (2 * P p + Γ p G - 4 * p.Δ)

def B_cF (p : Params) (ΔF G ρbar : Time) : Time :=
  ρbar + Γ p G + max (P p - 2 * p.Δ + epsF p ΔF) (2 * P p - 6 * p.Δ)

def D_cF (p : Params) (ρbar : Time) : Time :=
  ρbar + P p - p.Δ

def B_resetF (p : Params) (ΔF G ρbar : Time) : Time :=
  3 * P p + 2 * E_gF p ΔF G ρbar + 2 * E_jF p ΔF G ρbar +
    B_cF p ΔF G ρbar + D_cF p ρbar

def BF (p : Params) (ΔF G ρbar : Time) : Time :=
  B_resetF p ΔF G ρbar + Γ p G + 4 * p.Δ

def B_H2F (p : Params) (ΔF G : Time) : Time :=
  BF p ΔF G (ρΓ p G)

def B_H1F (p : Params) (ΔF G : Time) : Time :=
  BF p ΔF G (ρ₁ p G)

def B_HF (p : Params) (ΔF G : Time) : Time :=
  if p.k ≤ 2 * p.R + 1 then min (B_H2F p ΔF G) (B_H1F p ΔF G)
    else B_H2F p ΔF G

def B'_resetF (p : Params) (ΔF G : Time) : Time :=
  if p.k ≤ 2 * p.R + 1 then
    min (B_resetF p ΔF G (ρΓ p G)) (B_resetF p ΔF G (ρ₁ p G))
    else B_resetF p ΔF G (ρΓ p G)

def B_bestF (p : Params) (ΔF G : Time) (g : Nat) : Time :=
  min (B_heal p G g) (B_HF p ΔF G)

def ActionDeliveryBoundsW (p : Params) (ΔF : Time) (r : Nat) : Prop :=
  p.actionTime r + ΔF = (r : Time) * P p + 6 * p.Δ + ΔF ∧
    p.actionTime r + ΔF ≤ carrierTimeW p ΔF r ∧
    carrierTimeW p ΔF r ≤ ((r : Time) + 1) * P p

def KernelBeforeNextActionW (p : Params) (ΔF : Time) (r : Nat) : Prop :=
  kernelDeadlineW p ΔF r < p.actionTime (r + 1)

/-- The round bound for liveness. Delivery packages carry the row-delay lower bound. -/
structure LivenessBoundW (p : Params) (ΔF : Time) : Prop where
  kappa_le_R : kappaF p ΔF ≤ p.R

/-- Blueprint 22:211–227. The row delay fixes both κ and β. -/
def FE_W (p : Params) (ΔF : Time) (H : Slot → Prop) (GST horizon : Time) (g : Nat) : Prop :=
  Gen.Pure.RecFE_W H p.R (kappaF p ΔF) (P p) p.Δ (betaF p ΔF) GST horizon g

def F4_W (p : Params) (ΔF : Time) (H : Slot → Prop) (GST horizon : Time) (g : Nat) : Prop :=
  Gen.Pure.RecF4_W H p.R (kappaF p ΔF) (P p) p.Δ (betaF p ΔF) GST horizon g

def FGoodE_Wp (p : Params) (ΔF : Time) (H : Slot → Prop) (r : Nat) : Prop :=
  Gen.Pure.FGoodE_W H p.R (kappaF p ΔF) r

def FGood4_Wp (p : Params) (ΔF : Time) (H : Slot → Prop) (r : Nat) : Prop :=
  Gen.Pure.FGood4_W H p.R (kappaF p ΔF) r

def Tail_Wp (p : Params) (ΔF : Time) (H : Slot → Prop) (r : Nat) : Prop :=
  Gen.Pure.Tail_W H p.R (kappaF p ΔF) r

/-- Blueprint 22:1384. The healing bound plus the W search window. -/
def B_FW (p : Params) (ΔF G : Time) (g : Nat) : Time :=
  B_HF p ΔF G + W_W p ΔF g

theorem kappaF_def (p : Params) (ΔF : Time) :
    kappaF p ΔF =
      (((6 * p.Δ + ΔF + 4 * p.Δ - 1) / (4 * p.Δ)).toNat) := by rfl

theorem betaF_def (p : Params) (ΔF : Time) :
    betaF p ΔF =
      (4 * (kappaF p ΔF : Time) * p.Δ) := by rfl

theorem epsF_def (p : Params) (ΔF : Time) :
    epsF p ΔF =
      (betaF p ΔF - 8 * p.Δ) := by rfl

theorem carrierTimeW_def (p : Params) (ΔF : Time) (r : Nat) :
    carrierTimeW p ΔF r =
      ((r : Time) * P p + betaF p ΔF) := by rfl

theorem kernelDeadlineW_def (p : Params) (ΔF : Time) (r : Nat) :
    kernelDeadlineW p ΔF r =
      ((r : Time) * P p + betaF p ΔF + p.Δ) := by rfl

theorem W_W_def (p : Params) (ΔF : Time) (g : Nat) :
    W_W p ΔF g =
      (((g : Time) + 2) * P p + betaF p ΔF + p.Δ) := by rfl

theorem E_gF_def (p : Params) (ΔF G ρbar : Time) :
    E_gF p ΔF G ρbar =
      (ρbar + Γ p G + max (P p + 3 * p.Δ + epsF p ΔF) (2 * P p - p.Δ)) := by rfl

theorem E_jF_def (p : Params) (ΔF G ρbar : Time) :
    E_jF p ΔF G ρbar =
      (max (ρbar + P p + Γ p G + 3 * p.Δ + epsF p ΔF)
    (2 * P p + Γ p G - 4 * p.Δ)) := by rfl

theorem B_cF_def (p : Params) (ΔF G ρbar : Time) :
    B_cF p ΔF G ρbar =
      (ρbar + Γ p G + max (P p - 2 * p.Δ + epsF p ΔF) (2 * P p - 6 * p.Δ)) := by rfl

theorem D_cF_def (p : Params) (ρbar : Time) :
    D_cF p ρbar =
      (ρbar + P p - p.Δ) := by rfl

theorem B_resetF_def (p : Params) (ΔF G ρbar : Time) :
    B_resetF p ΔF G ρbar =
      (3 * P p + 2 * E_gF p ΔF G ρbar + 2 * E_jF p ΔF G ρbar +
    B_cF p ΔF G ρbar + D_cF p ρbar) := by rfl

theorem BF_def (p : Params) (ΔF G ρbar : Time) :
    BF p ΔF G ρbar =
      (B_resetF p ΔF G ρbar + Γ p G + 4 * p.Δ) := by rfl

theorem B_H2F_def (p : Params) (ΔF G : Time) :
    B_H2F p ΔF G =
      (BF p ΔF G (ρΓ p G)) := by rfl

theorem B_H1F_def (p : Params) (ΔF G : Time) :
    B_H1F p ΔF G =
      (BF p ΔF G (ρ₁ p G)) := by rfl

theorem B_HF_def (p : Params) (ΔF G : Time) :
    B_HF p ΔF G =
      (if p.k ≤ 2 * p.R + 1 then min (B_H2F p ΔF G) (B_H1F p ΔF G)
    else B_H2F p ΔF G) := by rfl

theorem B'_resetF_def (p : Params) (ΔF G : Time) :
    B'_resetF p ΔF G =
      (if p.k ≤ 2 * p.R + 1 then
    min (B_resetF p ΔF G (ρΓ p G)) (B_resetF p ΔF G (ρ₁ p G))
    else B_resetF p ΔF G (ρΓ p G)) := by rfl

theorem B_bestF_def (p : Params) (ΔF G : Time) (g : Nat) :
    B_bestF p ΔF G g =
      (min (B_heal p G g) (B_HF p ΔF G)) := by rfl

theorem ActionDeliveryBoundsW_def (p : Params) (ΔF : Time) (r : Nat) :
    ActionDeliveryBoundsW p ΔF r =
      (p.actionTime r + ΔF = (r : Time) * P p + 6 * p.Δ + ΔF ∧
    p.actionTime r + ΔF ≤ carrierTimeW p ΔF r ∧
    carrierTimeW p ΔF r ≤ ((r : Time) + 1) * P p) := by rfl

theorem KernelBeforeNextActionW_def (p : Params) (ΔF : Time) (r : Nat) :
    KernelBeforeNextActionW p ΔF r =
      (kernelDeadlineW p ΔF r < p.actionTime (r + 1)) := by rfl

theorem FE_W_def (p : Params) (ΔF : Time) (H : Slot → Prop) (GST horizon : Time) (g : Nat) :
    FE_W p ΔF H GST horizon g =
      Gen.Pure.RecFE_W H p.R (kappaF p ΔF) (P p) p.Δ (betaF p ΔF) GST horizon g := by rfl

theorem F4_W_def (p : Params) (ΔF : Time) (H : Slot → Prop) (GST horizon : Time) (g : Nat) :
    F4_W p ΔF H GST horizon g =
      Gen.Pure.RecF4_W H p.R (kappaF p ΔF) (P p) p.Δ (betaF p ΔF) GST horizon g := by rfl

theorem FGoodE_Wp_def (p : Params) (ΔF : Time) (H : Slot → Prop) (r : Nat) :
    FGoodE_Wp p ΔF H r = Gen.Pure.FGoodE_W H p.R (kappaF p ΔF) r := by rfl

theorem FGood4_Wp_def (p : Params) (ΔF : Time) (H : Slot → Prop) (r : Nat) :
    FGood4_Wp p ΔF H r = Gen.Pure.FGood4_W H p.R (kappaF p ΔF) r := by rfl

theorem Tail_Wp_def (p : Params) (ΔF : Time) (H : Slot → Prop) (r : Nat) :
    Tail_Wp p ΔF H r = Gen.Pure.Tail_W H p.R (kappaF p ΔF) r := by rfl

theorem B_FW_def (p : Params) (ΔF G : Time) (g : Nat) :
    B_FW p ΔF G g = B_HF p ΔF G + W_W p ΔF g := by rfl

end AvailableChain.FGSA.Run
