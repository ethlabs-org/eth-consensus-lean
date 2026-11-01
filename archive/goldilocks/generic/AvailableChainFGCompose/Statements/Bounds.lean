module
public import AvailableChainFGCompose.Statements.Timing

@[expose] public section

namespace AvailableChain.FGCompose

def P (T : FGTiming) : Time := 4 * (T.roundSlots : Time) * T.delta
def Γ (T : FGTiming) (G : Time) : Time :=
  4 * T.delta * ((G + 4 * T.delta - 1) / (4 * T.delta))
def kappaF (T : FGTiming) (deltaF : Time) : Nat :=
  ((6 * T.delta + deltaF + 4 * T.delta - 1) / (4 * T.delta)).toNat
def betaF (T : FGTiming) (deltaF : Time) : Time :=
  4 * (kappaF T deltaF : Time) * T.delta
def epsF (T : FGTiming) (deltaF : Time) : Time := betaF T deltaF - 8 * T.delta
def E_gF (T : FGTiming) (deltaF G repairAllowance : Time) : Time :=
  repairAllowance + Γ T G + max (FGCompose.P T + 3 * T.delta + epsF T deltaF) (2 * FGCompose.P T
    - T.delta)
def E_jF (T : FGTiming) (deltaF G repairAllowance : Time) : Time :=
  max (repairAllowance + FGCompose.P T + Γ T G + 3 * T.delta + epsF T deltaF)
    (2 * FGCompose.P T + Γ T G - 4 * T.delta)
def B_cF (T : FGTiming) (deltaF G repairAllowance : Time) : Time :=
  repairAllowance + Γ T G + max (FGCompose.P T - 2 * T.delta + epsF T deltaF) (2 * FGCompose.P T
    - 6 * T.delta)
def D_cF (T : FGTiming) (repairAllowance : Time) : Time :=
  repairAllowance + FGCompose.P T - T.delta
def B_resetF (T : FGTiming) (deltaF G repairAllowance : Time) : Time :=
  3 * FGCompose.P T + 2 * E_gF T deltaF G repairAllowance +
    2 * E_jF T deltaF G repairAllowance + B_cF T deltaF G repairAllowance +
    D_cF T repairAllowance
def carrierTimeW (T : FGTiming) (deltaF : Time) (r : Nat) : Time :=
  (r : Time) * FGCompose.P T + betaF T deltaF
def kernelDeadlineW (T : FGTiming) (deltaF : Time) (r : Nat) : Time :=
  (r : Time) * FGCompose.P T + betaF T deltaF + T.delta

def ActionDeliveryBoundsW (T : FGTiming) (deltaF : Time) (r : Nat) : Prop :=
  T.action r + deltaF = (r : Time) * FGCompose.P T + 6 * T.delta + deltaF ∧
    T.action r + deltaF ≤ carrierTimeW T deltaF r ∧
    carrierTimeW T deltaF r ≤ ((r : Time) + 1) * FGCompose.P T

def KernelBeforeNextActionW (T : FGTiming) (deltaF : Time) (r : Nat) : Prop :=
  kernelDeadlineW T deltaF r < T.action (r + 1)

structure LivenessBoundW (T : FGTiming) (deltaF : Time) : Prop where
  kappa_le_R : kappaF T deltaF ≤ T.roundSlots

end AvailableChain.FGCompose
end
