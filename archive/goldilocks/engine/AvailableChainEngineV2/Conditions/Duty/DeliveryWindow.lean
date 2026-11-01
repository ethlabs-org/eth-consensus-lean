module
public import AvailableChainEngineV2.Engine.Duty.Run -- shake: keep (re-export)
public import AvailableChainEngineV2.Conditions.Duty.Sleep

@[expose] public section

namespace AvailableChain.V2.D

open AvailableChain

variable {V In : Type} [DecidableEq V] {P : ProtocolSpecD In}

def ProcessedByActionCut (E : Generic.Env V) (rho : Run V P)
    (w : V) (o : P.Object) (a : Time) : Prop :=
  ∃ k, k ≤ Run.actionCut rho a ∧
    P.processed (Run.stateBefore E rho k w) o = true

def HandledBetween (E : Generic.Env V) (rho : Run V P)
    (w : V) (o : P.Object) (a d : Time) : Prop :=
  ∃ t', a ≤ t' ∧ t' < d ∧ ∃ j, Run.handlesAt E rho j w o t'

def DeliveryService (E : Generic.Env V) (rho : Run V P)
    (w : V) (o : P.Object) (a d : Time) : Prop :=
  ProcessedByActionCut E rho w o a ∨ HandledBetween E rho w o a d

def DeliveryDemand (E : Generic.Env V) (rho : Run V P)
    (src dst : V) (o : P.Object) (send : Time)
    (dl : Time → Time) (cut : Time) : Prop :=
  ∀ a, send ≤ a → 0 ≤ a → a < dl a →
    dl a ≤ cut → dl a ≤ rho.horizon →
    LinkReadyOn E rho src dst a (dl a) →
    P.excludes (Run.stateBeforeTime E rho (dl a) dst) o = false →
    DeliveryService E rho dst o a (dl a)

end AvailableChain.V2.D

end
