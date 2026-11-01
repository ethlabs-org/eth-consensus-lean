module
public import AvailableChainEngineV2.Conditions.Duty.DeliveryWindow

@[expose] public section

namespace AvailableChain.V2.D

open AvailableChain

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}

structure PartialSynchrony (E : Generic.Env V) (rho : Run V P) : Prop where
  broadcast_emitted : ∀ v ∈ rho.honest, ∀ o t,
    Run.emits E rho v o t → ∀ w ∈ rho.honest,
    DeliveryDemand E rho v w o t (fun a => max a E.t_GST + E.Δ) rho.horizon
  relay_accepted : ∀ v ∈ rho.honest, ∀ i o t,
    Run.acceptsAt E rho i v o t → ∀ w ∈ rho.honest,
    DeliveryDemand E rho v w o t (fun a => max a E.t_GST + E.Δ) rho.horizon

structure HealthyPrefixDelivery (E : Generic.Env V) (rho : Run V P) (cut : Time) : Prop where
  broadcast_emitted : ∀ v ∈ rho.honest, ∀ o t,
    Run.emits E rho v o t → ∀ w ∈ rho.honest,
    DeliveryDemand E rho v w o t (fun a => a + E.Δ) cut
  relay_accepted : ∀ v ∈ rho.honest, ∀ i o t,
    Run.acceptsAt E rho i v o t → ∀ w ∈ rho.honest,
    DeliveryDemand E rho v w o t (fun a => a + E.Δ) cut

end AvailableChain.V2.D

end
