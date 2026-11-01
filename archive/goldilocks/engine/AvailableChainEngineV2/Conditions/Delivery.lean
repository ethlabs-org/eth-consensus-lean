module
public import AvailableChainEngineV2.Conditions.DeliveryWindow

@[expose] public section

/-! Delivery conditions over V2 runs. Broadcast covers emitted objects; relay
covers accepted objects. Both use awake receiver windows, historical processing,
and the exclusion test at the deadline. There is no other forwarding rule. -/

namespace AvailableChain.V2

open AvailableChain

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}

/-- Broadcast and accepted-object relay provide service in each awake receiver
window whose deadline is within the run. The deadline is after GST. Historical
processing or exclusion at the deadline removes the need for a handler call. -/
structure PartialSynchrony (E : Generic.Env V) (rho : Run V P) : Prop where
  broadcast : ∀ v ∈ rho.honest, ∀ o t,
    Run.emits E rho v o t → ∀ w ∈ rho.honest,
    DeliveryDemand E rho v w o t (fun a => max a E.t_GST + E.Δ) rho.horizon
  relay : ∀ v ∈ rho.honest, ∀ i o t,
    Run.acceptsAt E rho i v o t → ∀ w ∈ rho.honest,
    DeliveryDemand E rho v w o t (fun a => max a E.t_GST + E.Δ) rho.horizon

/-- The same service on a finite healthy prefix, with deadlines within both
`cut` and the run horizon. -/
structure HealthyPrefixDelivery (E : Generic.Env V) (rho : Run V P) (cut : Time) : Prop where
  broadcast : ∀ v ∈ rho.honest, ∀ o t,
    Run.emits E rho v o t → ∀ w ∈ rho.honest,
    DeliveryDemand E rho v w o t (fun a => a + E.Δ) cut
  relay : ∀ v ∈ rho.honest, ∀ i o t,
    Run.acceptsAt E rho i v o t → ∀ w ∈ rho.honest,
    DeliveryDemand E rho v w o t (fun a => a + E.Δ) cut

end AvailableChain.V2

end
