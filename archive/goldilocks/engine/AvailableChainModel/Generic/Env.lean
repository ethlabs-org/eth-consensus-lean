module
public import AvailableChainModel.Objects.Time

@[expose] public section

namespace AvailableChain.Generic

/-- The environment. Validators are unit seats: every validator has weight 1,
so participation premises count validators. -/
structure Env (V : Type) where
  Δ : Time
  Δ_pos : 0 < Δ
  t_GST : Time
  t_GST_nonneg : 0 ≤ t_GST
  /-- Awake profile. The consuming engine defines sleep behavior.
  The v1 engine suppresses emissions while asleep. V2 valid schedules
  exclude local ticks, deliveries, and restarts while asleep. -/
  awake : V → Time → Bool

end AvailableChain.Generic

end
