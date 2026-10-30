module
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Window

public section

/-! # Goldilocks FG store: the FG service lemmas (G1.6–G1.8, G1.9 (a))

G1.6 and G1.7's first window are theorem A's core (`window_justifies`); G1.7's second window is
the core again at the actual entry `X`, whose state is the same at every honest node
(`σ_eq_of_held`), so its `P_E` is `(h, T_h)`. G1.8 (a): from slot `u + max(δ_t, r)` on, the
honest proposal of each `g`-slot window includes a progress quorum of current-entry rows, with a
mature entry, so the height is left there at the latest. G1.8 (b) is G1.7 with `T₁ ⪯ T_h`.
G1.9 (a): the justification step does not raise the head height floor for `σ = σ[B]`. -/

namespace Consensus.Goldilocks.Store

variable (P : Params) (ACP : Type)

/-- **G1.6.** -/
theorem bound_entry : BoundEntry P ACP := by
  sorry

/-- **G1.7.** -/
theorem unbound_entry : UnboundEntry P ACP := by
  sorry

/-- **G1.8 (a).** -/
theorem crossing : Crossing P ACP := by
  sorry

/-- **G1.8 (b).** -/
theorem coverage : Coverage P ACP := by
  sorry

/-- **G1.9 (a).** -/
theorem cache_acceptance : CacheAcceptance P ACP := by
  sorry

end Consensus.Goldilocks.Store

end
