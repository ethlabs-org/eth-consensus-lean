module
public import ConsensusLean.Instances.Goldilocks.Proofs.Growing.Continuation.Endpoint
public import ConsensusLean.Instances.Goldilocks.Proofs.Growing.Continuation.LiveAfter

public section

/-! # Continued liveness after a hand-over

`continued_live_growing`, the `continuedLive` claim of `Continues` for Goldilocks: on a valid run
that hands over at `T ≥ heal` with progress on `[ready, horizon]`, a transaction submitted at `t`
is read by every ready reader of the available and the stable output at every deadline from
`max t heal + ΔAC + lat` through the horizon, or the run has a hash collision.

* At or after the horizon the hand-over is the healthy regime (`continued_live_past_horizon`).
* Before the horizon the deadlines up to `T` are the healthy prefix's
  (`continued_live_upTo_handover`), and the deadlines after `T` the seeded proposal liveness's
  (`continued_live_after_handover`). -/

namespace Consensus.Goldilocks

open AsChainShape
open Blocks Shape

/-- **Continued liveness** (`Continues.continuedLive` for Goldilocks), from Goldilocks
correctness: the healthy regime past the horizon, and before it the healthy prefix through `T`
and the seeded proposal liveness after `T`. -/
theorem continued_live_growing (hc : GoldilocksCorrect) (S : Setup) (A : ContractAssumptions S)
    (V : Type) [Fintype V] [DecidableEq V] :
    let Sy := Model.sysOf schema (compiled (goldilocks S)) V
    let K := goldilocksContract A (contract_coefficients S A)
    ∀ cap g, (cap = .available ∨ cap = .stable) → Sy.schema.output cap = some g →
      ∀ i gst T, Sy.Holds
        (fun r => Sy.Handover K gst T r ∧ Sy.heal K cap i gst r ≤ T ∧
          Sy.prog (shapeProgress (goldilocks S) V) K cap i (Sy.ready K gst r) (Sy.pt r).horizon r)
        (fun r => (Sy.trace r).TxLive (Sy.cDur K r) g (Sy.heal K cap i gst r)
          (Sy.lat K cap i r)) := by
  intro Sy K cap g hcap hg i gst T r hv ⟨hh, hT, hp⟩
  rcases le_total (Sy.pt r).horizon T with hH | hH
  · exact continued_live_past_horizon hc S A V cap g hg i gst T r hv hh hH hp
  rcases continued_live_upTo_handover hc S A V cap g hg i gst T r hv hh hH hT hp with hle | hx
  · rcases continued_live_after_handover S A V cap g hcap hg i gst T r hv hh hT hp with hgt | hx
    · refine Or.inl fun x t t' hs hst hth v hr => ?_
      rcases le_or_gt t' T with h | h
      · exact hle x t t' hs hst h v hr
      · exact hgt x t t' hs hst h hth v hr
    · exact Or.inr hx
  · exact Or.inr hx

end Consensus.Goldilocks

end
