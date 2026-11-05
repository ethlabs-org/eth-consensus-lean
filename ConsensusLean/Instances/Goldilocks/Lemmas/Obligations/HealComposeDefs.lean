module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.Rise

public section

/-! # Goldilocks Obligations: definitions of the M1′ composition

The drain interface `DrainOutputs` and the sub-interval restriction `frameWindow_sub`, inputs of
the drain reset `exists_reset_of_drain_rounds` (`ResetOfDrainRounds`). This module imports only the
rise, so that it does not depend on the final-window or healed-safety layers. -/

namespace Consensus.Goldilocks.Obligations

open SA (gbar)
open Healing

section Drain

variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}

/-- **The drain outputs (to be supplied by the DrainWindow, P5).** For every slot-aligned
FrameWindow `[t_{s₀}, t_N + 2Δ]` with `ḡ + 4Δ ≤ t_{s₀}`, `s₀ + L_drain ≤ N`, `t_N + 2Δ ≤ b` (the
service horizon), no honest signature above `H_z` up to `t_N + 2Δ`, and the honest-proposer gap
`G` on `[s₀, N]`: an actual warm honest
proposal `P` of a slot `u ∈ [s₀ + 2k, s₀ + L_drain]` by its designated proposer, with
`σ[P].h ≥ H_z − 1` (`hlow` of `rise_reset_rounds`). The O1-L lock clause is derived from the warm
proposal and frame inside the rise, not an additional drain output. The uniform frame/warm
producer remains an input; this interface strengthening does not construct it. -/
structure DrainOutputs (tr : GoldilocksTrace sp ro) (proposer : Nat → Fin sp.n)
    (H : Set (Fin sp.n)) (g : Time) (G Ld : Nat) (b : Time) : Prop where
  warm : ∀ {s₀ N floor : Nat} {kindJ : Prop} {J : SA.Blk sp.n (List (FG.Att sp.n))},
    FrameWindow (tr := tr) (H := H) (sp.ts s₀) (sp.ts N + 2 * sp.Δ) floor kindJ J →
    gbar g + 4 * sp.Δ ≤ sp.ts s₀ → s₀ + Ld ≤ N → sp.ts N + 2 * sp.Δ ≤ b →
    (∀ v ∈ H, ∀ k att, tr.SignAt v k att → tr.time k ≤ sp.ts N + 2 * sp.Δ →
      att.h ≤ HZ tr H g) →
    (∀ a, s₀ ≤ a → a + G ≤ N + 1 → ∃ x, a ≤ x ∧ x < a + G ∧ proposer x ∈ H ∧
      ∃ k Q, tr.ProposesAt (proposer x) k Q ∧ Q.slot = x) →
    ∃ u, s₀ + 2 * sp.k ≤ u ∧ u ≤ s₀ + Ld ∧ ∃ z ∈ H, z = proposer u ∧
      ∃ kP P, tr.ProposesAt z kP P ∧ P.slot = u ∧
        HZ tr H g ≤ ((tr.state z (kP + 1)).fg.σ P.root).h + 1

/-- A FrameWindow restricts to every sub-interval. -/
theorem frameWindow_sub {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}
    {lo hi lo' hi' : Time} {floor : Nat} {kindJ : Prop}
    {J : SA.Blk sp.n (List (FG.Att sp.n))}
    (hf : FrameWindow (tr := tr) (H := H) lo hi floor kindJ J)
    (hlo : lo ≤ lo') (hhi : hi' ≤ hi) :
    FrameWindow (tr := tr) (H := H) lo' hi' floor kindJ J :=
  ⟨fun y hy i h1 h2 => hf.floor_eq y hy i (hlo.trans h1) (h2.trans hhi),
    fun y hy i h1 h2 => hf.kind_iff y hy i (hlo.trans h1) (h2.trans hhi),
    fun y hy i h1 h2 => hf.root_eq y hy i (hlo.trans h1) (h2.trans hhi)⟩

end Drain

end Consensus.Goldilocks.Obligations
