module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.WindowFieldsUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs

public section

/-! # The seed height of the route-A window, under growing faults

The growing form of `Obligations/WindowSeed`: an honest seed proposal `Q` at a slot `u` after the
drain, and an honest proposal `P₀` at a slot `s₀ ≥ u + δt` by the horizon `b`, give
`H_z + 2 ≤ σ[P₀].h` at every holder of `P₀` honest at an observation time after the holder's
earlier cuts (`seed_height_at`), and at the proposer of `P₀` just after its proposal cut
(`seed_height_held_at`, the height witness of `anchorSteps_gap_at`). -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **The seed height** under growing faults. With the finite reset premises, Catch(2Δ), the HS
premises through `b` (`ḡ_S ≤ t_u + 6Δ`), an honest seed proposal `Q` at slot `u > 0` with
`drainTime a ≤ t_u` and `ḡ + 4Δ ≤ t_u`, and an honest proposal `P₀` at slot `s₀ ≥ u + δt` with
`t_{s₀} ≤ b` (`2 ≤ δt`): every holder of `P₀` honest at an observation time `t` after its earlier
cuts has `H_z + 2 ≤ σ[P₀].h`. -/
theorem seed_height_at {g ΔR a b gS ΔF : Time}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔR a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    (hs : Healing.Growing.HSSharedUpTo tr H dg gS ΔF b)
    (hδ : 2 ≤ sp.toParams.fg.δt) {u s₀ : Nat} {Q P₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (hQ : Healing.Growing.HonestProposalRun tr H proposer u Q) (hu : 0 < u)
    (hR : Healing.drainTime sp a ≤ sp.ts u) (hgu : gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hP₀ : Healing.Growing.HonestProposalRun tr H proposer s₀ P₀)
    (hus : u + sp.toParams.fg.δt ≤ s₀) (hb : sp.ts s₀ ≤ b)
    (hgS : gbar gS ≤ sp.ts u + 6 * sp.Δ) :
    ∀ y k t, 0 ≤ t → (∀ q < k, tr.time q ≤ t) → y ∈ H t → P₀ ∈ (tr.state y k).fg.tree →
      Healing.Growing.HZ tr H g + 2 ≤ ((tr.state y k).fg.σ P₀.root).h := by
  sorry

/-- `seed_height_at` in the form of the height premise of `anchorSteps_gap_at`: the proposer of
`P₀` holds `P₀` just after its proposal cut, honest at that cut, at height at least `H_z + 2`. -/
theorem seed_height_held_at {g ΔR a b gS ΔF : Time}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔR a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    (hs : Healing.Growing.HSSharedUpTo tr H dg gS ΔF b)
    (hδ : 2 ≤ sp.toParams.fg.δt) {u s₀ : Nat} {Q P₀ : SA.Blk sp.n (List (FG.Att sp.n))}
    (hQ : Healing.Growing.HonestProposalRun tr H proposer u Q) (hu : 0 < u)
    (hR : Healing.drainTime sp a ≤ sp.ts u) (hgu : gbar g + 4 * sp.Δ ≤ sp.ts u)
    (hP₀ : Healing.Growing.HonestProposalRun tr H proposer s₀ P₀)
    (hus : u + sp.toParams.fg.δt ≤ s₀) (hb : sp.ts s₀ ≤ b)
    (hgS : gbar gS ≤ sp.ts u + 6 * sp.Δ) :
    ∃ y k, y ∈ H (tr.time k) ∧ P₀ ∈ (tr.state y k).fg.tree ∧
      Healing.Growing.HZ tr H g + 2 ≤ ((tr.state y k).fg.σ P₀.root).h := by
  obtain ⟨kX, -, hm, ht, hXm⟩ := proposal_held_at hp.run hp.noColl hP₀
  refine ⟨_, kX + 1, ht ▸ hm, hXm, seed_height_at hp hc hs hδ hQ hu hR hgu hP₀ hus hb hgS _
    (kX + 1) (tr.time kX) (hp.run.time_nonneg kX)
    (fun _ hq => hp.run.time_mono (by omega)) hm hXm⟩

end Consensus.Goldilocks.Obligations.Growing

end
