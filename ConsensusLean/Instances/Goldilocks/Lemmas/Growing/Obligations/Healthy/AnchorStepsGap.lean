module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.WindowFieldsUpTo
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Rows
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.AnchorStepsGap
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The route-A anchor steps at a gap `c`, under growing faults

The growing form of `Obligations/AnchorStepsGap`. A height witness is an honest holder at a cut,
honest at that cut's time; replay states of a block agree across independently honest holders
(`Healing.Growing.σ_eq_honest_at`), so a height bound read at one holder is read at every other.

* `anchorStep_gap_at`: one step `A → X`, `A` at slot `s`, `X` at slot `s + c`, `2 ≤ c`, with the
  delivery premise `t_s + 6Δ + ΔF ≤ t_{s+c}`;
* `anchorSteps_gap_at`: the three steps of the window, anchors at `s₀ + [0, c, 2c, 3c]`, with the
  slot-free delivery premise `6Δ + ΔF ≤ 4Δ·c`. -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n}

/-- **One route-A anchor step (gap `c`)** under growing faults. Honest proposals `A` at slot `s`
and `X` at slot `s + c`, `2 ≤ c`, after the drain and by the horizon, with `H_z + 2 ≤ σ[A].h` at
a holder honest at its cut: `AnchorStepAt tr H A X`. -/
theorem anchorStep_gap_at {g ΔR a b gS ΔF : Time}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔR a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    (hs : Healing.Growing.HSSharedUpTo tr H dg gS ΔF b)
    {s c s' : Nat} (hc2 : 2 ≤ c) (hs' : s' = s + c)
    (hdel : sp.ts s + 6 * sp.Δ + ΔF ≤ sp.ts s')
    {A X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hA : Healing.Growing.HonestProposalRun tr H proposer s A)
    (hX : Healing.Growing.HonestProposalRun tr H proposer s' X)
    (hR : Healing.drainTime sp a ≤ sp.ts s) (hb : sp.ts s' ≤ b)
    (hgS : gbar gS ≤ sp.ts s + 6 * sp.Δ)
    (hh : ∃ y k, y ∈ H (tr.time k) ∧ A ∈ (tr.state y k).fg.tree ∧
      Healing.Growing.HZ tr H g + 2 ≤ ((tr.state y k).fg.σ A.root).h) :
    AnchorStepAt tr H A X := by
  sorry

/-- A height bound at a holder honest at its cut carries to a later honest proposal above it,
read at its proposer just after the proposal cut. -/
private theorem height_next_at {g ΔR a b : Time}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔR a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ)) {s s' : Nat}
    {A X : SA.Blk sp.n (List (FG.Att sp.n))}
    (hA : Healing.Growing.HonestProposalRun tr H proposer s A)
    (hX : Healing.Growing.HonestProposalRun tr H proposer s' X) (hss : s + 2 ≤ s')
    (hR : Healing.drainTime sp a ≤ sp.ts s) (hb : sp.ts s' ≤ b) {c : Nat}
    (hh : ∃ y k, y ∈ H (tr.time k) ∧ A ∈ (tr.state y k).fg.tree ∧
      c ≤ ((tr.state y k).fg.σ A.root).h) :
    ∃ y k, y ∈ H (tr.time k) ∧ X ∈ (tr.state y k).fg.tree ∧
      c ≤ ((tr.state y k).fg.σ X.root).h := by
  have hrun := hp.run
  have hnc := hp.noColl
  have hAX : Anc (tr.HonestBlocksAt H) A X :=
    anchors_chain_upTo_at hp hc hA hR hX (by omega) hb (fun h => absurd h (by omega))
  obtain ⟨kX, -, hm, ht, hXm⟩ := proposal_held_at hrun hnc hX
  have hle1 : ∀ q < kX + 1, tr.time q ≤ tr.time kX := fun _ hq => hrun.time_mono (by omega)
  have h0 := hrun.time_nonneg kX
  have hAz := Healing.Growing.mem_of_honest_anc_at hrun hnc h0 hle1 hm hAX hXm
  have hle := Healing.h_le_of_store_anc (Healing.Growing.fg_reachable_at hrun h0 hle1 hm)
    (Healing.Growing.store_anc_of_honest_anc_at hrun hnc h0 hle1 hm hAX hXm)
  obtain ⟨y, k, hy, hAy, hcy⟩ := hh
  rw [Healing.Growing.σ_eq_honest_at hrun hnc h0 hle1 hm (hrun.time_nonneg k)
    (fun _ hq => hrun.time_mono hq.le) hy hAz hAy] at hle
  exact ⟨_, kX + 1, ht ▸ hm, hXm, by omega⟩

/-- **The three route-A anchor steps (gap `c`)** under growing faults. Four honest proposals
`P i` at the slots `s₀ + [0, c, 2c, 3c]`, `2 ≤ c`, after the drain, `t_{s₀+3c} ≤ b`, the HS
premises with `6Δ + ΔF ≤ 4Δ·c` and `ḡ_S ≤ t_{s₀} + 6Δ`, and `H_z + 2 ≤ σ[P₀].h` at a holder
honest at its cut: `AnchorStepAt tr H (P i) (P (i+1))` for `i < 3`. -/
theorem anchorSteps_gap_at {g ΔR a b gS ΔF : Time}
    (hp : Healing.Growing.ResetPremisesUpTo tr H proposer dg g ΔR a b)
    (hc : Healing.Growing.CatchRun tr H g (2 * sp.Δ))
    (hs : Healing.Growing.HSSharedUpTo tr H dg gS ΔF b) {c : Nat} (hc2 : 2 ≤ c)
    (hdel : 6 * sp.Δ + ΔF ≤ 4 * sp.Δ * c) {s₀ : Nat}
    {P : Fin 4 → SA.Blk sp.n (List (FG.Att sp.n))}
    (hP : ∀ i, Healing.Growing.HonestProposalRun tr H proposer
      (s₀ + ![0, c, 2 * c, 3 * c] i) (P i))
    (hR : Healing.drainTime sp a ≤ sp.ts s₀) (hb : sp.ts (s₀ + 3 * c : Nat) ≤ b)
    (hgS : gbar gS ≤ sp.ts s₀ + 6 * sp.Δ)
    (hh₀ : ∃ y k, y ∈ H (tr.time k) ∧ P 0 ∈ (tr.state y k).fg.tree ∧
      Healing.Growing.HZ tr H g + 2 ≤ ((tr.state y k).fg.σ (P 0).root).h) :
    ∀ i : Fin 3, AnchorStepAt tr H (P i.castSucc) (P i.succ) := by
  have hP0 : Healing.Growing.HonestProposalRun tr H proposer s₀ (P 0) := by simpa using hP 0
  have hP1 : Healing.Growing.HonestProposalRun tr H proposer (s₀ + c) (P 1) := by
    simpa using hP 1
  have hP2 : Healing.Growing.HonestProposalRun tr H proposer (s₀ + 2 * c) (P 2) := by
    simpa using hP 2
  have hP3 : Healing.Growing.HonestProposalRun tr H proposer (s₀ + 3 * c) (P 3) := by
    simpa using hP 3
  have hmono : ∀ m n : Nat, m ≤ n → sp.ts m ≤ sp.ts n := fun m n h =>
    (SA.ts_le_iff sp).2 (by exact_mod_cast h)
  have hΔ := sp.toParams.hΔ
  have h1 := height_next_at hp hc hP0 hP1 (by omega) hR ((hmono _ _ (by omega)).trans hb) hh₀
  have h2 := height_next_at hp hc hP0 hP2 (by omega) hR ((hmono _ _ (by omega)).trans hb) hh₀
  have st0 := anchorStep_gap_at hp hc hs hc2 rfl (gap_delivery hdel s₀) hP0 hP1 hR
    ((hmono _ _ (by omega)).trans hb) hgS hh₀
  have st1 := anchorStep_gap_at hp hc hs hc2 (by omega) (by
      have := gap_delivery hdel (s₀ + c)
      have e : s₀ + c + c = s₀ + 2 * c := by omega
      rwa [e] at this) hP1 hP2
    (hR.trans (hmono _ _ (by omega))) ((hmono _ _ (by omega)).trans hb)
    (by linarith [hmono s₀ (s₀ + c) (by omega)]) h1
  have st2 := anchorStep_gap_at hp hc hs hc2 (by omega) (by
      have := gap_delivery hdel (s₀ + 2 * c)
      have e : s₀ + 2 * c + c = s₀ + 3 * c := by omega
      rwa [e] at this) hP2 hP3
    (hR.trans (hmono _ _ (by omega))) hb
    (by linarith [hmono s₀ (s₀ + 2 * c) (by omega)]) h2
  intro i
  fin_cases i
  exacts [st0, st1, st2]

end Consensus.Goldilocks.Obligations.Growing

end
