module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Inclusion
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Reset

public section

/-! # Goldilocks Healing: H.4, healing of the available chain, assembled

H.4 is a conditional assembly (claims H.4, status S given its uses; proved, `available_healing`,
with HR.3 from `reset_existence`): with the bridge
(`BridgeAt`, H.3 (c)) for the reset `a_z` and `T_b ≥ 0`, `Inv(t₀)` holds for
`t₀ = a_z + T_b ≥ ḡ` (`a_z > c_z > ḡ`, HR.1 (c), HR.3 (a)), and `t₀ + 2Θ + 8Δ ≤ T_heal` by
HR.3 (c)'s bound; then H.2 (run) (ii) gives (i), and the claims' (ii), (iii) follow from (i)
(`available_healing_windows`, `available_healing_all`). The bridge is a premise (`BridgeAt`).
`IncludedFrom` is monotone in its start time (`IncludedFrom.mono`). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}

/-- Inclusion from `t₁` gives inclusion from every later `t₂`. -/
theorem IncludedFrom.mono {t₁ t₂ : Time} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : IncludedFrom tr H t₁ P) (ht : t₁ ≤ t₂) : IncludedFrom tr H t₂ P := by
  intro y hy j ℓ hj htj htick
  exact h y hy j ℓ hj (ht.trans htj) fun he => htick (le_antisymm (he ▸ ht) htj)

/-- **H.4 (ii) from (i)**: if every unanimous honest proposal from `T` on is included `6Δ` after
it, and from `T` on every window `[t, t + B]` has a unanimous honest proposal, then for every
`t ≥ T` some honest proposal released in `[t, t + B]` is included from `t + B + 6Δ` on. -/
theorem available_healing_windows {proposer : Nat → Fin sp.n} {T B : Time}
    (hi : ∀ (p : Nat) P, HonestProposalRun tr H proposer p P → T ≤ sp.ts p →
      Unanimous tr H p P → IncludedFrom tr H (sp.ts p + 6 * sp.Δ) P)
    (hB : ∀ t, T ≤ t → ∃ (p : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n))), t ≤ sp.ts p ∧
      sp.ts p ≤ t + B ∧ HonestProposalRun tr H proposer p P ∧ Unanimous tr H p P) :
    ∀ t, T ≤ t → ∃ (p : Nat) (P : SA.Blk sp.n (List (FG.Att sp.n))), t ≤ sp.ts p ∧
      sp.ts p ≤ t + B ∧ HonestProposalRun tr H proposer p P ∧
        IncludedFrom tr H (t + B + 6 * sp.Δ) P := fun t ht => by
  obtain ⟨p, P, h₁, h₂, hP, hu⟩ := hB t ht
  exact ⟨p, P, h₁, h₂, hP, (hi p P hP (ht.trans h₁) hu).mono (by linarith)⟩

/-- **H.4 (iii) from (i)**: if every unanimous honest proposal from `T` on is included `6Δ` after
it, and every honest proposal from `T` on is unanimous, then every honest proposal from `T` on is
included `6Δ` after it. -/
theorem available_healing_all {proposer : Nat → Fin sp.n} {T : Time}
    (hi : ∀ (p : Nat) P, HonestProposalRun tr H proposer p P → T ≤ sp.ts p →
      Unanimous tr H p P → IncludedFrom tr H (sp.ts p + 6 * sp.Δ) P)
    (hU : ∀ (p : Nat) P, HonestProposalRun tr H proposer p P → T ≤ sp.ts p →
      Unanimous tr H p P) :
    ∀ (p : Nat) P, HonestProposalRun tr H proposer p P → T ≤ sp.ts p →
      IncludedFrom tr H (sp.ts p + 6 * sp.Δ) P := fun p P hP htp =>
  hi p P hP htp (hU p P hP htp)

/-- **H.4, healing of the available chain, assembled.** -/
theorem available_healing : AvailableHealing := by
  intro sp ro proposer dg H tr g ΔF Gp hrun hs hc hp a Tb ha hTb hb
  have hr := reset_existence sp ro proposer dg H tr g ΔF Gp hrun hs hc hp
  have haz : cutZ sp.toParams g < a :=
    (cut_and_reset sp ro proposer dg H tr g ΔF hrun hs.healthy hs.noColl).2.2.2.2 a ha |>.1
  have hle : a ≤ gbar g + 24 * sp.Δ + 12 * C_HS sp ΔF Gp :=
    (hr.2.2.2.1 a ha).trans hr.2.2.2.2.1
  have hg : gbar g ≤ a + Tb := by linarith [lt_cutZ sp g, sp.toParams.hΔ, hTb]
  have hincl := (run_inclusion sp ro proposer dg H tr g ΔF
    hrun hs.noColl hs.genesisRoot hs.healthy hc).2
    (a + Tb) hg hb.1
  intro p P hP htp hu
  exact (hincl p P hP (by simp only [T_heal] at htp; linarith)).2 hu

end Consensus.Goldilocks.Healing

end
