module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Reset

public section

/-! # Goldilocks Healing: H.4, healing of the available chain, assembled

H.4 is a conditional assembly (claims H.4, status S given its uses): with the bridge
(`BridgeAt`, H.3 (c)) for the reset `a_z` and `T_b ≥ 0`, `Inv(t₀)` holds for
`t₀ = a_z + T_b ≥ ḡ` (`a_z > c_z > ḡ`, HR.1 (c), HR.3 (a)), and `t₀ + 2Θ + 8Δ ≤ T_heal` by
HR.3 (c)'s bound; then H.2 (run) (ii) gives (i), and (ii), (iii) follow from (i). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {tr : GoldilocksTrace sp ro} {H : Set (Fin sp.n)}

/-- Inclusion from `t₁` gives inclusion from every later `t₂`. -/
theorem IncludedFrom.mono {t₁ t₂ : Time} {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (h : IncludedFrom tr H t₁ P) (ht : t₁ ≤ t₂) : IncludedFrom tr H t₂ P := by
  intro y hy j ℓ hj htj htick
  exact h y hy j ℓ hj (ht.trans htj) fun he => htick (le_antisymm (he ▸ ht) htj)

/-- **H.4, healing of the available chain, assembled.** -/
theorem available_healing : AvailableHealing := by
  intro sp ro dg H tr g ΔF Gp hrun hs hc hp a Tb ha hTb hb
  have hr := reset_existence sp ro dg H tr g ΔF Gp hrun hs hc hp
  have haz : cutZ sp.toParams g < a :=
    (cut_and_reset sp ro dg H tr g ΔF hrun hs.healthy hs.noColl).2.2.2.2 a ha |>.1
  have hle : a ≤ gbar g + 24 * sp.Δ + 12 * C_HS sp ΔF Gp :=
    (hr.2.2.2.1 a ha).trans hr.2.2.2.2.1
  have hg : gbar g ≤ a + Tb := by linarith [lt_cutZ sp g, sp.toParams.hΔ]
  have hincl := (run_inclusion sp ro dg H tr g ΔF hrun hs.noColl hs.genesisRoot hs.healthy hc).2
    (a + Tb) hg hb.1
  have hi : ∀ (p : Nat) P, HonestProposalRun tr H p P → T_heal sp g ΔF Gp Tb ≤ sp.ts p →
      Unanimous tr H p P → IncludedFrom tr H (sp.ts p + 6 * sp.Δ) P := fun p P hP htp hu =>
    (hincl p P hP (by simp only [T_heal] at htp; linarith)).2 hu
  refine ⟨T_heal_eq sp g ΔF Gp Tb, hi, fun B hB t ht => ?_, fun hU p P hP htp => hi p P hP htp
    (hU p P hP htp)⟩
  obtain ⟨p, P, h₁, h₂, hP, hu⟩ := hB t ht
  exact ⟨p, P, h₁, h₂, hP, (hi p P hP (ht.trans h₁) hu).mono (by linarith)⟩

end Consensus.Goldilocks.Healing

end
