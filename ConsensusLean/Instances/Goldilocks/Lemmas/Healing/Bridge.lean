module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Reset
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention

public section

/-! # Goldilocks Healing: H.3, FG non-interference after the reset

H.3 (a) is HR.3, (b) is HR.4, and (c) is the bridge (claims H.3, status L), split here as the
paper splits it (workbench#14, healing-simple `h3-bridge.md` at `ab8459a`):

* `reset_inv`, the `Inv` half: **open on paper.** `Inv(a_z + T_b)` is not discharged by HR.4 as
  stated (its (R3) is about stored high origins at votes) nor by the per-duty join
  (phase-service §10, producer-reset-continuation §23). `h3-bridge.md` §3 isolates a sufficient
  supplier, the "RC package": for every raw (P1)/(P2)/(P3) target an accepted high seed by its
  first freeze (or the root alternative), the comparison of raw and actually returned high
  sources behind delayed certificates, and the transfer/lock join at every intervening admission;
  §4 shows that RC at `t₀ = a_z + 8Δ` gives `Inv(t₀)`. RC itself is open, and no fixed `T_b` is
  established without it, so `T_b` stays existential.
* `settled_geo`, the `Geo` half (H.3 (c3)): proved on paper (`h3-bridge.md` §5, from HS.1 and
  the proposal sandwich; the floor and the case are fixed in a settled stable phase, `F` may
  advance). It is taken here for `T_b ≥ 8Δ`, whose label alignment `r_AC(a_z + 8Δ) ≥ slot(a_z) + 3`
  is `h3-bridge.md` §1.
* `bridge` combines them at `max(T_b, 8Δ)`, by the monotonicity of `Inv` (`Inv.mono`).

Interfaces: `reset_inv` and `settled_geo` are open. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-- `Inv(t₀)` implies `Inv(t₀')` for `t₀ ≤ t₀'`: the protected blocks of `t₀'` are protected
blocks of `t₀`. -/
theorem _root_.Consensus.Goldilocks.SA.Inv.mono {sp : SAParams} {FGP : Type}
    {ro : ReplayOrder sp FGP} {tr : SA.SATrace sp FGP ro} {H : Set (Fin sp.n)}
    {U : Set (SA.Blk sp.n FGP)} {t₀ t₀' : Time} (h : SA.Inv tr H U t₀) (ht : t₀ ≤ t₀') :
    SA.Inv tr H U t₀' := by
  refine fun B j hB => h B j ?_
  rcases hB with ⟨x, hx, i, CV, hj, hl, hs⟩ | ⟨x, hx, i, hj, hl, hs⟩ | ⟨hp, hP, hs, hv⟩
  · exact Or.inl ⟨x, hx, i, CV, hj, hl, by linarith⟩
  · exact Or.inr (Or.inl ⟨x, hx, i, hj, hl, by linarith⟩)
  · exact Or.inr (Or.inr ⟨hp, hP, by linarith, hv⟩)

/-- **H.3 (c1)/(c2), retention after the reset** (open on paper: the RC package of
`h3-bridge.md` §3; with RC, `T_b = 8Δ` by §4). -/
theorem reset_inv : ∃ Tb : Nat → Time → Time → Nat → Nat → Time,
    (∀ n Δ ΔF k δt, 0 ≤ Tb n Δ ΔF k δt) ∧
    ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
      (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
      (tr : GoldilocksTrace sp ro) (g ΔF Gp : Time),
      GoldilocksRun dg H tr → HSShared tr H dg g ΔF → CatchRun tr H g (2 * sp.Δ) →
      PropPlus tr H g Gp → ∀ a, IsReset tr H g a →
        SA.Inv tr.projAC H (tr.HonestBlocks H) (a + Tb sp.n sp.Δ ΔF sp.k sp.toParams.δt) := by
  sorry

/-- **H.3 (c3), `Geo` in a settled phase** (`h3-bridge.md` §5, from HS.1): for `T_b ≥ 8Δ`, every
honest proposal of a slot `p ≥ s_AC(a_z + T_b)` whose proposal and votes lie in one settled
effective phase has `Geo(P)`. -/
theorem settled_geo {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {g ΔF Gp : Time} (hrun : GoldilocksRun dg H tr)
    (hs : HSShared tr H dg g ΔF) (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    {a Tb : Time} (ha : IsReset tr H g a) (hTb : 8 * sp.Δ ≤ Tb) (p : Nat)
    (P : SA.Blk sp.n (List (FG.Att sp.n))) (hP : HonestProposalRun tr H p P)
    (htp : a + Tb + 2 * SA.Θ sp + 8 * sp.Δ ≤ sp.ts p) (hph : InSettledPhase tr H g p) :
    SA.Geo tr.projAC H p P := by
  sorry

/-- **H.3 (c), the bridge**, from `reset_inv` and `settled_geo`. -/
theorem bridge : ∃ Tb : Nat → Time → Time → Nat → Nat → Time, (∀ n Δ ΔF k δt, 0 ≤ Tb n Δ ΔF k δt) ∧
    ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
      (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
      (tr : GoldilocksTrace sp ro) (g ΔF Gp : Time),
      GoldilocksRun dg H tr → HSShared tr H dg g ΔF → CatchRun tr H g (2 * sp.Δ) →
      PropPlus tr H g Gp → ∀ a, IsReset tr H g a →
        BridgeAt tr H g a (Tb sp.n sp.Δ ΔF sp.k sp.toParams.δt) := by
  obtain ⟨Tb, hTb, hinv⟩ := reset_inv
  refine ⟨fun n Δ ΔF k δt => max (Tb n Δ ΔF k δt) (8 * Δ), fun n Δ ΔF k δt =>
    (hTb n Δ ΔF k δt).trans (le_max_left _ _), fun sp ro dg H tr g ΔF Gp hrun hs hc hp a ha =>
    ⟨(hinv sp ro dg H tr g ΔF Gp hrun hs hc hp a ha).mono (add_le_add_right (le_max_left _ _) a),
      fun p P hP htp hph => settled_geo hrun hs hc hp ha (le_max_right _ _) p P hP htp hph⟩⟩

/-- **H.3, FG non-interference after the reset.** -/
theorem non_interference : NonInterference := by
  obtain ⟨Tb, hTb, hb⟩ := bridge
  refine ⟨Tb, hTb, fun sp ro dg H tr g ΔF Gp hrun hs hc hp => ?_⟩
  have hr := reset_existence sp ro dg H tr g ΔF Gp hrun hs hc hp
  obtain ⟨a, ha⟩ := hr.2.2.1
  exact ⟨a, ha, (hr.2.2.2.1 a ha).trans hr.2.2.2.2.1,
    height_scoped_retention sp ro dg H tr g ΔF hrun hs.healthy hs.noColl a ha,
    hb sp ro dg H tr g ΔF Gp hrun hs hc hp a ha⟩

end Consensus.Goldilocks.Healing

end
