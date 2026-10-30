module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Phase

public section

/-! # Goldilocks Healing: HR.3, reset existence

HR.3 over a Goldilocks run under the HS shared premises, `Catch(2Δ)` and `Prop⁺(G_p)`
(claims HR.3, status S given HS.0 and HS.5):
(a) `c_z > ḡ + 8Δ` (`lt_cutZ`), so HS.0 (`Settle(Δ)`, `settle`) applies at every `u ≥ c_z`;
(b) HS.5 (`Producer(A)`, `producer`): from a settled `w`, the effective phase changes by `w + A`;
(c) the count (`reset_count`, `producer-reset-continuation.md` §§14–15): from `c_z`, every
`Δ + A` the phase changes (settle within `Δ`, then produce within `A`); at most three phases per
frontier value (HR.2) and two rises above `H_z` reach a block of state height `H_z + 2`, whose
chain carries an honest row at `H_z + 1` (HR.1 (b)); so the reset exists by `c_z + 6(Δ + A)`.
The reset is unique (`IsReset` is a least time), and the bound's closed forms are in `Arith`.

`settle` and `producer` are HS.0 and HS.5 (claims §"Healing: phase service"; phase-service.md
§§1–8, the author's paper results with Astra's review applied), as the use in HR.3 needs them
(`κ = 2Δ`, `G = G_p`); they become the HS statements' theorems when those are stated.

Interfaces: `settle`, `producer` and `reset_count` are open. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-- **HS.0, bounded settling** (`Settle(Δ)`, with `κ = 2Δ`): from `u ≥ ḡ + 8Δ`, by `u + Δ`
the effective phase after all events at `u` has changed or the run is settled at `u + Δ`. -/
theorem settle {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {g ΔF : Time} (hrun : GoldilocksRun dg H tr)
    (hs : HSShared tr H dg g ΔF) (hc : CatchRun tr H g (2 * sp.Δ)) (u : Time)
    (hu : gbar g + 8 * sp.Δ ≤ u) (j j' : Nat) (hj : FirstCutAfter tr j u)
    (hj' : tr.FirstCutFrom j' (u + sp.Δ)) :
    PhaseChanged tr.projFG H j j' ∨ SettledAt tr H g (2 * sp.Δ) (u + sp.Δ) := by
  sorry

/-- **HS.5, `Producer(A)`** (with `κ = 2Δ`, `G = G_p`): from a settled `w`, the effective phase
has changed by `w + A_HS` (after all events there). -/
theorem producer {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {g ΔF Gp : Time} (hrun : GoldilocksRun dg H tr)
    (hs : HSShared tr H dg g ΔF) (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp)
    (w : Time) (hw : SettledAt tr H g (2 * sp.Δ) w) (j j' : Nat) (hj : tr.FirstCutFrom j w)
    (hj' : FirstCutAfter tr j' (w + A_HS sp ΔF Gp)) : PhaseChanged tr.projFG H j j' := by
  sorry

/-- **The reset count** (HR.3 (c)): the reset exists by `c_z + 6(Δ + A_HS)`. -/
theorem reset_count {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
    {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
    {tr : GoldilocksTrace sp ro} {g ΔF Gp : Time} (hrun : GoldilocksRun dg H tr)
    (hs : HSShared tr H dg g ΔF) (hc : CatchRun tr H g (2 * sp.Δ)) (hp : PropPlus tr H g Gp) :
    ∃ a, IsReset tr H g a ∧ a ≤ cutZ sp.toParams g + 6 * (sp.Δ + A_HS sp ΔF Gp) := by
  sorry

/-- The reset is unique. -/
theorem IsReset.eq {P : Params} {A : NodeAC P} {tr : RunTrace A} {H : Set (Fin P.n)} {g a a' : Time}
    (h : IsReset tr H g a) (h' : IsReset tr H g a') : a = a' := by
  obtain ⟨y, hy, k, att, hk, hh, hka⟩ := h.1
  obtain ⟨y', hy', k', att', hk', hh', hka'⟩ := h'.1
  exact le_antisymm ((h.2 y' hy' k' att' hk' hh').trans hka'.le)
    ((h'.2 y hy k att hk hh).trans hka.le)

/-- **HR.3, reset existence.** -/
theorem reset_existence : ResetExistence := by
  intro sp ro dg H tr g ΔF Gp hrun hs hc hp
  obtain ⟨a, ha, hle⟩ := reset_count hrun hs hc hp
  refine ⟨⟨lt_cutZ sp g, fun u hu j j' hj hj' =>
      settle hrun hs hc u (by linarith [lt_cutZ sp g]) j j' hj hj'⟩,
    fun w hw j j' hj hj' => producer hrun hs hc hp w hw j j' hj hj', ⟨a, ha⟩,
    fun a' ha' => ha'.eq ha ▸ hle, cutZ_add_le sp g ΔF Gp, reset_bound_eq sp g ΔF Gp,
    C_HS_eq sp ΔF Gp⟩

end Consensus.Goldilocks.Healing

end
