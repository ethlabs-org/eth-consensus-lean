module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Growing.Run

public section

/-! # Consequences of the lag-indexed reset bound

No uniform lag bound is assumed: choosing the per-time frontier itself as the lag always
satisfies `LagWithin`, since the cohort frontier is a natural number.
-/

namespace Consensus.Goldilocks.Healing.Growing

/-- The per-time frontier is always an upper bound on its lag behind any cohort. -/
theorem lagWithin_hz {P : Params} {A : NodeAC P} (tr : RunTrace A)
    (H : Time → Set (Fin P.n)) (g D : Time) : LagWithin tr H g D (HZ tr H g) :=
  Nat.le_add_left _ _

/-- HR.3's lag-indexed bound implies unconditional reset existence under its shared premises.
This does not claim any uniform bound on the cohort lag. -/
theorem ResetExistence.exists_reset (h : ResetExistence)
    {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
    {proposer : Nat → Fin sp.n}
    {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
    {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF Gp : Time}
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hs : HSShared tr H dg g ΔF) (hc : CatchRun tr H g (2 * sp.Δ))
    (hp : PropPlus tr H proposer g Gp) : ∃ a, IsReset tr H g a := by
  obtain ⟨_, _, hcount, _⟩ := h sp ro proposer dg H tr g ΔF Gp hrun hs hc hp
  obtain ⟨a, ha, _⟩ := hcount (HZ tr H g) (resetWindow sp g ΔF Gp (HZ tr H g))
    le_rfl (lagWithin_hz tr H g _)
  exact ⟨a, ha⟩

end Consensus.Goldilocks.Healing.Growing

end
