module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Reset
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention

public section

/-! # Goldilocks Healing: H.3, FG non-interference after the reset

H.3 (a) is HR.3, (b) is HR.4, and (c) is the bridge, which is **open on paper** (claims H.3,
status L), in three parts:
(c1) time scope: every protected block of a label `≥ r_AC(a_z + T_b)` is high, an ancestor of a
high origin, or at or below `fc_root`;
(c2) (R3) extended from high fast origins to (P2) slow origins and (P3) unanimous proposals, from
the stored block to the raw selected block, and from votes to every event (the conditional duty
join of phase-service §10 / producer-reset-continuation §23 is a per-duty conclusion and does
not close it);
(c3) `Geo` inside a settled phase, from HS.1.
The claims' candidate is `T_b = 8Δ`; it is not claimed, so `bridge` keeps `T_b` existential.

Interface: `bridge` (H.3 (c)) is open. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-- **H.3 (c), the bridge** (open on paper: (c1)–(c3) above). -/
theorem bridge : ∃ Tb : Nat → Time → Time → Nat → Nat → Time, (∀ n Δ ΔF k δt, 0 ≤ Tb n Δ ΔF k δt) ∧
    ∀ (sp : SAParams) (ro : ReplayOrder sp (List (FG.Att sp.n)))
      (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (H : Set (Fin sp.n))
      (tr : GoldilocksTrace sp ro) (g ΔF Gp : Time),
      GoldilocksRun dg H tr → HSShared tr H dg g ΔF → CatchRun tr H g (2 * sp.Δ) →
      PropPlus tr H g Gp → ∀ a, IsReset tr H g a →
        BridgeAt tr H g a (Tb sp.n sp.Δ ΔF sp.k sp.toParams.δt) := by
  sorry

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
