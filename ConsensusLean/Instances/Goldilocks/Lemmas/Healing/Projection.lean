module
public import ConsensusLean.Instances.Goldilocks.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Inclusion

public section

/-! # Goldilocks Healing: H.2 (run), AC inclusion in runs

The AC projection of a Goldilocks run is a driven AC trace (clause (a) from the FG's acceptance
tests, C0.5 (b) `Compose.ACSeesAcceptedBlocks`; clause (b) from C0.4), and `Healthy(g)` and
`Catch(2Δ)` read on it (from `Sync` over the run, `Compose.SyncProjection`, and the run's
`Catch`); then H.2 applies to the projection (`SA.ac_inclusion`), inside the honest blocks of the
run (`Compose.GoldilocksACProjection`). The claims mark H.2 (run) S: definitional in the node.

Interfaces: `projection_driven`, `projection_healthy` and `projection_catch` are open. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {g ΔF : Time}

/-- The AC projection of a Goldilocks run is driven (H.2 (run): clause (a) from the FG's
acceptance tests, clause (b) from C0.4). -/
theorem projection_driven (hrun : GoldilocksRun dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hroot : (sp.toParams.genesisBlock (goldilocksNode sp ro).genesisPayload).RootOk dg)
    (hh : tr.HealthyRun H ΔF g) : SA.Driven tr.projAC H := by
  sorry

/-- `Healthy(g)` over a run gives `Healthy(g)` on its AC projection. -/
theorem projection_healthy (hrun : GoldilocksRun dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hh : tr.HealthyRun H ΔF g) : SA.HealthyAC tr.projAC H (tr.HonestBlocks H) g := by
  sorry

/-- `Catch(κ)` over a run gives `Catch(κ)` on its AC projection (`Φ.F` is `Σ.F`). -/
theorem projection_catch (hrun : GoldilocksRun dg H tr) (hnc : Compose.NoCollRun dg tr)
    (hh : tr.HealthyRun H ΔF g) (hc : CatchRun tr H g (2 * sp.Δ)) :
    SA.CatchAC tr.projAC H (tr.HonestBlocks H) g (2 * sp.Δ) := by
  sorry

/-- **H.2 (run), AC inclusion in runs.** -/
theorem run_inclusion : RunInclusion := by
  intro sp ro dg H tr g ΔF hrun hnc hroot hh hc
  have hd := projection_driven hrun hnc hroot hh
  have hhe := projection_healthy hrun hnc hh
  have hca := projection_catch hrun hnc hh hc
  refine ⟨⟨hd, hhe, hca⟩, fun t₀ ht₀ hinv p P hP htp => ?_⟩
  have := SA.ac_inclusion sp _ ro H _ tr.projAC g t₀
    (Compose.goldilocks_ac_projection sp ro dg H tr hrun hnc) hd hhe hca ht₀ hinv p P hP.1 hP.2 htp
  exact ⟨this.1, fun hu y hy j ℓ hj ht hk => this.2 hu y hy j ℓ hj ht hk⟩

end Consensus.Goldilocks.Healing

end
