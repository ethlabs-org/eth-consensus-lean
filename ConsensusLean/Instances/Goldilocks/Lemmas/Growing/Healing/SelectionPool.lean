module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.SupplierFrames

public section

/-! # The reader-local part of operational update selection

The pool and live-lock hypotheses belong to one honest update. Only receiving-node
execution is retained; no reset, cache-origin or service invariant is made static.
-/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- The update handler's post-state conclusions follow from its selected confirmation.
This is local execution, independent of the historical source of the pool or locks. -/
theorem update_selection_of_confirmation_at
    (hrun : Consensus.Goldilocks.Growing.GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) {y : Fin sp.n} {j u : Nat}
    (hy : y ∈ H (tr.time j)) {ell : ACLabel (goldilocksNode sp ro)}
    {P : SA.Blk sp.n (List (FG.Att sp.n))}
    (hu : SA.UpdateAt tr.projAC y j u ell)
    (hconf : SA.getConfirmation sp (tr.projAC.state y j) ell.frame u = some P)
    (hnv : ¬ SA.conflictsWithLock sp (tr.projAC.state y j).locks ell.frame (tr.time j) P) :
    tr.projAC.post j = SA.updateConfirmation sp (tr.projAC.state y j) ell.frame (tr.time j) u ∧
      (tr.projAC.post j).latestConfirmed =
        (SA.updateLatestConfirmed sp (tr.projAC.state y j) ell.frame P).latestConfirmed := by
  have hr := (Compose.goldilocks_ac_projection sp ro dg (H (tr.time j))
    (tr.upTo (tr.time j)) proposer (hrun.upTo (hrun.time_nonneg j))
    (hnc.upTo (tr.time j))).localRun
  rw [RunTrace.upTo_projAC] at hr
  have hu' : SA.UpdateAt (tr.projAC.upTo (tr.time j)) y j u ell := by
    refine ⟨(Trace.upTo_callAt _).mpr ⟨le_rfl, hu.1⟩, hu.2.1, hu.2.2.1, ?_⟩
    simpa only [Trace.upTo_state tr.projAC y (fun _ hk => hrun.time_mono hk.le),
      Trace.upTo_time] using hu.2.2.2
  have he := hr.exec j ell hu'.1.2 (hu'.1.1 ▸ hy)
  rw [hu'.1.1, hu.2.1] at he
  rw [Trace.upTo_state tr.projAC y (fun _ hk => hrun.time_mono hk.le)] at he
  rw [Trace.upTo_post, Trace.upTo_time] at he
  have h1 : tr.projAC.post j =
      (SA.acOnTick sp y (tr.projAC.state y j) ell.frame (tr.time j)).1 :=
    (congrArg Prod.fst he).symm
  have ht : tr.time j = sp.ts u + 6 * sp.Δ := hu.2.2.1
  have hslot : sp.slot (tr.time j) = u + 1 := by
    rw [ht]
    exact SA.slot_of_mem sp (u + 1)
      (by simp only [SAParams.ts]; push_cast; linarith only [sp.toParams.hΔ])
      (by simp only [SAParams.ts]; push_cast; linarith only [sp.toParams.hΔ])
  have hpost : tr.projAC.post j =
      SA.updateConfirmation sp (tr.projAC.state y j) ell.frame (tr.time j) u := by
    rw [h1]
    unfold SA.acOnTick
    dsimp only
    have hn1 : ¬ tr.time j = sp.ts (u + 1 : Nat) + sp.Δ := by
      rw [ht]; simp only [SAParams.ts]; push_cast; linarith only [sp.toParams.hΔ]
    have h2 : tr.time j = sp.ts (u + 1 : Nat) + 2 * sp.Δ := by
      rw [ht]; simp only [SAParams.ts]; push_cast; ring
    have hj : SA.joined sp (tr.projAC.state y j) (tr.time j) := hu.2.2.2
    have hc2 : (tr.time j = sp.ts (u + 1 : Nat) + 2 * sp.Δ ∧ 0 < u + 1) = True :=
      eq_true ⟨h2, Nat.succ_pos u⟩
    rw [hslot]
    simp only [hj, not_true_eq_false, hn1, hc2, ↓reduceIte, Nat.add_sub_cancel]
  refine ⟨hpost, ?_⟩
  rw [hpost]
  unfold SA.updateConfirmation
  simp only [hconf, hnv, ↓reduceIte]
  unfold SA.updateLatestConfirmed
  split <;> rfl

end Consensus.Goldilocks.Healing.Growing

end
