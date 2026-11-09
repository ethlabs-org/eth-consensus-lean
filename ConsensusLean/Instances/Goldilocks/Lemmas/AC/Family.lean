module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Lemmas.Tactic.Linarith
meta import Mathlib.Tactic.Ring

public section

/-! # Discharging the update seam for the SA

The scheduled tick computation is isolated here, rather than repeated by consumers of the
projected trace. This does not assert that a candidate's projection executes the SA.
-/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}

/-- The SA's update tick computes the characterized post-state. -/
theorem update_characterization (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) :
    UpdateCharacterization tr H := by
  intro y hy c s ell hu
  have hΔ := sp.toParams.hΔ
  have hts : sp.ts (s + 1 : Nat) = sp.ts s + 4 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  have hslot : sp.slot (tr.time c) = s + 1 := slot_of_mem sp (s + 1)
    (by rw [hu.2.2.1, hts]; linarith)
    (by rw [hu.2.2.1, show sp.ts (s + 1 + 1 : Nat) =
      sp.ts (s + 1 : Nat) + 4 * sp.Δ by simp only [SAParams.ts]; push_cast; ring, hts]; linarith)
  have he := hr.exec c ell hu.1.2 (hu.1.1 ▸ hy)
  rw [hu.1.1, hu.2.1] at he
  have hpost : tr.post c = (acOnTick sp y (tr.state y c) ell.frame (tr.time c)).1 :=
    (congrArg Prod.fst he).symm
  rw [hpost]
  unfold acOnTick
  dsimp only
  rw [hslot]
  have ht1 : ¬ tr.time c = sp.ts (s + 1 : Nat) + sp.Δ := by
    rw [hu.2.2.1, hts]; linarith
  have ht2 : tr.time c = sp.ts (s + 1 : Nat) + 2 * sp.Δ := by
    rw [hu.2.2.1, hts]; ring
  rw [ite_eq_right (not_not.mpr hu.2.2.2), ite_eq_right ht1,
    ite_eq_left ⟨ht2, Nat.succ_pos s⟩]
  simp only [Nat.add_sub_cancel]

/-- Assemble only the facts consumed by the update-to-record slice. -/
theorem goldilocksContract (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) :
    ACContract (goldilocksFamily sp FGP ro) H tr where
  frame := fun _ hy _ _ hc => (frameIn_of_callAt hr hy hc).1
  update := update_characterization hr

end Consensus.Goldilocks.SA

end
