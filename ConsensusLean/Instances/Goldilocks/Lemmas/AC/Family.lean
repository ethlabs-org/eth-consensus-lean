module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Family
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Locks
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

/-- The ordinary unlock satisfies the release relation without a keep hypothesis. -/
theorem unlocksRel_unlock {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (L : Set Lock)
    (t : Time) (s : Int) (V : View sp.n) :
    UnlocksRel sp L Φ t s V (unlock sp L Φ t s V) := by
  refine ⟨?_, fun l hl => ⟨l, hl, rfl, rfl, rfl⟩, ?_⟩
  · intro l hl
    obtain ⟨l₀, hl₀, B, hB, hr, heq⟩ := hl
    have ht : ∃ T ∈ Φ.tree, T.root = l.block := by
      rw [heq]
      split_ifs
      · exact ⟨_, (unlockTarget_anc sp hΦ V s hB).1, rfl⟩
      · exact ⟨B, hB, hr⟩
    obtain ⟨T, hT, hrT⟩ := ht
    exact ⟨l, ⟨l₀, hl₀, B, hB, hr, heq⟩, rfl, rfl, rfl,
      T, hT, hrT, T, hT, hrT, .refl⟩
  · intro l hl hs
    obtain ⟨l₀, hl₀, B, hB, hr, ht, heq⟩ := hl
    have hm : l ∈ liveLocks sp L Φ t := ⟨l₀, hl₀, B, hB, hr, ht, heq⟩
    have hv := (viableAncestor_anc hΦ hB).1
    have hr' : (Φ.viableAncestor B).root = l.block := by rw [heq]
    refine ⟨l, hm, Φ.viableAncestor B, hv, hr', ?_⟩
    rw [ite_eq_right (not_lt.mpr hs)]

/-- The concrete tick computation, used only to discharge the fieldwise seams. -/
theorem update_post (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {c s : Nat}
    {ell : ACLabel (goldilocksSA sp FGP ro)} (hu : UpdateAt tr y c s ell) :
    tr.post c = updateConfirmation sp (tr.state y c) ell.frame (tr.time c) s := by
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

/-- The record formula is shared by every write mode. -/
theorem update_record_formula (m : WriteMode) (pre : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (s : Nat) : UpdateRecord pre (updateConfirmationM sp m pre Φ t s) Φ t s := by
  classical
  unfold UpdateRecord updateConfirmationM updateLatestConfirmed
  cases getConfirmation sp pre Φ s <;> simp only [Option.map_none, Option.map_some]
  · exact ⟨True.intro, True.intro⟩
  · split_ifs <;> exact ⟨rfl, rfl⟩

/-- The update frame is independent of the selected write mode. -/
theorem update_frame_formula (m : WriteMode) (pre : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (s : Nat) : UpdateFrame pre (updateConfirmationM sp m pre Φ t s) := by
  classical
  unfold UpdateFrame updateConfirmationM updateLatestConfirmed
  cases getConfirmation sp pre Φ s
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · dsimp only
    split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The concrete run discharges only the record conjunct requested by record consumers. -/
theorem update_record_at (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) :
    UpdateRecordAt tr H := by
  intro y hy c s ell hu
  rw [update_post hr hy hu]
  exact update_record_formula (WriteMode.parent sp) _ _ _ _

/-- Assemble only the facts consumed by the update-to-record slice. -/
theorem goldilocksContract (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) :
    ACContract (goldilocksFamily sp FGP ro) H tr where
  frame := fun _ hy _ _ hc => (frameIn_of_callAt hr hy hc).1
  updateRecord := update_record_at hr

end Consensus.Goldilocks.SA

end
