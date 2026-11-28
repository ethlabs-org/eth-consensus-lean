module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.Setting
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: the constants

The time arithmetic of the healing statements: the reset cut `c_z = t_{slot(ḡ)+3}` lies in
`(ḡ + 8Δ, ḡ + 12Δ]` (HR.1, HR.3 (a)), the reset bound `c_z + 6(Δ + A) ≤ ḡ + 24Δ + 12C` and its
closed form (HR.3 (c)). -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams gbar)

variable (sp : ACParams)

theorem cutZ_eq (g : Time) : cutZ sp.toParams g = sp.ts (sp.slot (gbar g) + 3 : Nat) :=
  sp.slotTime_eq _

/-- `c_z ≤ ḡ + 12Δ` (HR.1). -/
theorem cutZ_le (g : Time) : cutZ sp.toParams g ≤ gbar g + 12 * sp.Δ := by
  have h := (AC.ts_le_iff_le_slot sp (AC.gbar_nonneg g) (sp.slot (gbar g))).mpr le_rfl
  rw [cutZ_eq]
  simp only [ACParams.ts] at h ⊢
  push_cast
  linarith

/-- From a readiness duration `c ≥ 9Δ`, the frame base `max ready 0 + 4Δ`, with
`ready = max g 0 + c + 1`, is past the snapshot call `c_z + Δ` (`snapshotCall_of_awake`). -/
theorem cutZ_add_lt_ready_add (g c : Time) (hc : 9 * sp.Δ ≤ c) :
    cutZ sp.toParams g + sp.Δ + 1 ≤ max (max g 0 + c + 1) 0 + 4 * sp.Δ := by
  have hz := cutZ_le sp g
  unfold gbar at hz
  linarith [le_max_left (max g 0 + c + 1) 0]

/-- `ḡ + 8Δ < c_z` (HR.3 (a)). -/
theorem lt_cutZ (g : Time) : gbar g + 8 * sp.Δ < cutZ sp.toParams g := by
  have h : ¬ sp.ts (sp.slot (gbar g) + 1 : Int) ≤ gbar g := fun h => by
    have := (AC.ts_le_iff_le_slot sp (AC.gbar_nonneg g) _).mp h
    omega
  rw [cutZ_eq]
  simp only [ACParams.ts, not_le] at h ⊢
  push_cast at h ⊢
  linarith

/-- `ḡ` lies below every time at or after the high-origin cutoff `c_z`. -/
theorem gbar_le_of_cutZ_le {g t : Time} (h : cutZ sp.toParams g ≤ t) : gbar g ≤ t :=
  ((le_add_of_nonneg_right (mul_nonneg (Nat.ofNat_nonneg _) sp.toParams.hΔ.le)).trans
    (lt_cutZ sp g).le).trans h

end Consensus.Goldilocks.Healing

end
