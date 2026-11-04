module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule

public section

/-! # Goldilocks Healing: the constants

The time arithmetic of the healing statements: the reset cut `c_z = t_{slot(ḡ)+3}` lies in
`(ḡ + 8Δ, ḡ + 12Δ]` (HR.1, HR.3 (a)), the reset bound `c_z + 6(Δ + A) ≤ ḡ + 24Δ + 12C` and its
closed form (HR.3 (c)), and the closed form of `T_heal` (H.4). -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams gbar)

variable (sp : SAParams)

theorem gbar_nonneg (g : Time) : 0 ≤ gbar g := le_max_right g 0

theorem le_gbar (g : Time) : g ≤ gbar g := le_max_left g 0

theorem cutZ_eq (g : Time) : cutZ sp.toParams g = sp.ts (sp.slot (gbar g) + 3 : Nat) :=
  sp.slotTime_eq _

/-- `c_z ≤ ḡ + 12Δ` (HR.1). -/
theorem cutZ_le (g : Time) : cutZ sp.toParams g ≤ gbar g + 12 * sp.Δ := by
  have h := (SA.ts_le_iff_le_slot sp (gbar_nonneg g) (sp.slot (gbar g))).mpr le_rfl
  rw [cutZ_eq]
  simp only [SAParams.ts] at h ⊢
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
    have := (SA.ts_le_iff_le_slot sp (gbar_nonneg g) _).mp h
    omega
  rw [cutZ_eq]
  simp only [SAParams.ts, not_le] at h ⊢
  push_cast at h ⊢
  linarith

/-- `C_HS = (8k + 49 + 4δ_t)Δ + Δ_F + 3G` (HR.3 (c)). -/
theorem C_HS_eq (ΔF G : Time) :
    C_HS sp ΔF G = (8 * (sp.k : Time) + 49 + 4 * (sp.toParams.δt : Time)) * sp.Δ + ΔF + 3 * G := by
  simp only [C_HS, D_HS]
  ring

/-- `c_z + 6(Δ + A_HS) ≤ ḡ + 24Δ + 12C_HS` (HR.3 (c)). -/
theorem cutZ_add_le (g ΔF G : Time) :
    cutZ sp.toParams g + 6 * (sp.Δ + A_HS sp ΔF G) ≤ gbar g + 24 * sp.Δ + 12 * C_HS sp ΔF G := by
  have := cutZ_le sp g
  simp only [A_HS]
  linarith

/-- `ḡ + 24Δ + 12C_HS = ḡ + (96k + 612 + 48δ_t)Δ + 12Δ_F + 36G` (HR.3 (c)). -/
theorem reset_bound_eq (g ΔF G : Time) :
    gbar g + 24 * sp.Δ + 12 * C_HS sp ΔF G =
      gbar g + (96 * (sp.k : Time) + 612 + 48 * (sp.toParams.δt : Time)) * sp.Δ + 12 * ΔF +
        36 * G := by
  rw [C_HS_eq]
  ring

/-- The closed form of `T_heal` (H.4). -/
theorem T_heal_eq (g ΔF G Tb : Time) :
    T_heal sp g ΔF G Tb =
      gbar g + (104 * (sp.k : Time) + 628 + 48 * (sp.toParams.δt : Time)) * sp.Δ + 12 * ΔF +
        36 * G + Tb := by
  simp only [T_heal, SA.Θ, C_HS_eq]
  ring

end Consensus.Goldilocks.Healing

end
