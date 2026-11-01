module
public import AvailableChainGeneric.Statements.Pure.SlotGrid
import Mathlib.Tactic.Ring -- shake: keep (re-export)
import Mathlib.Tactic.Linarith -- shake: keep (re-export)
import Mathlib.Tactic.Push -- shake: keep (re-export)
import Mathlib.Tactic.NormNum -- shake: keep (re-export)

public section

namespace AvailableChain.Gen.Pure

open SlotGrid

/-- grid_identities proves the stated contract.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
theorem grid_identities : GridIdentitiesStatement := by
  rw [GridIdentitiesStatement_def]
  intro Δ s w k hΔ
  simp only [q_def, v_def, e_def, z_def, d_def, L_def, t_def, slotLen_def]
  push_cast
  exact ⟨by ring, by ring, by ring, by linarith, by ring, by ring⟩

/-- grid_predecessor proves the stated contract.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
theorem grid_predecessor : GridPredecessorStatement := by
  rw [GridPredecessorStatement_def]
  intro Δ s hs
  simp only [v_def, q_def, e_def, d_def, t_def, slotLen_def]
  push_cast [Nat.cast_sub hs]
  constructor <;> ring

/-- grid_round_equations proves the stated contract.
DC: DecoupledConsensusModel/Protocol/Grades.lean:54–84;
DecoupledConsensusProofs/ModelVocabulary/Healing/Schedule.lean:42,79–99.
INTENTIONAL: Keep the scalar clock with FG-SA R ≥ 2; 22-finality.md:977–989.
Consumers: F4.FF3/FF4/FF7. -/
theorem grid_round_equations : GridRoundEquationsStatement := by
  rw [GridRoundEquationsStatement_def]
  intro Δ R r
  refine ⟨?_, rfl, rfl⟩
  rw [T_def, t_def, slotLen_def, P_def]
  push_cast
  ring

/-- grid_offset_order proves the stated contract.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
theorem grid_offset_order : GridOffsetOrderStatement := by
  rw [GridOffsetOrderStatement_def]
  intro Δ c i j hΔ
  have hlen : 0 < slotLen Δ := by rw [slotLen_def]; linarith
  constructor
  · simp only [t_def, add_le_add_iff_right, mul_le_mul_iff_right₀ hlen, Int.ofNat_le]
  · simp only [t_def, add_lt_add_iff_right, mul_lt_mul_iff_right₀ hlen, Int.ofNat_lt]

/-- grid_in_flight_label proves the stated contract.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
theorem grid_in_flight_label : InFlightLabelAtGateStatement := by
  rw [InFlightLabelAtGateStatement_def]
  intro Δ s r hΔ hv hq
  simp only [v_def, d_def, q_def, t_def, slotLen_def] at hv hq
  have hlo : s < r := by
    by_contra h
    have hr : (r : Time) ≤ s := by exact_mod_cast (le_of_not_gt h)
    nlinarith
  have hhi : r ≤ s + 1 := by
    by_contra h
    have hr : (s : Time) + 2 ≤ r := by
      exact_mod_cast (show s + 2 ≤ r by omega)
    nlinarith
  omega

/-- no_gate_between_release_and_gate proves the stated contract.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137;
DecoupledConsensusProofs/ModelVocabulary/Goldfish/Objects.lean:53.
INTENTIONAL: Extract the integer slot clock; S1:519; 21-healing.md:217–228.
Consumers: F3.pending/outage (03:651–657), F4.FF3/FF4/FF7. -/
theorem no_gate_between_release_and_gate : NoGateBetweenReleaseAndGateStatement := by
  rw [NoGateBetweenReleaseAndGateStatement_def]
  rintro Δ s r hΔ ⟨hqr, hrs⟩
  have hr : r < s := (grid_offset_order Δ (6 * Δ) r s hΔ).2.mp hrs
  have hcast : (r : Time) + 1 ≤ s := by exact_mod_cast (show r + 1 ≤ s by omega)
  simp only [q_def, d_def, t_def, slotLen_def] at hqr
  nlinarith

/-- live_lease_label_bounds proves the stated contract.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137 (nearest clock).
INTENTIONAL: Add SA release and lease arithmetic; GridCO/Model/Protocol.lean:47–54;
21-healing.md:319–320,527,760–762. Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem live_lease_label_bounds : LiveLeaseLabelBoundsStatement := by
  rw [LiveLeaseLabelBoundsStatement_def]
  intro Δ s w k hΔ hcausal hexp
  rw [(grid_identities Δ s w k hΔ).2.2.2.2.2] at hexp
  have hupper : s < w + k := (grid_offset_order Δ (5 * Δ) s (w + k) hΔ).2.mp hexp
  have hlower : w < s := by
    by_contra h
    have hsw : s ≤ w := by omega
    have hd : d Δ s ≤ d Δ w := (grid_offset_order Δ (6 * Δ) s w hΔ).1.mpr hsw
    have hqd : q Δ s < d Δ s := by rw [q_def, d_def]; linarith
    exact (not_lt_of_ge (hqd.le.trans hd)) hcausal
  exact ⟨hlower, hupper⟩

/-- repair_expiry_equations proves the stated contract.
DC: DecoupledConsensusModel/Protocol/Schedule.lean:116–137 (nearest clock).
INTENTIONAL: Add SA release and lease arithmetic; GridCO/Model/Protocol.lean:47–54;
21-healing.md:319–320,527,760–762. Consumers: F3.pending/outage, F4.FF3/FF4/FF7. -/
theorem repair_expiry_equations : RepairExpiryEquationsStatement := by
  rw [RepairExpiryEquationsStatement_def]
  intro Δ b k hb hk
  have hbk : 2 ≤ b + k := by omega
  have hbkk : 1 ≤ b + 2 * k := by omega
  simp only [d_def, L_def, t_def, slotLen_def]
  push_cast [Nat.cast_sub hbk, Nat.cast_sub hbkk, Nat.cast_sub hb]
  exact ⟨by ring, by ring, by ring, by ring⟩

end AvailableChain.Gen.Pure
