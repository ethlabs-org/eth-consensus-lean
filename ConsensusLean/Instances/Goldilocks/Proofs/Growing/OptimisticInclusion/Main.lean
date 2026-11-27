module
public import ConsensusLean.Instances.Goldilocks.Results.Statements.OptimisticInclusion
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Growth
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Optimistic.Check
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Sleepy.Service.Inclusion
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Optimistic inclusion under growing faults, at a committee

* `Regimes.Growing.optimistic_inclusion : OptimisticInclusion`
  (`Results/Statements/OptimisticInclusion`): the record of the reader extends the proposal
  (`optimistic_record_extends_at`), so its read does (`read_extends_of_record_at`). The
  proposal's slot `p` is positive (`proposesAt_slot_pos`). The finite inputs come from the
  whole-run premises as in R.2 (`include_sleepy`), through the proof horizon
  `b = max t (t_p + 6Δ)`; `t_p + 6Δ` only bounds where the proposal's origin is read, the
  premise's honesty runs through `t_p + 2Δ`. -/

namespace Consensus.Goldilocks.Regimes.Growing

open AC (ACParams Payload)

/-- **Optimistic inclusion, under growing faults, at a committee.** -/
theorem optimistic_inclusion : OptimisticInclusion := by
  intro sp dg H tr proposer ΔF K hopt hrun hnc hKB hsl hCS p P hP hU hQ y t j ht hy hw hj
  have hΔ := sp.toParams.hΔ
  obtain ⟨p₀, kP, hpr, hph, hPa, hkP⟩ := hP
  have hPs := Compose.Growing.proposesAt_slot_eq hPa hkP
  have hpos : 0 < p := hPs ▸ Compose.Growing.proposesAt_slot_pos hrun (hkP ▸ hpr.1) hPa
  have hp0 : (0 : Time) ≤ sp.ts p := Compose.Growing.ts_natCast_nonneg p
  set b := max t (sp.ts p + 6 * sp.Δ)
  have hb0 : 0 ≤ b := le_trans (by linarith) (le_max_right _ _)
  have ht0 : 0 ≤ t := by linarith
  have hsync := sleepyServiceBefore_of_syncOnAt hrun hsl.1 b
  have hB := sleepyBoundsFrom_of_sleepyRunAt hrun.antitone hsl b
  have hBK := hCS.boundsFrom b
  have hinv := Compose.Growing.sleepy_invariant_at hrun hnc hKB hb0 hsync hB hBK
  have hcs : 0 < sp.committeeSize := by
    have := hCS.2 p (sp.ts p) le_rfl (by linarith)
    rw [hKB.hsize] at this
    omega
  obtain ⟨E, hE, hEr, hPE⟩ := Compose.Growing.optimistic_record_extends_at hrun hnc hb0 hsync hB
    hinv hKB hBK hopt hcs hph hPa hPs hpos (le_max_right _ _) hU hQ ht (le_max_left _ _) hy.1 hw hj
  exact read_extends_of_record_at hrun hnc hinv hsync hKB hBK ht0 hj hy (le_max_left _ _)
    ⟨E, hE, hEr, Or.inl hPE⟩

end Consensus.Goldilocks.Regimes.Growing

end
