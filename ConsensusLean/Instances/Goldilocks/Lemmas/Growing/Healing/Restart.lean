module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Projection.Run
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The last healthy restart at its own honest cut -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b : Time}
variable {hold : Time}

/-- The restart's sleep and the tick of the slot after `ḡ` come from the honest prefix
through the restart's time. -/
theorem ResetPremisesUpTo.restart_le_before_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k)) (hk : tr.RestartAt y k)
    (hkb : tr.time k ≤ b) : tr.time k ≤ sp.ts (sp.slot (gbar g) + 1 : Nat) := by
  have rc := hp.run
  have sc := rc.upTo (rc.time_nonneg k)
  by_contra hlt
  obtain ⟨w, -, hwk, hw, hprev⟩ :=
    sc.sleep_of_restart y hy k ((RunTrace.upTo_restartAt tr).mpr ⟨le_rfl, hk⟩)
  have hp₀ : gbar g ≤ sp.ts (sp.slot (gbar g) + 1 : Nat) := by
    have h := (AC.ts_le_iff_le_slot sp (AC.gbar_nonneg g)
      ((sp.slot (gbar g) + 1 : Nat) : Int)).not.mpr (by push_cast; omega)
    exact (not_le.mp h).le
  by_cases hgu : gbar g ≤ w
  · exact hw ⟨hp.awake y w (rc.antitone hwk.le hy) hgu (hwk.le.trans hkb), hwk.le⟩
  · have htk : sp.ts (sp.slot (gbar g) + 1 : Nat) ≤ tr.time k := (lt_of_not_ge hlt).le
    have hy' := rc.antitone htk hy
    obtain ⟨j, x, fgDue, hgt⟩ := sc.tick_of_awake y hy _ ((AC.gbar_nonneg g).trans hp₀)
      ⟨4 * ((sp.slot (gbar g) + 1 : Nat) : Int), by simp only [ACParams.ts]; ring⟩
      ⟨hp.awake y _ hy' hp₀ (htk.trans hkb), htk⟩
    obtain ⟨hc, ht⟩ := Healing.tick_first_cut hgt
    have hjk : j < k := by
      by_contra h
      exact hlt (ht ▸ rc.time_mono (not_lt.mp h))
    have := hprev j hjk ⟨_, hc⟩
    exact hgu (by linarith)

end Consensus.Goldilocks.Healing.Growing

end
