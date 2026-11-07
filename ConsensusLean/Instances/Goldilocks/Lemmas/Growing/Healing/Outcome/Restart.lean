module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Retention.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The causal restart bound at an honest observation

Awake service is consumed only through the restart being observed.
-/

namespace Consensus.Goldilocks.Healing.Growing.Outcome

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

/-- A validator honest at a bounded restart cannot restart after the first GST slot. -/
theorem restart_le_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {k : Nat} (hy : y ∈ H (tr.time k))
    (hk : tr.RestartAt y k) (hkb : tr.time k ≤ b) :
    tr.time k ≤ sp.ts (sp.slot (gbar g) + 1 : Nat) := by
  have hr := (hp.run.upTo (hp.run.time_nonneg k))
  have hk' : (tr.upTo (tr.time k)).RestartAt y k :=
    (RunTrace.upTo_restartAt tr).mpr ⟨le_rfl, hk⟩
  by_contra hlt
  obtain ⟨u, -, huk, hu, hprev⟩ := hr.sleep_of_restart y hy k hk'
  have hp₀ : gbar g ≤ sp.ts (sp.slot (gbar g) + 1 : Nat) := by
    have h := (SA.ts_le_iff_le_slot sp (Healing.gbar_nonneg g)
      ((sp.slot (gbar g) + 1 : Nat) : Int)).not.mpr (by push_cast; omega)
    exact (not_le.mp h).le
  by_cases hgu : gbar g ≤ u
  · exact hu ⟨hp.awake y u (hp.run.antitone huk.le hy) hgu (huk.le.trans hkb), huk.le⟩
  · obtain ⟨j, _x, hne, hcs, -⟩ := hr.tick_of_awake y hy _
      ((Healing.gbar_nonneg g).trans hp₀)
      ⟨4 * ((sp.slot (gbar g) + 1 : Nat) : Int), by simp only [SAParams.ts]; ring⟩
      ⟨hp.awake y _ (hp.run.antitone (lt_of_not_ge hlt).le hy) hp₀
        ((lt_of_not_ge hlt).le.trans hkb), (lt_of_not_ge hlt).le⟩
    obtain ⟨hn, ht, -, -, hl⟩ := hcs 0 (List.length_pos_of_ne_nil hne)
    simp only [Nat.add_zero] at hn ht hl
    have hjk : j < k := by
      by_contra h
      have := hr.time_mono (not_lt.mp h)
      exact hlt (ht ▸ this)
    have := hprev j hjk ⟨_, hn, hl⟩
    exact hgu (by linarith)

end Consensus.Goldilocks.Healing.Growing.Outcome

end
