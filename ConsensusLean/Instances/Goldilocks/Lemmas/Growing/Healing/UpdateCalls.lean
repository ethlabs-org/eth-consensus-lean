module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Restart
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Update calls while honest at their time -/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload gbar)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b : Time}
variable {hold : Time}

theorem ResetPremisesUpTo.update_call_of_awake
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold)
    {y : Fin sp.n} {u : Nat} (hy : y ∈ H (sp.ts u + 6 * sp.Δ))
    (hu : sp.ts (sp.slot (gbar g) + 1 : Nat) ≤ sp.ts u)
    (hub : sp.ts u + 6 * sp.Δ ≤ b) :
    ∃ j ell, AC.UpdateAt tr.projAC y j u ell := by
  let d := sp.ts u + 6 * sp.Δ
  have hDelta := sp.toParams.hΔ
  have hd : 0 ≤ d := by dsimp [d]; simp only [ACParams.ts]; positivity
  have hr := hp.run.upTo hd
  have hm := hp.run.time_mono
  have hgu : gbar g ≤ sp.ts u := by
    have hnext := (AC.ts_le_iff_le_slot sp (gbar_nonneg g)
      ((sp.slot (gbar g) + 1 : Nat) : Int)).not.mpr (by push_cast; omega)
    exact (not_le.mp hnext).le.trans hu
  have ha : (tr.upTo d).awake y d :=
    ⟨hp.awake y d hy (by dsimp [d]; linarith [sp.toParams.hΔ]) hub, le_rfl⟩
  have hj : ∀ i, (tr.upTo d).time i = d →
      AC.joined sp ((tr.upTo d).projAC.state y i) ((tr.upTo d).time i) := by
    intro i hi
    have hi' : tr.time i = d := hi
    have hac := (Compose.goldilocks_ac_projection_from hr (hp.noColl.upTo d)).localRun
    unfold AC.joined
    rcases AC.restartTime_stateU hac.toU hp.run.vstart hy i with h | ⟨r, hri, hrs, h⟩
    · rw [h]; exact bot_le
    · rw [h]
      apply WithBot.coe_le_coe.mpr
      have hrs' : tr.RestartAt y r :=
        ((RunTrace.upTo_restartAt tr).mp (Compose.projAC_restartAt.mp hrs)).2
      have hrd : tr.time r ≤ d := (hm hri.le).trans hi'.le
      have hrestart := hp.restart_le_before_at (hp.run.antitone hrd hy) hrs' (hrd.trans hub)
      have hslot : sp.slot d = u + 1 :=
        AC.slot_of_mem sp (u + 1)
          (by dsimp [d]; simp only [ACParams.ts]; linarith)
          (by dsimp [d]; simp only [ACParams.ts]; linarith)
      change tr.time r ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1)
      rw [hi', hslot]
      simpa using hrestart.trans hu
  obtain ⟨j, ell, huj⟩ := Healing.update_call_of_awake hr hy ha hj
  rw [RunTrace.upTo_projAC] at huj
  exact ⟨j, ell, (AC.upTo_updateAt hm).mp huj |>.2⟩

end Consensus.Goldilocks.Healing.Growing

end
