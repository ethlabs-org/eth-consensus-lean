module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Restart
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Supplier
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.AC.Run
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Adjacent update and to-FG calls while honest at their time -/

namespace Consensus.Goldilocks.Healing.Growing

open SA (SAParams ReplayOrder Payload gbar)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp ro} {g ΔF a b : Time}

theorem ResetPremisesUpTo.update_toFG_calls_at
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b)
    {y : Fin sp.n} {u : Nat} (hy : y ∈ H (sp.ts u + 6 * sp.Δ))
    (hu : sp.ts (sp.slot (gbar g) + 1 : Nat) ≤ sp.ts u)
    (hub : sp.ts u + 6 * sp.Δ ≤ b) :
    ∃ j ell ell', SA.UpdateAt tr.projAC y j u ell ∧
      tr.projAC.CallAt y (j + 1) ell' ∧ ell'.call = .toFG ∧
      tr.time (j + 1) = sp.ts u + 6 * sp.Δ ∧
      ell'.frame = ell.frame ∧
      SA.joined sp (tr.projAC.state y (j + 1)) (tr.time (j + 1)) := by
  let d := sp.ts u + 6 * sp.Δ
  have hDelta := sp.toParams.hΔ
  have hd : 0 ≤ d := by dsimp [d]; simp only [SAParams.ts]; positivity
  have hr := hp.run.upTo hd
  have hm := hp.run.time_mono
  have hgu : gbar g ≤ sp.ts u := by
    have hnext := (SA.ts_le_iff_le_slot sp (gbar_nonneg g)
      ((sp.slot (gbar g) + 1 : Nat) : Int)).not.mpr (by push_cast; omega)
    exact (not_le.mp hnext).le.trans hu
  have ha : (tr.upTo d).awake y d :=
    ⟨hp.awake y d hy (by dsimp [d]; linarith [sp.toParams.hΔ]) hub, le_rfl⟩
  have hj : ∀ i, (tr.upTo d).time i = d →
      SA.joined sp ((tr.upTo d).projAC.state y i) ((tr.upTo d).time i) := by
    intro i hi
    have hi' : tr.time i = d := hi
    have hac := (Compose.goldilocks_ac_projection sp ro dg (H d) (tr.upTo d) proposer
      hr (hp.noColl.upTo d)).localRun
    unfold SA.joined
    rcases SA.restartTime_state hac hy i with h | ⟨r, hri, hrs, h⟩
    · rw [h]; exact bot_le
    · rw [h]
      apply WithBot.coe_le_coe.mpr
      have hrs' : tr.RestartAt y r :=
        ((RunTrace.upTo_restartAt tr).mp (Compose.projAC_restartAt.mp hrs)).2
      have hrd : tr.time r ≤ d := (hm hri.le).trans hi'.le
      have hrestart := hp.restart_le_before_at (hp.run.antitone hrd hy) hrs' (hrd.trans hub)
      have hslot : sp.slot d = u + 1 :=
        SA.slot_of_mem sp (u + 1)
          (by dsimp [d]; simp only [SAParams.ts]; linarith)
          (by dsimp [d]; simp only [SAParams.ts]; linarith)
      change tr.time r ≤ sp.ts ((sp.slot (tr.time i) : Int) - 1)
      rw [hi', hslot]
      simpa using hrestart.trans hu
  obtain ⟨j, ell, ell', huj, hc, he, ht, hf, hjoin⟩ :=
    Healing.update_toFG_calls_of_awake hr hy ha hj
  have hstate : (tr.projAC.upTo d).state y (j + 1) = tr.projAC.state y (j + 1) :=
    Trace.upTo_state tr.projAC y (fun q hq => (hm hq.le).trans ht.le)
  rw [RunTrace.upTo_projAC] at huj hc hjoin
  exact ⟨j, ell, ell', (SA.upTo_updateAt hm).mp huj |>.2,
    (Trace.upTo_callAt tr.projAC).mp hc |>.2, he, ht, hf, hstate ▸ hjoin⟩

end Consensus.Goldilocks.Healing.Growing

end
