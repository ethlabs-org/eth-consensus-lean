module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.TickDuty
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.RelTrace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Ready validators are joined, over AC traces with the unlock given

`ready_joinedAC` (F.4, `Compose.ready_implies_joined`, over an AC trace with the unlock given at
a write mode and the tick duty in place of the composite run's tick): an honest validator awake
throughout `[max 0 (t − c − 1), t]` with `8Δ ≤ c + 1` is awake and joined at `t ≥ 0`. A restart
by `t` follows a sleep before the window (`ACLocalRunU.sleep_of_restart`), and the window holds
the public time `t_{slot(t) − 1}`, where the validator ticks (`TickDuty`), so the restart is not
after it. -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {wm : WriteMode} {u : Nat → Set Lock}

/-- **Ready validators are joined** (F.4 over the AC trace): an honest validator awake throughout
`[max 0 (t − c − 1), t]`, with `8Δ ≤ c + 1`, is awake and joined at `t ≥ 0`. -/
theorem ready_joinedAC (hr : ACLocalRunU wm u H U tr) (htick : TickDuty tr H) {y : Fin sp.n}
    (hy : y ∈ H) {t c : Time} (ht : 0 ≤ t) (hc : 8 * sp.Δ ≤ c + 1)
    (hawake : ∀ τ, max 0 (t - c - 1) ≤ τ → τ ≤ t → tr.awake y τ) :
    tr.awake y t ∧ JoinedAt tr y t := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hm : max 0 (t - c - 1) ≤ t := max_le ht (by linarith)
  refine ⟨hawake t hm le_rfl, fun k hk hkt => ?_⟩
  obtain ⟨ℓ, hck, hcall⟩ := hk
  obtain ⟨w, hw0, hwk, hs, hb⟩ := hr.sleep_of_restart y hy k ℓ hck hcall
  -- the sleep is before the window
  have hwm : w < max 0 (t - c - 1) := by
    by_contra hle
    exact hs (hawake w (not_lt.1 hle) (hwk.le.trans hkt))
  have hwt : w < t - c - 1 := by
    rcases lt_max_iff.1 hwm with h | h
    · linarith
    · exact h
  -- `p = t_{slot(t) − 1}` lies in the window
  set p := sp.ts ((sp.slot t : Int) - 1)
  have hup : t < sp.ts ((sp.slot t : Int) + 1) := by
    by_contra hle
    have := (ts_le_iff_le_slot sp ht _).1 (not_lt.1 hle)
    omega
  have hpt : p ≤ t := (ts_le_iff_le_slot sp ht _).2 (by omega)
  have hpw : t - c - 1 < p := by
    have : sp.ts ((sp.slot t : Int) + 1) = p + 8 * sp.Δ := by
      simp only [p, SAParams.ts]; ring
    linarith
  have hp0 : 0 ≤ p := by linarith
  have hpub : sp.toParams.IsPublic p :=
    Dvd.intro (4 * ((sp.slot t : Int) - 1)) (by simp only [p, SAParams.ts]; ring)
  obtain ⟨j, ℓj, hcj, -, htj⟩ := htick y hy p hp0 hpub
    (hawake p (max_le hp0 hpw.le) hpt)
  by_contra hgt
  push Not at hgt
  have hjk : j < k := by
    by_contra hkj
    have := hr.time_mono (not_lt.1 hkj)
    linarith
  have := hb j hjk ℓj hcj
  linarith

end Consensus.Goldilocks.SA

end
