module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HighReports
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Cut.Reset
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Bounded high-origin seeds from the reset signing

The signer need only be honest at its signing. The earlier report is read on that
signer's prefix, and its high origin is honest at its own writing cut.
-/

namespace Consensus.Goldilocks.Healing.Growing

open AC (ACParams Payload Vote)

variable {sp : ACParams}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Time → Set (Fin sp.n)} {tr : GoldilocksTrace sp} {g ΔF a b : Time}
variable {hold : Time}

/-- The reset signing supplies a high origin written by the reset time. -/
theorem ResetPremisesUpTo.reset_seed_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold) :
    ∃ v r l O, HighOrigin tr H g v r l O ∧ tr.time r ≤ a ∧ l ≤ sp.slot a := by
  obtain ⟨⟨y, k, att, hyz, hs, hh, hka⟩, -⟩ := hp.reset
  have hy := hp.run.antitone (le_max_right _ _) hyz
  have hr := hp.run.upTo (hp.run.time_nonneg k)
  obtain ⟨r, hkr, hrt, ell, C, E, hto, _, _, _, _, _, _, _, hCa⟩ :=
    Healing.signAt_report_entry hr hy ((RunTrace.upTo_signAt tr).mpr ⟨le_rfl, hs⟩)
  have hrk : r ≤ k := by omega
  have hrt' : tr.time r ≤ tr.time k := hp.run.time_mono hrk
  have hCa' : HZ tr H g + 1 ≤ ((tr.state y r).fg.σ C.root).h := by
    rw [RunTrace.upTo_state_of_le hp.run.time_mono hrt'] at hCa
    omega
  -- the reset time is inside the deep quarantine: below `b`, or below the drain of `a`
  have hq : ∀ D, sp.deepDepth = some D → tr.time r ≤ cutZ sp.toParams g + 4 * D * sp.Δ := by
    intro D hD
    refine (hrt'.trans hka.le).trans ?_
    rcases hp.deepCover D hD with hbq | hc
    · exact hp.reset_le.trans hbq
    · have := Healing.lt_drainTime (sp := sp) ((hp.run.time_nonneg k).trans hka.le)
      have := hc.drain_le D hD
      have := sp.toParams.hΔ
      linarith
  obtain ⟨io, hio, l, O, D, CV, ho, _, hfl, _, _⟩ := hp.high_report_origin_of_quarantine_at
    (hp.run.antitone (max_le_max le_rfl hrt') hyz) ((toFGAt_upTo_iff hp.run.time_mono hrt').mp hto)
    (hrt'.trans (hka.le.trans hp.reset_le)) hCa' hq
  have htime : sp.ts l ≤ tr.time io := by
    rcases hfl with ⟨ell', C', ⟨_, _, ht, _⟩, _⟩ | ⟨ell', A, _, hsl, _⟩
    · have ht' : tr.time io = sp.ts l + 6 * sp.Δ := ht
      rw [ht']
      have := sp.toParams.hΔ
      linarith
    · change sp.slot (tr.time io) = l at hsl
      exact (AC.ts_le_iff_le_slot sp (hp.run.time_nonneg io) l).mpr (by omega)
  have hia : tr.time io ≤ a := (hp.run.time_mono (hio.le.trans hrk)).trans hka.le
  refine ⟨y, io, l, O, ho, hia, ?_⟩
  exact_mod_cast (AC.ts_le_iff_le_slot sp ((hp.run.time_nonneg io).trans hia) l).mp
    (htime.trans hia)

/-- Every post-drain slot has a reset seed strictly before its start. -/
theorem ResetPremisesUpTo.reset_seed_before_slot_at
    {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b cm βK hold) {u : Nat}
    (hR : drainTime sp a ≤ sp.ts u) :
    ∃ v r l O, HighOrigin tr H g v r l O ∧ tr.time r ≤ b ∧ l < u ∧
      tr.time r < sp.ts u := by
  obtain ⟨v, r, l, O, ho, hra, hl⟩ := hp.reset_seed_at
  have hlu : l + 2 ≤ u := by
    rw [Healing.drainTime_eq] at hR
    have := (AC.ts_le_iff sp).mp hR
    omega
  refine ⟨v, r, l, O, ho, hra.trans hp.reset_le, by omega, ?_⟩
  obtain ⟨_, _, ⟨CV, ell, D, _, hfl, _⟩, _⟩ := ho
  rcases hfl with ⟨ell', C, ⟨_, _, ht, _⟩, _⟩ | ⟨ell', A, _, hsl, _⟩
  · have ht' : tr.time r = sp.ts l + 6 * sp.Δ := ht
    have hts := (AC.ts_le_iff sp).mpr (show (l : Int) + 2 ≤ u by omega)
    have := sp.toParams.hΔ
    simp only [ACParams.ts] at hts ht' ⊢
    linarith
  · by_contra h
    have := (AC.ts_le_iff_le_slot sp (hp.run.time_nonneg r) u).mp (not_lt.mp h)
    change sp.slot (tr.time r) = l at hsl
    omega

end Consensus.Goldilocks.Healing.Growing

end
