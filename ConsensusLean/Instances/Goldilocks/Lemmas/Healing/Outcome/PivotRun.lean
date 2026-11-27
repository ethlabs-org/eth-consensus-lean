module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Service.PivotBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.High
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Rows
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Committee
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Healing: proposal run and walk facts

Prerequisites for the post-reset proposal pivot. -/

namespace Consensus.Goldilocks.Healing

open AC (ACParams ReplayOrder Payload Vote)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {K : AC.CommitteeDict sp.n}
  {ini : Fin sp.n → (goldilocksNode sp ro).State} {g ΔF a : Time}

/-- An update of label `m` at `t_m + 6Δ` precedes the start of every slot `u ≥ m + 2`. -/
private theorem ts_add_six_lt {m u : Int} (h : m + 2 ≤ u) : sp.ts m + 6 * sp.Δ < sp.ts u := by
  have hΔ := sp.toParams.hΔ
  have := (AC.ts_le_iff sp).mpr h
  simp only [ACParams.ts] at this ⊢
  linarith

/-! ### Run facts -/

/-- A fast lock of label `s` is written at or after `t_s`. -/
theorem ts_le_of_fastLock (hp : ResetPremises tr H K proposer dg g ΔF a) {x : Fin sp.n}
    {i s : Nat} {D : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : AC.FastLockAt tr.projAC x i s D CV) : sp.ts s ≤ tr.time i := by
  have hr := (Compose.goldilocks_ac_projection_from hp.run hp.noColl).localRun
  have hΔ := sp.toParams.hΔ
  rcases hfl with ⟨ℓ, C, ⟨-, -, ht, -⟩, -⟩ | ⟨ℓ, A, -, hsl, -⟩
  · have ht' : tr.time i = sp.ts s + 6 * sp.Δ := ht
    rw [ht']
    exact le_add_of_nonneg_right (mul_nonneg (Nat.ofNat_nonneg _) hΔ.le)
  · have hsl' : sp.slot (tr.time i) = s := hsl
    exact (AC.ts_le_iff_le_slot sp (hr.time_nonneg i) s).2 (by omega)

/-- Bounded reset premises retain the operational timing of an older fast lock. -/
theorem ResetPremisesUpTo.fastLock_time_lt {b : Time}
    (hp : ResetPremisesUpTo tr H K proposer dg g ΔF a b) {x : Fin sp.n}
    {r m u : Nat} {D : AC.Blk sp.n (List (FG.Att sp.n))} {CV : Set (Vote sp.n)}
    (hfl : AC.FastLockAt tr.projAC x r m D CV) (hmu : m < u)
    (htr : tr.time r ≤ sp.ts u + sp.Δ) : tr.time r < sp.ts u := by
  rcases hfl with ⟨ell, C, ⟨_, _, ht, _⟩, _⟩ | ⟨ell, A, _, hsl, _⟩
  · have ht' : tr.time r = sp.ts m + 6 * sp.Δ := ht
    rw [ht'] at htr ⊢
    exact ts_add_six_lt (by exact_mod_cast Compose.ts_add_two_le htr)
  · change sp.slot (tr.time r) = m at hsl
    by_contra h
    have := (AC.ts_le_iff_le_slot sp (hp.run.time_nonneg r) u).mp (not_lt.mp h)
    omega

end Consensus.Goldilocks.Healing
