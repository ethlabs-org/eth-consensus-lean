module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameWindowExists
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameKey

public section

/-! # The key-dependent rise window

recovery_time_savings item 1, piece (3). On `HZ ≤ h_max ≤ HZ + 1` the merged key `κ′` has the
five values `2HZ + j`, `j < 5`, with the floors `HZ − 1, HZ − 1, HZ, HZ, HZ + 1`. The rise
from a warm proposal at or above the floor needs `r(v) = 2 − ⌊(v − 2HZ)/2⌋` rounds
(`2, 2, 1, 1, 0`): `HZ + 1 ≤ floor + r(v)` (`le_floor_add_riseRounds`).

`exists_riseWindow_of_service` instantiates `exists_frameWindow_seq_of_service` with the window
length `len(v) = d + r(v)·ρ + s` (drain `d`, round length `ρ`, slack `s`, all as times). The
cumulative bound is `∑_{j<5} (len(2HZ + j) + λ) = 5(d + s + λ) + 6ρ`, against
`5(d + 2ρ + s + λ) = 5(d + s + λ) + 10ρ` for the constant two-round length.
This module does not compose the reset or the heal. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-- The rise round count of the merged key value `v`: `2, 2, 1, 1, 0` for `v = 2HZ + j`. -/
def riseRounds (HZ v : Nat) : Nat := 2 - (v - 2 * HZ) / 2

/-- Unfolding equation of `riseRounds`. -/
theorem riseRounds_eq (HZ v : Nat) : riseRounds HZ v = 2 - (v - 2 * HZ) / 2 := by
  unfold riseRounds
  rfl

theorem riseRounds_le_two (HZ v : Nat) : riseRounds HZ v ≤ 2 := by
  unfold riseRounds
  omega

/-- The window length of key value `v`: the drain `d`, `r(v)` rounds of length `ρ`, slack `s`. -/
def riseLen (d ρ s : Time) (HZ v : Nat) : Time := d + (riseRounds HZ v : Time) * ρ + s

/-- Unfolding equation of `riseLen`. -/
theorem riseLen_eq (d ρ s : Time) (HZ v : Nat) :
    riseLen d ρ s HZ v = d + (riseRounds HZ v : Time) * ρ + s := by
  unfold riseLen
  rfl

theorem riseLen_nonneg {d ρ s : Time} (hd : 0 ≤ d) (hρ : 0 ≤ ρ) (hs : 0 ≤ s) (HZ v : Nat) :
    0 ≤ riseLen d ρ s HZ v := by
  unfold riseLen
  have : (0 : Time) ≤ (riseRounds HZ v : Time) := Nat.cast_nonneg _
  nlinarith

/-- The cumulative length of the five attempts: `5(d + s + λ) + 6ρ`. -/
theorem sum_riseLen (d ρ s lam : Time) (HZ : Nat) :
    ∑ j ∈ Finset.range 5, (riseLen d ρ s HZ (2 * HZ + j) + lam) =
      5 * (d + s + lam) + 6 * ρ := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, riseLen, riseRounds,
    Nat.add_sub_cancel_left]
  norm_num
  ring

/-- **The floor and the round count.** A store with `h_max ≥ 1` and merged key
`v ≥ 2HZ` has `HZ + 1 ≤ head_height_floor + r(v)`. -/
theorem le_floor_add_riseRounds {P : Params} {ACP : Type} (st : Store P ACP) {HZ : Nat}
    (h1 : 1 ≤ st.hmax) (hv : 2 * HZ ≤ frameKey' st) :
    HZ + 1 ≤ st.headHeightFloor + riseRounds HZ (frameKey' st) := by
  classical
  have hb := frameKey_bounds st
  rw [frameKey'_def, keyMerge_eq] at hv ⊢
  unfold riseRounds
  unfold Store.headHeightFloor
  by_cases hc : st.Contest
  · have hK : frameKey st = 3 * st.hmax + 2 := by
      rw [frameKey_def]
      simp [hc]
    simp only [hc, ↓reduceIte]
    omega
  · have hK : frameKey st ≤ 3 * st.hmax + 1 := by
      rw [frameKey_def]
      simp only [hc, ↓reduceIte]
      split_ifs <;> omega
    simp only [hc, ↓reduceIte]
    omega

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- **The key-dependent window.** `exists_frameWindow_seq_of_service` with
`len(v) = d + r(v)·ρ + s`. Some key value `v` holds on a window `[a, a + len(v)]` with a
`FrameWindow`, the window ends by the partial sum up to `v` and by
`lo + 5(d + s + λ) + 6ρ`, and at every honest cut of the window the frame floor satisfies
`HZ + 1 ≤ floor + r(v)`. -/
theorem exists_riseWindow_of_service (hrun : GoldilocksRun proposer dg H tr)
    (hnc : Compose.NoCollRun dg tr) (hf : Hᶜ.ncard < 2 * sp.toParams.fg.q - sp.n)
    {g ΔF b κ : Time} (hsvc : ResetService tr H g ΔF b) (hcatch : CatchRun tr H g κ)
    {lo lam T d ρ s : Time} {HZ : Nat} (hd : 0 ≤ d) (hρ : 0 ≤ ρ) (hs : 0 ≤ s)
    (hlam : 0 ≤ lam) (hlo : gbar g + κ ≤ lo)
    (hrange : ∀ y ∈ H, ∀ i, lo ≤ tr.time i → tr.time i < T →
      HZ ≤ (tr.state y i).fg.hmax ∧ (tr.state y i).fg.hmax ≤ HZ + 1)
    (hcall : ∀ z ∈ H, ∀ i m, lo ≤ tr.time i → tr.time i + lam ≤ tr.time m → tr.time m < T →
      ∃ j < m, tr.IsCall z j ∧ tr.deadline z j (max (tr.time i) g) sp.Δ ≤ tr.time j)
    (hT : lo + (5 * (d + s + lam) + 6 * ρ) < T) :
    ∃ v, 2 * HZ ≤ v ∧ v ≤ 2 * HZ + 4 ∧ ∃ a, lo + lam ≤ a ∧
      a + riseLen d ρ s HZ v ≤
        lo + ∑ j ∈ Finset.range (v - 2 * HZ + 1), (riseLen d ρ s HZ (2 * HZ + j) + lam) ∧
      a + riseLen d ρ s HZ v ≤ lo + (5 * (d + s + lam) + 6 * ρ) ∧
      (∀ y ∈ H, ∀ i, a ≤ tr.time i → tr.time i ≤ a + riseLen d ρ s HZ v →
        frameKey' (tr.state y i).fg = v) ∧
      ∃ floor kindJ J,
        FrameWindow (tr := tr) (H := H) a (a + riseLen d ρ s HZ v) floor kindJ J ∧
        ∀ y ∈ H, ∀ i, a ≤ tr.time i → tr.time i ≤ a + riseLen d ρ s HZ v →
          HZ + 1 ≤ floor + riseRounds HZ v := by
  have hlen := riseLen_nonneg hd hρ hs HZ
  obtain ⟨v, hv1, hv2, a, ha1, ha2, hK, floor, kindJ, J, hW⟩ :=
    exists_frameWindow_seq_of_service hrun hnc hf hsvc hcatch (riseLen d ρ s HZ) hlen hlam
      hlo hrange hcall (by rw [sum_riseLen]; exact hT)
  have hsub : ∑ j ∈ Finset.range (v - 2 * HZ + 1), (riseLen d ρ s HZ (2 * HZ + j) + lam) ≤
      ∑ j ∈ Finset.range 5, (riseLen d ρ s HZ (2 * HZ + j) + lam) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      fun j _ _ => add_nonneg (hlen _) hlam
  rw [sum_riseLen] at hsub
  refine ⟨v, hv1, hv2, a, ha1, ha2, by linarith, hK, floor, kindJ, J, hW, ?_⟩
  intro y hy i hi1 hi2
  have hkey := hK y hy i hi1 hi2
  have h1 : 1 ≤ (tr.state y i).fg.hmax := by
    have := hj_lt_hmax hrun hy i
    omega
  have hle := le_floor_add_riseRounds (tr.state y i).fg h1 (HZ := HZ) (by rw [hkey]; exact hv1)
  rw [hkey, hW.floor_eq y hy i hi1 hi2] at hle
  exact hle

end Consensus.Goldilocks.Healing

end
