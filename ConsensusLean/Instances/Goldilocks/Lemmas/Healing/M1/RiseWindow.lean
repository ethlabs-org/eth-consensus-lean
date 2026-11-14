module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameLag
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.PreAdvance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.M1.FrameKey

public section

/-! # The key-dependent rise window

On `HZ ≤ h_max ≤ HZ + 1` the merged key `κ′` has the
five values `2HZ + j`, `j < 5`, with the floors `HZ − 1, HZ − 1, HZ, HZ, HZ + 1`. The rise
from a warm proposal at or above the floor needs `r(v) = 2 − ⌊(v − 2HZ)/2⌋` rounds
(`2, 2, 1, 1, 0`): `HZ + 1 ≤ floor + r(v)` (`le_floor_add_riseRounds`).

The window length is `len(v) = d + r(v)·ρ + s` (drain `d`, round length `ρ`, slack `s`, all as
times; `riseLen`). The cumulative bound (`sum_riseLen`) is
`∑_{j<5} (len(2HZ + j) + λ) = 5(d + s + λ) + 6ρ`, against `5(d + 2ρ + s + λ) = 5(d + s + λ) + 10ρ`
for the constant two-round length.
This module does not compose the reset or the heal. -/

namespace Consensus.Goldilocks.Healing

open SA (SAParams ReplayOrder Payload gbar)

/-- The rise round count of the merged key value `v`: `2, 2, 1, 1, 0` for `v = 2HZ + j`. -/
def riseRounds (HZ v : Nat) : Nat := 2 - (v - 2 * HZ) / 2

/-- Unfolding equation of `riseRounds`. -/
theorem riseRounds_eq (HZ v : Nat) : riseRounds HZ v = 2 - (v - 2 * HZ) / 2 := by
  unfold riseRounds
  rfl

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
  positivity

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

end Consensus.Goldilocks.Healing

end
