module
public import ConsensusLean.Spec.Problem.Basic
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The release gap in the contract arithmetic

Arithmetic of the late-release contract over explicit natural parameters: the FG delay in slots
`f` (`fgSlots`), the release gap `R`, the signing gap `G` and the timeout `δt`. The FG delay bound
is `F = 4f − 6`, and the final gap is `c′ = ⌈(6 + F + R + G)/4⌉` (`releaseFinalSlots`). From the
timeout `3c′ ≤ δt`:

* `fgSlots_releaseGap_signGap_le`: `4f + R + G ≤ 4δt`, the timeout's member of the healing triple;
* `releaseFinalSlots_budget`: `6 + F + R + G ≤ 4c′`, the final gap pays the FG delay, the release
  wait and the signing wait;
* `releaseGap_signGap_δt`, `two_le_releaseFinalSlots`, `fgDelay_releaseGap_le`: the remaining
  timeout facts the healing and final routes read;
* `release_triple`, `release_final_delivery`: the same bounds in time, for a run-level FG delay
  `ΔF + R·Δ` whose protocol part satisfies `6Δ + ΔF ≤ 4Δ·f`.

At `R = 0` everything reduces to the arithmetic without a release gap (`releaseFinalSlots_zero`,
`fgSlots_signGap_le_of_timeout`, `finalSlots_budget_of_zero`). No lemma reads a setup or an
assumption set. -/

namespace Consensus.Goldilocks.Obligations

/-- The final gap with a release gap, `c′ = ⌈(6 + (4f − 6) + R + G)/4⌉`, over the FG delay in
slots `f`, the release gap `R` and the signing gap `G`. -/
def releaseFinalSlots (f R G : Nat) : Nat := (6 + (4 * f - 6) + R + G + 3) / 4

theorem releaseFinalSlots_eq (f R G : Nat) :
    releaseFinalSlots f R G = (6 + (4 * f - 6) + R + G + 3) / 4 := by rfl

/-- The final gap pays the FG delay bound, the release wait and the signing wait:
`6 + F + R + G ≤ 4c′`. -/
theorem releaseFinalSlots_budget (f R G : Nat) :
    6 + (4 * f - 6) + R + G ≤ 4 * releaseFinalSlots f R G := by
  rw [releaseFinalSlots_eq]
  omega

/-- The timeout pays the FG delay, the release wait and the signing wait:
`4·fgSlots + R + G ≤ 4·δt`. -/
theorem fgSlots_releaseGap_signGap_le {f R G δt : Nat} (h : 3 * releaseFinalSlots f R G ≤ δt) :
    4 * f + R + G ≤ 4 * δt := by
  rw [releaseFinalSlots_eq] at h
  omega

/-- The timeout pays the FG delay bound and the release wait, with the six delays of the
attestation round: `F + R + 6 ≤ 4·δt`. -/
theorem fgDelay_releaseGap_le {f R G δt : Nat}
    (h : 3 * releaseFinalSlots f R G ≤ δt) : (4 * f - 6) + R + 6 ≤ 4 * δt := by
  rw [releaseFinalSlots_eq] at h
  omega

/-- The timeout pays the signing wait of the reset's update round: `3 + ⌈G/4⌉ ≤ δt`. -/
theorem releaseGap_signGap_δt {f R G δt : Nat}
    (h : 3 * releaseFinalSlots f R G ≤ δt) : 3 + (G + 3) / 4 ≤ δt := by
  rw [releaseFinalSlots_eq] at h
  omega

/-- The final gap is at least two slots. -/
theorem two_le_releaseFinalSlots (f R G : Nat) : 2 ≤ releaseFinalSlots f R G := by
  rw [releaseFinalSlots_eq]
  omega

/-- **The healing triple at the run-level FG delay `ΔF + R·Δ`**: from the protocol bound
`6Δ + ΔF ≤ 4Δ·f` and the timeout, `6Δ + (ΔF + R·Δ) + G·Δ ≤ 4Δ·δt`. -/
theorem release_triple {f R G δt : Nat} {Δ ΔF : Time} (hΔ : 0 < Δ)
    (hd : 6 * Δ + ΔF ≤ 4 * Δ * (f : Time)) (h : 3 * releaseFinalSlots f R G ≤ δt) :
    6 * Δ + (ΔF + (R : Time) * Δ) + (G : Time) * Δ ≤ 4 * Δ * (δt : Time) := by
  have hc : (4 * f + R + G : Time) ≤ 4 * δt := by
    exact_mod_cast fgSlots_releaseGap_signGap_le h
  nlinarith [mul_le_mul_of_nonneg_left hc hΔ.le]

/-- **The final gap's delivery at the run-level FG delay `ΔF + R·Δ`**: from the protocol bound
`ΔF ≤ F·Δ`, `6Δ + G·Δ + (ΔF + R·Δ) ≤ 4Δ·c′`. -/
theorem release_final_delivery {f R G : Nat} {Δ ΔF : Time} (hΔ : 0 < Δ)
    (hd : ΔF ≤ ((4 * f - 6 : Nat) : Time) * Δ) :
    6 * Δ + (G : Time) * Δ + (ΔF + (R : Time) * Δ) ≤
      4 * Δ * (releaseFinalSlots f R G : Time) := by
  have hc : (6 + (4 * f - 6 : Nat) + R + G : Time) ≤ 4 * (releaseFinalSlots f R G : Time) := by
    exact_mod_cast releaseFinalSlots_budget f R G
  nlinarith [mul_le_mul_of_nonneg_left hc hΔ.le]

/-! ### No release gap -/

/-- At `R = 0` the final gap is `⌈(6 + (4f − 6) + G)/4⌉`, the gap without a release gap. -/
theorem releaseFinalSlots_zero (f G : Nat) :
    releaseFinalSlots f 0 G = (6 + (4 * f - 6) + G + 3) / 4 := by
  simp only [releaseFinalSlots_eq, Nat.add_zero]

/-- `fgSlots_signGap_le` over explicit parameters, as the `R = 0` case: the timeout
`3·⌈(6 + (4f − 6) + G)/4⌉ ≤ δt` gives `4f + G ≤ 4δt`. -/
theorem fgSlots_signGap_le_of_timeout {f G δt : Nat}
    (h : 3 * ((6 + (4 * f - 6) + G + 3) / 4) ≤ δt) : 4 * f + G ≤ 4 * δt := by
  rw [← releaseFinalSlots_zero] at h
  simpa only [Nat.add_zero] using fgSlots_releaseGap_signGap_le h

/-- The final budget without a release gap, over explicit parameters, as the `R = 0` case:
`6 + (4f − 6) + G ≤ 4·⌈(6 + (4f − 6) + G)/4⌉`. -/
theorem finalSlots_budget_of_zero (f G : Nat) :
    6 + (4 * f - 6) + G ≤ 4 * ((6 + (4 * f - 6) + G + 3) / 4) := by
  rw [← releaseFinalSlots_zero]
  simpa only [Nat.add_zero] using releaseFinalSlots_budget f 0 G

end Consensus.Goldilocks.Obligations
