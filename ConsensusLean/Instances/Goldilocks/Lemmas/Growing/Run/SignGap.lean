module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Model
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The signing gap at a public time

`SignGapAt` gives a signing time in `[t, t + (G + 1) · Δ)`; from a public `t` the signing time is
in `[t, t + G · Δ]` (`SignGapAt.of_public`). -/

namespace Consensus.Goldilocks

/-- From a public time `t`, the calendar allows signing at a public time at most `G · Δ` later. -/
theorem SignGapAt.of_public {P : Params} {sign : Fin P.n → Time → Bool} {G : Nat}
    {t₀ : Time} (h : SignGapAt P sign G t₀) {y : Fin P.n} {t : Time}
    (ht₀ : t₀ ≤ t) (hpub : P.IsPublic t) :
    ∃ t', t ≤ t' ∧ t' ≤ t + (G : Time) * P.Δ ∧ P.IsPublic t' ∧ sign y t' = true := by
  obtain ⟨t', h1, h2, h3, h4⟩ := h y t ht₀
  refine ⟨t', h1, ?_, h3, h4⟩
  obtain ⟨a, rfl⟩ := hpub
  obtain ⟨b, rfl⟩ := h3
  have hΔ := P.hΔ
  have hlt : b < a + G + 1 := by
    by_contra hb
    have : P.Δ * (a + G + 1) ≤ P.Δ * b := mul_le_mul_of_nonneg_left (by linarith) hΔ.le
    linarith
  have : P.Δ * b ≤ P.Δ * (a + G) :=
    mul_le_mul_of_nonneg_left (Int.lt_add_one_iff.mp hlt) hΔ.le
  linarith

/-- Responsive signing (every public time) has signing gap `0`. -/
theorem signGapAt_true (P : Params) (t₀ : Time) : SignGapAt P (fun _ _ => true) 0 t₀ := by
  intro y t _
  have hΔ := P.hΔ
  refine ⟨t + (-t) % P.Δ, ?_, ?_, ⟨-((-t) / P.Δ), ?_⟩, rfl⟩
  · linarith [Int.emod_nonneg (-t) hΔ.ne']
  · push_cast; linarith [Int.emod_lt_of_pos (-t) hΔ]
  · linarith [Int.emod_add_mul_ediv (-t) P.Δ]

end Consensus.Goldilocks
