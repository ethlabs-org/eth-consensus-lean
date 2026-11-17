module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.GoldilocksBridge
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Healing.AC
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # CS2 at a slot committee from the committee fault bound

`CommitteeFaultsUpTo.committee_cs2_at`: with `βK ≤ 1/2`, the committee fault bound leaves fewer
than half of a slot-`s` committee of `committeeSize` members faulty at every `d ∈ [0, b]`, for a
slot starting from `ḡ` by `b`. It reads only the fault bound, the fraction, the committee size at
`s` and its positivity; the finite reset record (`ResetPremisesUpTo.committee_cs2_at`) and the
reset-free committee half bound (`committeeHalf_of_committeeFaults`) both take it.
-/

namespace Consensus.Goldilocks.Generic

open SA (SAParams gbar)

variable {sp : SAParams}

/-- **CS2 at a slot committee** from the committee fault bound: fewer than half of the slot-`s`
committee is faulty at any `d ∈ [0, b]`, for a slot starting from `ḡ` by `b`. -/
theorem CommitteeFaultsUpTo.committee_cs2_at {cm : Time → Finset (Fin sp.n)} {βK : ℚ}
    {H : Time → Set (Fin sp.n)} {g b : Time}
    (hcf : CommitteeFaultsUpTo (P := sp.toParams) βK cm H g b) (hβ : βK ≤ 1 / 2)
    (hpos : 0 < sp.committeeSize) {s : Nat}
    (hsize : ((dictOfTime sp cm).committee s).ncard = sp.committeeSize)
    (hgs : gbar g ≤ sp.ts s) (hsb : sp.ts s ≤ b) {d : Time} (hd0 : 0 ≤ d) (hdb : d ≤ b) :
    2 * ((dictOfTime sp cm).committee s ∩ (H d)ᶜ).ncard < sp.committeeSize := by
  have hcard : (cm (sp.toParams.slotTime s)).card = sp.committeeSize := by
    rwa [dictOfTime, SA.CommitteeDict.committee, Set.ncard_coe_finset] at hsize
  have hne : (cm (sp.toParams.slotTime s)).Nonempty := Finset.card_pos.1 (hcard ▸ hpos)
  have hts : sp.toParams.slotTime s = sp.ts s := sp.slotTime_eq s
  have h := hcf (sp.toParams.slotTime s) d (by rw [hts]; exact hgs)
    (by rw [hts]; exact hsb) hd0 hdb hne
  have hc : (0 : ℚ) ≤ (cm (sp.toParams.slotTime s)).card := Nat.cast_nonneg _
  have h2 : ((2 * ((dictOfTime sp cm).committee s ∩ (H d)ᶜ).ncard : Nat) : ℚ) <
      (cm (sp.toParams.slotTime s)).card := by
    push_cast
    change 2 * (((↑(cm (sp.toParams.slotTime s)) : Set (Fin sp.n)) ∩ (H d)ᶜ).ncard : ℚ) < _
    linarith [mul_le_mul_of_nonneg_right hβ hc]
  rw [← hcard]
  exact_mod_cast h2

end Consensus.Goldilocks.Generic

end
