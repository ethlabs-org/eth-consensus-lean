module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Obligations: the slot of an anchor after the drain

An anchor of the route-A window is a proposal at a slot `s` whose time is after the drain of a
reset `a`. The reset is after the reset cut `c_z` of GST `g`, so `s` is placed by the slot schedule
alone, for constant and growing faults alike:

* `drained_anchor_slot`: from `c_z(g) < a` and `drainTime a ≤ t_s`, `slot a + 2k + 5 ≤ s` and
  `ḡ + 4Δ ≤ t_s`. -/

namespace Consensus.Goldilocks.Obligations

open SA (SAParams gbar)

variable {sp : SAParams}

/-- **The slot of an anchor after the drain.** With the reset after the reset cut,
`c_z(g) < a`, and the drain of `a` by the anchor's slot time, `drainTime a ≤ t_s`:
`slot a + 2k + 5 ≤ s` and `ḡ + 4Δ ≤ t_s`. -/
theorem drained_anchor_slot {g a : Time} {s : Nat} (hca : Healing.cutZ sp.toParams g < a)
    (hR : Healing.drainTime sp a ≤ sp.ts s) :
    sp.slot a + 2 * sp.k + 5 ≤ s ∧ gbar g + 4 * sp.Δ ≤ sp.ts s := by
  have hΔ := sp.toParams.hΔ
  have hcz := Healing.lt_cutZ sp g
  have ha0 : 0 ≤ a := by
    have := SA.gbar_nonneg g
    linarith
  have hau : sp.slot a + 2 * sp.k + 5 ≤ s := by
    rw [Healing.drainTime_eq] at hR
    exact_mod_cast (SA.ts_le_iff sp).1 hR
  refine ⟨hau, ?_⟩
  have ha' : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
    have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
    omega
  have hle : sp.ts ((sp.slot a : Int) + 2) ≤ sp.ts s := (SA.ts_le_iff sp).2 (by omega)
  have hgap : sp.ts ((sp.slot a : Int) + 2) = sp.ts ((sp.slot a : Int) + 1) + 4 * sp.Δ := by
    simp only [SAParams.ts]; ring
  rw [hgap] at hle
  linarith

end Consensus.Goldilocks.Obligations

end
