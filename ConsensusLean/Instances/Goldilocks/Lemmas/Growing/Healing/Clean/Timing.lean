module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetSource
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The clean window after the reset, under growing faults

The growing form of `Healing.ResetPremisesUpTo.clean_window_timing`: a clean label places the
whole slow window after the high-origin cutoff `c_z`. The static proof reads `c_z` below the slot
of a reset seed. Here `c_z < a` comes directly from the finite reset lower bound
`cutZ_lt_reset_at`, and every slot of the window starts after the reset `a`. -/

namespace Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

open SA (SAParams ReplayOrder Payload)

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro} {proposer : Nat → Fin sp.n} {g ΔF a b : Time}

/-- A clean-label bound places the whole slow window after the high-origin cutoff. -/
theorem clean_window_timing_at (hp : ResetPremisesUpTo tr H proposer dg g ΔF a b) {s : Nat}
    (hs : cleanLabel sp a + sp.k + 2 ≤ s) :
    ∀ j : Nat, (s : Int) - sp.k < j → cutZ sp.toParams g ≤ sp.ts j := by
  intro j hj
  have hca := hp.cutZ_lt_reset_at
  have ha0 : 0 ≤ a := by
    have := Healing.lt_cutZ sp g
    have := SA.gbar_nonneg g
    have := sp.toParams.hΔ
    linarith
  rw [Healing.cleanLabel_eq] at hs
  have ha' : a < sp.ts ((sp.slot a : Int) + 1) := not_le.1 fun h => by
    have := (SA.ts_le_iff_le_slot sp ha0 _).1 h
    omega
  have hle : sp.ts ((sp.slot a : Int) + 1) ≤ sp.ts j := (SA.ts_le_iff sp).2 (by omega)
  linarith

end Consensus.Goldilocks.Healing.Growing.ResetPremisesUpTo

end
