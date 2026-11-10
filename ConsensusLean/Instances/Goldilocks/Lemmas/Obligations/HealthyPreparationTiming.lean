module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Obligations: the timing of a healthy preparation

A healthy preparation query's ready and heal points are scalars of its run, GST, capability and
index only. The timing facts below are stated on these, so the preparation of constant faults and
that of growing faults use them alike:

* `healthy_heal_margin`: a heal coefficient `H ≥ C + M + 3` over the catch-up `C` gives
  `ready + M·Δ + 2 ≤ heal`;
* `healthy_preparation_timing`: with the reserve `ready + (R + 8k + 4X + 26)·Δ + 2 ≤ heal`
  (`R = healthyResetCoeff`), the base slot `w = slot(ready) + 1` has the base timing, and every
  reset `0 ≤ a ≤ ready + R·Δ + r` with a seed label `l ≤ slot a` has its query lower bound at most
  `ready + (R + 8k + 20)·Δ`. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape
open Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The heal margin over readiness.** With engine delay `d ≥ 1`, `Δ = d`,
`ready = g₀ + C·d + 1` and `heal = g₀ + H·d`, a heal coefficient `H ≥ C + M + 3` gives
`heal − ready − M·Δ ≥ 2d ≥ 2`. -/
theorem healthy_heal_margin (run : (Sys (goldilocks S) V).Run) (hn : 1 ≤ Fintype.card V)
    (cap : Capability) (index : (K S A).Idx) (gst : Time) {M : Nat}
    (hM : (contract_catchUp S A : Nat) + M + 3 ≤ contract_heal S A cap index) :
    (Sys (goldilocks S) V).ready (K S A) gst run +
        (M : Time) * (S.params (Model.pubOf run.1) hn).Δ + 2 ≤
      (Sys (goldilocks S) V).heal (K S A) cap index gst run := by
  have hd : (1 : Time) ≤ run.1.ΔAC := run.1.ΔAC_pos
  have hΔ : (S.params (Model.pubOf run.1) hn).Δ = run.1.ΔAC := rfl
  have hready : (Sys (goldilocks S) V).ready (K S A) gst run =
      max gst 0 + ((contract_catchUp S A : Nat) : Time) * run.1.ΔAC + 1 := by
    change max gst 0 + (((contract_coefficients S A).catchUp : Nat) : Time) * run.1.ΔAC + 1 = _
    rw [contract_coefficients_catchUp]
  have hheal : (Sys (goldilocks S) V).heal (K S A) cap index gst run =
      max gst 0 + (contract_heal S A cap index : Time) * run.1.ΔAC := by
    change max gst 0 + ((contract_coefficients S A).heal cap index : Time) * run.1.ΔAC = _
    rw [contract_coefficients_heal]
  have hH : ((contract_catchUp S A : Nat) : Time) + M + 3 ≤ (contract_heal S A cap index : Time) :=
    by exact_mod_cast hM
  rw [hready, hheal, hΔ]
  linarith only [mul_le_mul_of_nonneg_right hH (zero_le_one.trans hd), hd]

/-- **The base slot and the query bound of a healthy preparation.** With the reserve
`ready + (R + 8k + 4X + 26)·Δ + 2 ≤ heal` (`R = healthyResetCoeff`, `X` the index): the base slot
`w = slot(ready) + 1` has `ready ≤ t_w`, `t_w + 6Δ ≤ heal`, `t_{w+2} ≤ heal`, `t_{w+k} ≤ heal`
and `t_{w+2} + 6Δ ≤ heal`; and every reset `0 ≤ a ≤ ready + R·Δ + r` (`r = healthyResetSlack`)
with a seed label `l ≤ slot a` has
`max(ready, drainTime a, t_w, ḡ + 4Δ, 0, t_{l+1}) ≤ ready + (R + 8k + 20)·Δ`. -/
theorem healthy_preparation_timing (run : (Sys (goldilocks S) V).Run) (hn : 1 ≤ Fintype.card V)
    (cap : Capability) (index : (K S A).Idx) (gst : Time)
    (hB : (Sys (goldilocks S) V).ready (K S A) gst run +
        ((healthyResetCoeff S index : Time) + 8 * (S.k : Time) + 4 * ((index : Nat) : Time) + 26) *
          (S.params (Model.pubOf run.1) hn).Δ + 2 ≤
      (Sys (goldilocks S) V).heal (K S A) cap index gst run) :
    let sp := S.params (Model.pubOf run.1) hn
    let ready := (Sys (goldilocks S) V).ready (K S A) gst run
    let heal := (Sys (goldilocks S) V).heal (K S A) cap index gst run
    ∃ w : Nat, (ready ≤ sp.ts w ∧ sp.ts w + 6 * sp.Δ ≤ heal ∧ sp.ts (w + 2 : Nat) ≤ heal ∧
        sp.ts (w + sp.k : Nat) ≤ heal ∧ sp.ts (w + 2 : Nat) + 6 * sp.Δ ≤ heal) ∧
      ∀ (a : Time) (l : Nat), 0 ≤ a →
        a ≤ ready + (healthyResetCoeff S index : Time) * sp.Δ + (healthyResetSlack S index : Time) →
        l ≤ sp.slot a →
        max ready (max (Healing.drainTime sp a) (max (sp.ts w)
            (max (SA.gbar gst + 4 * sp.Δ) (max 0 (sp.ts (l + 1 : Nat)))))) ≤
          ready + ((healthyResetCoeff S index : Time) + 8 * (S.k : Time) + 20) * sp.Δ := by
  intro sp ready heal
  have hd : (1 : Time) ≤ run.1.ΔAC := run.1.ΔAC_pos
  have hD0 : (0 : Time) ≤ sp.Δ := zero_le_one.trans hd
  have hΔ : sp.Δ = run.1.ΔAC := rfl
  have hready : ready = max gst 0 + ((contract_catchUp S A : Nat) : Time) * run.1.ΔAC + 1 := by
    change max gst 0 + (((contract_coefficients S A).catchUp : Nat) : Time) * run.1.ΔAC + 1 = _
    rw [contract_coefficients_catchUp]
  have hC : (19 : Time) ≤ (contract_catchUp S A : Nat) := by
    exact_mod_cast contract_catchUp_ge_sleepy S A
  have hkk : (sp.k : Time) = S.k := rfl
  have hR0 : (24 : Time) ≤ healthyResetCoeff S index := by
    rw [healthyResetCoeff_val]; push_cast
    linarith only [Nat.cast_nonneg (α := Time) (healthyDrainLen S index)]
  have hX0 : (0 : Time) ≤ ((index : Nat) : Time) := Nat.cast_nonneg _
  have hr0 : 0 ≤ ready := by
    rw [hready]
    exact add_nonneg (add_nonneg (le_max_right _ _) (mul_nonneg (Nat.cast_nonneg _) hD0))
      zero_le_one
  have hgr : SA.gbar gst + 4 * sp.Δ ≤ ready := by
    change max gst 0 + _ ≤ _
    rw [hready, hΔ]
    linarith only [mul_le_mul_of_nonneg_right hC (zero_le_one.trans hd), hd]
  -- the base slot `w = slot(ready) + 1`: `ready < t_w ≤ ready + 4Δ`
  have hts (s j : Nat) : sp.ts (s + j : Nat) = sp.ts s + 4 * sp.Δ * j := by
    simp only [SA.SAParams.ts]; push_cast; ring
  set w : Nat := sp.slot ready + 1 with hw
  have hw0 : sp.ts (sp.slot ready : Nat) ≤ ready :=
    (SA.ts_le_iff_le_slot sp hr0 _).mpr le_rfl
  have hw1 : ready < sp.ts w := by
    have h := (SA.ts_le_iff_le_slot sp hr0 (w : Int)).not.mpr (by rw [hw]; push_cast; omega)
    exact lt_of_not_ge h
  have hw2 : sp.ts w ≤ ready + 4 * sp.Δ := by
    rw [hw, hts]; push_cast; linarith only [hw0]
  have hkD : (0 : Time) ≤ (S.k : Time) * sp.Δ := mul_nonneg (Nat.cast_nonneg _) hD0
  have hRD := mul_le_mul_of_nonneg_right hR0 hD0
  have hXD : (0 : Time) ≤ ((index : Nat) : Time) * sp.Δ := mul_nonneg hX0 hD0
  refine ⟨w, ⟨hw1.le, by linarith only [hw2, hB, hRD, hkD, hXD, hD0],
    by rw [hts]; push_cast; linarith only [hw2, hB, hRD, hkD, hXD, hD0],
    by rw [hts, hkk]; linarith only [hw2, hB, hRD, hkD, hXD, hD0],
    by rw [hts]; push_cast; linarith only [hw2, hB, hRD, hkD, hXD, hD0]⟩,
    fun a l ha0 ha hla => ?_⟩
  -- the reset, its drain and its seed
  rw [healthyResetSlack_val] at ha
  push_cast at ha
  have hsa : sp.ts (sp.slot a : Nat) ≤ a := (SA.ts_le_iff_le_slot sp ha0 _).mpr le_rfl
  have hdrain : Healing.drainTime sp a ≤ a + (8 * (S.k : Time) + 20) * sp.Δ := by
    rw [Healing.drainTime_eq, show sp.slot a + 2 * sp.k + 5 = sp.slot a + (2 * S.k + 5) from rfl,
      hts]
    push_cast; linarith only [hsa]
  have hseed : sp.ts (l + 1 : Nat) ≤ a + 4 * sp.Δ := by
    have hl : ((l + 1 : Nat) : Int) ≤ (sp.slot a : Int) + 1 := by push_cast; omega
    have := mul_le_mul_of_nonneg_left hl (mul_nonneg zero_le_four hD0)
    simp only [SA.SAParams.ts] at hsa ⊢
    linarith only [this, hsa]
  exact max_le (by linarith only [hRD, hkD, hD0]) (max_le (by linarith only [hdrain, ha])
    (max_le (by linarith only [hw2, hRD, hkD, hD0])
      (max_le (by linarith only [hgr, hRD, hkD, hD0])
        (max_le (by linarith only [hr0, hRD, hkD, hD0])
          (by linarith only [hseed, ha, hkD, hD0])))))

end Consensus.Goldilocks.Obligations

end
