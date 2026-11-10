module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Outcome.Foundation
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Obligations: the timing of a healthy repair schedule

A healthy repair schedule from a reset `a` has the query `max(ready, drainTime a)` and the old
label `slot a + 2k + 4`, and its operational openings are placed between the query and the heal
point. These facts read the run's scalars and the slot schedule only, so the repair schedule of
constant faults and that of growing faults use them alike:

* `healthy_repair_lower`: the catch-up duration is at least `18Δ`, and the canonical query is at
  least `max(ready, drainTime a, t_{slot a + 2k + 4}, ḡ + 4Δ, 0)`;
* `healthy_opening_timing`: an opening slot `s` after a query `q` bounded by that maximum, with
  `t_s ≤ q + 4XΔ`, `q + (4X + 6)Δ < heal − 1` and `heal ≤ b`, has `t_s + 6Δ ≤ b`,
  `drainTime r ≤ t_s`, `ḡ + 4Δ ≤ t_s` and `t_{slot ḡ + 1} ≤ t_s`. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape
open Blocks Shape

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The duration and the canonical query of a repair schedule.** With `ready = ḡ + C·d + 1`
and the catch-up `C ≥ 19`: `18Δ ≤ C·d`, and the query `max(ready, drainTime a)` of a reset `a`
bounds `ready`, `drainTime a`, `t_{slot a + 2k + 4}`, `ḡ + 4Δ` and `0`. -/
theorem healthy_repair_lower (run : (Sys (goldilocks S) V).Run) (hn : 1 ≤ Fintype.card V)
    (gst a : Time) :
    let sp := S.params (Model.pubOf run.1) hn
    let ready := (Sys (goldilocks S) V).ready (K S A) gst run
    18 * sp.Δ ≤ (Sys (goldilocks S) V).cDur (K S A) run ∧
      max ready (max (Healing.drainTime sp a)
          (max (sp.ts (sp.slot a + 2 * sp.k + 4 : Nat)) (max (SA.gbar gst + 4 * sp.Δ) 0))) ≤
        max ready (Healing.drainTime sp a) := by
  intro sp ready
  have hc : (19 : Time) ≤ (contract_catchUp S A : Nat) := by
    exact_mod_cast contract_catchUp_ge_sleepy S A
  have hd : (1 : Time) ≤ run.1.ΔAC := run.1.ΔAC_pos
  have hduration : 18 * sp.Δ + 1 ≤ (Sys (goldilocks S) V).cDur (K S A) run := by
    simp only [System.cDur, Params.standard, contract_coefficients_catchUp]
    change 18 * run.1.ΔAC + 1 ≤ (contract_catchUp S A : Nat) * run.1.ΔAC
    linarith [mul_le_mul_of_nonneg_right hc (by linarith : (0 : Time) ≤ run.1.ΔAC)]
  have hΔ := sp.toParams.hΔ
  have hready : SA.gbar gst + 4 * sp.Δ ≤ ready := by
    change max gst 0 + 4 * sp.Δ ≤ max gst 0 + (Sys (goldilocks S) V).cDur (K S A) run + 1
    linarith
  have hzero : 0 ≤ ready := by
    change 0 ≤ max gst 0 + (Sys (goldilocks S) V).cDur (K S A) run + 1
    linarith [le_max_right gst 0]
  have hold : sp.ts (sp.slot a + 2 * sp.k + 4 : Nat) ≤ Healing.drainTime sp a := by
    rw [Healing.drainTime_eq]
    exact (SA.ts_le_iff sp).mpr (by omega)
  exact ⟨by linarith, max_le (le_max_left _ _) (max_le (le_max_right _ _)
    (max_le (hold.trans (le_max_right _ _))
      (max_le (hready.trans (le_max_left _ _)) (hzero.trans (le_max_left _ _)))))⟩

/-- **The timing of an operational opening.** A query `q` at least
`max(ready, drainTime r, t_old, ḡ + 4Δ, 0)`, an opening slot `s` with `q < t_s ≤ q + 4XΔ`, the
reserve `q + (4X + 6)Δ < heal − 1` and `heal ≤ b`: the update tick `t_s + 6Δ` is by `b`, and
`t_s` is after the drain of `r`, after `ḡ + 4Δ` and after the joining slot `slot ḡ + 1`. -/
theorem healthy_opening_timing {sp : SA.SAParams} {ready r q heal b g X : Time} {old s : Nat}
    (hlower : max ready (max (Healing.drainTime sp r)
      (max (sp.ts old) (max (SA.gbar g + 4 * sp.Δ) 0))) ≤ q)
    (hfresh : q < sp.ts s) (hbounded : sp.ts s ≤ q + 4 * X * sp.Δ)
    (hreserve : q + (4 * X + 6) * sp.Δ < heal - 1) (hb : heal ≤ b) :
    sp.ts s + 6 * sp.Δ ≤ b ∧ Healing.drainTime sp r ≤ sp.ts s ∧
      SA.gbar g + 4 * sp.Δ ≤ sp.ts s ∧ sp.ts (sp.slot (SA.gbar g) + 1 : Nat) ≤ sp.ts s := by
  have hd := sp.toParams.hΔ
  have hR : Healing.drainTime sp r ≤ sp.ts s :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans hlower)).trans hfresh.le
  have hgu : SA.gbar g + 4 * sp.Δ ≤ sp.ts s :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hlower)))).trans hfresh.le
  refine ⟨by linarith, hR, hgu, ?_⟩
  have hbase := (SA.ts_le_iff_le_slot sp (SA.gbar_nonneg g) (sp.slot (SA.gbar g))).mpr le_rfl
  simp only [SA.SAParams.ts] at hbase hgu ⊢
  push_cast at hbase hgu ⊢
  linarith

end Consensus.Goldilocks.Obligations

end
