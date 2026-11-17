module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.RunMap
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.SleepyWindows
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ClaimTransports
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.PreparationInitialize
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.HealedSafetyConditional
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Healthy.Opening
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Healing.Kernel.ResetSource
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Arith
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The reset-heal budget of a Goldilocks run

`goldilocks_resetHealBudgetSupply`: at the advertised contract `K S A` and any vote binding `S`, the
local supplier at its data equations (drain `2k + 5`, margin `6Δ`) selects, for every healthy
nonfinal query with progress up to a heal point within the horizon, an actual reset whose drain
slot fits before the heal point, together with an honest opening at or after that drain slot.
The reset, the repair schedule and the opening are those of the healthy preparation of the query
(`healthy_preparation_initialize_late_at`, `healthy_repair_schedule_of_preparation_at`,
`healthy_bounded_repairing_opening_at`) at bound `horizon`. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape Blocks Generic Obligations Obligations.Growing
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The reset-heal budget at the advertised contract**, at any vote binding: the reset of the
healthy preparation, its drain slot, and the honest opening of the preparation's repair
schedule. -/
theorem goldilocks_resetHealBudgetSupply (S : Setup) (A : ContractAssumptions S) {E : Env V}
    (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid)
    (C : ACCorrectLocal (goldilocksNode (S.params (pubOf E) hn) (S.ro _)) (fun v => v.val))
    (hC : GoldilocksLocalData (S.params (pubOf E) hn) (S.ro _) C)
    (hsg : (fun v => v.val) = (goldilocksRunMap S rho hn hv).signer) :
    ResetHealBudgetSupply (goldilocksRunMap S rho hn hv) (K S A) (hsg ▸ C) := by
  classical
  obtain ⟨hmargin, hdrainC⟩ := Generic.ACCorrectLocal.cast_signer hsg C
    (fun _ C' => C'.margin = C.margin ∧ C'.healing.drain = C.healing.drain) ⟨rfl, rfl⟩
  obtain ⟨⟨-, -, -, hdrain, -⟩, -, -, -, -, -, hm, -⟩ := hC
  intro hv' hnc cap idx gst hcap hH hp hhb
  rw [goldilocksRunMap_trace, goldilocksRunMap_honest, goldilocksRunMap_proposer]
  obtain ⟨hps, hon, hΔF, hcom⟩ := hH
  let sp := S.params (pubOf E) hn
  let Q : HealthyPreparationQueryAt S A V :=
    { run := ⟨E, rho⟩
      hn := hn
      cap := cap
      nonfinal := hcap
      index := idx
      gst := gst
      bound := rho.horizon
      valid := hv'
      noCollision := hnc
      bound_le := le_rfl
      healthy := ⟨hps, hon, hΔF⟩
      committeeHealthy := hcom }
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hheal0 : 0 ≤ Q.heal := by
    change 0 ≤ max gst 0 + ((K S A).params.heal cap idx : Time) * E.ΔAC
    have := E.ΔAC_pos
    positivity
  obtain ⟨W, Dprep, hlate⟩ := healthy_preparation_initialize_late_at S A V Q hheal0 hhb hp
  obtain ⟨D, -, -, hDq⟩ := healthy_repair_schedule_of_preparation_at S A V Q W Dprep
  obtain ⟨O⟩ := healthy_bounded_repairing_opening_at S A V Q hhb hp D
  have hts : ∀ s : Nat, sp.toParams.slotTime s = sp.ts s := fun s => by
    rw [sp.slotTime_eq]; simp [SA.SAParams.ts]
  have hslot : ∀ a, sp.toParams.slotOf a = sp.slot a := fun _ => rfl
  -- the drain slot is the preparation's drain time
  have hdt : sp.toParams.slotTime (sp.toParams.slotOf D.resetTime + (hsg ▸ C).healing.drain) =
      Healing.drainTime sp D.resetTime := by
    rw [hdrainC, hdrain, hslot, hts, Healing.drainTime_eq, ← add_assoc]
  have hlow := D.lower
  simp only [max_le_iff] at hlow
  obtain ⟨-, hdq, -, -, -⟩ := hlow
  have hcz := D.reset.cutZ_lt_reset_at
  have hgz := Healing.lt_cutZ (sp := sp) gst
  have ha0 : 0 ≤ D.resetTime := by
    have := SA.gbar_nonneg gst
    linarith
  have hadrain : D.resetTime < Healing.drainTime sp D.resetTime := by
    rw [Healing.drainTime_eq]
    by_contra h
    have h' := (SA.ts_le_iff_le_slot sp ha0 _).mp (not_lt.mp h)
    push_cast at h'
    omega
  have hX : (1 : Time) ≤ (idx : Nat) := by exact_mod_cast idx.pos
  have hbound := O.bounded
  have hres : D.query + (4 * ((idx : Nat) : Time) + 14) * sp.Δ + 2 ≤ Q.heal := by
    rw [hDq]; exact hlate
  have hmΔ : (hsg ▸ C).margin = 6 * sp.Δ := by rw [hmargin, hm]
  have hsd : Healing.drainTime sp D.resetTime ≤ sp.ts O.slot := O.drain
  have hs₁ : sp.slot D.resetTime + 2 * sp.k + 5 ≤ O.slot := by
    rw [Healing.drainTime_eq] at hsd
    exact_mod_cast (SA.ts_le_iff sp).mp hsd
  refine ⟨D.resetTime, D.reset.reset, D.reset.reset_le, ?_, ?_, O.slot,
    runProposer S rho hn O.slot, O.cut, O.block, ?_, ?_, ?_, ?_,
    ⟨O.held, rfl, O.proposes, O.label⟩⟩
  · rw [hdt]
    unfold SA.gbar at hgz
    linarith
  · rw [hdt, hmΔ]
    linarith [mul_nonneg (zero_le_one.trans hX) hΔ.le]
  · rw [hdrainC, hdrain, hslot]
    exact hs₁
  · rw [hts]; exact O.late
  · rw [hts]; exact O.service
  · rw [hts, hmΔ]
    linarith [mul_nonneg (zero_le_one.trans hX) hΔ.le]

end Consensus.Goldilocks.Simulation

end
