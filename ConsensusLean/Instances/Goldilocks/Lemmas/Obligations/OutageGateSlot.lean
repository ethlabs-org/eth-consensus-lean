module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ContractDefs
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks outage: the slot arithmetic of a reader's latest gate

A reader ready at `t` from the recovery point `b₁ + 9Δ` has its latest gate at the slot
`s = slot(t − 6Δ)`. Its timing reads the slot schedule only, not the run or its fault model:

* `outage_stop_nonneg`: the outage ends at `b₁ ≥ 0`;
* `outage_latest_gate`: `b₁ ≤ t_s + Δ` and `t_s + 6Δ ≤ t < t_s + 10Δ`;
* `outage_gate_restarts`: the gate tick `t_s + 6Δ` is in slot `s + 1`, so a restart up to `t_s + 6Δ`
  is at or before `t_s`, and every restart allowed by joining at `t` is before the tick;
* `latestView_label_of_gate`: every latest view at `t` has label `s + 1`. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape
open Blocks Shape

/-- The outage ends at a time `b₁ ≥ 0`: `0 ≤ T`, `T + lag·Δ_AC ≤ b₀ ≤ b₁`. -/
theorem outage_stop_nonneg {S : Setup} {A : ContractAssumptions S} {V : Type} [Fintype V]
    [DecidableEq V] {run : (Sys (goldilocks S) V).Run} {T start stop : Time}
    (h : (Sys (goldilocks S) V).Outage
      (shapeProgress (goldilocks S) V).toExternal (K S A) T start stop run) : 0 ≤ stop := by
  obtain ⟨hT, hlag, h01, -⟩ := h.times
  have : (0 : Time) ≤ ((K S A).params.lag : Time) * run.1.ΔAC := by
    have := run.1.ΔAC_pos; positivity
  change T + _ * run.1.ΔAC ≤ start at hlag
  change start ≤ stop at h01
  linarith

variable (sp : SA.SAParams)

/-- **The latest gate of a read at `t`** from the recovery point `b + 9Δ` (`b ≥ 0`): the slot
`s = slot(t − 6Δ)` has `b ≤ t_s + Δ` and `t_s + 6Δ ≤ t < t_s + 10Δ`. -/
theorem outage_latest_gate {b t : Time} (hb : 0 ≤ b) (ht : b + 9 * sp.Δ ≤ t) :
    ∃ s : Nat, b ≤ sp.ts s + sp.Δ ∧ sp.ts s + 6 * sp.Δ ≤ t ∧ t < sp.ts s + 10 * sp.Δ := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have h6 : 0 ≤ t - 6 * sp.Δ := by linarith
  obtain ⟨s, hs⟩ : ∃ s, s = sp.slot (t - 6 * sp.Δ) := ⟨_, rfl⟩
  have hs₁ : 4 * sp.Δ * s ≤ t - 6 * sp.Δ := by
    have := (SA.ts_le_iff_le_slot sp h6 (s : Int)).2 (by rw [hs])
    simpa only [SA.SAParams.ts] using this
  have hs₂ : t - 6 * sp.Δ < 4 * sp.Δ * s + 4 * sp.Δ := by
    by_contra hh
    have := (SA.ts_le_iff_le_slot sp h6 ((s : Int) + 1)).1 (by
      simp only [SA.SAParams.ts]; linarith)
    omega
  refine ⟨s, ?_, ?_, ?_⟩ <;> simp only [SA.SAParams.ts] <;> linarith

/-- **The restarts around a gate.** With `t_s + 6Δ ≤ t < t_s + 10Δ`: the gate tick `t_s + 6Δ` is in
slot `s + 1`, so `t_{slot(t_s + 6Δ) − 1} = t_s`; and `slot t ≤ s + 2`, so
`t_{slot t − 1} ≤ t_s + 6Δ`. -/
theorem outage_gate_restarts {s : Nat} {t : Time} (h₁ : sp.ts s + 6 * sp.Δ ≤ t)
    (h₂ : t < sp.ts s + 10 * sp.Δ) :
    sp.ts ((sp.slot (sp.ts s + 6 * sp.Δ) : Int) - 1) = sp.ts s ∧
      sp.ts ((sp.slot t : Int) - 1) ≤ sp.ts s + 6 * sp.Δ := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hs0 : (0 : Time) ≤ 4 * sp.Δ * s := by positivity
  simp only [SA.SAParams.ts] at h₁ h₂
  have ht0 : 0 ≤ t := by linarith
  have hslt : (sp.slot t : Int) ≤ s + 2 := by
    by_contra hh
    have := (SA.ts_le_iff_le_slot sp ht0 ((s : Int) + 3)).2 (by omega)
    simp only [SA.SAParams.ts] at this
    linarith
  have hslu : sp.slot (sp.ts s + 6 * sp.Δ) = s + 1 :=
    SA.slot_of_mem sp (s + 1) (by simp only [SA.SAParams.ts]; push_cast; linarith)
      (by simp only [SA.SAParams.ts]; push_cast; linarith)
  refine ⟨by rw [hslu]; push_cast; ring_nf, ?_⟩
  have h₃ : 4 * sp.Δ * ((sp.slot t : Int) - 1) ≤ 4 * sp.Δ * ((s : Int) + 1) :=
    mul_le_mul_of_nonneg_left (show (sp.slot t : Int) - 1 ≤ (s : Int) + 1 by omega)
      (by linarith)
  simp only [SA.SAParams.ts]
  linarith

/-- **The label of the latest view at a gate.** With `t_s + 6Δ ≤ t < t_s + 10Δ`, every latest view
at `t` has label `s + 1`. -/
theorem latestView_label_of_gate {FGP : Type} (st : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP)
    {s : Nat} {t : Time} (h₁ : sp.ts s + 6 * sp.Δ ≤ t) (h₂ : t < sp.ts s + 10 * sp.Δ) :
    (SA.latestView sp st Φ t).2 = ((s + 1 : Nat) : Int) := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hs0 : (0 : Time) ≤ 4 * sp.Δ * s := by positivity
  simp only [SA.SAParams.ts] at h₁ h₂
  unfold SA.latestView
  dsimp only
  by_cases hlt : t < 4 * sp.Δ * s + 8 * sp.Δ
  · have hsl : sp.slot t = s + 1 :=
      SA.slot_of_mem sp (s + 1) (by simp only [SA.SAParams.ts]; push_cast; linarith)
        (by simp only [SA.SAParams.ts]; push_cast; linarith)
    split_ifs with hc
    · rw [hsl]
    · exfalso; apply hc; rw [hsl]; simp only [SA.SAParams.ts]; push_cast; linarith
  · have hsl : sp.slot t = s + 2 :=
      SA.slot_of_mem sp (s + 2) (by simp only [SA.SAParams.ts]; push_cast; linarith)
        (by simp only [SA.SAParams.ts]; push_cast; linarith)
    split_ifs with hc
    · exfalso; rw [hsl] at hc; simp only [SA.SAParams.ts] at hc; push_cast at hc; linarith
    · rw [hsl]; omega

end Consensus.Goldilocks.Obligations

end
