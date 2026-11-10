module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.FinalWindowBase
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ResetOfDrainRounds
public import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ResetCoefficients
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.FinalHealHorizon
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.ProposerGap
import ConsensusLean.Lemmas.Blocks.Facts
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks Obligations: the scalar timing of a final query

A final query's progress, maturity and horizon bound are premises on its run, GST, query time and
index only. The timing facts below are stated on these, so the final query of constant faults and
that of growing faults use them alike:

* `final_query_duty`: the final recurrence (`recurrence_gap` on the pattern `[0, c, 2c, 3c]`) gives,
  in every slot window `[x₀, x₀ + X)` inside `[s₀, N]`, a slot `x > 0` with `t_x ≤ horizon` whose
  designated proposer duty is honest and ready;
* `final_reset_bounds`: the ready scalar, the snapshot fit, the reset bound
  `B = ready + (20 L_drain + 24δ_t + 24X + 40)·Δ` between `ready + 4Δ` and the horizon, the horizon
  of every gap window that the reset frame reads (`final_heal_horizon_fit`), and the placement
  (H3) of every reset `0 ≤ a ≤ B` at `u_min = slot a + 2k + 5`. The coefficient input is
  `contract_heal_ge_final`. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open Blocks Shape
open SA (gbar)

variable (S : Setup) (A : ContractAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- The grid of the run's family has the protocol slot times. -/
private theorem grid_slotTime (run : (Sys (goldilocks S) V).Run) (hn : 1 ≤ Fintype.card V)
    (s : Nat) :
    (goldilocks S (Model.pubOf run.1)).skel.grid.slotTime s =
      (S.params (Model.pubOf run.1) hn).ts s := by
  change (s : Time) * (4 * run.1.ΔAC) = 4 * run.1.ΔAC * s
  ring

/-- The grid's slot length is `4Δ`. -/
private theorem grid_slotLen (run : (Sys (goldilocks S) V).Run) (hn : 1 ≤ Fintype.card V) :
    (goldilocks S (Model.pubOf run.1)).skel.grid.slotLen =
      4 * (S.params (Model.pubOf run.1) hn).Δ := by
  have h1 := grid_slotTime S V run hn 1
  simp only [TimeGrid.slotTime, SA.SAParams.ts] at h1
  push_cast at h1
  linarith only [h1]

/-- **The honest-ready duties of a final query.** For the final pattern `[0, c, 2c, 3c]` (`hpat`,
span `3c`), with `max ready 0 + 4Δ ≤ t_{s₀}` and `t_{N + 3c} ≤ horizon`, every slot window
`[x₀, x₀ + X)` inside `[s₀, N]` has a slot `x > 0` with `t_x ≤ horizon` whose designated proposer
duty is honest and ready for the catch-up duration, with the hold `Δ_AC`. -/
theorem final_query_duty (run : (Sys (goldilocks S) V).Run) (hn : 1 ≤ Fintype.card V)
    (index : (K S A).Idx) (gst : Time)
    (hprog : (Sys (goldilocks S) V).prog (shapeProgress (goldilocks S) V) (K S A) .final index
      ((Sys (goldilocks S) V).ready (K S A) gst run) run.2.horizon run)
    {c : Nat} (hpat : (finalWindow A).offsets = [0, c, 2 * c, 3 * c]) {s₀ N : Nat}
    (hs : max ((Sys (goldilocks S) V).ready (K S A) gst run) 0 +
        4 * (S.params (Model.pubOf run.1) hn).Δ ≤ (S.params (Model.pubOf run.1) hn).ts s₀)
    (hN : (S.params (Model.pubOf run.1) hn).ts (N + 3 * c : Nat) ≤ run.2.horizon) :
    ∀ x₀, s₀ ≤ x₀ → x₀ + (index : Nat) ≤ N + 1 → ∃ x, x₀ ≤ x ∧ x < x₀ + (index : Nat) ∧
      0 < x ∧ (S.params (Model.pubOf run.1) hn).ts x ≤ run.2.horizon ∧
      HonestReadyIn run.2.point run.2.key (fun s => run.2.sel (.proposer s)) x
        ((Sys (goldilocks S) V).cDur (K S A) run)
        ((goldilocks S (Model.pubOf run.1)).skel.grid.slotTime x) run.2.point.env.ΔAC := by
  have hrec : PatternRecurrence run.2.point run.2.key
      (fun s => run.2.sel (.proposer s)) (goldilocks S (Model.pubOf run.1)).skel.grid
      ⟨finalWindow A, index, 1⟩ ((Sys (goldilocks S) V).cDur (K S A) run)
      ((Sys (goldilocks S) V).ready (K S A) gst run) run.2.horizon := by
    simpa only [System.prog, shapeProgress, shapeHolds, goldilocksContract, ↓reduceIte,
      Model.sysExternal, System.pt, Sys, Model.sysOf, Model.Run.point] using hprog
  have hspan : (goldilocks S (Model.pubOf run.1)).skel.grid.slotTime N +
      (((⟨finalWindow A, index, 1⟩ : Recurrence).pattern.span : Nat) : Time) *
        (goldilocks S (Model.pubOf run.1)).skel.grid.slotLen =
      (S.params (Model.pubOf run.1) hn).ts (N + 3 * c : Nat) := by
    rw [← grid_slotTime S V run hn, (goldilocks S (Model.pubOf run.1)).skel.grid.slotTime_add]
    simp [finalWindow_span_of_offsets S A hpat]
  have hgap := recurrence_gap hrec (by rw [hpat]; simp) (s₀ := s₀) (N := N)
    (by rw [grid_slotLen S V run hn, grid_slotTime S V run hn]; exact hs)
    (by rw [hspan]; exact hN) (by rw [hspan]; exact hN)
  have hΔ := (S.params (Model.pubOf run.1) hn).toParams.hΔ
  intro x₀ hx₀ hxN
  obtain ⟨x, hxl, hxr, hx⟩ := hgap x₀ hx₀ hxN
  have hxr : x < x₀ + (index : Nat) := hxr
  have hxN : x₀ + (index : Nat) ≤ N + 1 := hxN
  have hx0 : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · exfalso
      have hs0 : s₀ = 0 := Nat.eq_zero_of_le_zero (hx₀.trans (hxl.trans h.le))
      subst hs0
      have := le_max_right ((Sys (goldilocks S) V).ready (K S A) gst run) 0
      simp only [SA.SAParams.ts] at hs
      push_cast at hs
      linarith only [hs, this, hΔ]
    · exact h
  have hxts : (S.params (Model.pubOf run.1) hn).ts x ≤
      (S.params (Model.pubOf run.1) hn).ts (N + 3 * c : Nat) :=
    (SA.ts_le_iff _).2 (by exact_mod_cast
      (Nat.le_of_lt_succ (hxr.trans_le hxN)).trans (Nat.le_add_right N (3 * c)))
  exact ⟨x, hxl, hxr, hx0, hxts.trans hN, by simpa using hx⟩

/-- **The scalar bounds of a final reset.** For a final query at a gap `c` with `2 ≤ c` and
`3c ≤ δ_t` (maturity `hmature`, the deadline within the horizon `hbounded`), with the reset bound
`B = resetBoundRounds ready Δ 2Δ δ_t X L_drain` (`X` the index, `L_drain = healthyDrainLen`):
`0 ≤ ready`, `ḡ ≤ ready`, the snapshot fit `c_z + Δ + 1 ≤ ready + 4Δ`, `ready + 4Δ ≤ B ≤
horizon`; every gap window that the reset frame reads, `t_N + 2Δ < B`, ends within the horizon,
`t_{N + 3c} ≤ horizon`; and every reset `0 ≤ a ≤ B` has the placement (H3) of the two queries at
`u_min = slot a + 2k + 5`. -/
theorem final_reset_bounds (run : (Sys (goldilocks S) V).Run) (hn : 1 ≤ Fintype.card V)
    (index : (K S A).Idx) (gst query : Time)
    (hmature : (Sys (goldilocks S) V).heal (K S A) .final index gst run ≤ query)
    (hbounded : query + ((K S A).params.latency .final index : Time) * run.1.ΔAC ≤
      run.2.horizon)
    {c : Nat} (hc2 : 2 ≤ c) (h3c : 3 * c ≤ S.δt) :
    let sp := S.params (Model.pubOf run.1) hn
    let ready := (Sys (goldilocks S) V).ready (K S A) gst run
    let B := resetBoundRounds ready sp.Δ (2 * sp.Δ) sp.toParams.fg.δt (index : Nat)
      (healthyDrainLen S index)
    let G := (goldilocks S (Model.pubOf run.1)).skel.grid
    0 ≤ ready ∧ gbar gst ≤ ready ∧ Healing.cutZ sp.toParams gst + sp.Δ + 1 ≤ ready + 4 * sp.Δ ∧
      ready + 4 * sp.Δ ≤ B ∧ B ≤ run.2.horizon ∧
      (∀ N : Nat, sp.ts N + 2 * sp.Δ < B → sp.ts (N + 3 * c : Nat) ≤ run.2.horizon) ∧
      ∀ a, 0 ≤ a → a ≤ B →
        max (max ready 0) (G.slotTime (sp.slot a + 2 * sp.k + 5) - 1) +
          ((((index : Nat) + S.δt : Nat) : Time)) * G.slotLen ≤ query + G.slotLen := by
  intro sp ready B G
  let X : Nat := (index : Nat)
  set Ld : Nat := healthyDrainLen S index with hLddef
  set D := sp.Δ with hDdef
  have hD : 0 < D := sp.toParams.hΔ
  have hDe : D = run.1.ΔAC := rfl
  have hd : (1 : Time) ≤ run.1.ΔAC := run.1.ΔAC_pos
  have hδeq : sp.toParams.fg.δt = S.δt := rfl
  -- the ready scalar
  have hready : ready = max gst 0 + ((contract_catchUp S A : Nat) : Time) * run.1.ΔAC + 1 := by
    change max gst 0 + (((contract_coefficients S A).catchUp : Nat) : Time) * run.1.ΔAC + 1 = _
    rw [contract_coefficients_catchUp]
  have hcd : (0 : Time) ≤ ((contract_catchUp S A : Nat) : Time) * run.1.ΔAC :=
    mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hd)
  have hr0 : 0 ≤ ready := by
    rw [hready]; linarith only [le_max_right gst 0, hcd]
  have hgr : gbar gst ≤ ready := by
    change max gst 0 ≤ ready
    rw [hready]; linarith only [hcd]
  have hcz := cutZ_fit_of_catchUp A V (contract_coefficients S A)
    (by rw [contract_coefficients_catchUp]; exact contract_catchUp_ge_sleepy S A) run hn gst
  change Healing.cutZ sp.toParams gst + D + 1 ≤ max ready 0 + 4 * D at hcz
  rw [max_eq_left hr0] at hcz
  -- heal and the coefficient budget, in node delays `D = Δe`
  have hheal : max gst 0 + ((K S A).params.heal .final index : Time) * run.1.ΔAC ≤ query :=
    hmature
  have hbud : ((contract_catchUp S A : Nat) : Time) +
      (20 * (Ld : Time) + 8 * S.k + 28 * S.δt + 28 * X + 56) ≤
      ((K S A).params.heal .final index : Time) := by
    have h := contract_heal_ge_final S A index
    have he : (K S A).params.heal .final index = contract_heal S A .final index := by
      simp only [Params.standard, contract_coefficients_heal]
    rw [he]
    exact_mod_cast h
  set Mf : Time := 20 * (Ld : Time) + 8 * S.k + 28 * S.δt + 28 * X + 56 with hMf
  have hq : ready + Mf * D - 1 ≤ query := by
    have h1 := mul_le_mul_of_nonneg_right hbud (zero_le_one.trans hd)
    rw [hready, hDe]; linarith only [h1, hheal]
  have hqh : query ≤ run.2.horizon := by
    linarith only [hbounded, (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hd) :
      (0 : Time) ≤ ((K S A).params.latency .final index : Time) * run.1.ΔAC)]
  -- the reset bound `B`
  have hBeq : B = ready + (20 * (Ld : Time) + 24 * S.δt + 24 * X + 40) * D := by
    change resetBoundRounds ready D (2 * D) sp.toParams.fg.δt X Ld = _
    rw [resetBoundRounds_eq, hδeq]; ring
  have hX1 : (1 : Time) ≤ X := by exact_mod_cast index.pos
  have hLd0 : (0 : Time) ≤ Ld := Nat.cast_nonneg _
  have hBc : B + (12 * (c : Time) - 2) * D ≤ run.2.horizon := by
    have := final_heal_horizon_fit (k := (S.k : Time)) (Ld := (Ld : Time)) hD (Nat.cast_nonneg _)
      (Nat.cast_nonneg X) (show 3 * (c : Time) ≤ (S.δt : Time) by exact_mod_cast h3c)
    rw [hBeq]; rw [hMf] at hq; linarith only [this, hq, hqh]
  have hc2' : (2 : Time) ≤ c := by exact_mod_cast hc2
  have hBh : B ≤ run.2.horizon := by
    linarith only [hBc, mul_nonneg (show (0 : Time) ≤ 12 * c - 2 by linarith only [hc2']) hD.le]
  have h4B : ready + 4 * D ≤ B := by
    have : (4 : Time) * D ≤ (20 * (Ld : Time) + 24 * S.δt + 24 * X + 40) * D :=
      mul_le_mul_of_nonneg_right (by linarith only [hLd0, hX1, Nat.cast_nonneg (α := Time) S.δt])
        hD.le
    rw [hBeq]; linarith only [this]
  -- the horizon of the gap windows that the reset frame reads
  have hgapN : ∀ N : Nat, sp.ts N + 2 * D < B → sp.ts (N + 3 * c : Nat) ≤ run.2.horizon := by
    intro N hN
    have : sp.ts (N + 3 * c : Nat) = sp.ts N + 12 * (c : Time) * D := by
      simp only [SA.SAParams.ts]; push_cast; ring
    rw [this]; linarith only [hN, hBc]
  refine ⟨hr0, hgr, hcz, h4B, hBh, hgapN, fun a ha0 hab => ?_⟩
  -- the placement (H3)
  have hsa : sp.ts (sp.slot a : Int) ≤ a := (SA.ts_le_iff_le_slot sp ha0 _).2 le_rfl
  have hseed : G.slotTime (sp.slot a + 2 * sp.k + 5) ≤ a + 4 * D * (2 * S.k + 5) := by
    rw [show sp.slot a + 2 * sp.k + 5 = sp.slot a + 2 * S.k + 5 from rfl,
      grid_slotTime S V run hn]
    simp only [SA.SAParams.ts] at hsa ⊢
    rw [← hDdef] at hsa ⊢
    push_cast; linarith only [hsa]
  rw [grid_slotLen S V run hn, max_eq_left hr0]
  push_cast
  apply add_le_of_le_sub_right
  apply max_le
  · have : (4 * (X : Time) + 4 * S.δt) * D ≤ Mf * D := by
      apply mul_le_mul_of_nonneg_right _ hD.le
      rw [hMf]
      linarith only [hLd0, Nat.cast_nonneg (α := Time) S.k, Nat.cast_nonneg (α := Time) S.δt,
        Nat.cast_nonneg (α := Time) X]
    have h1D : (1 : Time) ≤ D := hD
    linarith only [this, hq, h1D]
  · have : (20 * (Ld : Time) + 24 * S.δt + 24 * X + 40) * D + 4 * D * (2 * S.k + 5) +
        (X + S.δt) * (4 * D) - 4 * D = Mf * D := by rw [hMf]; ring
    rw [hBeq] at hab
    linarith only [this, hab, hseed, hq]

end Consensus.Goldilocks.Obligations

end
