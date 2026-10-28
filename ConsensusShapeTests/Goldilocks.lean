module
public import ConsensusShape
public import Mathlib.Tactic
@[expose] public section

/-! # Tests of the Goldilocks value and sheet

* `pp223_numbers`: the pinned formulas give the FG-SA paper's reference
  numbers (`reference_bounds`), and the heal and latency tables read them; at
  `R = 2`, `lockK = 2`, `eta = 3`: catch-up `18`, lag `4`, budget `3`,
  look-back `η = 3`, standard thresholds, and the finality recurrence at
  `gf = 1` has `8` consecutive proposers (span `7`) per `2` slots.
* `EnvPoint.two_mul_card_faulty_union_lt`: the outage cover ½ at `b₀` gives
  FG-SA's `OutageE1` (migration obligation 4 of the sheet).
* `stable_is_confirmed`: the schema aliases stable to confirmed (`rfl`).
* `collapse_prefix_only`, `outageWindow_prefix_only`: a run whose
  participation collapses inside the outage is η-sleepy on the prefix
  `[0, b₀]` but not through `b₁ − 1`; A2 asks only for the prefix.
* `weakPremise_inhabited` (P-NV-CONTINUATION): the weak-continuation premise
  holds on the generic healthy witness, so the weak extras are not vacuous. -/

namespace Consensus

namespace EnvPoint

variable {V : Type} [Fintype V] [DecidableEq V] {p : EnvPoint V}

/-- If every validator ready at `t` is in an honest set `C`, and `W` avoids
`C`, then more than half of all validators ready gives `2·|faulty ∪ W| < n`
(the outage cover at `b₀` with `cover = ½` gives FG-SA's `OutageE1`: faulty
validators and uncovered wakers are fewer than half). -/
theorem two_mul_card_faulty_union_lt {c t : Time} {C W : Finset V}
    (hR : p.readyAt c t ⊆ C) (hC : C ⊆ p.honest) (hW : Disjoint W C)
    (h : p.ReadyOfAll (1 / 2) c t) : 2 * (p.faulty ∪ W).card < Fintype.card V := by
  have hdis : Disjoint (p.faulty ∪ W) C := by
    refine Finset.disjoint_union_left.mpr ⟨?_, hW⟩
    refine Finset.disjoint_left.mpr fun v hv hvC => ?_
    exact (Finset.mem_sdiff.mp hv).2 (hC hvC)
  have hsum : (p.faulty ∪ W).card + C.card ≤ Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hdis]
    exact Finset.card_le_univ _
  have hRC : (p.readyAt c t).card ≤ C.card := Finset.card_le_card hR
  have h' : (Fintype.card V : ℚ) < 2 * (p.readyAt c t).card := by
    unfold ReadyOfAll at h; linarith
  have h'' : Fintype.card V < 2 * (p.readyAt c t).card := by exact_mod_cast h'
  omega

end EnvPoint

end Consensus

namespace Consensus.Shape.Tests.Goldilocks

open Consensus Blocks Shape

/-- `R = 2`, `lockK = 2`, `eta = 3`. -/
def pp223 : FGSAParams := ⟨2, 2, 3, le_rfl, le_rfl, by decide⟩

/-- The reference numbers and the heal and latency tables at them; the pinned
outage and catch-up numbers at `⟨2, 2, 3⟩` and standard thresholds; the
finality recurrence at `R = 2`, `gf = 1`: `8` consecutive proposers (span `7`)
per window of `2` slots. -/
theorem pp223_numbers :
    (⟨2, 2, 1, le_rfl, le_rfl, le_rfl⟩ : FGSAParams).bhf 2 = 295 ∧
      (⟨3, 2, 1, by decide, le_rfl, le_rfl⟩ : FGSAParams).bhf 2 = 343 ∧
      pp223.heal .available 2 = 29 + 295 ∧ pp223.heal .stable 2 = 29 + 295 ∧
      pp223.latency .available 2 = 14 ∧
      pp223.heal .final 1 = 29 + pp223.bhf 2 + pp223.wW 1 ∧
      pp223.latency .final 1 = 4 * 2 + 6 + pp223.wW 1 ∧
    (goldilocksContract pp223).params.catchUp = 18 ∧ (goldilocksContract pp223).params.lag = 4 ∧
      (goldilocksContract pp223).params.budget = 3 ∧ (goldilocksContract pp223).params.η = 3 ∧
      (goldilocksContract pp223).params.θ = 1 / 2 ∧ (goldilocksContract pp223).params.φ = 2 / 3 ∧
      (goldilocksContract pp223).params.cover = 1 / 2 ∧
      (goldilocksContract pp223).params.α = 1 / 3 ∧
    (pp223.finRec 1).pattern.span = 7 ∧ ((pp223.finRec 1).gap : Nat) = 2 :=
  ⟨reference_bounds.1, reference_bounds.2.1, by decide, by decide, by decide, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, (Pattern.span_range _).trans rfl, rfl⟩

/-- The schema aliases stable (and available) to confirmed. -/
theorem stable_is_confirmed :
    goldilocksSchema.output .stable = some GOut.confirmed ∧
      goldilocksSchema.output .available = some GOut.confirmed ∧
      goldilocksSchema.output .final = some GOut.finalized :=
  ⟨rfl, rfl, rfl⟩

/-! ### A2 participation only on the prefix -/

/-- Five validators, `0` faulty, `1` honest and always awake, `2`–`4` honest
and awake up to time `5`, asleep after it: participation collapses at `6`,
inside an outage `[b₀, b₁) = [5, 10)`. `Δ = 1`, horizon `10`. -/
def collapsePoint : EnvPoint (Fin 5) :=
  ⟨⟨1, by decide, fun v t => decide ((v : Nat) ≤ 1 ∨ t ≤ 5)⟩, Finset.univ.erase 0, 10,
    fun _ _ => []⟩

theorem collapsePoint_faulty : collapsePoint.faulty = {0} := by
  unfold EnvPoint.faulty collapsePoint; ext v; simp

theorem collapsePoint_readyAt {t : Time} (h5 : t ≤ 5) :
    collapsePoint.readyAt 0 t = Finset.univ.erase 0 := by
  classical
  ext v
  simp only [EnvPoint.readyAt, EnvPoint.Ready, EnvPoint.AwakeOnClosed, collapsePoint,
    Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, decide_eq_true_eq]
  constructor
  · exact fun h => h.1
  · intro hv
    exact ⟨hv, hv, fun u _ hu => Or.inr (le_trans hu h5)⟩

theorem collapsePoint_readyAt_six : collapsePoint.readyAt 0 6 ⊆ {1} := by
  classical
  intro v hv
  simp only [EnvPoint.readyAt, EnvPoint.Ready, EnvPoint.AwakeOnClosed, collapsePoint,
    Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, decide_eq_true_eq] at hv
  obtain ⟨hv0, -, hA⟩ := hv
  have h6 := hA 6 (by norm_num) le_rfl
  have hle : (v : Nat) ≤ 1 := by
    rcases h6 with h | h
    · exact h
    · norm_num at h
  simp only [Finset.mem_singleton]
  fin_cases v <;> simp_all

/-- The collapsing run is ½-η-sleepy (look-back `3`) on the prefix `[0, 5]`
but not on `[0, 9]`: at `6` one validator is ready while all four honest ones
were awake in `[3, 6]`. A2's premise (`outageWindow_prefix_only`) asks only
for the prefix, so it applies here; the stage-5 premise on `[0, b₁ − 1]` did
not. -/
theorem collapse_prefix_only :
    collapsePoint.EtaSleepyOn (1 / 2) 3 0 0 5 ∧ ¬ collapsePoint.EtaSleepyOn (1 / 2) 3 0 0 9 := by
  classical
  refine ⟨fun t _ ht5 => ?_, fun h => ?_⟩
  · rw [EnvPoint.EtaReadyAbove,
      ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (3 : Time) ≤ 0 by norm_num)),
      collapsePoint_readyAt ht5]
    have hc : ((Finset.univ.erase (0 : Fin 5) ∪ collapsePoint.awakeIn (max 0 (t - 3)) t ∪
        collapsePoint.faulty).card : ℚ) ≤ 5 := by
      have := Finset.card_le_univ (Finset.univ.erase (0 : Fin 5) ∪
        collapsePoint.awakeIn (max 0 (t - 3)) t ∪ collapsePoint.faulty)
      rw [Fintype.card_fin] at this
      exact_mod_cast this
    have h4 : ((Finset.univ.erase (0 : Fin 5)).card : ℚ) = 4 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; rfl
    rw [h4]; linarith
  · have h6 := h 6 (by norm_num) (by norm_num)
    rw [EnvPoint.EtaReadyAbove,
      ite_eq_right_of_eq_false _ _ (eq_false (show ¬ (3 : Time) ≤ 0 by norm_num))] at h6
    have hin : collapsePoint.readyAt 0 6 ∪ collapsePoint.awakeIn (max 0 (6 - 3)) 6 ∪
        collapsePoint.faulty = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro v
      by_cases h0 : v = 0
      · exact Finset.mem_union_right _ (by rw [collapsePoint_faulty, h0]; simp)
      · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
        simp only [EnvPoint.awakeIn, collapsePoint, Finset.mem_filter, Finset.mem_erase,
          Finset.mem_univ, and_true, decide_eq_true_eq]
        exact ⟨h0, 3, by norm_num, by norm_num, Or.inr (by norm_num)⟩
    have hcard : ((collapsePoint.readyAt 0 6).card : ℚ) ≤ 1 := by
      have := (Finset.card_le_card collapsePoint_readyAt_six).trans
        (Finset.card_singleton (1 : Fin 5)).le
      exact_mod_cast this
    rw [hin, Finset.card_univ, Fintype.card_fin] at h6
    norm_num at h6
    linarith

/-- A2 takes η-sleepy participation on the prefix `[0, b₀]` only (and nothing
after `b₀`): this statement fails to type-check if the premise is extended
into the outage window again. -/
theorem outageWindow_prefix_only {Info : Type} [DecidableEq Info] [Encodable Info]
    {F : ShapeFamily goldilocksSchema Info} {pp : FGSAParams} (h : GoldilocksExtra F pp)
    {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (rho : Model.Run (compiled F) E)
    (T b₀ b₁ : Time) (hv : rho.ExecutionValid)
    (hT : OutageTimes (goldilocksContract pp).params E.Δ T b₀ b₁)
    (hs : CommLog.SyncUntil rho.point rho.log b₀)
    (hη : rho.point.EtaSleepyOn (1 / 2) ((pp.eta : Time) * E.Δ)
      (shapeC (goldilocksContract pp) rho) 0 b₀)
    (hc : rho.point.ReadyOfAll (1 / 2) (shapeC (goldilocksContract pp) rho) b₀) :
    (chainTrace rho).ProtectedUpTo (shapeC (goldilocksContract pp) rho) gConfirmed gConfirmed
      T b₀ b₁ (min (b₁ - 1) rho.horizon) ∨ rho.HashCollision :=
  h.outageWindow T b₀ b₁ V E rho hv hT hs hη hc

/-- **P-NV-CONTINUATION.** The weak-continuation premise is inhabited, so the
weak extras (`weakSafe`, `weakCrossNest`, `weakInclude`, `weakGrow`) are not
vacuous: the generic healthy witness (everyone awake, five validators) is
healthy up to the heal point, has the recurrence of `k`, and is sleepy after
the heal point. -/
theorem weakPremise_inhabited {Info : Type} [DecidableEq Info] [Encodable Info]
    (F : ShapeFamily goldilocksSchema Info) (hb : GoldilocksBindings F) (pp : FGSAParams)
    (k : ℕ+) {Δ : Time} (hΔ : 0 < Δ) (g : Time) :
    ∃ (E : Env (Fin 5)) (rho : Model.Run (compiled F) E), rho.ExecutionValid ∧
      WeakPremise pp rho g k := by
  let K := goldilocksContract pp
  let key : Fin (Fintype.card (Fin 5)) ≃ Fin 5 := (Fintype.equivFin (Fin 5)).symm
  have hn : 5 ≤ Fintype.card (Fin 5) := by simp
  have ha := goldilocks_admissible pp
  have hf := goldilocks_progressFits pp F (fun pub => by rw [hb pub]; rfl)
  have hL := progLen_nonneg F K .available k (⟨Δ, hΔ, allAwake⟩ : Env (Fin 5))
  have hlat : 0 ≤ K.params.latDur Δ .available k := mul_nonneg (by positivity) hΔ.le
  have hheal : 0 ≤ K.params.healPoint Δ .available k g :=
    add_nonneg (le_max_right _ _) (mul_nonneg (by positivity) hΔ.le)
  have hrdy : 0 ≤ readyFrom (K.params.cDur Δ) g := by
    unfold readyFrom Params.cDur
    have := le_max_right g 0
    have : (0 : Time) ≤ (K.params.catchUp : Time) * Δ := mul_nonneg (by positivity) hΔ.le
    linarith
  obtain ⟨rho, hpt, -, hw, -, hH, hp, -, -, -⟩ := healthy_witness (F := F) (K := K) key hn hΔ
    (K.params.healPoint Δ .available k g + readyFrom (K.params.cDur Δ) g +
      K.params.latDur Δ .available k + progLen F K .available k ⟨Δ, hΔ, allAwake⟩ + Δ + 2)
    ha hf .available k g (by linarith) (by linarith) (by linarith)
  have hhh : shapeHeal K rho .available k g ≤ rho.horizon := by
    have hh : rho.horizon = rho.point.horizon := rfl
    rw [hh, hpt]
    change K.params.healPoint Δ .available k g ≤ K.params.healPoint Δ .available k g +
      readyFrom (K.params.cDur Δ) g + K.params.latDur Δ .available k +
      progLen F K .available k ⟨Δ, hΔ, allAwake⟩ + Δ + 2
    linarith
  refine ⟨_, rho, hw.1, (Model.sysOf_delivers_iff rho _ _).mp hH.1, ?_,
    (shapeProgress F (Fin 5)).mono le_rfl hhh hp, ?_⟩
  · obtain ⟨S, hS, hcard, hawk⟩ := hH.2
    exact ⟨S, hS, hcard, fun v hv u h1 h2 => hawk v hv u h1 (h2.trans hhh)⟩
  · intro t _ _
    rw [hpt]
    refine readyAbove_of_card hn ha.θ_range _ t ?_ ?_
    · rw [realPoint_faulty]; rfl
    · exact (allAwake_readyAt key hn hΔ _ _ t).trans (Nat.le_succ _)

end Consensus.Shape.Tests.Goldilocks

end
