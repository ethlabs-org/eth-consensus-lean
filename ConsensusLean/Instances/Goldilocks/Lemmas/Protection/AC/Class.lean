module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Comparison.ProtAC
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Tier A protection: monotonicity of the class and of the defaults

* `etaSleepyAC_mono`: η-sleepiness at a smaller threshold `θ' ≥ 0`, a shorter look-back and a
  shorter catch-up follows (a shorter catch-up admits more ready validators; every ready validator
  is awake at `t`, hence inside the look-back);
* `noSleepOnAC_mono`, `cohortOnAC_mono`: no sleep on a sub-window, and the cohort margin on a
  window that starts later (but not after the old end, or at the same start) and ends earlier,
  under no sleep on the old window (the cohort at the old start is still awake at the new one,
  and a late waker of the new window is one of the old);
* `ProtClassAC0.mono`: the class at `q` is in the class at every `q' ≥ q` with `0 ≤ q'.θ`. The
  parameters `ahead`, `cohortAhead` and `src` do not enter the class (static faults; the read is
  the confirmed tip);
* `protLagAC0_mono`, `protRecAC0_mono`: the defaults are adverse-monotone (a point below a
  contract point is a contract point). -/

namespace Consensus.Goldilocks.Comparison

open SA Consensus.Comparison

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}

/-! ### Participation -/

/-- A shorter catch-up admits more ready validators. -/
theorem readyAtAC_mono {c c' t : Time} (hc : c' ≤ c) :
    readyAtAC tr H c t ⊆ readyAtAC tr H c' t := fun _ hy =>
  ⟨hy.1, fun τ hτ hτt => hy.2 τ ((max_le_max le_rfl (by linarith)).trans hτ) hτt⟩

/-- A ready validator is awake in every look-back window ending at `t`. -/
theorem readyAtAC_subset_awakeIn {c η t : Time} (hc : 0 ≤ c) (ht : 0 ≤ t) (hη : 0 ≤ η) :
    readyAtAC tr H c t ⊆ awakeInAC tr H (max 0 (t - η)) t := fun _ hy =>
  ⟨hy.1, t, max_le ht (by linarith), le_rfl, hy.2 t (max_le ht (by linarith)) le_rfl⟩

/-- A shorter look-back holds fewer validators. -/
theorem awakeInAC_mono {a a' b : Time} (ha : a ≤ a') :
    awakeInAC tr H a' b ⊆ awakeInAC tr H a b := fun _ ⟨hy, u, hu, hub, hw⟩ =>
  ⟨hy, u, ha.trans hu, hub, hw⟩

/-- The ready validators are honest, so they are disjoint from the faulty ones. -/
theorem ncard_readyAtAC_union_compl (c t : Time) :
    (readyAtAC tr H c t ∪ Hᶜ).ncard = (readyAtAC tr H c t).ncard + Hᶜ.ncard :=
  Set.ncard_union_eq (Set.disjoint_left.2 fun _ hy hn => hn hy.1)

/-- **η-sleepiness is monotone**: at a smaller threshold `θ' ≥ 0`, a shorter look-back `η'` and a
shorter catch-up `c' ≥ 0`. -/
theorem etaSleepyAC_mono {θ θ' : ℚ} {η η' c c' : Time} (hθ' : 0 ≤ θ') (hθ : θ' ≤ θ)
    (hη : η' ≤ η) (hc' : 0 ≤ c') (hc : c' ≤ c) (h : EtaSleepyAC tr H θ η c) :
    EtaSleepyAC tr H θ' η' c' := by
  intro t ht
  have h := h t ht
  set R := readyAtAC tr H c t
  set R' := readyAtAC tr H c' t
  have hRR : R ⊆ R' := readyAtAC_mono hc
  have hr : (R.ncard : ℚ) ≤ R'.ncard := by exact_mod_cast Set.ncard_le_ncard hRR (Set.toFinite _)
  have hf : (0 : ℚ) ≤ Hᶜ.ncard := by positivity
  have hr0 : (0 : ℚ) ≤ R.ncard := by positivity
  -- the old count bounds `|R' ∪ Hᶜ|` once the old look-back is positive
  have hold : ¬ η ≤ 0 → ((R' ∪ Hᶜ).ncard : ℚ) ≤
      ((R ∪ awakeInAC tr H (max 0 (t - η)) t ∪ Hᶜ).ncard : ℚ) := fun hpos => by
    have hs : R' ∪ Hᶜ ⊆ R ∪ awakeInAC tr H (max 0 (t - η)) t ∪ Hᶜ :=
      Set.union_subset_union_left _
        ((readyAtAC_subset_awakeIn hc' ht (by linarith)).trans Set.subset_union_right)
    exact_mod_cast Set.ncard_le_ncard hs (Set.toFinite _)
  by_cases hη0' : η' ≤ 0
  · simp only [hη0', ↓reduceIte]
    by_cases hη0 : η ≤ 0
    · simp only [hη0, ↓reduceIte] at h
      push_cast at h ⊢
      rcases le_or_gt θ' 1 with h1 | h1
      · nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hr),
          mul_nonneg (sub_nonneg.2 hθ) (add_nonneg hr0 hf)]
      · nlinarith [mul_nonneg (by linarith : (0 : ℚ) ≤ θ - 1) hr0,
          mul_nonneg (by linarith : 0 ≤ θ) hf]
    · simp only [hη0, ↓reduceIte] at h
      have hX := hold hη0
      rw [show R'.ncard + Hᶜ.ncard = (R' ∪ Hᶜ).ncard from
        (ncard_readyAtAC_union_compl c' t).symm]
      have hX0 : (0 : ℚ) ≤ ((R ∪ awakeInAC tr H (max 0 (t - η)) t ∪ Hᶜ).ncard : ℚ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hX hθ', mul_le_mul_of_nonneg_right hθ hX0]
  · have hη0 : ¬ η ≤ 0 := fun h0 => hη0' (hη.trans h0)
    simp only [hη0', ↓reduceIte]
    simp only [hη0, ↓reduceIte] at h
    have hsub : R' ∪ awakeInAC tr H (max 0 (t - η')) t ∪ Hᶜ ⊆
        R ∪ awakeInAC tr H (max 0 (t - η)) t ∪ Hᶜ := by
      refine Set.union_subset_union_left _ (Set.union_subset ?_ ?_)
      · exact (readyAtAC_subset_awakeIn hc' ht (by linarith)).trans Set.subset_union_right
      · exact (awakeInAC_mono (max_le_max le_rfl (by linarith))).trans Set.subset_union_right
    have hX : ((R' ∪ awakeInAC tr H (max 0 (t - η')) t ∪ Hᶜ).ncard : ℚ) ≤
        ((R ∪ awakeInAC tr H (max 0 (t - η)) t ∪ Hᶜ).ncard : ℚ) := by
      exact_mod_cast Set.ncard_le_ncard hsub (Set.toFinite _)
    have hX0 : (0 : ℚ) ≤ ((R ∪ awakeInAC tr H (max 0 (t - η)) t ∪ Hᶜ).ncard : ℚ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hX hθ', mul_le_mul_of_nonneg_right hθ hX0]

/-- No sleep on a sub-window. -/
theorem noSleepOnAC_mono {a a' b b' : Time} (ha : a ≤ a') (hb : b' ≤ b)
    (h : NoSleepOnAC tr H a b) : NoSleepOnAC tr H a' b' := fun y hy t hat htb hw u htu hub =>
  h y hy t (ha.trans hat) (htb.trans hb) hw u htu (hub.trans hb)

/-- Under no sleep on `[a, b]`, the honest validators awake at `a` are awake at every
`a' ∈ [a, b]`. -/
theorem awakeAtAC_mono {a a' b : Time} (hns : NoSleepOnAC tr H a b) (ha : a ≤ a') (hab : a' ≤ b) :
    awakeAtAC tr H a ⊆ awakeAtAC tr H a' := fun y ⟨hy, hw⟩ =>
  ⟨hy, hns y hy a le_rfl (ha.trans hab) hw a' ha hab⟩

/-- Under no sleep on `[a, b]`, a late waker of `[a', b']` (with `a ≤ a' ≤ b`, `b' ≤ b`) is a
late waker of `[a, b]`. -/
theorem lateWakersAC_mono {a a' b b' : Time} (hns : NoSleepOnAC tr H a b) (ha : a ≤ a')
    (hab : a' ≤ b) (hb : b' ≤ b) : lateWakersAC tr H a' b' ⊆ lateWakersAC tr H a b :=
  fun _ ⟨⟨hy, u, hu, hub, hw⟩, hn⟩ =>
    ⟨⟨hy, u, ha.trans hu, hub.trans hb, hw⟩, fun hwa => hn (awakeAtAC_mono hns ha hab hwa)⟩

/-- **The cohort margin on a later, shorter window**, under no sleep on the old window, for a
new start equal to the old one or not after the old end. -/
theorem cohortOnAC_mono {a a' b b' : Time} (hns : NoSleepOnAC tr H a b) (ha : a ≤ a')
    (hab : a' = a ∨ a' ≤ b) (hb : b' ≤ b) (h : CohortOnAC tr H a b) :
    CohortOnAC tr H a' b' ∧ (awakeAtAC tr H a).ncard ≤ (awakeAtAC tr H a').ncard := by
  have hsub : awakeAtAC tr H a ⊆ awakeAtAC tr H a' ∧
      lateWakersAC tr H a' b' ⊆ lateWakersAC tr H a b := by
    rcases hab with rfl | hab
    · exact ⟨le_rfl, fun y ⟨⟨hy, u, hu, hub, hw⟩, hn⟩ => ⟨⟨hy, u, hu, hub.trans hb, hw⟩, hn⟩⟩
    · exact ⟨awakeAtAC_mono hns ha hab, lateWakersAC_mono hns ha hab hb⟩
  have h1 := Set.ncard_le_ncard hsub.1 (Set.toFinite _)
  have h2 := Set.ncard_le_ncard (Set.union_subset_union_right Hᶜ hsub.2) (Set.toFinite _)
  exact ⟨lt_of_le_of_lt h2 (lt_of_lt_of_le h h1), h1⟩

/-! ### The class -/

/-- **The class is monotone**: a run of the class at `q` is in the class at every `q' ≥ q` with
`0 ≤ q'.θ` (the side condition of η-sleepiness at a smaller threshold). -/
theorem ProtClassAC0.mono {q q' : ProtQ} (hq : q ≤ q') (hθ : 0 ≤ q'.θ) {T b₀ b₁ : Time}
    (h : ProtClassAC0 q T b₀ b₁ tr H U) : ProtClassAC0 q' T b₀ b₁ tr H U := by
  obtain ⟨hT, h01, hβ, hsy, hps, htk, htp, htv, hes, hns, hco, hA, hf⟩ := h
  obtain ⟨hβq, hAq, hfq, -, hηq, -, hnsq, -, hθq, hcq⟩ := hq
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hcast : ∀ {x y : ℕ}, x ≤ y → (x : Time) * sp.Δ ≤ (y : Time) * sp.Δ := fun h =>
    mul_le_mul_of_nonneg_right (by exact_mod_cast h) hΔ.le
  have hnn : ∀ x : ℕ, (0 : Time) ≤ (x : Time) * sp.Δ := fun x => by positivity
  have hns' := hcast hnsq
  have ha : protStartAC sp q b₀ ≤ protStartAC sp q' b₀ :=
    max_le_max le_rfl (by linarith)
  have hb : protEndAC sp q' b₁ ≤ protEndAC sp q b₁ := by
    unfold protEndAC; linarith
  have hab : protStartAC sp q' b₀ = protStartAC sp q b₀ ∨
      protStartAC sp q' b₀ ≤ protEndAC sp q b₁ := by
    unfold protStartAC protEndAC
    rcases le_or_gt (b₀ - (q'.noSleep : Time) * sp.Δ) 0 with h0 | h0
    · left
      rw [max_eq_left h0, max_eq_left (by linarith)]
    · right
      rw [max_eq_right h0.le]
      linarith [hnn q.noSleep, hnn q'.noSleep]
  obtain ⟨hco', hcard⟩ := cohortOnAC_mono hns ha hab hb hco
  exact ⟨hT, h01, hβ.trans (by linarith [hcast hβq]), hsy, hps, htk, htp, htv,
    etaSleepyAC_mono hθ hθq (hcast hηq) (hnn _) (hcast hcq) hes,
    noSleepOnAC_mono ha hb hns, hco', hAq.trans (hA.trans hcard), hf.trans hfq⟩

/-! ### The defaults -/

/-- A point below a contract point is a contract point. -/
theorem ProtPointAC0.of_le {q q' : ProtQ} (hq : q ≤ q') (h : ProtPointAC0 sp q') :
    ProtPointAC0 sp q := by
  obtain ⟨hβq, -, -, -, -, haq, hnsq, hoff, hθq, hcq⟩ := hq
  obtain ⟨hβ, ha, hns, hsum, hθ, hc⟩ := h
  exact ⟨hβq.trans hβ, ha.trans haq, hns.trans hnsq, hoff.trans hsum, hθ.trans hθq, hc.trans hcq⟩

/-- A default that is a constant at the contract points and `⊤` elsewhere is adverse-monotone. -/
private theorem adverseMonotone_ite (x : ℕ) :
    AdverseMonotone (fun q => if ProtPointAC0 sp q then ((x : ℕ) : WithTop ℕ) else ⊤) := by
  intro q q' hq
  by_cases hp' : ProtPointAC0 sp q'
  · simp only [hp'.of_le hq, hp', ↓reduceIte, le_rfl]
  · simp only [hp', ↓reduceIte, le_top]

/-- **The default lag is adverse-monotone.** -/
theorem protLagAC0_mono : AdverseMonotone (protLagAC0 sp) :=
  adverseMonotone_ite (4 * sp.k + 6)

/-- **The default recovery is adverse-monotone.** -/
theorem protRecAC0_mono : AdverseMonotone (protRecAC0 sp) :=
  adverseMonotone_ite 9

end Consensus.Goldilocks.Comparison

end
