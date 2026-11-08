module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Class
public import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Frontier.Induction
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Tier A protection: the fault bound from η-sleepiness

* `ready_joinedAC`: on an AC run with the tick duty, an honest validator awake throughout
  `[max 0 (t − c − 1), t]` with `8Δ ≤ c + 1` is awake and joined at `t ≥ 0` (`Compose`'s F.4 over
  the AC trace: a restart by `t` follows a sleep before the window, and the window holds the
  public time `t_{slot(t) − 1}`, where the validator ticks, so the restart is not after it);
* `faultBound_of_etaSleepyAC`: η-sleepiness at `θ ≥ 1/2` with such a catch-up gives `f < h_t` at
  every `t ≥ 0` (the ready validators outnumber the faulty ones and are awake and joined);
* `ProtClassAC0.faultBound`, `ProtClassAC0.frontier`: at a point with `θ ≥ 1/2` and
  `catchUp ≥ 8`, the class supplies the fault bound at every `t ≥ 0`, hence the pre-`b₀`
  frontier for every lawful unlock oracle at every write mode (`frontier_beforeAC`), for
  `b₀ ≥ 0`. -/

namespace Consensus.Goldilocks.Comparison

open SA Consensus.Comparison

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {wm : WriteMode} {u : Nat → Set Lock}

/-- **Ready validators are joined** (F.4 over the AC trace): an honest validator awake throughout
`[max 0 (t − c − 1), t]`, with `8Δ ≤ c + 1`, is awake and joined at `t ≥ 0`. -/
theorem ready_joinedAC (hr : ACLocalRunU wm u H U tr) (htick : TickDuty tr H) {y : Fin sp.n}
    (hy : y ∈ H) {t c : Time} (ht : 0 ≤ t) (hc : 8 * sp.Δ ≤ c + 1)
    (hawake : ∀ τ, max 0 (t - c - 1) ≤ τ → τ ≤ t → tr.awake y τ) :
    tr.awake y t ∧ JoinedAt tr y t := by
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hm : max 0 (t - c - 1) ≤ t := max_le ht (by linarith)
  refine ⟨hawake t hm le_rfl, fun k hk hkt => ?_⟩
  obtain ⟨ℓ, hck, hcall⟩ := hk
  obtain ⟨w, hw0, hwk, hs, hb⟩ := hr.sleep_of_restart y hy k ℓ hck hcall
  -- the sleep is before the window
  have hwm : w < max 0 (t - c - 1) := by
    by_contra hle
    exact hs (hawake w (not_lt.1 hle) (hwk.le.trans hkt))
  have hwt : w < t - c - 1 := by
    rcases lt_max_iff.1 hwm with h | h
    · linarith
    · exact h
  -- `p = t_{slot(t) − 1}` lies in the window
  set p := sp.ts ((sp.slot t : Int) - 1)
  have hup : t < sp.ts ((sp.slot t : Int) + 1) := by
    by_contra hle
    have := (ts_le_iff_le_slot sp ht _).1 (not_lt.1 hle)
    omega
  have hpt : p ≤ t := (ts_le_iff_le_slot sp ht _).2 (by omega)
  have hpw : t - c - 1 < p := by
    have : sp.ts ((sp.slot t : Int) + 1) = p + 8 * sp.Δ := by
      simp only [p, SAParams.ts]; ring
    linarith
  have hp0 : 0 ≤ p := by linarith
  have hpub : sp.toParams.IsPublic p :=
    Dvd.intro (4 * ((sp.slot t : Int) - 1)) (by simp only [p, SAParams.ts]; ring)
  obtain ⟨j, ℓj, hcj, -, htj⟩ := htick y hy p hp0 hpub
    (hawake p (max_le hp0 hpw.le) hpt)
  by_contra hgt
  push Not at hgt
  have hjk : j < k := by
    by_contra hkj
    have := hr.time_mono (not_lt.1 hkj)
    linarith
  have := hb j hjk ℓj hcj
  linarith

/-- **The fault bound from η-sleepiness**: at `θ ≥ 1/2` with a catch-up `c`, `8Δ ≤ c + 1`, the
faulty validators are fewer than the honest ones awake and joined at every `t ≥ 0`. -/
theorem faultBound_of_etaSleepyAC (hr : ACLocalRunU wm u H U tr) (htick : TickDuty tr H)
    {θ : ℚ} {η c : Time} (hes : EtaSleepyAC tr H θ η c) (hθ : (1 / 2 : ℚ) ≤ θ)
    (hc : 8 * sp.Δ ≤ c + 1) {t : Time} (ht : 0 ≤ t) : FaultBound tr H t := by
  have h := hes t ht
  set R := readyAtAC tr H c t
  -- the ready validators outnumber the faulty ones
  have hlt : Hᶜ.ncard < R.ncard := by
    have hRF : ((R ∪ Hᶜ).ncard : ℚ) = R.ncard + Hᶜ.ncard := by
      exact_mod_cast ncard_readyAtAC_union_compl c t
    have hle : θ * ((R ∪ Hᶜ).ncard : ℚ) < R.ncard := by
      split_ifs at h with hη
      · push_cast at h; rw [hRF]; exact h
      · have hs : ((R ∪ Hᶜ).ncard : ℚ) ≤
            ((R ∪ awakeInAC tr H (max 0 (t - η)) t ∪ Hᶜ).ncard : ℚ) := by
          exact_mod_cast Set.ncard_le_ncard
            (Set.union_subset_union_left _ Set.subset_union_left) (Set.toFinite _)
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hs (by linarith)) h
    rw [hRF] at hle
    have h0 : (0 : ℚ) ≤ (Hᶜ.ncard : ℚ) := by positivity
    have : ((Hᶜ.ncard : ℕ) : ℚ) < R.ncard := by nlinarith
    exact_mod_cast this
  -- the ready validators are awake and joined
  have hsub : R ⊆ {y | y ∈ H ∧ tr.awake y t ∧ JoinedAt tr y t} := fun y hy =>
    ⟨hy.1, ready_joinedAC hr htick hy.1 ht hc hy.2⟩
  exact lt_of_lt_of_le hlt (Set.ncard_le_ncard hsub (Set.toFinite _))

/-- **The class supplies the fault bound**: at a point with `θ ≥ 1/2` and `catchUp ≥ 8`, `f < h_t`
at every `t ≥ 0`. -/
theorem ProtClassAC0.faultBound {q : ProtQ} {T b₀ b₁ : Time} (hr : ACLocalRunU wm u H U tr)
    (hcl : ProtClassAC0 q T b₀ b₁ tr H U) (hθ : (1 / 2 : ℚ) ≤ q.θ) (hcu : 8 ≤ q.catchUp)
    {t : Time} (ht : 0 ≤ t) : FaultBound tr H t := by
  obtain ⟨-, -, -, -, -, htick, -, -, hes, -⟩ := hcl
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have hcu' : (8 : Time) ≤ q.catchUp := by exact_mod_cast hcu
  exact faultBound_of_etaSleepyAC hr htick hes hθ (by nlinarith) ht

/-- **The pre-`b₀` frontier from the class**: at a point with `θ ≥ 1/2` and `catchUp ≥ 8`, for
`b₀ ≥ 0`, every lawful unlock oracle at every write mode has the frontier up to `b₀`. -/
theorem ProtClassAC0.frontier {m : WriteMode} {proposer : Nat → Fin sp.n} {q : ProtQ}
    {T b₀ b₁ : Time} (hrun : ACRunU m u proposer tr H U) (hcl : ProtClassAC0 q T b₀ b₁ tr H U)
    (hθ : (1 / 2 : ℚ) ≤ q.θ) (hcu : 8 ≤ q.catchUp) (hb : 0 ≤ b₀) : FrontierAC tr H U b₀ := by
  have hfb := fun t ht => hcl.faultBound hrun.localRun hθ hcu (t := t) ht
  obtain ⟨-, -, -, hsync, -, htick, -, htriv, -⟩ := hcl
  refine frontier_beforeAC hrun htriv htick hb hsync fun s d hd _ => hfb _ ?_
  have hΔ : 0 < sp.Δ := sp.toParams.hΔ
  have := ts_nonnegAC (sp := sp) s
  rcases hd with rfl | rfl
  · simpa using this
  · linarith

/-- The contract points have `θ ≥ 1/2` and `catchUp ≥ 8`. -/
theorem ProtPointAC0.sleepy {q : ProtQ} (h : ProtPointAC0 sp q) :
    (1 / 2 : ℚ) ≤ q.θ ∧ 8 ≤ q.catchUp :=
  ⟨h.2.2.2.2.1, by have := h.2.2.2.2.2; omega⟩

end Consensus.Goldilocks.Comparison

end
