module
public import ConsensusLean.Lemmas.Problem.Facts.Regimes
import Mathlib.Tactic.Linarith

public section

/-! # Outage premises at other numbers (L0 facts)

How the outage regime's premises move when its numbers change:

* the η-sleepy budget weakens at a smaller threshold (`EtaReadyAbove.theta_mono`), a shorter
  look-back (`EtaReadyAbove.eta_mono`), a shorter catch-up (`EtaReadyAbove.catchUp_mono`) and an
  earlier retention (upstream's `EtaReadyAbove.retain_mono`); it fails at every threshold `θ ≥ 1`
  (`EtaReadyAbove.theta_lt_one`); `EtaSleepyOn.weaken` combines them;
* on one retained view, `NoSleepOn` and `CohortOn` on a window give both on every subwindow that
  starts no earlier and ends no later (`NoSleepOn.retain_sub`, `CohortOn.retain_sub`), provided the
  new start is the old one or is within the old window;
* readiness at a longer catch-up implies readiness at a shorter one (`EnvPoint.Ready.catchUp_mono`),
  so recovery for the readers of a shorter catch-up gives it for a longer one
  (`Trace.ProtectedReadyUpTo.catchUp_mono`). -/

namespace Consensus

namespace EnvPoint

variable {V : Type} (p : EnvPoint V)

/-- Readiness at catch-up `c'` implies readiness at every shorter catch-up `c ≤ c'`. -/
theorem Ready.catchUp_mono {c c' : Time} {v : V} {t : Time} (h : p.Ready c' v t) (hc : c ≤ c') :
    p.Ready c v t :=
  ⟨h.1, fun u hu hut => h.2 u ((max_le_max_left 0 (by linarith)).trans hu) hut⟩

variable [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem readyAt_catchUp_mono {c c' t : Time} (hc : c ≤ c') : p.readyAt c' t ⊆ p.readyAt c t := by
  intro v hv
  simp only [readyAt, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  exact Ready.catchUp_mono p hv hc

/-- The η-sleepy budget fails at every threshold `θ ≥ 1`: the counted set contains the ready
validators. -/
theorem EtaReadyAbove.theta_lt_one {θ : ℚ} {η c t : Time} (h : p.EtaReadyAbove θ η c t) :
    θ < 1 := by
  classical
  by_contra hθ
  rw [not_lt] at hθ
  unfold EtaReadyAbove at h
  split_ifs at h with hη
  · unfold ReadyAbove at h
    have : (0 : ℚ) ≤ (p.faultCount t : ℚ) := by positivity
    nlinarith
  · have hsub : p.readyAt c t ⊆ p.readyAt c t ∪ p.awakeIn (max 0 (t - η)) t ∪ p.faultyAt t :=
      Finset.subset_union_left.trans Finset.subset_union_left
    have hc : ((p.readyAt c t).card : ℚ) ≤
        (p.readyAt c t ∪ p.awakeIn (max 0 (t - η)) t ∪ p.faultyAt t).card := by
      exact_mod_cast Finset.card_le_card hsub
    nlinarith

/-- The η-sleepy budget weakens at a smaller threshold. -/
theorem EtaReadyAbove.theta_mono {θ θ' : ℚ} {η c t : Time} (h : p.EtaReadyAbove θ η c t)
    (hθ : θ' ≤ θ) : p.EtaReadyAbove θ' η c t := by
  unfold EtaReadyAbove ReadyAbove at h ⊢
  split_ifs at h ⊢ <;>
  · refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right hθ (by positivity)) h

/-- The η-sleepy budget weakens at a shorter look-back (`θ ≥ 0`). -/
theorem EtaReadyAbove.eta_mono {θ : ℚ} {η η' c t : Time} (h : p.EtaReadyAbove θ η c t)
    (hη : η' ≤ η) (h0 : 0 ≤ θ) : p.EtaReadyAbove θ η' c t := by
  classical
  by_cases hη' : η' ≤ 0
  · have := h.readyAbove h0
    unfold EtaReadyAbove
    simp only [hη', ↓reduceIte]
    exact this
  · have hηpos : ¬ η ≤ 0 := fun h' => hη' (hη.trans h')
    unfold EtaReadyAbove at h ⊢
    simp only [hηpos, ↓reduceIte] at h
    simp only [hη', ↓reduceIte]
    have hsub : p.readyAt c t ∪ p.awakeIn (max 0 (t - η')) t ∪ p.faultyAt t ⊆
        p.readyAt c t ∪ p.awakeIn (max 0 (t - η)) t ∪ p.faultyAt t := by
      refine Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) ?_)
        (Finset.Subset.refl _)
      intro v hv
      simp only [awakeIn, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      obtain ⟨u, hau, hut, hh, haw⟩ := hv
      exact ⟨u, (max_le_max_left 0 (by linarith)).trans hau, hut, hh, haw⟩
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.card_le_card hsub)
      h0) h

/-- The η-sleepy budget weakens at a shorter, nonnegative catch-up (`θ ≤ 1`, at a time `t ≥ 0`):
more validators are ready, and with a positive look-back every ready validator is already counted
among the awake ones. -/
theorem EtaReadyAbove.catchUp_mono {θ : ℚ} {η c c' t : Time} (h : p.EtaReadyAbove θ η c t)
    (hc : c' ≤ c) (hc0 : 0 ≤ c') (h1 : θ ≤ 1) (ht : 0 ≤ t) :
    p.EtaReadyAbove θ η c' t := by
  classical
  have hr := p.readyAt_catchUp_mono (t := t) hc
  have hrc : ((p.readyAt c t).card : ℚ) ≤ (p.readyAt c' t).card := by
    exact_mod_cast Finset.card_le_card hr
  unfold EtaReadyAbove at h ⊢
  split_ifs at h ⊢ with hη
  · unfold ReadyAbove at h ⊢
    nlinarith
  · have hready : ∀ c₀, 0 ≤ c₀ → p.readyAt c₀ t ⊆ p.awakeIn (max 0 (t - η)) t := by
      intro c₀ hc₀ v hv
      simp only [readyAt, awakeIn, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact ⟨t, max_le ht (by linarith), le_rfl, hv.1,
        hv.2 t (max_le (by linarith) (by linarith)) le_rfl⟩
    have heq : ∀ c₀, 0 ≤ c₀ → p.readyAt c₀ t ∪ p.awakeIn (max 0 (t - η)) t ∪ p.faultyAt t =
        p.awakeIn (max 0 (t - η)) t ∪ p.faultyAt t := fun c₀ hc₀ => by
      rw [Finset.union_eq_right.mpr (hready c₀ hc₀)]
    rw [heq c (hc0.trans hc)] at h
    rw [heq c' hc0]
    exact lt_of_lt_of_le h hrc

/-- The η-sleepy participation on `[a, b]` (`a ≥ 0`) weakens at a smaller threshold, a shorter
look-back, a shorter catch-up and a shorter look-ahead, provided the smaller threshold is
nonnegative. -/
theorem EtaSleepyOn.weaken {θ θ' : ℚ} {η η' c c' W W' a b : Time}
    (h : p.EtaSleepyOn θ η c W a b) (ha : 0 ≤ a) (hθ : θ' ≤ θ) (hθ0 : 0 ≤ θ') (hη : η' ≤ η)
    (hc : c' ≤ c) (hc0 : 0 ≤ c') (hW : W' ≤ W) : p.EtaSleepyOn θ' η' c' W' a b := by
  intro t hat htb
  have ht := h t hat htb
  have hlt : θ < 1 := EtaReadyAbove.theta_lt_one _ ht
  have h1 : θ' ≤ 1 := by linarith
  have hd : p.lookAhead W' t ≤ p.lookAhead W t := min_le_min_right _ (by linarith)
  have h2 := (EtaReadyAbove.theta_mono _ ht hθ).retain_mono hd h1 hθ0
  exact ((EtaReadyAbove.eta_mono _ h2 hη hθ0).catchUp_mono _ hc hc0 h1 (ha.trans hat))

omit [Fintype V] [DecidableEq V] in
/-- `NoSleepOn` on a retained view passes to every subwindow. -/
theorem NoSleepOn.retain_sub {d a z a' z' : Time} (h : (p.retain d).NoSleepOn a z)
    (ha : a ≤ a') (hz : z' ≤ z) : (p.retain d).NoSleepOn a' z' := by
  intro v hv t hat htz haw u hu hu'
  exact h v hv t (ha.trans hat) (htz.trans hz) haw u hu (hu'.trans hz)

/-- On a retained view with `NoSleepOn` on `[a, z]`, a validator honest and awake at `a` is honest
and awake at a later start `a'` that is the old start or within the window. -/
theorem NoSleepOn.awakeAt_sub {d a z a' : Time} (h : (p.retain d).NoSleepOn a z) (ha : a ≤ a')
    (haz : a = a' ∨ a' ≤ z) : (p.retain d).awakeAt a ⊆ (p.retain d).awakeAt a' := by
  rcases haz with rfl | haz
  · exact Finset.Subset.refl _
  intro v hv
  simp only [awakeAt, honestAt, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
    true_and] at hv ⊢
  exact ⟨hv.1, h v hv.1 a le_rfl (ha.trans haz) hv.2 a' ha haz⟩

/-- On a retained view, the late wakers of a subwindow `[a', z']` (with `NoSleepOn` on `[a, z]`)
are late wakers of `[a, z]`. -/
theorem NoSleepOn.lateWakers_sub {d a z a' z' : Time} (h : (p.retain d).NoSleepOn a z)
    (ha : a ≤ a') (hz : z' ≤ z) :
    (p.retain d).lateWakers a' z' ⊆ (p.retain d).lateWakers a z := by
  intro v hv
  simp only [lateWakers, awakeIn, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
    true_and] at hv ⊢
  obtain ⟨⟨u, hau, huz, hh, haw⟩, hn⟩ := hv
  refine ⟨⟨u, ha.trans hau, huz.trans hz, hh, haw⟩, fun hva => hn ?_⟩
  exact NoSleepOn.awakeAt_sub p h ha (Or.inr ((hau.trans huz).trans hz)) hva

/-- `CohortOn` with `NoSleepOn` on a retained view passes to every subwindow whose start is the old
start or within the old window. -/
theorem CohortOn.retain_sub {d a z a' z' : Time} (hns : (p.retain d).NoSleepOn a z)
    (h : (p.retain d).CohortOn a z) (ha : a ≤ a') (hz : z' ≤ z) (haz : a = a' ∨ a' ≤ z) :
    (p.retain d).CohortOn a' z' := by
  unfold CohortOn at h ⊢
  have hF : (p.retain d).faultyAt z' = (p.retain d).faultyAt z := rfl
  rw [hF]
  calc ((p.retain d).faultyAt z ∪ (p.retain d).lateWakers a' z').card
      ≤ ((p.retain d).faultyAt z ∪ (p.retain d).lateWakers a z).card :=
        Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl _)
          (NoSleepOn.lateWakers_sub p hns ha hz))
    _ < ((p.retain d).awakeAt a).card := h
    _ ≤ ((p.retain d).awakeAt a').card :=
        Finset.card_le_card (NoSleepOn.awakeAt_sub p hns ha haz)

end EnvPoint

namespace Trace

variable {V α Id : Type} (tr : Trace V α Id)

/-- Recovery for the ready readers of a shorter catch-up gives it for a longer one. -/
theorem ProtectedReadyUpTo.catchUp_mono {c c' : Time} {src dst : Id} {T t₀ b : Time}
    (h : tr.ProtectedReadyUpTo c src dst T t₀ b) (hc : c ≤ c') :
    tr.ProtectedReadyUpTo c' src dst T t₀ b :=
  fun v hv t ht₀ htb w hw => h v (hv.catchUp_mono _ hc) t ht₀ htb w (hw.catchUp_mono _ hc)

end Trace

end Consensus

end
