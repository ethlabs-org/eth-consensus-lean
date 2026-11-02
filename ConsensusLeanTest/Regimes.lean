module
public import ConsensusLean.Spec.Problem.Good
public import ConsensusLean.Lemmas.Problem.DerivedFacts
public import ConsensusLean.Lemmas.Problem.Facts.Atoms
public import ConsensusLean.Lemmas.Problem.Facts.Transfer
public import ConsensusLean.Lemmas.Problem.Facts.Network
public import ConsensusLean.Lemmas.Problem.Facts.Properties
public import ConsensusLean.Lemmas.Problem.Facts.Regimes
public import ConsensusLean.Lemmas.Problem.Facts.Good
public import Mathlib.Tactic
@[expose] public section

/-! # Regime tests (L0)

Concrete points and logs that show what each fixed L0 regime admits and what
it rejects.

* `psync_lost_message`: two honest, always-awake validators, `Δ = 1`, horizon
  `10`; validator 0 sends at `0` and nobody receives. The log is not partially
  synchronous for any GST `g ≤ 9` (validator 1 must hold the message at
  `max 0 g + 1 ≤ 10`), and is for `g = 10` (every deadline is past the
  horizon): a lost honest message is excused only by a GST so late that
  nothing is promised in the run.
* `outage_async_log` (M8): validator 0 sends at `3`, validator 1 receives
  at `7 = max 3 6 + Δ`. The log meets the outage network `OutageNet 3 6`
  (asynchronous during `[3, 6)`), but not synchrony (`PSync 0`), nor
  synchrony up to `4`: the outage regime admits real asynchrony.
* `sleepy_with_sleeper` (M9): five validators, one faulty, honest validator 4
  asleep on `[2, 5]`. The point is ½-sleepy at every catch-up, and with the
  silent log every contract with `θ ≤ ½` has the sleepy regime there; it is not
  healthy from `0` at any fault bound (an honest validator sleeps, and the
  healthy regime is full participation): sleepy participation is the weaker,
  dynamic regime.
* `healthy_wake_at_gst` (M11): three honest validators asleep before `5` and
  awake from `5`. Healthy from GST `5` at `β = ⅓` (the healthy regime counts awake,
  not ready: a wake at GST is allowed), although nobody is ready at `5` with
  catch-up `2`; everyone is ready at `max 5 0 + 2 + 1 = 8`, where progress
  windows start.
* `healthy_needs_full_participation`: three honest validators, one always
  asleep: not healthy at any fault bound `β` (the regime is full
  participation); with everyone awake, healthy at every `β > 0`.
* `faulty_third_not_healthy` (M21): healthy at `β` bounds the faults below `β`
  (`HealthyOn.faultsBelow`), on every point; so a point with one faulty
  validator among three is never healthy at `β = ⅓`, however awake.
* `outage_cohort_teeth`: the no-sleep conjunct rejects an honest validator
  falling asleep in the window and accepts a late waker; the cohort count
  accepts one late waker against three honest validators awake at the window
  start and rejects two late wakers against two.
* `outage_times_teeth`: with lag `2`, budget `3`, `Δ = 1`, `OutageTimes`
  accepts `T = 0, [2, 5)`, and rejects an arming at a negative time, an arming
  less than `lag·Δ` before the window, a window longer than `budget·Δ`, and an
  inverted window. -/

/-! ## Explanatory L0 facts (moved from the library; no library proof uses them)

Monotonicity of the participation atoms and regimes in their thresholds, the
`η = 0` reduction of the η-sleepy participation, and its awake-count form. -/

namespace Consensus

namespace EnvPoint

variable {V : Type} [Fintype V] [DecidableEq V] (p : EnvPoint V)

/-- A smaller ready fraction is weaker. -/
theorem ReadyAbove.mono {θ θ' : ℚ} {c t : Time} (h : p.ReadyAbove θ' c t)
    (hle : θ ≤ θ') : p.ReadyAbove θ c t :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle (by positivity)) h

/-- With look-back `0`, η-sleepy is plain sleepy (by definition). -/
theorem etaReadyAbove_zero (θ : ℚ) (c t : Time) :
    p.EtaReadyAbove θ 0 c t ↔ p.ReadyAbove θ c t := by
  rw [EtaReadyAbove, ite_eq_left_of_eq_true _ _ (eq_true le_rfl)]

/-- The η-sleepy count set grows with the look-back window. -/
theorem etaSet_mono {η η' c t : Time} (hη : η ≤ η') :
    p.readyAt c t ∪ p.awakeIn (max 0 (t - η)) t ∪ p.faulty ⊆
      p.readyAt c t ∪ p.awakeIn (max 0 (t - η')) t ∪ p.faulty := by
  classical
  refine Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) ?_)
    (Finset.Subset.refl _)
  intro v hv
  simp only [awakeIn, Finset.mem_filter] at hv ⊢
  obtain ⟨hv, u, h1, h2, ha⟩ := hv
  exact ⟨hv, u, le_trans (max_le_max le_rfl (by linarith)) h1, h2, ha⟩

/-- A smaller fraction (`θ ≥ 0`) and a shorter look-back are weaker. -/
theorem EtaReadyAbove.mono {θ θ' : ℚ} {η η' c t : Time} (h : p.EtaReadyAbove θ' η' c t)
    (h0 : 0 ≤ θ) (hθ : θ ≤ θ') (hη : η ≤ η') : p.EtaReadyAbove θ η c t := by
  classical
  by_cases hη0 : η ≤ 0
  · rw [EtaReadyAbove, ite_eq_left_of_eq_true _ _ (eq_true hη0)]
    exact (h.readyAbove (h0.trans hθ)).mono p hθ
  have hη0' : ¬ η' ≤ 0 := fun h' => hη0 (hη.trans h')
  rw [EtaReadyAbove, ite_eq_right_of_eq_false _ _ (eq_false hη0)]
  rw [EtaReadyAbove, ite_eq_right_of_eq_false _ _ (eq_false hη0')] at h
  have hc : ((p.readyAt c t ∪ p.awakeIn (max 0 (t - η)) t ∪ p.faulty).card : ℚ) ≤
      (p.readyAt c t ∪ p.awakeIn (max 0 (t - η')) t ∪ p.faulty).card := by
    exact_mod_cast Finset.card_le_card (p.etaSet_mono hη)
  exact lt_of_le_of_lt
    ((mul_le_mul_of_nonneg_left hc h0).trans
      (mul_le_mul_of_nonneg_right hθ (by positivity))) h

omit [Fintype V] [DecidableEq V] in
/-- A ready validator (catch-up `c ≥ 0`) at `t ≥ 0` is awake at `t`. -/
theorem readyAt_subset_awakeAt {c t : Time} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    p.readyAt c t ⊆ p.awakeAt t := by
  classical
  intro v hv
  simp only [readyAt, awakeAt, Finset.mem_filter] at hv ⊢
  exact ⟨hv.1, hv.2.2 t (max_le ht (by linarith)) le_rfl⟩

/-- With positive look-back, η-sleepy (`θ ≥ 0`, catch-up `c ≥ 0`, `t ≥ 0`) implies the
awake-count form: the honest validators awake at `t` exceed fraction `θ` of
those awake at some time in `[max 0 (t − η), t]` together with the faulty
ones. -/
theorem EtaReadyAbove.awakeForm {θ : ℚ} {η c t : Time} (h : p.EtaReadyAbove θ η c t)
    (h0 : 0 ≤ θ) (hη : 0 < η) (hc0 : 0 ≤ c) (ht : 0 ≤ t) :
    θ * ((p.awakeIn (max 0 (t - η)) t ∪ p.faulty).card : ℚ) < (p.awakeAt t).card := by
  classical
  rw [EtaReadyAbove, ite_eq_right_of_eq_false _ _ (eq_false (not_le.mpr hη))] at h
  have hsub : p.awakeIn (max 0 (t - η)) t ∪ p.faulty ⊆
      p.readyAt c t ∪ p.awakeIn (max 0 (t - η)) t ∪ p.faulty :=
    Finset.union_subset_union Finset.subset_union_right (Finset.Subset.refl _)
  have hc : ((p.awakeIn (max 0 (t - η)) t ∪ p.faulty).card : ℚ) ≤
      (p.readyAt c t ∪ p.awakeIn (max 0 (t - η)) t ∪ p.faulty).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hr : ((p.readyAt c t).card : ℚ) ≤ (p.awakeAt t).card := by
    exact_mod_cast Finset.card_le_card (p.readyAt_subset_awakeAt hc0 ht)
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hc h0) (lt_of_lt_of_le h hr)

omit [DecidableEq V] in
/-- A smaller fraction of all validators is weaker. -/
theorem ReadyOfAll.mono {φ φ' : ℚ} {c t : Time} (h : p.ReadyOfAll φ' c t)
    (hle : φ ≤ φ') : p.ReadyOfAll φ c t :=
  lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle (by positivity)) h

variable {p}

/-- A smaller fraction is weaker. -/
theorem SleepyOn.mono {θ θ' : ℚ} {c a b : Time} (h : p.SleepyOn θ' c a b) (hle : θ ≤ θ') :
    p.SleepyOn θ c a b :=
  fun t ha hb => (h t ha hb).mono p hle

/-- With look-back `0`, η-sleepy is plain sleepy. -/
theorem etaSleepyOn_zero (θ : ℚ) (c a b : Time) :
    p.EtaSleepyOn θ 0 c a b ↔ p.SleepyOn θ c a b :=
  forall_congr' fun t => imp_congr_right fun _ => imp_congr_right fun _ =>
    p.etaReadyAbove_zero θ c t

/-- η-sleepy (`θ ≥ 0`) implies plain sleepy. -/
theorem EtaSleepyOn.sleepyOn {θ : ℚ} {η c a b : Time} (h : p.EtaSleepyOn θ η c a b)
    (h0 : 0 ≤ θ) : p.SleepyOn θ c a b :=
  fun t ha hb => (h t ha hb).readyAbove h0

/-- A smaller fraction (`θ ≥ 0`) and a shorter look-back are weaker. -/
theorem EtaSleepyOn.mono {θ θ' : ℚ} {η η' c a b : Time} (h : p.EtaSleepyOn θ' η' c a b)
    (h0 : 0 ≤ θ) (hθ : θ ≤ θ') (hη : η ≤ η') : p.EtaSleepyOn θ η c a b :=
  fun t ha hb => (h t ha hb).mono p h0 hθ hη

/-- A larger fault bound is weaker. -/
theorem HealthyOn.mono {β β' : ℚ} {g b : Time} (h : p.HealthyOn β' g b) (hle : β' ≤ β) :
    p.HealthyOn β g b :=
  ⟨lt_of_lt_of_le h.1 (mul_le_mul_of_nonneg_right hle (by positivity)), h.2⟩

omit [Fintype V] [DecidableEq V] in
/-- A no-sleep window keeps its property on every subwindow. -/
theorem NoSleepOn.mono {a b a' b' : Time} (h : p.NoSleepOn a b) (ha : a ≤ a') (hb : b' ≤ b) :
    p.NoSleepOn a' b' :=
  fun v hv t ht1 ht2 hat u hu1 hu2 =>
    h v hv t (ha.trans ht1) (ht2.trans hb) hat u hu1 (hu2.trans hb)

/-- Under no-sleep on `[a, b]`, the cohort count on `[a, b]` holds on every
subwindow `[a', b']`: the late wakers of `[a', b']` are late wakers of
`[a, b]` (a validator awake at `a` stays awake through `a'`), and the
validators awake at `a` are still awake at `a'`. -/
theorem CohortOn.mono {a b a' b' : Time} (hns : p.NoSleepOn a b) (h : p.CohortOn a b)
    (ha : a ≤ a') (hab : a' ≤ b') (hb : b' ≤ b) : p.CohortOn a' b' := by
  classical
  have hab' : a ≤ b := ha.trans (hab.trans hb)
  have hsub : p.faulty ∪ p.lateWakers a' b' ⊆ p.faulty ∪ p.lateWakers a b := by
    apply Finset.union_subset_union_right
    intro v hv
    simp only [EnvPoint.lateWakers, EnvPoint.awakeIn, EnvPoint.awakeAt, Finset.mem_sdiff,
      Finset.mem_filter] at hv ⊢
    obtain ⟨⟨hh, u, hu1, hu2, hu⟩, hn⟩ := hv
    exact ⟨⟨hh, u, ha.trans hu1, hu2.trans hb, hu⟩,
      fun h0 => hn ⟨hh, hns v hh a le_rfl hab' h0.2 a' ha (hab.trans hb)⟩⟩
  have hA : p.awakeAt a ⊆ p.awakeAt a' := by
    intro v hv
    simp only [EnvPoint.awakeAt, Finset.mem_filter] at hv ⊢
    exact ⟨hv.1, hns v hv.1 a le_rfl hab' hv.2 a' ha (hab.trans hb)⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_le_card hA
  unfold CohortOn at h ⊢
  omega

end EnvPoint

namespace System

variable {V : Type} [Fintype V] [DecidableEq V] {S : System V} {Prog Prog' : Type}
  {K : Contract Prog} {K' : Contract Prog'} {r : S.Run}

/-- With look-back `η = 0`, the outage regime's participation is plain
sleepy throughout. -/
theorem outage_eta_zero (hη : K.params.η = 0) {T b₀ b₁ : Time} :
    S.Outage K T b₀ b₁ r ↔ OutageTimes K.params (S.pt r).env.Δ T b₀ b₁ ∧
      (S.log r).OutageNet (S.pt r) b₀ b₁ ∧
      (S.pt r).SleepyOn K.params.θ (S.cDur K r) 0 (S.pt r).horizon ∧
      (S.pt r).NoSleepOn (S.outageStart K b₀ r) (S.outageEnd K b₁ r) ∧
      (S.pt r).CohortOn (S.outageStart K b₀ r) (S.outageEnd K b₁ r) := by
  unfold Outage
  rw [show ((K.params.η : Time) * (S.pt r).env.Δ) = 0 by simp [hη], EnvPoint.etaSleepyOn_zero]

omit [Fintype V] [DecidableEq V] in
theorem cDur_of_catchUp (hc : K'.params.catchUp = K.params.catchUp) :
    S.cDur K' r = S.cDur K r := by
  unfold cDur; rw [hc]

/-- Weaker thresholds (same catch-up) keep the sleepy regime. -/
theorem Sleepy.of_le (hc : K'.params.catchUp = K.params.catchUp) (hθ : K'.params.θ ≤ K.params.θ)
    (h : S.Sleepy K r) : S.Sleepy K' r := by
  refine ⟨h.1, ?_⟩
  rw [cDur_of_catchUp hc]
  exact EnvPoint.SleepyOn.mono h.2 hθ

/-- A weaker fault bound keeps the healthy regime. -/
theorem Healthy.of_le {g : Time} (hβ : K.params.β ≤ K'.params.β) (h : S.Healthy K g r) :
    S.Healthy K' g r :=
  ⟨h.1, EnvPoint.HealthyOn.mono h.2 hβ⟩

/-- Weaker thresholds (`θ' ≥ 0`), a shorter look-back, a shorter lag, a
larger budget and a smaller no-sleep margin (same catch-up) keep the outage
regime. -/
theorem Outage.of_le {T b₀ b₁ : Time} (hc : K'.params.catchUp = K.params.catchUp)
    (h0 : 0 ≤ K'.params.θ) (hθ : K'.params.θ ≤ K.params.θ) (hη : K'.params.η ≤ K.params.η)
    (hl : K'.params.lag ≤ K.params.lag) (hb : K.params.budget ≤ K'.params.budget)
    (hC : K'.params.noSleep ≤ K.params.noSleep) (h : S.Outage K T b₀ b₁ r) :
    S.Outage K' T b₀ b₁ r := by
  obtain ⟨⟨hT, hlag, h01, hbud⟩, hn, hs, hns, hco⟩ := h
  have hΔ : (0 : Time) ≤ (S.pt r).env.Δ := (S.pt r).env.Δ_pos.le
  have hl' : ((K'.params.lag : Nat) : Time) ≤ (K.params.lag : Time) := by exact_mod_cast hl
  have hb' : ((K.params.budget : Nat) : Time) ≤ (K'.params.budget : Time) := by exact_mod_cast hb
  have hC' : ((K'.params.noSleep : Nat) : Time) ≤ (K.params.noSleep : Time) := by exact_mod_cast hC
  have hlag0 : (0 : Time) ≤ (K.params.lag : Time) * (S.pt r).env.Δ := by positivity
  have hC0 : (0 : Time) ≤ (K'.params.noSleep : Time) * (S.pt r).env.Δ := by positivity
  have ha : S.outageStart K b₀ r ≤ S.outageStart K' b₀ r := by
    unfold outageStart
    exact min_le_min (max_le_max le_rfl (by nlinarith)) le_rfl
  have hz : S.outageEnd K' b₁ r ≤ S.outageEnd K b₁ r := by
    unfold outageEnd
    exact min_le_min (by nlinarith) le_rfl
  have haz : S.outageStart K' b₀ r ≤ S.outageEnd K' b₁ r := by
    unfold outageStart outageEnd
    exact min_le_min (max_le (by linarith) (by linarith)) le_rfl
  refine ⟨⟨hT, ?_, h01, ?_⟩, hn, ?_, hns.mono ha hz, hco.mono hns ha haz hz⟩
  · nlinarith
  · nlinarith
  · rw [cDur_of_catchUp hc]
    have hη' : ((K'.params.η : Nat) : Time) ≤ (K.params.η : Time) := by exact_mod_cast hη
    exact EnvPoint.EtaSleepyOn.mono hs h0 hθ (by nlinarith)

end System

end Consensus

namespace Consensus.Shape.Tests.Regimes
open Consensus

/-- The log with no sends, no receipts and empty inboxes. -/
def silentLog (V M : Type) : CommLog V M :=
  ⟨fun _ _ _ => False, fun _ _ _ => False, fun _ _ => []⟩

/-- With no submissions, the silent log meets every delivery requirement
vacuously. -/
theorem silentLog_delivers {V M : Type} (p : EnvPoint V) (hs : ∀ v t, p.submit v t = [])
    (dl : Time → Time) (cut : Time) : (silentLog V M).Delivers p dl cut := by
  refine ⟨fun _ _ _ _ h => h.elim, ?_⟩
  intro u _ x τ _ _ hx
  rw [hs] at hx
  exact absurd hx List.not_mem_nil

section Lost

/-- Two honest validators, always awake, `Δ = 1`, horizon `10`. -/
def ptL : EnvPoint (Fin 2) := ⟨⟨1, by decide, fun _ _ => true⟩, Finset.univ, 10, fun _ _ => []⟩

/-- Validator 0 sends at `0`; nobody receives anything. -/
def logL : CommLog (Fin 2) Unit := ⟨fun v _ t => v = 0 ∧ t = 0, fun _ _ _ => False, fun _ _ => []⟩

/-- A lost honest message: not partially synchronous for any GST `g ≤ 9`; for
`g = 10` every deadline is past the horizon and nothing is required. -/
theorem psync_lost_message : (∀ g : Time, g ≤ 9 → ¬ logL.PSync ptL g) ∧ logL.PSync ptL 10 := by
  refine ⟨fun g hg h => ?_, ⟨?_, ?_⟩⟩
  · have hd : max 0 g + 1 ≤ 10 := by
      have : max 0 g ≤ 9 := max_le (by decide) hg
      dsimp only [Time] at *; omega
    obtain ⟨t', -, hs, -⟩ := h.msgs 0 (Finset.mem_univ _) () 0 ⟨rfl, rfl⟩ 1 (Finset.mem_univ _)
      0 le_rfl hd hd (fun _ _ _ => rfl)
    rcases hs with ⟨h1, -⟩ | h1
    · exact absurd h1 (by decide)
    · exact h1
  · rintro v - m t ⟨-, rfl⟩ w - a - hc - -
    change max a 10 + 1 ≤ 10 at hc
    have := le_max_right a 10
    dsimp only [Time] at *; omega
  · intro u _ x τ _ _ hx
    exact absurd hx List.not_mem_nil

end Lost

section Async

/-- Validator 0 sends at `3`; validator 1 receives it at `7`. -/
def logA : CommLog (Fin 2) Unit :=
  ⟨fun v _ t => v = 0 ∧ t = 3, fun v _ t => v = 1 ∧ t = 7, fun _ _ => []⟩

/-- Nobody ever wakes at `ptL` (always awake). -/
theorem ptL_no_wake (w : Fin 2) (u : Time) : ¬ Wakes ptL.env w u := fun h => by
  have := h.2
  simp [ptL] at this

/-- From `7` on, both validators hold the message. -/
theorem logA_held (w : Fin 2) (d : Time) (hd : 7 ≤ d) : logA.Held ptL w () d := by
  fin_cases w
  · exact ⟨3, by dsimp only [Time] at *; omega, Or.inl ⟨rfl, rfl⟩,
      fun u _ _ => ptL_no_wake 0 u⟩
  · exact ⟨7, hd, Or.inr ⟨rfl, rfl⟩, fun u _ _ => ptL_no_wake 1 u⟩

/-- An asynchronous log: it meets the outage network for the window `[3, 6)`,
but neither synchrony nor synchrony up to `4`. -/
theorem outage_async_log :
    logA.OutageNet ptL 3 6 ∧ ¬ logA.PSync ptL 0 ∧ ¬ logA.SyncUntil ptL 4 := by
  have hnot : ∀ dl cut, dl 3 = 4 → 4 ≤ cut → ¬ logA.Delivers ptL dl cut := by
    intro dl cut h3 hc h
    obtain ⟨t', ht', hs, -⟩ := h.msgs 0 (Finset.mem_univ _) () 3 ⟨rfl, rfl⟩ 1
      (Finset.mem_univ _) 3 le_rfl (by rw [h3]; exact hc) (by rw [h3]; decide)
      (fun _ _ _ => rfl)
    rw [h3] at ht'
    rcases hs with ⟨h1, -⟩ | ⟨-, rfl⟩
    · exact absurd h1 (by decide)
    · exact absurd ht' (by decide)
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, hnot _ _ rfl (by decide), hnot _ _ rfl le_rfl⟩
  · rintro v - m t ⟨-, rfl⟩ w - a ha hc - -
    change a + 1 ≤ 3 at hc
    dsimp only [Time] at *; omega
  · intro u _ x τ _ _ hx
    exact absurd hx List.not_mem_nil
  · rintro v - m t ⟨-, rfl⟩ w - a - - - -
    refine logA_held w _ ?_
    change 7 ≤ max a 6 + 1
    have := le_max_right a 6
    dsimp only [Time] at *; omega
  · intro u _ x τ _ _ hx
    exact absurd hx List.not_mem_nil

end Async

section Sleeper

/-- Five validators, `0` faulty; honest `4` asleep on `[2, 5]`; `Δ = 1`,
horizon `10`, no submissions. -/
def ptS : EnvPoint (Fin 5) :=
  ⟨⟨1, by decide, fun v t => decide (v ≠ 4 ∨ t < 2 ∨ 5 < t)⟩, Finset.univ.erase 0, 10,
    fun _ _ => []⟩

theorem ptS_faulty : ptS.faulty = {0} := by
  ext v; simp [EnvPoint.faulty, ptS]

/-- Validators `1, 2, 3` are ready at every time, at every catch-up. -/
theorem ptS_readyAt (c t : Time) : ({1, 2, 3} : Finset (Fin 5)) ⊆ ptS.readyAt c t := by
  classical
  intro v hv
  unfold EnvPoint.readyAt
  refine Finset.mem_filter.mpr ⟨?_, ?_, fun u _ _ => ?_⟩ <;>
    fin_cases hv <;> simp [ptS]

theorem ptS_readyAbove (c t : Time) : ptS.ReadyAbove (1 / 2) c t := by
  have h3 : (3 : ℚ) ≤ (ptS.readyAt c t).card := by
    have := Finset.card_le_card (ptS_readyAt c t)
    exact_mod_cast this
  unfold EnvPoint.ReadyAbove
  rw [ptS_faulty, Finset.card_singleton]
  push_cast
  linarith

/-- A sleeper: honest validator `4` sleeps at `2`. The point is ½-sleepy at
every catch-up; with the silent log, every contract with `θ ≤ ½` has the
sleepy regime; the point is not healthy from `0` at any fault bound. -/
theorem sleepy_with_sleeper :
    (4 : Fin 5) ∈ ptS.honest ∧ ptS.env.awake 4 2 = false ∧
    (∀ c, ptS.SleepyOn (1 / 2) c 0 ptS.horizon) ∧
    (∀ {Idx : Type} (P : Params Idx), P.θ ≤ 1 / 2 →
      (silentLog (Fin 5) Unit).PSync ptS 0 ∧
        ptS.SleepyOn P.θ ((P.catchUp : Time) * ptS.env.Δ) 0 ptS.horizon) ∧
    ∀ β, ¬ ptS.HealthyOn β 0 ptS.horizon := by
  refine ⟨by decide, by decide, fun c t _ _ => ptS_readyAbove c t, fun P hθ => ?_, ?_⟩
  · exact ⟨silentLog_delivers _ (fun _ _ => rfl) _ _,
      fun t _ _ => (ptS_readyAbove _ t).mono _ hθ⟩
  · rintro β ⟨-, ha⟩
    have := ha 4 (by decide) 2 (by decide) (by decide)
    exact absurd this (by decide)

end Sleeper

section WakeAtGST

/-- Three honest validators, all asleep before `5` and awake from `5`; `Δ = 1`,
horizon `20`. -/
def ptG : EnvPoint (Fin 3) :=
  ⟨⟨1, by decide, fun _ t => decide (5 ≤ t)⟩, Finset.univ, 20, fun _ _ => []⟩

/-- A wake at GST: healthy from `5` at `β = ⅓` (and the healthy regime holds
with the silent log for every `β ≥ ⅓`), nobody ready at `5` with catch-up `2`,
everyone ready at `max 5 0 + 2 + 1 = 8`. -/
theorem healthy_wake_at_gst :
    ptG.HealthyOn (1 / 3) 5 ptG.horizon ∧
    (∀ {Idx : Type} (P : Params Idx), 1 / 3 ≤ P.β →
      (silentLog (Fin 3) Unit).PSync ptG 5 ∧ ptG.HealthyOn P.β 5 ptG.horizon) ∧
    ptG.readyAt 2 5 = ∅ ∧ (max 5 0 + 2 + 1 : Time) = 8 ∧ ∀ v, ptG.Ready 2 v (max 5 0 + 2 + 1) := by
  have hH : ptG.HealthyOn (1 / 3) 5 ptG.horizon := by
    have hf : ptG.faulty = ∅ := by ext v; simp [EnvPoint.faulty, ptG]
    refine ⟨by rw [hf]; norm_num, fun v _ u hu _ => ?_⟩
    simp only [ptG, decide_eq_true_eq]
    exact le_trans (le_max_left _ _) hu
  refine ⟨hH, fun P hφ => ⟨silentLog_delivers _ (fun _ _ => rfl) _ _, hH.mono hφ⟩, ?_,
    by decide, fun v => ⟨Finset.mem_univ _, fun u hu _ => ?_⟩⟩
  · classical
    unfold EnvPoint.readyAt
    apply Finset.filter_false_of_mem
    rintro v - ⟨-, hA⟩
    have := hA 2 (by decide) (by decide)
    simp [ptG] at this
  · change max 0 (max 5 0 + 2 + 1 - 2 - 1) ≤ u at hu
    simp only [ptG, decide_eq_true_eq]
    have := le_max_right (0 : Time) (max 5 0 + 2 + 1 - 2 - 1)
    simp only [max_eq_left (show (0 : Time) ≤ 5 by decide)] at hu this
    dsimp only [Time] at *; omega

end WakeAtGST

section FullParticipation

/-- Three honest validators; validator `2` always asleep. -/
def ptT : EnvPoint (Fin 3) :=
  ⟨⟨1, by decide, fun v _ => decide (v ≠ 2)⟩, Finset.univ, 10, fun _ _ => []⟩

/-- Three honest validators, everyone always awake. -/
def ptA : EnvPoint (Fin 3) :=
  ⟨⟨1, by decide, fun _ _ => true⟩, Finset.univ, 10, fun _ _ => []⟩

/-- The healthy regime is full participation: two of three honest validators
awake throughout (no faults) is not healthy at any fault bound `β`; with
everyone awake it is healthy at every `β > 0`. -/
theorem healthy_needs_full_participation :
    (∀ β, ¬ ptT.HealthyOn β 0 ptT.horizon) ∧ ∀ β, 0 < β → ptA.HealthyOn β 0 ptA.horizon := by
  refine ⟨fun β h => ?_, fun β hβ => ⟨?_, fun _ _ _ _ _ => rfl⟩⟩
  · have := h.2 2 (Finset.mem_univ _) 0 (by decide) (by decide)
    exact absurd this (by decide)
  · have hf : ptA.faulty = ∅ := by ext v; simp [EnvPoint.faulty, ptA]
    rw [hf]; simp only [Finset.card_empty, Nat.cast_zero, Fintype.card_fin]; positivity

end FullParticipation

section Faults

/-- One faulty validator among three, everyone awake. -/
def ptF : EnvPoint (Fin 3) :=
  ⟨⟨1, by decide, fun _ _ => true⟩, Finset.univ.erase 0, 10, fun _ _ => []⟩

/-- So one faulty validator among three is never healthy at `β = ⅓`, on any
window. -/
theorem faulty_third_not_healthy (g b : Time) : ¬ ptF.HealthyOn (1 / 3) g b := by
  intro h
  have := h.faultsBelow
  rw [EnvPoint.faultsBelow_iff] at this
  have hf : ptF.faulty = {0} := by ext v; simp [EnvPoint.faulty, ptF]
  rw [hf] at this
  norm_num at this

end Faults

section Times

/-- Standard thresholds, lag `2`, budget `3`. -/
def P23 : Params Unit := Params.standard 1 2 3 (fun _ _ => 0) (fun _ _ => 0)

/-- `OutageTimes` has teeth: it accepts `T = 0, [2, 5)` at `Δ = 1`, and
rejects a negative arming time, a lag shorter than `2·Δ`, a window longer than
`3·Δ`, and an inverted window. -/
theorem outage_times_teeth :
    OutageTimes P23 1 0 2 5 ∧ ¬ OutageTimes P23 1 (-1) 1 2 ∧ ¬ OutageTimes P23 1 0 1 2 ∧
      ¬ OutageTimes P23 1 0 2 6 ∧ ¬ OutageTimes P23 1 0 3 2 := by
  simp only [OutageTimes, P23, Params.standard]
  norm_num

end Times

section OutageCohort

/-- Five validators, `0` faulty; honest `4` asleep before `3` and awake from
`3` (a late waker); `Δ = 1`, horizon `10`, no submissions. -/
def ptW : EnvPoint (Fin 5) :=
  ⟨⟨1, by decide, fun v t => decide (v ≠ 4 ∨ 3 ≤ t)⟩, Finset.univ.erase 0, 10,
    fun _ _ => []⟩

/-- As `ptW`, with honest `3` and `4` both waking at `3`. -/
def ptW2 : EnvPoint (Fin 5) :=
  ⟨⟨1, by decide, fun v t => decide ((v ≠ 3 ∧ v ≠ 4) ∨ 3 ≤ t)⟩, Finset.univ.erase 0, 10,
    fun _ _ => []⟩

theorem ptW_lateWakers : ptW.lateWakers 0 10 = {4} := by
  ext v
  simp only [EnvPoint.lateWakers, EnvPoint.awakeIn, EnvPoint.awakeAt, Finset.mem_sdiff,
    Finset.mem_filter]
  fin_cases v <;> simp [ptW]
  exact ⟨3, by norm_num⟩

theorem ptW_awakeAt : ptW.awakeAt 0 = {1, 2, 3} := by
  ext v; fin_cases v <;> simp [EnvPoint.awakeAt, ptW]

theorem ptW_faulty : ptW.faulty = {0} := by
  ext v; simp [EnvPoint.faulty, ptW]

theorem ptW2_lateWakers : ptW2.lateWakers 0 10 = {3, 4} := by
  ext v
  simp only [EnvPoint.lateWakers, EnvPoint.awakeIn, EnvPoint.awakeAt, Finset.mem_sdiff,
    Finset.mem_filter]
  fin_cases v <;> simp [ptW2] <;> exact ⟨3, by norm_num⟩

theorem ptW2_awakeAt : ptW2.awakeAt 0 = {1, 2} := by
  ext v; fin_cases v <;> simp [EnvPoint.awakeAt, ptW2]

theorem ptW2_faulty : ptW2.faulty = {0} := by
  ext v; simp [EnvPoint.faulty, ptW2]

/-- The outage's no-sleep and cohort conjuncts have teeth, on the window
`[0, 10]`:
* the sleeper point `ptS` (honest `4` awake at `0`, asleep at `2`) violates
  `NoSleepOn`: an honest validator falls asleep in the window;
* `ptW` (honest `4` wakes at `3`) meets `NoSleepOn` (waking is allowed) and
  `CohortOn` with a nonempty late-waker set: `|{0} ∪ {4}| = 2 < 3 = |{1, 2, 3}|`;
* `ptW2` (honest `3` and `4` wake at `3`) meets `NoSleepOn` but violates
  `CohortOn`: the late wakers count against the cohort,
  `|{0} ∪ {3, 4}| = 3 ≮ 2 = |{1, 2}|`, although every honest validator is
  awake from `3`. -/
theorem outage_cohort_teeth :
    ¬ ptS.NoSleepOn 0 10 ∧
    ptW.NoSleepOn 0 10 ∧ ptW.CohortOn 0 10 ∧ (ptW.lateWakers 0 10).Nonempty ∧
    ptW2.NoSleepOn 0 10 ∧ ¬ ptW2.CohortOn 0 10 := by
  refine ⟨fun h => ?_, fun v _ t _ _ ht u htu _ => ?_, ?_, ?_, fun v _ t _ _ ht u htu _ => ?_, ?_⟩
  · have := h 4 (by decide) 0 le_rfl (by norm_num) (by decide) 2 (by norm_num) (by norm_num)
    revert this; decide
  · simp only [ptW, decide_eq_true_eq] at ht ⊢
    rcases ht with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans htu)
  · unfold EnvPoint.CohortOn
    rw [ptW_lateWakers, ptW_awakeAt, ptW_faulty]; decide
  · rw [ptW_lateWakers]; exact Finset.singleton_nonempty _
  · simp only [ptW2, decide_eq_true_eq] at ht ⊢
    rcases ht with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans htu)
  · unfold EnvPoint.CohortOn
    rw [ptW2_lateWakers, ptW2_awakeAt, ptW2_faulty]; decide

end OutageCohort

end Consensus.Shape.Tests.Regimes

end
