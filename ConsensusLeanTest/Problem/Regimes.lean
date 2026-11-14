module
public import ConsensusLean.Spec.Problem.CorrectProtocol
public import ConsensusLean.Lemmas.Problem.DerivedFacts
public import ConsensusLean.Lemmas.Problem.Facts.Atoms
public import ConsensusLean.Lemmas.Problem.Facts.Transfer
public import ConsensusLean.Lemmas.Problem.Facts.Network
public import ConsensusLean.Lemmas.Problem.Facts.Properties
public import ConsensusLean.Lemmas.Problem.Facts.Regimes
public import ConsensusLean.Lemmas.Problem.Facts.CorrectProtocol
public import ConsensusLean.Lemmas.Problem.Constant
import ConsensusLean.Lemmas.Tactic.Linarith
public import Mathlib.Tactic.FinCases
@[expose] public section

/-! # Regime tests (L0)

Concrete points and logs that show what each fixed L0 regime admits and what
it rejects.

* `psync_lost_message`: two honest, always-awake validators, `Δ = 2`, horizon
  `10`; validator 0 sends at `0` and nobody receives. The log is not partially
  synchronous for any GST `g ≤ 9` (validator 1 must hold the message at
  `max 0 g + Δ − 1 = max 0 g + 1 ≤ 10`), and is for `g = 10` (every deadline is past the
  horizon): a lost honest message is excused only by a GST so late that
  nothing is promised in the run.
* `outage_async_log` (M8): validator 0 sends at `3`, validator 1 receives
  at `7 = max 3 6 + Δ − 1`. The log meets the outage network `OutageNet 3 6`
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
* `outage_lookback_teeth`: the outage's η-sleepy count admits an honest
  validator falling asleep in the window and one late waker against three
  validators ready throughout, and rejects two late wakers against two ready
  ones, where plain sleepy participation holds.
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

omit [DecidableEq V] in
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
    p.readyAt c t ∪ p.awakeIn (max 0 (t - η)) t ∪ p.faultyAt t ⊆
      p.readyAt c t ∪ p.awakeIn (max 0 (t - η')) t ∪ p.faultyAt t := by
  classical
  refine Finset.union_subset_union (Finset.union_subset_union (Finset.Subset.refl _) ?_)
    (Finset.Subset.refl _)
  intro v hv
  simp only [awakeIn, Finset.mem_filter] at hv ⊢
  obtain ⟨hv, u, h1, h2, hh, ha⟩ := hv
  exact ⟨hv, u, le_trans (max_le_max le_rfl (by linarith)) h1, h2, hh, ha⟩

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
  have hc : ((p.readyAt c t ∪ p.awakeIn (max 0 (t - η)) t ∪ p.faultyAt t).card : ℚ) ≤
      (p.readyAt c t ∪ p.awakeIn (max 0 (t - η')) t ∪ p.faultyAt t).card := by
    exact_mod_cast Finset.card_le_card (p.etaSet_mono hη)
  exact lt_of_le_of_lt
    ((mul_le_mul_of_nonneg_left hc h0).trans
      (mul_le_mul_of_nonneg_right hθ (by positivity))) h

/-- A ready validator (catch-up `c ≥ 0`) at `t ≥ 0` is awake at `t`. -/
theorem readyAt_subset_awakeAt {c t : Time} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    p.readyAt c t ⊆ p.awakeAt t := by
  classical
  intro v hv
  simp only [readyAt, awakeAt, honestAt, Finset.mem_filter, Finset.mem_sdiff,
    Finset.mem_univ, true_and] at hv ⊢
  exact ⟨hv.1, hv.2 t (max_le ht (by linarith)) le_rfl⟩

/-- With positive look-back, η-sleepy (`θ ≥ 0`, catch-up `c ≥ 0`, `t ≥ 0`) implies the
awake-count form: the honest validators awake at `t` exceed fraction `θ` of
those awake at some time in `[max 0 (t − η), t]` together with the faulty
ones. -/
theorem EtaReadyAbove.awakeForm {θ : ℚ} {η c t : Time} (h : p.EtaReadyAbove θ η c t)
    (h0 : 0 ≤ θ) (hη : 0 < η) (hc0 : 0 ≤ c) (ht : 0 ≤ t) :
    θ * ((p.awakeIn (max 0 (t - η)) t ∪ p.faultyAt t).card : ℚ) < (p.awakeAt t).card := by
  classical
  rw [EtaReadyAbove, ite_eq_right_of_eq_false _ _ (eq_false (not_le.mpr hη))] at h
  have hsub : p.awakeIn (max 0 (t - η)) t ∪ p.faultyAt t ⊆
      p.readyAt c t ∪ p.awakeIn (max 0 (t - η)) t ∪ p.faultyAt t :=
    Finset.union_subset_union Finset.subset_union_right (Finset.Subset.refl _)
  have hc : ((p.awakeIn (max 0 (t - η)) t ∪ p.faultyAt t).card : ℚ) ≤
      (p.readyAt c t ∪ p.awakeIn (max 0 (t - η)) t ∪ p.faultyAt t).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hr : ((p.readyAt c t).card : ℚ) ≤ (p.awakeAt t).card := by
    exact_mod_cast Finset.card_le_card (p.readyAt_subset_awakeAt hc0 ht)
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hc h0) (lt_of_lt_of_le h hr)

variable {p}

omit [DecidableEq V] in
/-- A smaller fraction is weaker. -/
theorem SleepyOn.mono {θ θ' : ℚ} {c W a b : Time} (h : p.SleepyOn θ' c W a b)
    (hle : θ ≤ θ') : p.SleepyOn θ c W a b :=
  fun t ha hb => (h t ha hb).mono _ hle

/-- With look-back `0`, η-sleepy is plain sleepy. -/
theorem etaSleepyOn_zero (θ : ℚ) (c W a b : Time) :
    p.EtaSleepyOn θ 0 c W a b ↔ p.SleepyOn θ c W a b :=
  forall_congr' fun t => imp_congr_right fun _ => imp_congr_right fun _ =>
    (p.retain (p.lookAhead W t)).etaReadyAbove_zero θ c t

/-- η-sleepy (`θ ≥ 0`) implies plain sleepy. -/
theorem EtaSleepyOn.sleepyOn {θ : ℚ} {η c W a b : Time} (h : p.EtaSleepyOn θ η c W a b)
    (h0 : 0 ≤ θ) : p.SleepyOn θ c W a b :=
  fun t ha hb => (h t ha hb).readyAbove h0

/-- A smaller fraction (`θ ≥ 0`) and a shorter look-back are weaker. -/
theorem EtaSleepyOn.mono {θ θ' : ℚ} {η η' c W a b : Time} (h : p.EtaSleepyOn θ' η' c W a b)
    (h0 : 0 ≤ θ) (hθ : θ ≤ θ') (hη : η ≤ η') : p.EtaSleepyOn θ η c W a b :=
  fun t ha hb => (h t ha hb).mono _ h0 hθ hη

/-- The guarded committee budget weakens with its fraction and look-back. -/
theorem CommitteeSleepyOn.mono {K : Time → Finset V} {θ θ' : ℚ} {η η' c W a b : Time}
    (h : p.CommitteeSleepyOn K θ' η' c W a b)
    (h0 : 0 ≤ θ) (hθ : θ ≤ θ') (hη : η ≤ η') :
    p.CommitteeSleepyOn K θ η c W a b := by
  classical
  intro t hat htb hK
  have ht := h t hat htb hK
  dsimp only at ht ⊢
  let q := p.retain (p.lookAhead W t)
  have hd : Disjoint (q.readyAt c t ∩ K t) (q.faultyAt t ∩ K t) := by
    apply Finset.disjoint_left.mpr
    intro v hr hf
    have hr' := (Finset.mem_inter.mp hr).1
    simp only [readyAt, Finset.mem_filter, Finset.mem_univ, true_and] at hr'
    exact hr'.1 (Finset.mem_inter.mp hf).1
  have hbase : (q.readyAt c t ∩ K t).card + (q.faultyAt t ∩ K t).card =
      ((q.readyAt c t ∪ q.faultyAt t) ∩ K t).card := by
    rw [Finset.union_inter_distrib_right, Finset.card_union_of_disjoint hd]
  by_cases hη0 : η ≤ 0
  · simp only [ite_eq_left hη0]
    by_cases hη0' : η' ≤ 0
    · simp only [ite_eq_left hη0'] at ht
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hθ (by positivity)) ht
    · simp only [ite_eq_right hη0'] at ht
      have hsub : (q.readyAt c t ∪ q.faultyAt t) ∩ K t ⊆
          (q.readyAt c t ∪ q.awakeIn (max 0 (t - η')) t ∪ q.faultyAt t) ∩ K t :=
        Finset.inter_subset_inter
          (Finset.union_subset_union Finset.subset_union_left (Finset.Subset.refl _))
          (Finset.Subset.refl _)
      have hn : (((q.readyAt c t ∩ K t).card + (q.faultyAt t ∩ K t).card : Nat) : ℚ) ≤
          (((q.readyAt c t ∪ q.awakeIn (max 0 (t - η')) t ∪ q.faultyAt t) ∩ K t).card : ℚ) := by
        have hh := Finset.card_le_card hsub
        rw [← hbase] at hh
        exact_mod_cast hh
      exact lt_of_le_of_lt ((mul_le_mul_of_nonneg_left hn h0).trans
        (mul_le_mul_of_nonneg_right hθ (by positivity))) ht
  · have hη0' : ¬ η' ≤ 0 := fun h' => hη0 (hη.trans h')
    simp only [ite_eq_right hη0]
    simp only [ite_eq_right hη0'] at ht
    have hn : (((q.readyAt c t ∪ q.awakeIn (max 0 (t - η)) t ∪ q.faultyAt t) ∩ K t).card : ℚ) ≤
        (((q.readyAt c t ∪ q.awakeIn (max 0 (t - η')) t ∪ q.faultyAt t) ∩ K t).card : ℚ) := by
      exact_mod_cast Finset.card_le_card
        (Finset.inter_subset_inter (q.etaSet_mono hη) (Finset.Subset.refl (K t)))
    exact lt_of_le_of_lt ((mul_le_mul_of_nonneg_left hn h0).trans
      (mul_le_mul_of_nonneg_right hθ (by positivity))) ht

omit [DecidableEq V] in
/-- A larger fault bound is weaker. -/
theorem HealthyOn.mono {β β' : ℚ} {g b : Time} (h : p.HealthyOn β' g b) (hle : β' ≤ β) :
    p.HealthyOn β g b :=
  ⟨lt_of_lt_of_le h.1 (mul_le_mul_of_nonneg_right hle (by positivity)), h.2⟩

end EnvPoint

namespace System

variable {V : Type} [Fintype V] [DecidableEq V] {S : System V} {Prog Prog' : Type}
  {K : Contract Prog} {K' : Contract Prog'} {r : S.Run}

/-- With look-back `η = 0`, the outage regime's participation is plain sleepy
throughout, in the population and in each selected committee, at the readers'
catch-up `cDur` (the outage catch-up `max cDur (0 − 1)` is `cDur`). -/
theorem outage_eta_zero {X : External S} (hη : K.params.η = 0) {T b₀ b₁ : Time} :
    S.Outage X K T b₀ b₁ r ↔ OutageTimes K.params (S.pt r).env.ΔAC T b₀ b₁ ∧
      (S.log r).OutageNet (S.pt r) b₀ b₁ ∧
      (S.pt r).SleepyOn K.params.θ (S.cDur K r) (S.aheadDur K r) 0 (S.pt r).horizon ∧
      (S.pt r).CommitteeSleepyOn (X.selected (S.pt r).env (X.ext r)) K.params.θ
        0 (S.cDur K r) (S.committeeAheadDur K r) 0 (S.pt r).horizon := by
  have h0 : ((K.params.η : Time) * (S.pt r).env.ΔAC) = 0 := by simp [hη]
  have hc : max (S.cDur K r) (0 - 1) = S.cDur K r := by
    refine max_eq_left ?_
    have : (0 : Time) ≤ S.cDur K r := mul_nonneg (by positivity) (S.pt r).env.ΔAC_pos.le
    linarith
  unfold Outage
  rw [h0, hc, EnvPoint.etaSleepyOn_zero]
  refine and_congr_right' (and_congr_right' (and_congr_right' ⟨fun h => ?_, fun h δ hδ0 hδ => ?_⟩))
  · intro t ht htb hne
    have := h 0 le_rfl le_rfl t ht htb (by simpa only [sub_zero, max_eq_right ht] using hne)
    simpa only [sub_zero, max_eq_right ht] using this
  · obtain rfl : δ = 0 := le_antisymm hδ hδ0
    intro t ht htb hne
    have := h t ht htb (by simpa only [sub_zero, max_eq_right ht] using hne)
    simpa only [sub_zero, max_eq_right ht] using this

omit [Fintype V] [DecidableEq V] in
theorem cDur_of_catchUp (hc : K'.params.catchUp = K.params.catchUp) :
    S.cDur K' r = S.cDur K r := by
  unfold cDur; rw [hc]

omit [DecidableEq V] in
/-- Weaker thresholds (same catch-up) keep the sleepy regime. -/
theorem Sleepy.of_le (hc : K'.params.catchUp = K.params.catchUp) (hθ : K'.params.θ ≤ K.params.θ)
    (hW : K'.params.ahead = K.params.ahead)
    (h : S.Sleepy K r) : S.Sleepy K' r := by
  refine ⟨h.1, ?_⟩
  rw [cDur_of_catchUp hc]
  simpa only [aheadDur, hW] using EnvPoint.SleepyOn.mono h.2 hθ

omit [DecidableEq V] in
/-- A weaker fault bound and a larger FG delay bound keep the healthy regime. -/
theorem Healthy.of_le {g : Time} (hβ : K.params.β ≤ K'.params.β)
    (hr : K.params.fgDelay ≤ K'.params.fgDelay) (h : S.Healthy K g r) : S.Healthy K' g r := by
  refine ⟨h.1, EnvPoint.HealthyOn.mono h.2.1 hβ, h.2.2.trans ?_⟩
  have hr' : ((K.params.fgDelay : Nat) : Time) ≤ (K'.params.fgDelay : Nat) := by
    exact_mod_cast hr
  exact mul_le_mul_of_nonneg_right hr' (S.pt r).env.ΔAC_pos.le

/-- Weaker thresholds (`θ' ≥ 0`), a shorter lag and a larger budget (same
catch-up, look-back and look-aheads) keep the outage regime. -/
theorem Outage.of_le {X : External S} {T b₀ b₁ : Time}
    (hc : K'.params.catchUp = K.params.catchUp)
    (h0 : 0 ≤ K'.params.θ) (hθ : K'.params.θ ≤ K.params.θ) (hη : K'.params.η = K.params.η)
    (hl : K'.params.lag ≤ K.params.lag) (hb : K.params.budget ≤ K'.params.budget)
    (hW : K'.params.ahead = K.params.ahead)
    (hCommittee : K'.params.committeeAhead = K.params.committeeAhead)
    (h : S.Outage X K T b₀ b₁ r) : S.Outage X K' T b₀ b₁ r := by
  obtain ⟨⟨hT, hlag, h01, hbud⟩, hn, hs, hcs⟩ := h
  have hΔ : (0 : Time) ≤ (S.pt r).env.ΔAC := (S.pt r).env.ΔAC_pos.le
  have hl' : ((K'.params.lag : Nat) : Time) ≤ (K.params.lag : Time) := by exact_mod_cast hl
  have hb' : ((K.params.budget : Nat) : Time) ≤ (K'.params.budget : Time) := by exact_mod_cast hb
  refine ⟨⟨hT, ?_, h01, ?_⟩, hn, ?_, fun δ hδ0 hδ => ?_⟩
  · exact le_trans (add_le_add_right (mul_le_mul_of_nonneg_right hl' hΔ) _) hlag
  · exact hbud.trans (add_le_add_right (mul_le_mul_of_nonneg_right hb' hΔ) _)
  · rw [cDur_of_catchUp hc, hη]
    simpa only [aheadDur, hW] using EnvPoint.EtaSleepyOn.mono hs h0 hθ le_rfl
  · rw [hη] at hδ
    rw [cDur_of_catchUp hc, hη]
    simpa only [committeeAheadDur, hCommittee] using
      EnvPoint.CommitteeSleepyOn.mono (hcs δ hδ0 hδ) h0 hθ le_rfl

end System

end Consensus

namespace Consensus.Shape.Tests.Regimes
open Consensus

/-- The log with no sends, no receipts and empty inboxes. -/
def silentLog (V M : Type) : CommLog V M :=
  ⟨fun _ _ _ => False, fun _ _ _ => False, fun _ _ => [], fun _ => False⟩

/-- With no submissions, the silent log meets every delivery requirement
vacuously. -/
theorem silentLog_delivers {V M : Type} (p : EnvPoint V) (hs : ∀ v t, p.submit v t = [])
    (dl dlF : Time → Time) (cut : Time) : (silentLog V M).Delivers p dl dlF cut := by
  refine ⟨fun _ _ _ h => h.elim, fun _ _ _ h => h.elim, ?_⟩
  intro u x τ _ _ _ hx
  rw [hs] at hx
  exact absurd hx List.not_mem_nil

section Lost

/-- Two honest validators, always awake, `Δ = 2` (deadlines `a + 1` before the GST shift),
horizon `10`. -/
def ptL : EnvPoint (Fin 2) :=
  ⟨⟨2, by decide, 2, by decide, fun _ _ => true⟩, fun _ => ∅,
    monotone_const, 10, fun _ _ => []⟩

/-- Validator 0 sends at `0`; nobody receives anything. -/
def logL : CommLog (Fin 2) Unit :=
  ⟨fun v _ t => v = 0 ∧ t = 0, fun _ _ _ => False, fun _ _ => [], fun _ => False⟩

/-- A lost honest message: not partially synchronous for any GST `g ≤ 9`; for
`g = 10` every deadline is past the horizon and nothing is required. -/
theorem psync_lost_message : (∀ g : Time, g ≤ 9 → ¬ logL.PSync ptL g) ∧ logL.PSync ptL 10 := by
  refine ⟨fun g hg h => ?_, ⟨?_, fun _ _ _ _ _ h => h.elim, ?_⟩⟩
  · have hd : max 0 g + 2 - 1 ≤ 10 := by
      have : max 0 g ≤ 9 := max_le (by decide) hg
      dsimp only [Time] at *; omega
    obtain ⟨t', -, hs, -⟩ := h.msgs 0 () 0 ⟨rfl, rfl⟩
      (by simp [EnvPoint.HonestAt, ptL]) id 1
      0 le_rfl hd hd (by simp [EnvPoint.HonestAt, ptL]) (fun _ _ _ => rfl)
    rcases hs with ⟨h1, -⟩ | h1
    · exact absurd h1 (by decide)
    · exact h1
  · rintro v m t ⟨-, rfl⟩ - - w a - hc - - -
    change max a 10 + 2 - 1 ≤ 10 at hc
    have := le_max_right a 10
    dsimp only [Time] at *; omega
  · intro u x τ _ _ _ hx
    exact absurd hx List.not_mem_nil

end Lost

section Async

/-- Validator 0 sends at `3`; validator 1 receives it at `7`. -/
def logA : CommLog (Fin 2) Unit :=
  ⟨fun v _ t => v = 0 ∧ t = 3, fun v _ t => v = 1 ∧ t = 7, fun _ _ => [], fun _ => False⟩

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
  have hnot : ∀ dl dlF cut, dl 3 = 4 → 4 ≤ cut → ¬ logA.Delivers ptL dl dlF cut := by
    intro dl dlF cut h3 hc h
    obtain ⟨t', ht', hs, -⟩ := h.msgs 0 () 3 ⟨rfl, rfl⟩
      (by simp [EnvPoint.HonestAt, ptL]) id 1
      3 le_rfl (by rw [h3]; exact hc) (by rw [h3]; decide)
      (by simp [EnvPoint.HonestAt, ptL]) (fun _ _ _ => rfl)
    rw [h3] at ht'
    rcases hs with ⟨h1, -⟩ | ⟨-, rfl⟩
    · exact absurd h1 (by decide)
    · exact absurd ht' (by decide)
  refine ⟨⟨⟨?_, fun _ _ _ _ _ h => h.elim, ?_⟩, ⟨?_, fun _ _ _ _ _ h => h.elim, ?_⟩⟩,
    hnot _ _ _ rfl (by decide), hnot _ _ _ rfl le_rfl⟩
  · rintro v m t ⟨-, rfl⟩ - - w a ha hc - - -
    change a + 2 - 1 ≤ 3 at hc
    dsimp only [Time] at *; omega
  · intro u x τ _ _ _ hx
    exact absurd hx List.not_mem_nil
  · rintro v m t ⟨-, rfl⟩ - - w a - - - - -
    refine logA_held w _ ?_
    change 7 ≤ max a 6 + 2 - 1
    have := le_max_right a 6
    dsimp only [Time] at *; omega
  · intro u x τ _ _ _ hx
    exact absurd hx List.not_mem_nil

end Async

section Sleeper

/-- Five validators, `0` faulty; honest `4` asleep on `[2, 5]`; `Δ = 1`,
horizon `10`, no submissions. -/
def ptS : EnvPoint (Fin 5) :=
  ⟨⟨1, by decide, 1, by decide, fun v t => decide (v ≠ 4 ∨ t < 2 ∨ 5 < t)⟩,
    fun _ => {0}, monotone_const, 10,
    fun _ _ => []⟩

theorem ptS_faulty (t : Time) : ptS.faultyAt t = {0} := rfl

/-- Validators `1, 2, 3` are ready at every time, at every catch-up. -/
theorem ptS_readyAt (c t : Time) : ({1, 2, 3} : Finset (Fin 5)) ⊆ ptS.readyAt c t := by
  classical
  intro v hv
  unfold EnvPoint.readyAt
  refine Finset.mem_filter.mpr ⟨?_, ?_, fun u _ _ => ?_⟩ <;>
    fin_cases hv <;> simp [ptS, EnvPoint.HonestAt]

theorem ptS_readyAbove (c t : Time) : ptS.ReadyAbove (1 / 2) c t := by
  have h3 : (3 : ℚ) ≤ (ptS.readyAt c t).card := by
    have := Finset.card_le_card (ptS_readyAt c t)
    exact_mod_cast this
  unfold EnvPoint.ReadyAbove EnvPoint.faultCount
  rw [ptS_faulty, Finset.card_singleton]
  push_cast
  linarith

/-- A sleeper: honest validator `4` sleeps at `2`. The point is ½-sleepy at
every catch-up; with the silent log, every contract with `θ ≤ ½` has the
sleepy regime; the point is not healthy from `0` at any fault bound. -/
theorem sleepy_with_sleeper :
    ptS.HonestAt (4 : Fin 5) 2 ∧ ptS.env.awake 4 2 = false ∧
    (∀ c W, ptS.SleepyOn (1 / 2) c W 0 ptS.horizon) ∧
    (∀ {Idx : Type} (P : Params Idx), P.θ ≤ 1 / 2 →
      (silentLog (Fin 5) Unit).PSync ptS 0 ∧
        ptS.SleepyOn P.θ ((P.catchUp : Time) * ptS.env.ΔAC)
          ((P.ahead : Time) * ptS.env.ΔAC) 0 ptS.horizon) ∧
    ∀ β, ¬ ptS.HealthyOn β 0 ptS.horizon := by
  have hret : ∀ d, ptS.retain d = ptS := fun _ => rfl
  refine ⟨by simp [EnvPoint.HonestAt, ptS], by decide,
    fun c W t _ _ => ?_, fun P hθ => ?_, ?_⟩
  · rw [hret]; exact ptS_readyAbove c t
  · exact ⟨silentLog_delivers _ (fun _ _ => rfl) _ _ _,
      fun t _ _ => by rw [hret]; exact (ptS_readyAbove _ t).mono _ hθ⟩
  · rintro β ⟨-, ha⟩
    have := ha 4 2 (by decide) (by decide) (by simp [EnvPoint.HonestAt, ptS])
    exact absurd this (by decide)

end Sleeper

section WakeAtGST

/-- Three honest validators, all asleep before `5` and awake from `5`; `Δ = 1`,
horizon `20`. -/
def ptG : EnvPoint (Fin 3) :=
  ⟨⟨1, by decide, 1, by decide, fun _ t => decide (5 ≤ t)⟩, fun _ => ∅,
    monotone_const, 20, fun _ _ => []⟩

/-- A wake at GST: healthy from `5` at `β = ⅓` (and the healthy regime holds
with the silent log for every `β ≥ ⅓`), nobody ready at `5` with catch-up `2`,
everyone ready at `max 5 0 + 2 + 1 = 8`. -/
theorem healthy_wake_at_gst :
    ptG.HealthyOn (1 / 3) 5 ptG.horizon ∧
    (∀ {Idx : Type} (P : Params Idx), 1 / 3 ≤ P.β →
      (silentLog (Fin 3) Unit).PSync ptG 5 ∧ ptG.HealthyOn P.β 5 ptG.horizon) ∧
    ptG.readyAt 2 5 = ∅ ∧ (max 5 0 + 2 + 1 : Time) = 8 ∧ ∀ v, ptG.Ready 2 v (max 5 0 + 2 + 1) := by
  have hH : ptG.HealthyOn (1 / 3) 5 ptG.horizon := by
    refine ⟨by norm_num [EnvPoint.faultCount, ptG], fun v u hu _ _ => ?_⟩
    simp only [ptG, decide_eq_true_eq]
    exact le_trans (le_max_left _ _) hu
  refine ⟨hH, fun P hφ => ⟨silentLog_delivers _ (fun _ _ => rfl) _ _ _, hH.mono hφ⟩, ?_,
    by decide, fun v => ⟨by simp [EnvPoint.HonestAt, ptG], fun u hu _ => ?_⟩⟩
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
  ⟨⟨1, by decide, 1, by decide, fun v _ => decide (v ≠ 2)⟩, fun _ => ∅,
    monotone_const, 10, fun _ _ => []⟩

/-- Three honest validators, everyone always awake. -/
def ptA : EnvPoint (Fin 3) :=
  ⟨⟨1, by decide, 1, by decide, fun _ _ => true⟩, fun _ => ∅,
    monotone_const, 10, fun _ _ => []⟩

/-- The healthy regime is full participation: two of three honest validators
awake throughout (no faults) is not healthy at any fault bound `β`; with
everyone awake it is healthy at every `β > 0`. -/
theorem healthy_needs_full_participation :
    (∀ β, ¬ ptT.HealthyOn β 0 ptT.horizon) ∧ ∀ β, 0 < β → ptA.HealthyOn β 0 ptA.horizon := by
  refine ⟨fun β h => ?_, fun β hβ => ⟨?_, fun _ _ _ _ _ => rfl⟩⟩
  · have := h.2 2 0 (by decide) (by decide) (by simp [EnvPoint.HonestAt, ptT])
    exact absurd this (by decide)
  · simp only [EnvPoint.faultCount, ptA, Finset.card_empty, Nat.cast_zero, Fintype.card_fin]
    positivity

end FullParticipation

section Faults

/-- One faulty validator among three, everyone awake. -/
def ptF : EnvPoint (Fin 3) :=
  ⟨⟨1, by decide, 1, by decide, fun _ _ => true⟩, fun _ => {0},
    monotone_const, 10, fun _ _ => []⟩

/-- So one faulty validator among three is never healthy at `β = ⅓`, on any
window. -/
theorem faulty_third_not_healthy (g b : Time) : ¬ ptF.HealthyOn (1 / 3) g b := by
  intro h
  have := h.1
  norm_num [EnvPoint.faultCount, ptF] at this

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

section OutageLookBack

/-- Five validators, `0` faulty; honest `4` asleep before `3` and awake from
`3` (a late waker); `Δ = 1`, horizon `10`, no submissions. -/
def ptW : EnvPoint (Fin 5) :=
  ⟨⟨1, by decide, 1, by decide, fun v t => decide (v ≠ 4 ∨ 3 ≤ t)⟩,
    fun _ => {0}, monotone_const, 10,
    fun _ _ => []⟩

/-- As `ptW`, with honest `3` and `4` both waking at `3`. -/
def ptW2 : EnvPoint (Fin 5) :=
  ⟨⟨1, by decide, 1, by decide, fun v t => decide ((v ≠ 3 ∧ v ≠ 4) ∨ 3 ≤ t)⟩,
    fun _ => {0}, monotone_const, 10,
    fun _ _ => []⟩

theorem ptW_readyAt (c t : Time) : ({1, 2, 3} : Finset (Fin 5)) ⊆ ptW.readyAt c t := by
  classical
  intro v hv
  unfold EnvPoint.readyAt
  refine Finset.mem_filter.mpr ⟨?_, ?_, fun u _ _ => ?_⟩ <;>
    fin_cases hv <;> simp [ptW, EnvPoint.HonestAt]

theorem ptW2_readyAt (c t : Time) : ({1, 2} : Finset (Fin 5)) ⊆ ptW2.readyAt c t := by
  classical
  intro v hv
  unfold EnvPoint.readyAt
  refine Finset.mem_filter.mpr ⟨?_, ?_, fun u _ _ => ?_⟩ <;>
    fin_cases hv <;> simp [ptW2, EnvPoint.HonestAt]

/-- At `ptW2`, a validator ready at `10` with catch-up `9` is awake at `0`, so it is `1` or `2`. -/
theorem ptW2_readyAt_sub : ptW2.readyAt 9 10 ⊆ ({1, 2} : Finset (Fin 5)) := by
  classical
  intro v hv
  obtain ⟨-, hh, hr⟩ := Finset.mem_filter.mp hv
  have h0 := hr 0 (by norm_num) (by norm_num)
  fin_cases v <;> simp_all [ptW2, EnvPoint.HonestAt]

/-- At `ptW2`, every honest validator is awake at `3`, so the look-back set with the faulty `0`
is every validator. -/
theorem ptW2_lookBack_univ :
    ptW2.readyAt 9 10 ∪ ptW2.awakeIn (max 0 (10 - 10)) 10 ∪ ptW2.faultyAt 10 = Finset.univ := by
  classical
  refine Finset.eq_univ_of_forall fun v => ?_
  by_cases hv : v = 0
  · subst hv; exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  · refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, 3, by norm_num, by norm_num, ?_, ?_⟩))
    · simpa [ptW2, EnvPoint.HonestAt] using hv
    · simp [ptW2]

/-- The outage's η-sleepy count (`θ = ½`, look-back `10`, catch-up `9`, at `10`, so the window
`[0, 10]`) has teeth:
* the sleeper point `ptS` (honest `4` asleep on `[2, 5]`) meets it: sleeping in the window is
  allowed, and the sleeper counts against the three validators ready throughout;
* `ptW` (honest `4` wakes at `3`) meets it: `½·5 < 3`;
* `ptW2` (honest `3` and `4` wake at `3`) violates it: the late wakers count against the ready
  validators, `½·5 ≮ 2`, although every honest validator is awake from `3` and the plain sleepy
  count (`η = 0`) holds there. -/
theorem outage_lookback_teeth :
    ptS.EtaReadyAbove (1 / 2) 10 9 10 ∧ ptW.EtaReadyAbove (1 / 2) 10 9 10 ∧
      ¬ ptW2.EtaReadyAbove (1 / 2) 10 9 10 ∧ ptW2.ReadyAbove (1 / 2) 9 10 := by
  have hpos : ¬ (10 : Time) ≤ 0 := by norm_num
  have key : ∀ U R : Finset (Fin 5), 3 ≤ R.card → (1 / 2 : ℚ) * U.card < R.card := by
    intro U R hR
    have hU : (U.card : ℚ) ≤ 5 := by
      exact_mod_cast (Finset.card_le_univ U).trans (by simp)
    have hR' : (3 : ℚ) ≤ R.card := by exact_mod_cast hR
    linarith
  refine ⟨?_, ?_, fun h => ?_, ?_⟩
  · simp only [EnvPoint.EtaReadyAbove, hpos, ↓reduceIte]
    have h3 := Finset.card_le_card (ptS_readyAt 9 10)
    rw [show ({1, 2, 3} : Finset (Fin 5)).card = 3 from rfl] at h3
    exact key _ _ h3
  · simp only [EnvPoint.EtaReadyAbove, hpos, ↓reduceIte]
    have h3 := Finset.card_le_card (ptW_readyAt 9 10)
    rw [show ({1, 2, 3} : Finset (Fin 5)).card = 3 from rfl] at h3
    exact key _ _ h3
  · simp only [EnvPoint.EtaReadyAbove, hpos, ↓reduceIte, ptW2_lookBack_univ, Finset.card_univ,
      Fintype.card_fin] at h
    have h2 : ((ptW2.readyAt 9 10).card : ℚ) ≤ 2 := by
      exact_mod_cast Finset.card_le_card ptW2_readyAt_sub
    push_cast at h
    linarith
  · have h2 : (2 : ℚ) ≤ (ptW2.readyAt 9 10).card := by
      exact_mod_cast Finset.card_le_card (ptW2_readyAt 9 10)
    unfold EnvPoint.ReadyAbove EnvPoint.faultCount
    rw [show ptW2.faultyAt 10 = {0} from rfl, Finset.card_singleton]
    push_cast
    linarith

end OutageLookBack

end Consensus.Shape.Tests.Regimes

end
