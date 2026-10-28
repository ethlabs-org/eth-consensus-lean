module
public import ConsensusProblem
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
  healthy from `0` at ⅔ (three validators awake throughout are not more than
  ⅔ of five): sleepy participation is the weaker, dynamic regime.
* `healthy_wake_at_gst` (M11): three honest validators asleep before `5` and
  awake from `5`. Healthy from GST `5` at ⅔ (the healthy regime counts awake,
  not ready: a wake at GST is allowed), although nobody is ready at `5` with
  catch-up `2`; everyone is ready at `readyFrom 2 5 = 8`, where progress
  windows start.
* `healthy_needs_two_thirds`: three honest validators, one always asleep:
  exactly ⅔ awake is not healthy at `φ = ⅔` (the regime needs *more* than
  ⅔), but is at `φ = ½`.
* `healthy_faultsBelow` (M21): healthy at ⅔ bounds the faults below ⅓, on every
  point; so a point with one faulty validator among three is never healthy at
  ⅔, however awake.
* `outage_times_teeth`: with lag `2`, budget `3`, `Δ = 1`, `OutageTimes`
  accepts `T = 0, [2, 5)`, and rejects an arming at a negative time, an arming
  less than `lag·Δ` before the window, a window longer than `budget·Δ`, and an
  inverted window. -/

namespace Consensus.Shape.Tests.Regimes
open Consensus

/-- The log with no sends, no receipts and empty inboxes. -/
def silentLog (V M : Type) : CommLog V M :=
  ⟨fun _ _ _ => False, fun _ _ _ => False, fun _ _ => []⟩

/-- With no submissions, the silent log meets every delivery requirement
vacuously. -/
theorem silentLog_delivers {V M : Type} (p : EnvPoint V) (hs : ∀ v t, p.submit v t = [])
    (dl : Time → Time) (cut : Time) : (silentLog V M).Delivers p dl cut := by
  refine ⟨fun _ _ _ _ h => h.elim, fun _ _ _ _ h => h.elim, ?_⟩
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
  refine ⟨fun g hg h => ?_, ⟨?_, ?_, ?_⟩⟩
  · have hd : max 0 g + 1 ≤ 10 := by
      have : max 0 g ≤ 9 := max_le (by decide) hg
      dsimp only [Time] at *; omega
    obtain ⟨t', -, hs, -⟩ := h.msgs 0 (Finset.mem_univ _) () 0 ⟨rfl, rfl⟩ 1 (Finset.mem_univ _)
      hd hd rfl
    rcases hs with ⟨h1, -⟩ | h1
    · exact absurd h1 (by decide)
    · exact h1
  · rintro v - m t ⟨-, rfl⟩ w - hc - -
    change max 0 10 + 1 ≤ 10 at hc
    exact absurd hc (by decide)
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
      (Finset.mem_univ _) (by rw [h3]; exact hc) (by rw [h3]; decide) (by rw [h3]; rfl)
    rw [h3] at ht'
    rcases hs with ⟨h1, -⟩ | ⟨-, rfl⟩
    · exact absurd h1 (by decide)
    · exact absurd ht' (by decide)
  refine ⟨⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩, hnot _ _ rfl (by decide), hnot _ _ rfl le_rfl⟩
  · rintro v - m t ⟨-, rfl⟩ w - hc - -
    exact absurd hc (by decide)
  · rintro v - m t ⟨-, rfl⟩ w - a ha hc - -
    change a + 1 ≤ 3 at hc
    dsimp only [Time] at *; omega
  · intro u _ x τ _ _ hx
    exact absurd hx List.not_mem_nil
  · rintro v - m t ⟨-, rfl⟩ w - - - -
    exact logA_held w _ (by decide)
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
sleepy regime; the point is not healthy from `0` at ⅔. -/
theorem sleepy_with_sleeper :
    (4 : Fin 5) ∈ ptS.honest ∧ ptS.env.awake 4 2 = false ∧
    (∀ c, ptS.Sleepy (1 / 2) c) ∧
    (∀ {Idx : Type} (P : Params Idx), P.θ ≤ 1 / 2 →
      Regime.Sleepy P ptS (silentLog (Fin 5) Unit)) ∧
    ¬ ptS.HealthyFrom (2 / 3) 0 := by
  refine ⟨by decide, by decide, fun c t _ _ => ptS_readyAbove c t, fun P hθ => ?_, ?_⟩
  · exact ⟨silentLog_delivers _ (fun _ _ => rfl) _ _,
      fun t _ _ => (ptS_readyAbove _ t).mono _ hθ⟩
  · rintro ⟨H, hH, hc, ha⟩
    have hsub : H ⊆ {1, 2, 3} := by
      intro v hv
      have hvh := hH hv
      have h4 : v ≠ 4 := by
        rintro rfl
        have := ha 4 hv 2 (by decide) (by decide)
        exact absurd this (by decide)
      fin_cases v <;> simp_all [ptS]
    have : (H.card : ℚ) ≤ 3 := by exact_mod_cast Finset.card_le_card hsub
    norm_num at hc
    linarith

end Sleeper

section WakeAtGST

/-- Three honest validators, all asleep before `5` and awake from `5`; `Δ = 1`,
horizon `20`. -/
def ptG : EnvPoint (Fin 3) :=
  ⟨⟨1, by decide, fun _ t => decide (5 ≤ t)⟩, Finset.univ, 20, fun _ _ => []⟩

/-- A wake at GST: healthy from `5` at ⅔ (and the healthy regime holds with the
silent log for every `φ ≤ ⅔`), nobody ready at `5` with catch-up `2`,
everyone ready at `readyFrom 2 5 = 8`. -/
theorem healthy_wake_at_gst :
    ptG.HealthyFrom (2 / 3) 5 ∧
    (∀ {Idx : Type} (P : Params Idx), P.φ ≤ 2 / 3 →
      Regime.Healthy P ptG (silentLog (Fin 3) Unit) 5) ∧
    ptG.readyAt 2 5 = ∅ ∧ readyFrom 2 5 = 8 ∧ ∀ v, ptG.Ready 2 v (readyFrom 2 5) := by
  have hH : ptG.HealthyFrom (2 / 3) 5 := by
    refine ⟨Finset.univ, subset_rfl, by norm_num, fun v _ u hu _ => ?_⟩
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
  · change max 0 (readyFrom 2 5 - 2 - 1) ≤ u at hu
    simp only [ptG, decide_eq_true_eq]
    simp only [readyFrom] at hu
    have := le_max_right (0 : Time) (max 5 0 + 2 + 1 - 2 - 1)
    simp only [max_eq_left (show (0 : Time) ≤ 5 by decide)] at hu this
    dsimp only [Time] at *; omega

end WakeAtGST

section TwoThirds

/-- Three honest validators; validator `2` always asleep. -/
def ptT : EnvPoint (Fin 3) :=
  ⟨⟨1, by decide, fun v _ => decide (v ≠ 2)⟩, Finset.univ, 10, fun _ _ => []⟩

/-- Exactly ⅔ awake is not healthy at `φ = ⅔`; it is at `φ = ½`. -/
theorem healthy_needs_two_thirds : ¬ ptT.HealthyFrom (2 / 3) 0 ∧ ptT.HealthyFrom (1 / 2) 0 := by
  refine ⟨?_, ⟨{0, 1}, Finset.subset_univ _, by norm_num, ?_⟩⟩
  · rintro ⟨H, -, hc, ha⟩
    have hsub : H ⊆ {0, 1} := by
      intro v hv
      have h2 : v ≠ 2 := by
        rintro rfl
        have := ha 2 hv 0 (by decide) (by decide)
        exact absurd this (by decide)
      fin_cases v <;> simp_all
    have h2 : H.card ≤ 2 := (Finset.card_le_card hsub).trans (by decide)
    have hc' : (2 : ℚ) < H.card := by simpa using hc
    have : 2 < H.card := by exact_mod_cast hc'
    omega
  · intro v hv u _ _
    fin_cases hv <;> rfl

end TwoThirds

section Faults

/-- Healthy at ⅔ bounds the faults below ⅓, on every point and window. -/
theorem healthy_faultsBelow {V : Type} [Fintype V] [DecidableEq V] (p : EnvPoint V) (g b : Time)
    (h : p.HealthyOn (2 / 3) g b) : p.FaultsBelow (1 / 3) := by
  have := h.faultsBelow
  norm_num at this
  exact this

/-- One faulty validator among three, everyone awake. -/
def ptF : EnvPoint (Fin 3) :=
  ⟨⟨1, by decide, fun _ _ => true⟩, Finset.univ.erase 0, 10, fun _ _ => []⟩

/-- So one faulty validator among three is never healthy at ⅔, on any window. -/
theorem faulty_third_not_healthy (g b : Time) : ¬ ptF.HealthyOn (2 / 3) g b := by
  intro h
  have := healthy_faultsBelow ptF g b h
  unfold EnvPoint.FaultsBelow at this
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

end Consensus.Shape.Tests.Regimes

end
