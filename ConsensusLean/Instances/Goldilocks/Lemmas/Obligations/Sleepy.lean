module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunSimulates
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Order
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Defs
import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Regimes.Inclusion
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Chains
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Regimes.Sleepy
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Provenance
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Compare
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.FrameLabels
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Transfer
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.Served
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
public import ConsensusLean.Spec.Shape.Run
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Finite sleepy engine bridges

Binding-generic facts of the stored clock and of event cuts (`event_before_endCut`,
`readPoint_after_event`, `now_*`, `ready_at_stored_now`). No whole-run `SleepyRun` or `HealthyRun`
is inferred from a finite engine horizon. The growing-fault engine-to-node bridges of the Sleepy
regime are in `Lemmas/Growing/Sleepy/Engine`. -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation

open Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup) (hn : 1 ≤ Fintype.card V)

theorem event_before_endCut {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
    (hv : rho.ExecutionValid) {t : Time} (ht : 0 ≤ t)
    {i : Nat} {e : Model.Event V (Model.protoOf (compiled (goldilocks S)) E).Object}
    (he : rho.events[i]? = some e) :
    i < (chainTrace rho).endCut t ↔ e.time ≤ t := by
  classical
  let n := (chainTrace rho).endCut t
  have hnle : n ≤ rho.events.length := Nat.findGreatest_le _
  have hnTime : rho.cutTime n ≤ t :=
    Nat.findGreatest_spec (P := fun i => rho.cutTime i ≤ t)
      (Nat.zero_le _) (by simpa [Model.Run.cutTime] using ht)
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  constructor
  · intro hin
    cases hn : n with
    | zero => omega
    | succ k =>
      have hk : k < rho.events.length := by omega
      let f := rho.events[k]
      have hf : rho.events[k]? = some f := List.getElem?_eq_getElem hk
      have hft : f.time ≤ t := by simpa [hn, Model.Run.cutTime, hf] using hnTime
      have hik : i ≤ k := by omega
      rcases hik.lt_or_eq with hik | rfl
      · have horder := keyLe_of_lt S rho hv he hf hik
        have hef : e.time ≤ f.time := by
          rcases horder with h | ⟨h, _⟩
          · exact h.le
          · exact h.le
        exact hef.trans hft
      · rw [he] at hf
        exact (Option.some.inj hf) ▸ hft
  · intro het
    have hle : i + 1 ≤ Nat.findGreatest (fun k => rho.cutTime k ≤ t) rho.events.length :=
      Nat.le_findGreatest (by omega)
      (by simpa [Model.Run.cutTime, he] using het)
    exact hle

/-- The mapped post-event cut is a nonstrict read point at the event time.
Other nodes may still have events at the same time. -/
theorem readPoint_after_event {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hv : rho.ExecutionValid) {i : Nat}
    {e : Model.Event V (Model.protoOf (compiled (goldilocks S)) E).Object}
    (he : rho.events[i]? = some e) :
    Regimes.ReadPoint (simTrace S rho hn) (cutMap S rho hn (i + 1)) e.time := by
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  constructor
  · intro k hk
    have hlen : k < (allCuts S rho hn).length := by
      rw [length_allCuts]
      exact hk.trans_le (cutMap_mono S rho hn (by omega))
    have hl : (simTrace S rho hn).label k ≠ none := by
      rw [simTrace_label, List.getElem?_eq_getElem hlen]
      simp
    obtain ⟨_, j, f, _, hf, hj, _, _, _, ht, _⟩ := simTrace_cut S rho hn hl
    have hji : j ≤ i := by
      by_contra h
      have := cutMap_mono S rho hn (show i + 1 ≤ j by omega)
      omega
    rw [ht]
    rcases hji.lt_or_eq with h | rfl
    · rcases keyLe_of_lt S rho hv hf he h with h | ⟨h, _⟩
      · exact h.le
      · exact h.le
    · rw [he] at hf
      exact (Option.some.inj hf) ▸ le_rfl
  · cases hr : (allCuts S rho hn)[cutMap S rho hn (i + 1)]? with
    | none =>
      rw [(simTrace_of_getElem?_none S rho hn hr).2]
      have := (hv.in_horizon e (List.mem_of_getElem? he)).2
      linarith
    | some r =>
      have hl : (simTrace S rho hn).label (cutMap S rho hn (i + 1)) ≠ none := by
        rw [simTrace_label, hr]; simp
      obtain ⟨_, j, f, _, hf, _, hj, _, _, ht, _⟩ := simTrace_cut S rho hn hl
      have hij : i < j := by
        by_contra h
        have := cutMap_mono S rho hn (show j + 1 ≤ i + 1 by omega)
        omega
      rw [ht]
      rcases keyLe_of_lt S rho hv he hf hij with h | ⟨h, _⟩
      · exact h.le
      · exact h.le

section Clock

variable (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)
  (hn : 1 ≤ Fintype.card V)

/-- A completed local event leaves the stored clock at that event's time, including
deliveries (whose preceding tick is forced by execution validity). -/
theorem now_after_local_event (hv : rho.ExecutionValid) {v : V} {i : Nat}
    {e : Model.Event V (Model.protoOf (compiled (goldilocks S)) E).Object}
    (he : rho.events[i]? = some e) (hev : e.node = v) :
    (stateAt S rho hn v (i + 1)).now = e.time := by
  rw [now_eq_lastClock S rho hn hv]
  cases e with
  | tick w t =>
    simp only [Model.Event.node] at hev
    subst v
    exact lastClock_succ_tick S rho w he
  | restart w t =>
    simp only [Model.Event.node] at hev
    subst v
    exact lastClock_succ_restart S rho w he
  | deliver w o t =>
    simp only [Model.Event.node] at hev
    subst v
    rw [lastClock_succ_deliver S rho w he]
    exact lastClock_of_deliver S rho hv w he

/-- At any cut the reader is still initial, or its state is the post-state of a
complete local event. Other nodes' later events do not move this reader's clock. -/
theorem stateAt_last_local_event (hv : rho.ExecutionValid) (v : V) : ∀ i,
    stateAt S rho hn v i = stateAt S rho hn v 0 ∨
      ∃ j < i, ∃ e, rho.events[j]? = some e ∧ e.node = v ∧
        stateAt S rho hn v i = stateAt S rho hn v (j + 1) ∧
        (stateAt S rho hn v i).now = e.time
  | 0 => Or.inl rfl
  | i + 1 => by
    cases he : rho.events[i]? with
    | none =>
      rw [stateAt_succ_none S rho hn v he]
      rcases stateAt_last_local_event hv v i with h | ⟨j, hj, e, he, hev, hs, ht⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, by omega, e, he, hev, hs, ht⟩
    | some e =>
      by_cases hev : e.node = v
      · exact Or.inr ⟨i, Nat.lt_succ_self i, e, he, hev, rfl,
          now_after_local_event S rho hn hv he hev⟩
      · rw [state_of_other S rho hn v i e he hev]
        rcases stateAt_last_local_event hv v i with h | ⟨j, hj, e, he, hev, hs, ht⟩
        · exact Or.inl h
        · exact Or.inr ⟨j, by omega, e, he, hev, hs, ht⟩

/-- A positive own tick no later than the stored clock has completed, provided
the reader did not restart at that tick's time. Equality uses event phase order. -/
theorem tick_before_stored_clock (hv : rho.ExecutionValid) {v : V} {p i : Nat} {t : Time}
    (he : rho.events[p]? = some (.tick v t)) (ht : 0 < t)
    (hti : t ≤ (stateAt S rho hn v i).now)
    (hnr : ∀ q < i, rho.events[q]? ≠ some (.restart v t)) : p < i := by
  by_contra hpi
  have hip : i ≤ p := by omega
  rcases stateAt_last_local_event S rho hn hv v i with h | ⟨q, hqi, e, hq, hnode, _, htime⟩
  · rw [h, stateAt_eq S rho hn] at hti
    change t ≤ 0 at hti
    linarith
  · have hqp : q < p := by omega
    have horder := keyLe_of_lt S rho hv hq he hqp
    have hte : t ≤ e.time := hti.trans_eq htime
    rcases horder with horder | ⟨heq, hphase⟩
    · exact (not_lt_of_ge hte) horder
    · cases e with
      | tick w u =>
        simp only [Model.Event.node] at hnode
        simp only [Model.Event.time] at heq
        subst w; subst u
        have := index_eq_of_events S rho hv hq he
        omega
      | restart w u =>
        simp only [Model.Event.node] at hnode
        simp only [Model.Event.time] at heq
        subst w; subst u
        exact hnr q hqi hq
      | deliver w o u => simp only [Model.Event.phase] at hphase; omega

/-- A stored clock cannot be ahead of the next engine event. -/
theorem now_le_event (hv : rho.ExecutionValid) (v : V) {i : Nat}
    {e : Model.Event V (Model.protoOf (compiled (goldilocks S)) E).Object}
    (he : rho.events[i]? = some e) : (stateAt S rho hn v i).now ≤ e.time := by
  rcases stateAt_last_local_event S rho hn hv v i with h | ⟨j, hj, f, hf, _, _, ht⟩
  · rw [h, stateAt_eq S rho hn]
    exact (hv.in_horizon e (List.mem_of_getElem? he)).1
  · rw [ht]
    rcases keyLe_of_lt S rho hv hf he hj with h | ⟨h, _⟩
    · exact h.le
    · exact h.le

/-- Restarts, ticks and deliveries never decrease the stored clock. -/
theorem now_mono (hv : rho.ExecutionValid) (v : V) :
    Monotone (fun i => (stateAt S rho hn v i).now) := by
  apply monotone_nat_of_le_succ
  intro i
  cases he : rho.events[i]? with
  | none => rw [stateAt_succ_none S rho hn v he]
  | some e =>
    by_cases hev : e.node = v
    · rw [now_after_local_event S rho hn hv he hev]
      exact now_le_event S rho hn hv v he
    · rw [state_of_other S rho hn v i e he hev]

/-- At a valid event cut the stored clock is between zero and the cut time. -/
theorem now_bounds_cut (hv : rho.ExecutionValid) (v : V) {i : Nat}
    (hi : i ≤ rho.events.length) :
    0 ≤ (stateAt S rho hn v i).now ∧ (stateAt S rho hn v i).now ≤ rho.cutTime
        i := by
  have hmono := now_mono S rho hn hv v (Nat.zero_le i)
  dsimp only at hmono
  rw [stateAt_eq S rho hn v 0] at hmono
  refine ⟨hmono, ?_⟩
  cases i with
  | zero => rw [stateAt_eq S rho hn]; exact le_rfl
  | succ i =>
    have hi' : i < rho.events.length := by omega
    let e := rho.events[i]
    have he : rho.events[i]? = some e := List.getElem?_eq_getElem hi'
    simp only [Model.Run.cutTime, he]
    by_cases hev : e.node = v
    · exact (now_after_local_event S rho hn hv he hev).le
    · rw [state_of_other S rho hn v i e he hev]
      exact now_le_event S rho hn hv v he

/-- Unit-time ticks bound a ready reader's clock lag, even before its tick at
the current cut time. The extra unit of catch-up pays for this lag. -/
theorem stored_now_ge_cutTime_sub_one (hv : rho.ExecutionValid) {v : V} {i : Nat}
    (hi : i ≤ rho.events.length) {c : Time} (hc : 0 ≤ c)
    (hr : rho.point.Ready (c + 1) v (rho.cutTime i)) :
    rho.cutTime i - 1 ≤ (stateAt S rho hn v i).now := by
  obtain ⟨hn0, hnT⟩ := now_bounds_cut S rho hn hv v hi
  have hlag : rho.cutTime i - 1 ≤ (stateAt S rho hn v i).now := by
    by_cases ht : 0 ≤ rho.cutTime i - 1
    · have hth : rho.cutTime i - 1 ≤ rho.horizon := by
        cases i with
        | zero => simp [Model.Run.cutTime] at ht
        | succ i =>
          have hi' : i < rho.events.length := by omega
          have he := List.getElem?_eq_getElem hi'
          have := (hv.in_horizon _ (List.mem_of_getElem? he)).2
          simp only [Model.Run.cutTime, he]
          linarith
      have hw : E.awake v (rho.cutTime i - 1) = true := hr.2 _
        (max_le ht (by linarith)) (by linarith)
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp
        (hv.tick_total v (rho.cutTime i - 1) ht hth
          (fun h => hr.1 (rho.faultyAt_mono
            (sub_le_self _ (by decide : (0 : Int) ≤ 1)) h)) hw)
      have hji : j < i := by
        cases i with
        | zero => simp [Model.Run.cutTime] at ht
        | succ k =>
          have hk : k < rho.events.length := by omega
          have he := List.getElem?_eq_getElem hk
          have htime : rho.cutTime (k + 1) = (rho.events[k]).time := by
            simp [Model.Run.cutTime, he]
          by_contra h
          have hkj : k < j := by omega
          have horder := keyLe_of_lt S rho hv he hj hkj
          change (rho.events[k]).time < rho.cutTime (k + 1) - 1 ∨
            (rho.events[k]).time = rho.cutTime (k + 1) - 1 ∧ _ at horder
          rw [htime] at horder
          rcases horder with horder | ⟨horder, _⟩ <;> linarith
      have hclock := now_after_local_event S rho hn hv (v := v) hj rfl
      have hm := now_mono S rho hn hv v (show j + 1 ≤ i by omega)
      dsimp only at hm
      rw [hclock] at hm
      exact hm
    · linarith
  exact hlag

/-- The extra unit of ready history pays for the stored clock's one-unit lag. -/
theorem ready_at_stored_now (hv : rho.ExecutionValid) {v : V} {i : Nat}
    (hi : i ≤ rho.events.length) {c : Time} (hc : 0 ≤ c)
    (hr : rho.point.Ready (c + 1) v (rho.cutTime i)) :
    rho.point.Ready c v (stateAt S rho hn v i).now := by
  obtain ⟨hn0, hnT⟩ := now_bounds_cut S rho hn hv v hi
  have hlag := stored_now_ge_cutTime_sub_one S rho hn hv hi hc hr
  refine ⟨fun h => hr.1 (rho.faultyAt_mono hnT h),
    fun τ hlo hhi => hr.2 τ ?_ (hhi.trans hnT)⟩
  apply max_le
  · exact (le_max_left _ _).trans hlo
  · have := (le_max_right _ _).trans hlo
    linarith

end Clock

end Consensus.Goldilocks.Obligations

end
