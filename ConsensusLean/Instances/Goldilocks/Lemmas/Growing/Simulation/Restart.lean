module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Events

public section

/-! # Restarts while honesty is time-indexed

The wake required by validity precedes the observation where the node is honest.
Monotonic compromise therefore supplies precisely the honesty needed at that wake.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Shape
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

private theorem restart_at {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.restart v t)) :
    (simTrace S rho hn).RestartAt (rho.ownKey v) (cutMap S rho hn i) ∧
      (simTrace S rho hn).time (cutMap S rho hn i) = t ∧
      cutMap S rho hn (i + 1) = cutMap S rho hn i + 1 := by
  obtain ⟨hsucc, r, hr, hn', ht, ℓ, hl, hc⟩ := restart_getElem? S rho hn he
  refine ⟨⟨ℓ, ⟨?_, ?_⟩, hc⟩, ?_, hsucc⟩
  · rw [simTrace_node, hr]; exact hn'
  · rw [simTrace_label, hr, Option.map_some, hl]
  · rw [simTrace_time, hr]; exact ht

private theorem exists_wake (f : Time → Bool) {u t : Time} (hu : f u = false) (ht : f t = true)
    (h : u ≤ t) : ∃ w, u < w ∧ w ≤ t ∧ f w = true ∧ f (w - 1) = false := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, t = u + n := ⟨(t - u).toNat, by unfold Time at *; omega⟩
  clear h
  induction n with
  | zero => simp [hu] at ht
  | succ n ih =>
    by_cases hft : f (u + n) = true
    · obtain ⟨w, h1, h2, h3⟩ := ih hft
      exact ⟨w, h1, by push_cast at h2 ⊢; linarith only [h2], h3⟩
    · refine ⟨u + (n + 1 : Nat), by push_cast; linarith only [Int.natCast_nonneg n], le_rfl, ht,
        ?_⟩
      have : u + ((n + 1 : Nat) : Int) - 1 = u + n := by push_cast; ring
      rw [this]
      simpa using hft

/-- A node honest at the later awake time has restarted since an earlier sleep. -/
theorem simTraceAt_restart_at_wake (hv : rho.ExecutionValid) :
    ∀ y (u v : Time), y ∈ honestKeysAt S rho v → 0 ≤ u → u < v →
      ¬ (simTraceAt S rho hn).awake y u → (simTraceAt S rho hn).awake y v →
        ∃ k, (simTraceAt S rho hn).RestartAt y k ∧ u < (simTraceAt S rho hn).time k ∧
          (simTraceAt S rho hn).time k ≤ v := by
  intro y u v hy hu0 huv hsu hav
  obtain ⟨hwv, -, hvh⟩ := (simTraceAt_awake_bounds S rho hn y v).mp hav
  have hwu : E.awake (rho.key y) u = false := by
    by_contra h
    exact hsu ((simTraceAt_awake_bounds S rho hn y u).mpr
      ⟨by simpa using h, hu0, huv.le.trans hvh⟩)
  obtain ⟨w, huw, hwv', hw1, hw2⟩ := exists_wake _ hwu hwv huv.le
  have hhon : rho.key y ∉ rho.faultyAt w := by
    rw [mem_honestKeysAt_iff, min_eq_left hvh] at hy
    exact fun hf => hy (rho.faultyAt_mono hwv' hf)
  obtain ⟨ir, hir⟩ := List.mem_iff_getElem?.mp
    (hv.wake_restart _ w (by linarith only [hu0, huw])
      (hwv'.trans hvh) hhon ⟨hw1, hw2⟩)
  obtain ⟨hR, ht, -⟩ := restart_at S rho hn hir
  rw [ownKey_key] at hR
  rw [simTraceAt_eq]
  exact ⟨_, hR, by rw [ht]; exact huw, by rw [ht]; exact hwv'⟩

/-- The first call after a sleep is the restart required at the intervening wake. -/
theorem simTraceAt_restart_of_sleep (hv : rho.ExecutionValid) :
    ∀ y i (u : Time), y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i) →
      (simTraceAt S rho hn).IsCall y i → 0 ≤ u →
      u < (simTraceAt S rho hn).time i → ¬ (simTraceAt S rho hn).awake y u →
      (∀ j < i, (simTraceAt S rho hn).IsCall y j → (simTraceAt S rho hn).time j < u) →
        (simTraceAt S rho hn).RestartAt y i := by
  intro y i u hy hc hu0 hut hsleep hprev
  obtain ⟨k, hr, huk, hki⟩ := simTraceAt_restart_at_wake S rho hn hv y u _ hy hu0 hut
    hsleep (simTraceAt_awake_of_call S rho hn hv hc)
  have hik : i ≤ k := by
    by_contra h
    have := hprev k (by omega) ⟨_, hr.choose_spec.1⟩
    exact (not_lt_of_ge huk.le) this
  obtain ⟨c, hnode, hlab⟩ := hc
  obtain ⟨ℓ, ⟨hnode', hlab'⟩, hcall⟩ := hr
  rw [simTraceAt_eq] at hnode hlab hnode' hlab' hki
  obtain ⟨-, i₀, ev, -, he, h1, h2, -, hn', ht, -⟩ :=
    simTrace_cut S rho hn (by rw [hlab]; simp)
  obtain ⟨r, ir, evr, -, her, h1r, h2r, hidx, hnr, htr, -, hlr⟩ :=
    simTrace_cut S rho hn (by rw [hlab']; simp)
  have hrl : r.label = .ac ℓ := Option.some.inj (hlr.symm.trans hlab')
  obtain ⟨v, t, rfl⟩ :=
    restart_of_mem_eventCuts S rho hn her (List.mem_of_getElem? hidx) hrl hcall
  have hir₀ : ir = i₀ := by
    rcases lt_trichotomy ir i₀ with h | h | h
    · have := cutMap_mono S rho hn (show ir + 1 ≤ i₀ from h)
      omega
    · exact h
    · rcases keyLe_of_lt S rho hv he her h with h' | ⟨h', h''⟩
      · rw [ht, htr] at hki
        exact absurd hki (not_le.mpr h')
      · have hkey : ev.node = v := by
          apply rho.key.symm.injective
          exact (hn'.symm.trans hnode).trans (hnr.symm.trans hnode').symm
        cases ev with
        | restart v' s =>
          simp only [Model.Event.node, Model.Event.time] at hkey h'
          subst hkey h'
          exact absurd (index_eq_of_events S rho hv he her) (by omega)
        | tick => simp [Model.Event.phase] at h''
        | deliver => simp [Model.Event.phase] at h''
  subst hir₀
  obtain ⟨-, -, hsucc⟩ := restart_at S rho hn her
  have : i = k := by omega
  subst this
  rw [simTraceAt_eq]
  exact ⟨ℓ, ⟨hnode', hlab'⟩, hcall⟩

/-- An observed restart has the same preceding sleep as in the canonical static trace.
Only node-local history is used; honesty at the restart implies honesty at zero. -/
theorem simTraceAt_sleep_of_restart (hv : rho.ExecutionValid) :
    ∀ y i, y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i) →
      (simTraceAt S rho hn).RestartAt y i →
      ∃ u : Time, 0 ≤ u ∧ u < (simTraceAt S rho hn).time i ∧
        ¬ (simTraceAt S rho hn).awake y u ∧
        ∀ j < i, (simTraceAt S rho hn).IsCall y j → (simTraceAt S rho hn).time j < u := by
  intro y i hy hr
  have hy0 : y ∈ honestKeys S rho := by
    rw [mem_honestKeys_iff]
    rw [mem_honestKeysAt_iff] at hy
    exact fun hf => hy (rho.faultyAt_mono
      (le_min (simTraceAt_time_nonneg S rho hn hv i) hv.horizon_nonneg) hf)
  rw [simTraceAt_eq] at hr ⊢
  exact simTrace_sleep_of_restart S rho hn hv y hy0 i hr

end Consensus.Goldilocks.Simulation
