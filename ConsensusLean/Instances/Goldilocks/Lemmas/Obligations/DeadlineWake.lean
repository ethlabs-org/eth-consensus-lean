module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Model
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks run traces: the wake behind a delivery deadline

The delivery deadline of a recipient `y` at a cut `j` is `max(τ, w) + Δ`, with `w` the time of
`y`'s latest restart at a cut `≤ j` (`RunTrace.deadline`). Two facts about it read the trace and
the restart laws of `y` only, so constant and growing faults use them alike:

* `RunTrace.deadline_awake_of_call`: when `y` is called at `j`, it is awake from the deadline's
  start `max(τ, w)` through the call, given the restart laws of `y` up to the call;
* `RunTrace.deadline_mono_cut_of_time_mono`: with monotone cut times, a later cut has a later
  deadline. -/

namespace Consensus.Goldilocks.RunTrace

variable {P : Params} {A : NodeAC P} (tr : RunTrace A)

/-- **A recipient is awake from its deadline start through its call.** Premises, for `y` and its
call `j`: the cut times are monotone (`hmono`); `y` is awake at the call (`hwj`); a sleep of `y`
before an awake call time ends at a restart in between (`hwake`, the law `restart_at_wake` at the
call time); a restart of `y` at or before the call's time follows a sleep after all of `y`'s
earlier calls (`hsleep`, the law `sleep_of_restart`). Then the deadline at `j` is `a + Δ` for a
start `a ≥ τ` with `y` awake on `[a, t_j]`. -/
theorem deadline_awake_of_call (hmono : Monotone tr.time) {y : Fin P.n} {j : Nat}
    (hj : tr.IsCall y j) (hwj : tr.awake y (tr.time j))
    (hwake : ∀ u, 0 ≤ u → u < tr.time j → ¬ tr.awake y u → tr.awake y (tr.time j) →
      ∃ k, tr.RestartAt y k ∧ u < tr.time k ∧ tr.time k ≤ tr.time j)
    (hsleep : ∀ k, tr.RestartAt y k → tr.time k ≤ tr.time j →
      ∃ u : Time, 0 ≤ u ∧ u < tr.time k ∧ ¬ tr.awake y u ∧
        ∀ i < k, tr.IsCall y i → tr.time i < u)
    {τ : Time} (hτ : 0 ≤ τ) (Δ : Time) :
    ∃ a, τ ≤ a ∧ tr.deadline y j τ Δ = a + Δ ∧ ∀ u, a ≤ u → u ≤ tr.time j → tr.awake y u := by
  let a := Option.elim (tr.lastWake y j) τ (fun w => max τ w)
  have hτa : τ ≤ a := by
    dsimp [a]
    cases tr.lastWake y j with
    | bot => exact le_rfl
    | coe w => exact le_max_left _ _
  have hrestart : ∀ k ≤ j, tr.RestartAt y k → tr.time k ≤ a := by
    have hmax : ∀ c, ∀ k ≤ c, tr.RestartAt y k →
        (tr.time k : WithBot Time) ≤ tr.lastWake y c := by
      intro c
      induction c with
      | zero =>
        intro k hk hk'
        obtain rfl : k = 0 := by omega
        simp [RunTrace.lastWake, hk']
      | succ c ih =>
        intro k hk hk'
        by_cases hc : tr.RestartAt y (c + 1)
        · simp only [RunTrace.lastWake, hc, ite_true]
          exact WithBot.coe_le_coe.mpr (hmono hk)
        · have hk0 : k ≤ c := by
            by_contra h
            obtain rfl : k = c + 1 := by omega
            exact hc hk'
          simpa only [RunTrace.lastWake, hc, ite_false] using ih k hk0 hk'
    intro k hk hk'
    have hm := hmax j k hk hk'
    dsimp [a]
    cases hw : tr.lastWake y j with
    | bot => rw [hw] at hm; exact (WithBot.not_coe_le_bot _ hm).elim
    | coe w =>
      rw [hw] at hm
      exact (WithBot.coe_le_coe.mp hm).trans (le_max_right _ _)
  refine ⟨a, hτa, rfl, fun u hau huj => ?_⟩
  have hu0 : 0 ≤ u := hτ.trans (hτa.trans hau)
  by_contra hsu
  have huj' : u < tr.time j := lt_of_le_of_ne huj fun heq => hsu (heq ▸ hwj)
  obtain ⟨k, hk, huk, hkj⟩ := hwake u hu0 huj' hsu hwj
  have hkidx : k ≤ j := by
    by_contra h
    obtain ⟨v, _, hvk, _, hvprev⟩ := hsleep k hk hkj
    have := hvprev j (by omega) hj
    linarith only [this, hvk, hkj]
  have := hrestart k hkidx hk
  linarith only [this, huk, hau]

/-- **Later observation cuts can only increase a recipient's deadline**, when the cut times are
monotone. -/
theorem deadline_mono_cut_of_time_mono (hmono : Monotone tr.time) (y : Fin P.n) (τ Δ : Time) :
    Monotone (fun j => tr.deadline y j τ Δ) := by
  have hw : ∀ c (w : Time), tr.lastWake y c = (w : WithBot Time) → w ≤ tr.time c := by
    intro c
    induction c with
    | zero =>
      intro w h
      unfold RunTrace.lastWake at h
      split at h
      · exact (WithBot.coe_injective h).ge
      · cases h
    | succ c ih =>
      intro w h
      unfold RunTrace.lastWake at h
      split at h
      · exact (WithBot.coe_injective h).ge
      · exact (ih w h).trans (hmono (Nat.le_succ c))
  apply monotone_nat_of_le_succ
  intro c
  change tr.deadline y c τ Δ ≤ tr.deadline y (c + 1) τ Δ
  unfold RunTrace.deadline
  rw [RunTrace.lastWake]
  split
  · cases heq : tr.lastWake y c with
    | bot =>
      change τ + Δ ≤ max τ (tr.time (c + 1)) + Δ
      have := le_max_left τ (tr.time (c + 1))
      dsimp [Time] at *
      omega
    | coe w =>
      change max τ w + Δ ≤ max τ (tr.time (c + 1)) + Δ
      have hle : w ≤ tr.time (c + 1) := (hw c w heq).trans (hmono (Nat.le_succ c))
      simp only [Time] at hle ⊢
      omega
  · exact le_rfl

end Consensus.Goldilocks.RunTrace

end
