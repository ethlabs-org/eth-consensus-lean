module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.UpTo

public section

namespace Consensus.Goldilocks

namespace Trace

variable {N S L : Type} (tr : Trace N S L) {d : Time}

theorem upTo_label (i : Nat) :
    (tr.upTo d).label i = if tr.time i ≤ d then tr.label i else none := rfl

theorem upTo_time : (tr.upTo d).time = tr.time := rfl

theorem upTo_node : (tr.upTo d).node = tr.node := rfl

theorem upTo_post : (tr.upTo d).post = tr.post := rfl

theorem upTo_awake (y : N) (t : Time) : (tr.upTo d).awake y t ↔ tr.awake y t ∧ t ≤ d := Iff.rfl

/-- A call of the prefix is a call of the run at a time `≤ d`. -/
theorem upTo_callAt {y : N} {i : Nat} {ℓ : L} :
    (tr.upTo d).CallAt y i ℓ ↔ tr.time i ≤ d ∧ tr.CallAt y i ℓ := by
  unfold Trace.CallAt
  rw [upTo_label, upTo_node]
  by_cases h : tr.time i ≤ d <;> simp [h]

/-- At a cut at a time `≤ d`, the prefix has exactly the run's calls. -/
theorem upTo_callAt_of_le {y : N} {i : Nat} {ℓ : L} (h : tr.time i ≤ d) :
    (tr.upTo d).CallAt y i ℓ ↔ tr.CallAt y i ℓ := by
  rw [upTo_callAt]
  exact and_iff_right h

/-- Before a cut whose earlier cuts are all at times `≤ d`, the prefix holds the run's state. -/
theorem upTo_state (y : N) : ∀ {i : Nat}, (∀ k < i, tr.time k ≤ d) →
    (tr.upTo d).state y i = tr.state y i
  | 0, _ => rfl
  | i + 1, h => by
    have hl : (tr.upTo d).label i = tr.label i := by simp [upTo_label, h i (Nat.lt_succ_self i)]
    have ih := upTo_state y (i := i) fun k hk => h k (Nat.lt_succ_of_lt hk)
    simp only [Trace.state]
    rw [hl, ih]
    rfl

/-- Every state of the prefix is a state of the run before a cut whose earlier cuts are all at
times `≤ d` (in a run whose cuts are in time order). -/
theorem upTo_state_exists (hmono : Monotone tr.time) (y : N) :
    ∀ i, ∃ i₀ ≤ i, (∀ k < i₀, tr.time k ≤ d) ∧ (tr.upTo d).state y i = tr.state y i₀
  | 0 => ⟨0, le_rfl, fun _ hk => absurd hk (Nat.not_lt_zero _), rfl⟩
  | i + 1 => by
    obtain ⟨i₀, hi₀, hb, hs⟩ := upTo_state_exists hmono y i
    by_cases hi : tr.time i ≤ d
    · have hb' : ∀ k < i + 1, tr.time k ≤ d := fun k hk => (hmono (Nat.lt_succ_iff.mp hk)).trans hi
      exact ⟨i + 1, le_rfl, hb', upTo_state tr y hb'⟩
    · refine ⟨i₀, hi₀.trans (Nat.le_succ i), hb, ?_⟩
      have hl : (tr.upTo d).label i = none := by simp [upTo_label, hi]
      simp only [Trace.state]
      rw [hl, ← hs]
      simp

theorem upTo_label_eq_some {i : Nat} {ℓ : L} :
    (tr.upTo d).label i = some ℓ ↔ tr.time i ≤ d ∧ tr.label i = some ℓ := by
  rw [upTo_label]
  by_cases h : tr.time i ≤ d <;> simp [h]

end Trace

end Consensus.Goldilocks

end
