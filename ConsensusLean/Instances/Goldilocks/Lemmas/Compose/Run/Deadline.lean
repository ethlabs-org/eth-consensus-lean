module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Model

public section

/-! # Deadlines after restarts, over any node run trace

The relay deadline `max(τ, w_y) + Δ'` of `RunTrace.deadline` after a node's restarts, for the node
of any `NodeAC`. The run-trace definitions are in `Milestones.Spec.Run`, which no Common or FG
lemma layer may import, so these two lemmas sit in `Compose.Run`; the module holds nothing else,
and the generic healing leaves reach it by an exact exception. -/

namespace Consensus.Goldilocks.Compose

variable {P : Params} {A : NodeAC P} {tr : RunTrace A}

/-- Through the restarts up to cut `c`, the latest wake is at most a bound of those restarts. -/
private theorem lastWake_le {y : Fin P.n} {a : Time} :
    ∀ {c : Nat}, (∀ k ≤ c, tr.RestartAt y k → tr.time k ≤ a) →
      ∀ w : Time, tr.lastWake y c = (w : WithBot Time) → w ≤ a
  | 0, h, w, hw => by
    unfold RunTrace.lastWake at hw
    split_ifs at hw with hr
    · rw [← WithBot.coe_injective hw]; exact h 0 le_rfl hr
    · simp at hw
  | c + 1, h, w, hw => by
    unfold RunTrace.lastWake at hw
    split_ifs at hw with hr
    · rw [← WithBot.coe_injective hw]; exact h _ le_rfl hr
    · exact lastWake_le (fun k hk => h k (hk.trans (Nat.le_succ c))) w hw

/-- With every restart up to cut `c` at or before `a`, the deadline of `τ` is at most
`max(τ, a) + Δ'`. -/
theorem deadline_le_of_restarts {y : Fin P.n} {c : Nat} {a : Time}
    (h : ∀ k ≤ c, tr.RestartAt y k → tr.time k ≤ a) (τ Δ' : Time) :
    tr.deadline y c τ Δ' ≤ max τ a + Δ' := by
  unfold RunTrace.deadline
  rcases hw : tr.lastWake y c with _ | w
  · change τ + Δ' ≤ max τ a + Δ'
    exact add_le_add (le_max_left τ a) le_rfl
  · change max τ w + Δ' ≤ max τ a + Δ'
    exact add_le_add (max_le_max (le_refl τ) (lastWake_le h w hw)) le_rfl

end Consensus.Goldilocks.Compose
