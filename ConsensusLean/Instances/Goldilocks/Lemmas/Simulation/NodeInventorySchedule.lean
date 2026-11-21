module
public import ConsensusLean.Spec.Shape.Run

public section

namespace Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

open Shape

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
variable {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
variable {F : ChainShapeFamily O I} (rho : Model.Run (compiled F) E)

/-- Events in a valid run are sorted by their scheduling key. -/
theorem keyLe_of_lt (hv : rho.ExecutionValid) {j k : Nat}
    {e f : Model.Event V (Model.protoOf (compiled F) E).Object}
    (hj : rho.events[j]? = some e) (hk : rho.events[k]? = some f) (hjk : j < k) :
    e.keyLe f := by
  obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.1 hj
  obtain ⟨hk', rfl⟩ := List.getElem?_eq_some_iff.1 hk
  exact List.pairwise_iff_getElem.1 hv.sorted j k hj' hk' hjk

/-- The last event of `v` before cut `i` is a restart. -/
def LastRestart (v : V) (i : Nat) : Prop :=
  ∃ r < i, ∃ t, rho.events[r]? = some (.restart v t) ∧
    ∀ l, r < l → l < i → ∀ e, rho.events[l]? = some e → e.node ≠ v

omit [DecidableEq V] in
/-- A restart with no later event of this node before the cut. -/
theorem lastRestart_iff (v : V) (i : Nat) : LastRestart rho v i ↔
    ∃ r < i, ∃ t, rho.events[r]? = some (.restart v t) ∧
      ∀ l, r < l → l < i → ∀ e, rho.events[l]? = some e → e.node ≠ v := by
  rfl

omit [DecidableEq V] in
/-- With no event of this node at the cut, its last restart still qualifies at the next cut.
Kept for a downstream consumer. -/
theorem lastRestart_other {v : V} {i : Nat}
    (hev : ∀ ev, rho.events[i]? = some ev → ev.node ≠ v) (h : LastRestart rho v i) :
    LastRestart rho v (i + 1) := by
  obtain ⟨r, hr, t, he, hno⟩ := (lastRestart_iff rho v i).1 h
  refine (lastRestart_iff rho v (i + 1)).2 ⟨r, by omega, t, he, fun l h₁ h₂ ev hl => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 h₂ with h₂ | rfl
  · exact hno l h₁ h₂ ev hl
  · exact hev ev hl

/-- A delivery cannot directly follow a restart of its node: a tick comes in between. -/
theorem not_lastRestart_deliver (hv : rho.ExecutionValid) {i : Nat} {v : V}
    {o : (Model.protoOf (compiled F) E).Object} {t : Time}
    (he : rho.events[i]? = some (.deliver v o t)) : ¬ LastRestart rho v i := by
  rintro ⟨r, hri, t', hr, hno⟩
  have hmr := List.mem_of_getElem? hr
  obtain ⟨_, hw, -⟩ := hv.restart_at_wake v t' hmr
  have hh := hv.in_horizon _ hmr
  obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp
    (hv.tick_total v t' hh.1 hh.2 (hv.honest_only _ hmr) hw)
  have hrq : r < q := by
    rcases lt_trichotomy q r with h | rfl | h
    · rcases keyLe_of_lt rho hv hq hr h with h' | h'
      · exact absurd h' (lt_irrefl _)
      · exact absurd h'.2 (by simp [Model.Event.phase])
    · rw [hr] at hq; cases hq
    · exact h
  have hqi : q < i := by
    rcases lt_trichotomy q i with h | rfl | h
    · exact h
    · rw [he] at hq; cases hq
    · have h1 := keyLe_of_lt rho hv hr he hri
      rcases keyLe_of_lt rho hv he hq h with h' | h'
      · rcases h1 with h1 | h1
        · have a : t' < t := h1
          have b : t < t' := h'
          exact absurd (a.trans b) (lt_irrefl _)
        · have a : t' = t := h1.1
          have b : t < t' := h'
          rw [a] at b
          exact absurd b (lt_irrefl _)
      · exact absurd h'.2 (by simp [Model.Event.phase])
  exact hno q hrq hqi _ hq rfl

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace
