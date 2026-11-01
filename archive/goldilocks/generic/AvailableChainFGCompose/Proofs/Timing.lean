module
public import AvailableChainFGCompose.Statements.Timing
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith -- shake: keep (re-export)

public section

namespace AvailableChain.FGCompose

/-- The action reads the next label's early clock. -/
theorem action_eq_early_next (T : FGTiming) (hT : FGTimingLaws T) (q : Nat) :
    T.action q = T.early (q * T.roundSlots + 1) := by
  rw [hT.action_eq, hT.gate_eq, hT.early_eq, hT.proposal_eq, hT.proposal_eq]
  push_cast
  ring

/-- The finality HEAD uses label qR+1, with the original horizon and delta equality. -/
theorem finality_action_time_bounds (T : FGTiming) (hT : FGTimingLaws T)
    (r q : Nat) (hrq : r ≤ q) (G Δ horizon : Time)
    (hGST : G ≤ T.proposal (r * T.roundSlots)) (hΔ : Δ = T.delta)
    (hhor : T.action q ≤ horizon) :
    G ≤ T.vote (q * T.roundSlots + 1) ∧
      T.vote (q * T.roundSlots + 1) + Δ ≤ T.early (q * T.roundSlots + 1) ∧
      T.early (q * T.roundSlots + 1) ≤ horizon ∧
      T.vote (q * T.roundSlots + 1) ≤ horizon := by
  have heh : T.early (q * T.roundSlots + 1) ≤ horizon :=
    (action_eq_early_next T hT q) ▸ hhor
  have hvte : T.vote (q * T.roundSlots + 1) + Δ ≤
      T.early (q * T.roundSlots + 1) := by
    rw [hT.vote_eq, hT.early_eq, hΔ]
    linarith
  have hd := hT.delta_pos
  refine ⟨hGST.trans ?_, hvte, heh, ?_⟩
  · have hs : r * T.roundSlots ≤ q * T.roundSlots + 1 :=
      (Nat.mul_le_mul_right T.roundSlots hrq).trans (Nat.le_succ _)
    have hcast : ((r * T.roundSlots : Nat) : Time) ≤
        ((q * T.roundSlots + 1 : Nat) : Time) := by exact_mod_cast hs
    rw [hT.vote_eq, hT.proposal_eq, hT.proposal_eq]
    nlinarith
  · rw [hΔ] at hvte
    linarith

end AvailableChain.FGCompose
end
