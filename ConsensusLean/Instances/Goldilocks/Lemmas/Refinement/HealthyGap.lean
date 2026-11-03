module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.HealthySuppliers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.ProposerGap

public section

/-! # Goldilocks Refinement: the honest-proposer gap of a healthy query (#136, S3)

`hgp_of_healthyQuery`: for a `HealthyPreparationQuery` with nonfinal progress on `[ready, heal]`,
every slot window `[a, a + X)` with `X = Q.index` inside `[s₀, N]` has an actual honest designated
proposal. This is the premise `hgp` of `Healing.FrameWindow.rise_reset` at `G = X`.

The proof uses only the nonfinal `Pattern.single` recurrence (span `0`) from `hp`, with
`recurrence_gap` at start `ready` and stop `heal`. The endpoint is `ts N ≤ heal ≤ horizon`. The
duty gives the proposal through `duty_proposal_run`. The guards `0 < x` and `ts x ≤ horizon`
follow from `hs`, `x ≤ N`, `hN` and `hb`. No reset, frame, coefficient or whole-run progress is
assumed. -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape

variable (S : Setup) (A : AcceptanceAssumptions S) (V : Type) [Fintype V] [DecidableEq V]

/-- **The premise GP of the rise from a healthy query.** Nonfinal progress on `[ready, heal]`,
`heal ≤ horizon`, `max ready 0 + 4Δ ≤ t_{s₀}` and `t_N ≤ heal` give, in every slot window
`[a, a + X)` with `X = Q.index` inside `[s₀, N]`, a slot `x` whose designated proposer is honest
and actually proposes a block of slot `x`. -/
theorem hgp_of_healthyQuery (Q : HealthyPreparationQuery S A V)
    (hb : Q.heal ≤ Q.run.2.horizon)
    (hp : (Sys (family S) V).prog (shapeProgress (family S) V) (K S A)
      Q.cap Q.index Q.ready Q.heal Q.run)
    {s₀ N : Nat} (hs : max Q.ready 0 + 4 * Q.params.Δ ≤ Q.params.ts s₀)
    (hN : Q.params.ts N ≤ Q.heal) :
    ∀ a, s₀ ≤ a → a + (Q.index : Nat) ≤ N + 1 → ∃ x, a ≤ x ∧ x < a + (Q.index : Nat) ∧
      runProposer S Q.run.2 Q.hn x ∈ honestKeys S Q.run.2 ∧
      ∃ k P, Q.trace.ProposesAt (runProposer S Q.run.2 Q.hn x) k P ∧ P.slot = x := by
  sorry

end Consensus.Goldilocks.Refinement

end
