module
public import AvailableChainSAPC.Proofs.ProposalHeads
public import AvailableChainSAPC.Proofs.CleanService

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- Honest awake proposals have common exact HEAD choices before their
own gate. The predecessor's gate bound follows from that deadline. -/
theorem clean_proposal_choices_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (r : Slot) (ht : t₀ < proposalTime p r) (hp : HonestAwakeProposer E rho r)
    (hh : gateTime p r ≤ rho.horizon) :
    ∃ b, HonestProposalAt E (sapcInterface p).toInterface rho r b ∧
      ∀ v ∈ rho.honest, (headData p rho r v).target = b := by
  have positive : 0 < r := by
    by_contra hn
    have hz : r = 0 := Nat.eq_zero_of_not_pos hn
    simp [hz, hs.start_zero, proposalTime, GridCO.proposalTime] at ht
  have proposalBound : proposalTime p r ≤ rho.horizon := by
    apply le_trans _ hh
    change 4 * p.Δ * (r : Time) ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
    linarith [p.deltaPos]
  obtain ⟨b, hb⟩ := honest_proposal_exists hs.execution hΔ r positive hp proposalBound
  refine ⟨b, hb, ?_⟩
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  exact clean_honest_proposal_head p E rho hΔ t₀ hs s
    (((GridCO.gateTime_le_iff p.engine s (s + 1)).mpr (Nat.le_succ s)).trans hh) b hb

/-- Plain Sleepy gives both base inclusion claims in 6Δ, for all a<h.
The proved run invariant supplies both guards at the raw proposal gate. -/
theorem included_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀) :
    IncludedFrom (sapc p) E (sapcInterface p).toInterface rho (sapcInterface p).stable
      t₀ (6 * p.Δ) ∧
    IncludedFrom (sapc p) E (sapcInterface p).toInterface rho (sapcInterface p).confirmed
      t₀ (6 * p.Δ) :=
  clean_inclusion_of_run_invariant_and_heads p E rho hΔ t₀ hs
    (clean_run_invariant p E rho hΔ t₀ hs rho.events.length (le_refl _))
    (clean_proposal_choices_from_engine p E rho hΔ t₀ hs)

/-- The stable inclusion field follows with the declared SA-PC delay. -/
theorem stable_included_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G t₀ : Time)
    (hs : StableSleepyRegime (sapc p) E (sapcInterface p).toInterface (sapcConstants p G) rho t₀) :
    IncludedFrom (sapc p) E (sapcInterface p).toInterface rho (sapcInterface p).stable
      t₀ (sapcConstants p G).D_s :=
  (included_from_engine p E rho hΔ t₀ hs.toSleepyRegime).1

/-- Fast inclusion has the same 6Δ delay and needs no extra proof premise. -/
theorem fast_included_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (G t₀ : Time) (hs : FastRegime (sapc p) E (sapcInterface p).toInterface rho t₀) :
    IncludedFrom (sapc p) E (sapcInterface p).toInterface rho (sapcInterface p).stable
      t₀ (sapcConstants p G).D_f :=
  (included_from_engine p E rho hΔ t₀ hs.toSleepyRegime).1

end AvailableChain.SAPC
end
