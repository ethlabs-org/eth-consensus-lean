module
public import AvailableChainSAPC.Proofs.RunCleanGates

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- Chronological preservation for every event under the cap. Between
scheduled duties, clock changes and PC authority use the existing step. -/
theorem jointClean_event_capped {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (i : Nat) (e : Event V (sapc p).Object) (he : rho.events[i]? = some e)
    (h : JointCleanInvariant p E rho i) : JointCleanInvariant p E rho (i + 1) := by
  set_option backward.isDefEq.respectTransparency false in
  classical
  cases e with
  | deliver v obj t => exact jointClean_delivery_of_sleepy p E rho t₀ hs i v obj t he h
  | tick v t =>
    by_cases early : ∃ r, t = earlyTime p r
    · obtain ⟨r, rfl⟩ := early
      exact jointClean_early_tick_capped p E rho hΔ t₀ hs cap i v r he h
    by_cases head : ∃ r, t = voteTime p r
    · obtain ⟨r, rfl⟩ := head
      exact jointClean_head_tick_capped p E rho hΔ t₀ hs cap i v r he h
    refine jointClean_tick_between_duties p E rho hs.execution i v t he
      (fun r ht => early ⟨r, ht⟩) (fun r ht => head ⟨r, ht⟩) ?_ h ?_
    · intro r ht
      apply early
      refine ⟨r + 1, ht.trans ?_⟩
      change 4 * p.Δ * (r : Time) + 6 * p.Δ =
        4 * p.Δ * ((r + 1 : Nat) : Time) + 2 * p.Δ
      push_cast
      ring
    · intro r c _ _ _ hc
      rw [clock_bestPC] at hc
      exact installedPC_on_cleanRunPath p E rho hs.execution cap i v c hc

/-- The run-sourced joint invariant is proved from Sleepy and the cap.
There is no assumed invariant, source order, or HEAD coverage premise.
The uncapped induction is still needed for the base contract. -/
theorem clean_run_invariant_capped {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho) (i : Nat) (hi : i ≤ rho.events.length) :
    JointCleanInvariant p E rho i := by
  induction i with
  | zero => exact jointClean_initial p E rho
  | succ i ih =>
    have h := ih (Nat.le_of_succ_le hi)
    cases he : rho.events[i]? with
    | none =>
      have hn := List.getElem?_eq_none_iff.mp he
      omega
    | some e => exact jointClean_event_capped p E rho hΔ t₀ hs cap i e he h

/-- Capped clean safety and monotonicity now have no induction premise.
This is a helper for the capped line, not the uncapped base bundle. -/
theorem clean_safety_capped_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho) :
    SafeFrom (sapc p) rho (sapcInterface p).stable t₀ ∧
      SafeFrom (sapc p) rho (sapcInterface p).confirmed t₀ :=
  clean_safety_of_run_invariant p E rho hs.execution.toScheduleWellFormed
    (clean_run_invariant_capped p E rho hΔ t₀ hs cap rho.events.length (le_refl _)) t₀

end AvailableChain.SAPC
end
