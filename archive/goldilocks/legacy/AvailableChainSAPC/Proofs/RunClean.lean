module
public import AvailableChainSAPC.Proofs.RunCleanActivePath
public import AvailableChainSAPC.Proofs.RunCleanDisabledGates
public import AvailableChainSAPC.Proofs.RunCleanCapped

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- Source comparison permits the HEAD step to add a new PC authority.
Genuine continuation uses compatibility with that authority, while finite
roots and all previous history remain on the input path. -/
theorem jointClean_head_tick_of_chain {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (i : Nat) (reader : V) (r : Slot)
    (he : rho.events[i]? = some (.tick reader (voteTime p r)))
    (h : JointCleanInvariant p E rho i)
    (chain : CleanPath (cleanRunPath p rho (i + 1))) :
    JointCleanInvariant p E rho (i + 1) := by
  have oldGate (j : Nat) (hj : j < i + 1) (v : V) (s : Slot)
      (tick : rho.events[j]? = some (.tick v (gateTime p s))) : j < i := by
    have ne : j ≠ i := by
      rintro rfl
      exact voteTime_ne_gateTime p r s
        (congrArg Event.time (Option.some.inj (he.symm.trans tick)))
    omega
  constructor
  · apply cleanPathFacts_of_chain_and_transfer p E rho hs.execution
      (sleepy_quorum_above_faults p E rho t₀ hs) (i + 1) chain
    intro j hj v hv s b tick raw k hk w hw label hsl head
    have hji := oldGate j hj v s tick
    by_cases hki : k < i
    · exact h.facts.transferred j hji v hv s b tick raw k hki w hw label hsl head
    have eq : k = i := by omega
    subst k
    have node := congrArg Event.node (Option.some.inj (he.symm.trans head))
    change reader = w at node
    subst w
    have time := congrArg Event.time (Option.some.inj (he.symm.trans head))
    have labelEq : r = label := by
      have cast : (r : Time) = label := by
        change 4 * p.Δ * (r : Time) + p.Δ = 4 * p.Δ * (label : Time) + p.Δ at time
        nlinarith [p.deltaPos]
      exact_mod_cast cast
    subst label
    cases r with
    | zero => exact (Nat.not_lt_zero s hsl).elim
    | succ r =>
      have cover := genuine_head_continuation_of_compatible_authority p E rho hΔ t₀ hs
        i reader hw r he h (by
          intro active cert selected a ha
          rw [headState,
            ← stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed he]
            at active selected
          exact chain.comparable cert.target a
            (Or.inr ⟨cert.target, .head i (Nat.lt_succ_self i) reader hw (r + 1)
              cert he active selected, GridCO.block_preceq_self _⟩)
            (cleanRunPath_mono p rho (Nat.le_succ i) ha)) j hji v hv s b tick raw
      rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed he]
      exact cover
  · apply h.ordered.step_of_no_gate
    intro v s tick
    exact voteTime_ne_gateTime p r s
      (congrArg Event.time (Option.some.inj (he.symm.trans tick)))

/-- Between HEAD and gate duties, source comparison suffices for all
historical facts. This includes a new active proposal authority. -/
theorem jointClean_between_tick_of_chain {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (ha : (faulty rho).card < pcQuorum p)
    (i : Nat) (reader : V) (t : Time)
    (he : rho.events[i]? = some (.tick reader t))
    (noHead : ∀ r, t ≠ voteTime p r) (noGate : ∀ r, t ≠ gateTime p r)
    (h : JointCleanInvariant p E rho i)
    (chain : CleanPath (cleanRunPath p rho (i + 1))) :
    JointCleanInvariant p E rho (i + 1) := by
  have old (j : Nat) (hj : j < i + 1) (v : V) (u : Time)
      (tick : rho.events[j]? = some (.tick v u)) (ne : t ≠ u) : j < i := by
    have hne : j ≠ i := by
      rintro rfl
      exact ne (congrArg Event.time (Option.some.inj (he.symm.trans tick)))
    omega
  constructor
  · apply cleanPathFacts_of_chain_and_transfer p E rho hx ha (i + 1) chain
    intro j hj v hv r b tick raw k hk w hw s hrs head
    exact h.facts.transferred j (old j hj v _ tick (noGate r)) v hv r b tick raw
      k (old k hk w _ head (noHead s)) w hw s hrs head
  · apply h.ordered.step_of_no_gate
    intro v s tick
    exact noGate s (congrArg Event.time (Option.some.inj (he.symm.trans tick)))

/-- Uncapped chronological preservation. Cap changes retain the input
invariant. Disabled duties use SA transfer; active duties compare their
actual PC sources through successful timely transfer. -/
theorem jointClean_event {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (i : Nat) (e : Event V (sapc p).Object) (he : rho.events[i]? = some e)
    (h : JointCleanInvariant p E rho i) : JointCleanInvariant p E rho (i + 1) := by
  classical
  by_cases cap : FaultBound (sapc p) (pcFaultCap p) rho
  · exact jointClean_event_capped p E rho hΔ t₀ hs cap i e he h
  cases e with
  | deliver v obj t => exact jointClean_delivery_of_sleepy p E rho t₀ hs i v obj t he h
  | tick v t =>
    have activeChain (active : capBroken p (Run.stateBefore (sapc p) rho i v) = false) :
        CleanPath (cleanRunPath p rho (i + 1)) :=
      cleanRunPath_chain_at_active_tick p E rho hΔ t₀ hs cap i v t he h active
    by_cases early : ∃ r, t = earlyTime p r
    · obtain ⟨r, rfl⟩ := early
      cases mode : capBroken p (Run.stateBefore (sapc p) rho i v) with
      | false =>
        exact jointClean_early_tick_of_chain p E rho hΔ t₀ hs i v r he h
          (activeChain mode)
      | true => exact jointClean_early_tick_disabled p E rho hΔ t₀ hs i v r he h mode
    by_cases head : ∃ r, t = voteTime p r
    · obtain ⟨r, rfl⟩ := head
      cases mode : capBroken p (Run.stateBefore (sapc p) rho i v) with
      | false =>
        exact jointClean_head_tick_of_chain p E rho hΔ t₀ hs i v r he h
          (activeChain mode)
      | true => exact jointClean_head_tick_disabled p E rho hΔ t₀ hs i v r he h mode
    have noGate (r : Slot) : t ≠ gateTime p r := by
      intro eq
      apply early
      refine ⟨r + 1, eq.trans ?_⟩
      change 4 * p.Δ * (r : Time) + 6 * p.Δ =
        4 * p.Δ * ((r + 1 : Nat) : Time) + 2 * p.Δ
      push_cast
      ring
    cases mode : capBroken p (Run.stateBefore (sapc p) rho i v) with
    | false =>
      exact jointClean_between_tick_of_chain p E rho hs.execution
        (sleepy_quorum_above_faults p E rho t₀ hs) i v t he
        (fun r ht => head ⟨r, ht⟩) noGate h (activeChain mode)
    | true =>
      exact jointClean_tick_between_duties_disabled p E rho hs.execution i v t he
        (fun r ht => early ⟨r, ht⟩) (fun r ht => head ⟨r, ht⟩) noGate h mode

/-- The joint clean invariant holds for every event prefix from plain
Sleepy. The fault cap is not a premise of this base result. -/
theorem clean_run_invariant {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (i : Nat) (hi : i ≤ rho.events.length) : JointCleanInvariant p E rho i := by
  induction i with
  | zero => exact jointClean_initial p E rho
  | succ i ih =>
    have h := ih (Nat.le_of_succ_le hi)
    cases he : rho.events[i]? with
    | none =>
      have hn := List.getElem?_eq_none_iff.mp he
      omega
    | some e => exact jointClean_event p E rho hΔ t₀ hs i e he h

/-- Both base outputs are safe and monotone under plain Sleepy, for
all fault counts allowed by that regime. -/
theorem clean_safety_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀) :
    SafeFrom (sapc p) rho (sapcInterface p).stable t₀ ∧
      SafeFrom (sapc p) rho (sapcInterface p).confirmed t₀ :=
  clean_safety_of_run_invariant p E rho hs.execution.toScheduleWellFormed
    (clean_run_invariant p E rho hΔ t₀ hs rho.events.length (le_refl _)) t₀

end AvailableChain.SAPC
end
