module
public import AvailableChainSAPC.Proofs.CleanPCPath
public import AvailableChainSAPC.Proofs.Preservation

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- At a HEAD, the finite root is still on the input path. The clock
can expire or release rows, but it cannot create a row at this phase. -/
theorem headRoot_on_cleanRunPath {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (i : Nat) (reader : V)
    (hr : reader ∈ rho.honest) (r : Slot)
    (h : JointCleanInvariant p E rho i) :
    cleanRunPath p rho i (GridCO.liveRoot
      (clock p (Run.stateBefore (sapc p) rho i reader) (voteTime p r)).base) := by
  set_option backward.isDefEq.respectTransparency false in
  apply CleanStateOnPath.liveRoot h.facts.chain
  rw [clock_eq_preGate_of_no_gate p _ _ (voteTime_ne_gateTime p r)]
  exact (clockPreGate_clean p _ _ (h.facts.states i (le_refl _) reader hr)).1

/-- The capped timely-N transfer now has its finite-root premise from
the run invariant. It needs only the next HEAD in the horizon, including
a last incomplete label with no following gate. -/
theorem timely_nextHead_of_run_invariant {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (i : Nat) (reader : V) (hr : reader ∈ rho.honest) (r : Slot)
    (he : rho.events[i]? = some (.tick reader (voteTime p (r + 1))))
    (h : JointCleanInvariant p E rho i) (b : Block)
    (source : HonestTimelySource p rho i r b) :
    Block.Preceq b (headData p rho (r + 1) reader).target := by
  set_option backward.isDefEq.respectTransparency false in
  have hb : cleanRunPath p rho i b :=
    Or.inr ⟨b, .timely r b cap source, GridCO.block_preceq_self b⟩
  obtain ⟨v, hv, j, _, _, saved⟩ := source
  have root := headRoot_on_cleanRunPath p E rho i reader hr (r + 1) h
  rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed he] at root
  have ha : capBroken p (headState p rho (r + 1) reader) = false := by
    rw [headState, capBroken_clock]
    exact capBroken_false_beforeTime p E rho hs.execution cap reader _
  have hsync : E.t_GST ≤ earlyTime p r := by
    rw [hs.gst_zero]
    change 0 ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  exact synchronous_timely_active_head_covers p E rho hs.execution hΔ hs.acceptedRelay r hsync
    v reader hv hr (hs.execution.in_horizon _ (List.mem_of_getElem? he)).2 b
    (savedTimely_candidate_at_early p E rho hs.execution.toScheduleWellFormed (j + 1) v r b saved)
    ha (h.facts.chain.comparable _ _ root hb)

/-- Earlier genuine results continue through active or disabled HEADs.
Only active PC authority needs a path premise. Finite roots come from
the retained invariant, including at the first disabled duty. -/
theorem genuine_head_continuation_of_compatible_authority {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (i : Nat) (reader : V) (hr : reader ∈ rho.honest) (s : Slot)
    (he : rho.events[i]? = some (.tick reader (voteTime p (s + 1))))
    (h : JointCleanInvariant p E rho i)
    (authority : capBroken p (headState p rho (s + 1) reader) = false →
      ∀ cert, selectedPC p (headState p rho (s + 1) reader) (s + 1) = some cert →
        ∀ b, cleanRunPath p rho i b → Block.Compatible cert.target b)
    (j : Nat) (hj : j < i) (v : V) (hv : v ∈ rho.honest) (r : Slot) (b : Block)
    (ht : rho.events[j]? = some (.tick v (gateTime p r)))
    (raw : SA.confirmation p (Run.stateBefore (sapc p) rho j v).base r = some b) :
    Block.Preceq b (headData p rho (s + 1) reader).target := by
  have htime : gateTime p r ≤ voteTime p (s + 1) := by
    by_contra hn
    have := eventIndex_lt_of_time_lt hs.execution.toScheduleWellFormed he ht (lt_of_not_ge hn)
    omega
  have hrs : r < s := by
    by_contra hn
    have hle : (s : Time) ≤ r := by exact_mod_cast le_of_not_gt hn
    change 4 * p.Δ * (r : Time) + 6 * p.Δ ≤
      4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ at htime
    push_cast at htime
    nlinarith [p.deltaPos]
  have hhead : voteTime p s < voteTime p (s + 1) := by
    change 4 * p.Δ * (s : Time) + p.Δ < 4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ
    push_cast
    linarith [p.deltaPos]
  have hnow := (hs.execution.in_horizon _ (List.mem_of_getElem? he)).2
  have coverage (w : V) (hw : w ∈ rho.honest) :
      Block.Preceq b (headData p rho s w).target := by
    have hpub : PublicTime E (voteTime p s) := by
      refine ⟨4 * s + 1, ?_⟩
      change 4 * p.Δ * (s : Time) + p.Δ = _
      rw [hΔ]
      push_cast
      ring
    have hn : 0 ≤ voteTime p s := by
      change 0 ≤ 4 * p.Δ * (s : Time) + p.Δ
      nlinarith [p.deltaPos, Int.natCast_nonneg s]
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp
      (hs.execution.tick_total w hw _ hpub hn (hhead.le.trans hnow))
    have hki := eventIndex_lt_of_time_lt hs.execution.toScheduleWellFormed hk he hhead
    have cover := h.facts.transferred j hj v hv r b ht raw k hki w hw s hrs hk
    rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed hk] at cover
    exact cover
  have hearly : earlyTime p s ≤ rho.horizon := by
    apply le_trans _ hnow
    change 4 * p.Δ * (s : Time) + 2 * p.Δ ≤
      4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ
    push_cast
    linarith [p.deltaPos]
  obtain ⟨c, hc, hbc⟩ := sleepy_preserve_from_heads p E rho hΔ t₀ hs s hearly b coverage reader hr
  have hb := h.facts.genuine j hj v hv r b ht raw
  have root := headRoot_on_cleanRunPath p E rho i reader hr (s + 1) h
  rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed he] at root
  have hsync : E.t_GST ≤ earlyTime p s := by
    rw [hs.gst_zero]
    change 0 ≤ 4 * p.Δ * (s : Time) + 2 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg s]
  have hf : freezeTime p s ≤ rho.horizon := by
    apply le_trans _ hnow
    change 4 * p.Δ * (s : Time) + 3 * p.Δ ≤
      4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ
    push_cast
    linarith [p.deltaPos]
  apply synchronous_local_genuine_activePC_head_covers p E rho hs.execution hΔ hs.acceptedRelay
    s hsync hf reader hr b c hc hbc (h.facts.chain.comparable _ _ root hb)
  intro active cert selected
  exact authority active cert selected b hb

/-- Earlier genuine results continue through active or disabled HEADs.
Only active PC authority needs a path premise. Finite roots come from
the retained invariant, including at the first disabled duty. -/
theorem genuine_head_continuation_of_active_authority {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (i : Nat) (reader : V) (hr : reader ∈ rho.honest) (s : Slot)
    (he : rho.events[i]? = some (.tick reader (voteTime p (s + 1))))
    (h : JointCleanInvariant p E rho i)
    (authority : capBroken p (headState p rho (s + 1) reader) = false →
      ∀ cert, selectedPC p (headState p rho (s + 1) reader) (s + 1) = some cert →
        cleanRunPath p rho i cert.target)
    (j : Nat) (hj : j < i) (v : V) (hv : v ∈ rho.honest) (r : Slot) (b : Block)
    (ht : rho.events[j]? = some (.tick v (gateTime p r)))
    (raw : SA.confirmation p (Run.stateBefore (sapc p) rho j v).base r = some b) :
    Block.Preceq b (headData p rho (s + 1) reader).target := by
  apply genuine_head_continuation_of_compatible_authority p E rho hΔ t₀ hs
    i reader hr s he h ?_ j hj v hv r b ht raw
  intro active cert selected b hb
  exact h.facts.chain.comparable _ _ (authority active cert selected) hb

/-- An earlier genuine result continues at every capped HEAD, including
the final incomplete label. Local raw transfer and both root premises
come from the actual run and the input invariant. -/
theorem genuine_head_continuation_of_run_invariant {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (i : Nat) (reader : V) (hr : reader ∈ rho.honest) (s : Slot)
    (he : rho.events[i]? = some (.tick reader (voteTime p (s + 1))))
    (h : JointCleanInvariant p E rho i)
    (j : Nat) (hj : j < i) (v : V) (hv : v ∈ rho.honest) (r : Slot) (b : Block)
    (ht : rho.events[j]? = some (.tick v (gateTime p r)))
    (raw : SA.confirmation p (Run.stateBefore (sapc p) rho j v).base r = some b) :
    Block.Preceq b (headData p rho (s + 1) reader).target := by
  apply genuine_head_continuation_of_active_authority p E rho hΔ t₀ hs i reader hr s he h
    ?_ j hj v hv r b ht raw
  intro _ cert selected
  apply selectedPC_on_cleanRunPath p E rho hs.execution cap
    i reader (voteTime p (s + 1)) (s + 1) cert
  rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed he]
  exact selected

/-- A HEAD adds no source when every active selection is already on the
input path. Disabled selection adds no source, even if an old PC conflicts. -/
theorem cleanRunPath_eq_at_head_of_authority {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (rho : Run V (sapc p)) (i : Nat) (reader : V) (r : Slot)
    (he : rho.events[i]? = some (.tick reader (voteTime p r)))
    (authority : reader ∈ rho.honest →
      capBroken p (clock p (Run.stateBefore (sapc p) rho i reader) (voteTime p r)) = false →
      ∀ c, selectedPC p (clock p (Run.stateBefore (sapc p) rho i reader)
        (voteTime p r)) r = some c → cleanRunPath p rho i c.target) :
    cleanRunPath p rho (i + 1) = cleanRunPath p rho i := by
  have old (j : Nat) (hj : j < i + 1) (v : V) (t : Time)
      (ht : rho.events[j]? = some (.tick v t)) (hn : voteTime p r ≠ t) : j < i := by
    have hne : j ≠ i := by
      rintro rfl
      exact hn (congrArg Event.time (Option.some.inj (he.symm.trans ht)))
    omega
  have noProposal (s : Slot) : voteTime p r ≠ proposalTime p s := by
    simpa only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_one, one_mul] using!
      duty_phase_ne p r s 1 0 (by decide) (by decide) (by decide)
  have source (b : Block) (hb : CleanRunSource p rho (i + 1) b) : cleanRunPath p rho i b := by
    have lift (h : CleanRunSource p rho i b) : cleanRunPath p rho i b :=
      Or.inr ⟨b, h, GridCO.block_preceq_self b⟩
    cases hb with
    | genuine j hj v hv s b ht hb =>
      exact lift (.genuine j (old j hj v _ ht (voteTime_ne_gateTime p r s)) v hv s b ht hb)
    | timely s b cap src =>
      obtain ⟨v, hv, j, hj, ht, hb⟩ := src
      exact lift (.timely s b cap
        ⟨v, hv, j, old j hj v _ ht (voteTime_ne_earlyTime p r s), ht, hb⟩)
    | gate j hj v hv s c ht ha hc =>
      exact lift (.gate j (old j hj v _ ht (voteTime_ne_gateTime p r s)) v hv s c ht ha hc)
    | proposal j hj v hv s c ht ha hc =>
      exact lift (.proposal j (old j hj v _ ht (noProposal s)) v hv s c ht ha hc)
    | head j hj v hv s c ht ha hc =>
      by_cases hji : j < i
      · exact lift (.head j hji v hv s c ht ha hc)
      · have hji : j = i := by omega
        subst j
        have eq := Option.some.inj (he.symm.trans ht)
        have hv' : reader = v := congrArg Event.node eq
        have ht' : voteTime p r = voteTime p s := congrArg Event.time eq
        have hrs : r = s := by
          have hcast : (r : Time) = s := by
            change 4 * p.Δ * (r : Time) + p.Δ = 4 * p.Δ * (s : Time) + p.Δ at ht'
            nlinarith [p.deltaPos]
          exact_mod_cast hcast
        subst v
        subst s
        exact authority hv ha c hc
  funext b
  apply propext
  constructor
  · rintro (hg | ⟨c, hc, hp⟩)
    · exact Or.inl hg
    · exact cleanRunPath_closed p rho i b c hp (source c hc)
  · exact cleanRunPath_mono p rho (Nat.le_succ i)

/-- The HEAD/release step works in either mode with active authority on
the input path. All historical facts are retained across the step. -/
theorem jointClean_head_tick_of_authority {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (i : Nat) (reader : V) (r : Slot)
    (he : rho.events[i]? = some (.tick reader (voteTime p r)))
    (h : JointCleanInvariant p E rho i)
    (authority : reader ∈ rho.honest →
      capBroken p (clock p (Run.stateBefore (sapc p) rho i reader) (voteTime p r)) = false →
      ∀ c, selectedPC p (clock p (Run.stateBefore (sapc p) rho i reader)
        (voteTime p r)) r = some c → cleanRunPath p rho i c.target) :
    JointCleanInvariant p E rho (i + 1) := by
  have label (s : Slot) (ht : voteTime p r = voteTime p s) : s = r := by
    have hcast : (s : Time) = r := by
      change 4 * p.Δ * (r : Time) + p.Δ = 4 * p.Δ * (s : Time) + p.Δ at ht
      nlinarith [p.deltaPos]
    exact_mod_cast hcast
  constructor
  · rw [cleanRunPath_eq_at_head_of_authority p rho i reader r he authority]
    apply cleanPathFacts_tick_of_no_early_no_gate p E rho hs.execution i reader _ he
      (voteTime_ne_earlyTime p r) (voteTime_ne_gateTime p r) h.facts
    · intro s c ht
      have hn := duty_phase_ne p r s 1 0 (by decide) (by decide) (by decide)
      exact (hn (by simpa only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_one, one_mul]
        using! ht)).elim
    · intro s c ht hr ha hc
      have eq := label s ht
      subst s
      exact authority hr ha c hc
    · intro j hj v hv s b ht raw current hsl htime hr
      have eq := label current htime
      subst current
      cases r with
      | zero => exact (Nat.not_lt_zero s hsl).elim
      | succ r =>
        have cover := genuine_head_continuation_of_active_authority p E rho hΔ t₀ hs
          i reader hr r he h (by
            rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed he]
              at authority
            exact authority hr) j hj v hv s b ht raw
        rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed he]
        exact cover
  · apply h.ordered.step_of_no_gate
    intro v s ht
    exact voteTime_ne_gateTime p r s (congrArg Event.time (Option.some.inj (he.symm.trans ht)))

/-- At a disabled HEAD, the uncapped step uses SA with the current
invariant. No PC compatibility, fault cap, or future gate is needed. -/
theorem jointClean_head_tick_disabled {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (i : Nat) (reader : V) (r : Slot)
    (he : rho.events[i]? = some (.tick reader (voteTime p r)))
    (h : JointCleanInvariant p E rho i)
    (disabled : capBroken p (Run.stateBefore (sapc p) rho i reader) = true) :
    JointCleanInvariant p E rho (i + 1) := by
  set_option backward.isDefEq.respectTransparency false in
  apply jointClean_head_tick_of_authority p E rho hΔ t₀ hs i reader r he h
  intro _ active
  rw [capBroken_clock, disabled] at active
  cases active

/-- The complete capped HEAD/release step, including the final HEAD
when its following gate is outside the run. -/
theorem jointClean_head_tick_capped {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (i : Nat) (reader : V) (r : Slot)
    (he : rho.events[i]? = some (.tick reader (voteTime p r)))
    (h : JointCleanInvariant p E rho i) :
    JointCleanInvariant p E rho (i + 1) := by
  apply jointClean_head_tick_of_authority p E rho hΔ t₀ hs i reader r he h
  intro _ _ c hc
  exact selectedPC_on_cleanRunPath p E rho hs.execution cap i reader _ r c hc

end AvailableChain.SAPC
end
