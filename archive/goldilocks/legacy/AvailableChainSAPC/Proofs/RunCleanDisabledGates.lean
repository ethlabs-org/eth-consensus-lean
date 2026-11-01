module
public import AvailableChainSAPC.Proofs.RunCleanAuthority
public import AvailableChainSAPC.Proofs.RunCleanGates

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- Raw results cover later HEADs through an early input, including the
pending result at that same early/gate time. No fault cap is needed. -/
theorem genuine_heads_before_early {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (i : Nat) (reader : V) (last : Slot)
    (he : rho.events[i]? = some (.tick reader (earlyTime p last)))
    (h : JointCleanInvariant p E rho i) (r s : Slot) (b : Block)
    (source : V) (hsource : source ∈ rho.honest)
    (raw : SA.confirmation p
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r = some b)
    (hrs : r < s) (hsl : s ≤ last)
    (v : V) (hv : v ∈ rho.honest) : Block.Preceq b (headData p rho s v).target := by
  cases s with
  | zero => exact (Nat.not_lt_zero r hrs).elim
  | succ s =>
    have history := clean_history_before_early p E rho hΔ t₀ hs
      i reader last he h s ((Nat.lt_succ_self s).trans_le hsl)
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hrs) with rfl | hlt
    · exact history.2 source hsource b raw v hv
    · obtain ⟨c, hc, hp⟩ := history.1 r hlt source hsource b raw source hsource
      exact GridCO.prefix_trans b c _ hp (history.2 source hsource c hc v hv)

/-- The pending raw result is compatible with every retained source.
Old PCs use their successful first transfer and continuation on the
current path, even after mode changes. -/
theorem genuine_compatible_run_path_before_early
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (nocap : ¬ FaultBound (sapc p) (pcFaultCap p) rho)
    (i : Nat) (reader : V) (last : Slot)
    (he : rho.events[i]? = some (.tick reader (earlyTime p last)))
    (h : JointCleanInvariant p E rho i) (r : Slot) (hr : r < last)
    (source : V) (honest : source ∈ rho.honest) (b : Block)
    (raw : SA.confirmation p
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r = some b)
    (a : Block) (ha : cleanRunPath p rho i a) : Block.Compatible a b := by
  have horizon := (hs.execution.in_horizon _ (List.mem_of_getElem? he)).2
  have timele (j : Nat) (hj : j < i) (v : V) (t : Time)
      (tick : rho.events[j]? = some (.tick v t)) : t ≤ earlyTime p last := by
    by_contra hn
    have idx := eventIndex_lt_of_time_lt hs.execution.toScheduleWellFormed he tick
      (lt_of_not_ge hn)
    omega
  have gateBound : gateTime p r ≤ rho.horizon := by
    apply le_trans _ horizon
    have cast : (r : Time) + 1 ≤ last := by exact_mod_cast hr
    change 4 * p.Δ * (r : Time) + 6 * p.Δ ≤ 4 * p.Δ * (last : Time) + 2 * p.Δ
    nlinarith [p.deltaPos]
  have sync (s : Slot) : E.t_GST ≤ earlyTime p s := by
    rw [hs.gst_zero]
    change 0 ≤ 4 * p.Δ * (s : Time) + 2 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg s]
  rcases ha with rfl | ⟨c, hc, hp⟩
  · exact Bool.or_eq_true_iff.mpr (Or.inl (GridCO.genesis_prefix b))
  have onPath : cleanRunPath p rho i c := Or.inr ⟨c, hc, GridCO.block_preceq_self c⟩
  have comp : Block.Compatible c b := by
    rcases cleanRunSource_raw_or_transferred_timely p E rho hΔ t₀ hs nocap i h c hc with
      ⟨j, hj, v, hv, s, tick, rawC⟩ | ⟨s, src, first⟩
    · have time := timele j hj v _ tick
      have hs' : s < last := by
        by_contra hn
        have cast : (last : Time) ≤ s := by exact_mod_cast le_of_not_gt hn
        change 4 * p.Δ * (s : Time) + 6 * p.Δ ≤
          4 * p.Δ * (last : Time) + 2 * p.Δ at time
        nlinarith [p.deltaPos]
      rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed tick] at rawC
      rcases lt_trichotomy s r with hsr | rfl | hrs
      · obtain ⟨d, hd, hp⟩ := (clean_history_before_early p E rho hΔ t₀ hs
          i reader last he h r hr).1 s hsr v hv c rawC source honest
        exact Bool.or_eq_true_iff.mpr (Or.inl ((Option.some.inj (hd.symm.trans raw)) ▸ hp))
      · exact synchronous_sameLabel p E rho hs.execution hΔ hs.acceptedRelay s
          (sync s) gateBound v source hv honest c b rawC raw
      · obtain ⟨d, hd, hp⟩ := (clean_history_before_early p E rho hΔ t₀ hs
          i reader last he h s hs').1 r hrs source honest b raw v hv
        exact Bool.or_eq_true_iff.mpr (Or.inr ((Option.some.inj (hd.symm.trans rawC)) ▸ hp))
    · obtain ⟨v, hv, j, hj, tick, saved⟩ := src
      have time := timele j hj v _ tick
      have hs' : s ≤ last := by
        by_contra hn
        have cast : (last : Time) < s := by exact_mod_cast lt_of_not_ge hn
        change 4 * p.Δ * (s : Time) + 2 * p.Δ ≤
          4 * p.Δ * (last : Time) + 2 * p.Δ at time
        nlinarith [p.deltaPos]
      rcases lt_trichotomy s r with hsr | rfl | hrs
      · have headTime : voteTime p r < earlyTime p last := by
          have cast : (r : Time) ≤ last := by exact_mod_cast hr.le
          change 4 * p.Δ * (r : Time) + p.Δ < 4 * p.Δ * (last : Time) + 2 * p.Δ
          nlinarith [p.deltaPos]
        have cover := timely_continues_on_run_path p E rho hΔ t₀ hs i _ he h s c
          onPath first r hsr headTime
        have earlyBound : earlyTime p r ≤ rho.horizon := by
          apply le_trans _ gateBound
          change 4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
          linarith [p.deltaPos]
        obtain ⟨d, hd, hp⟩ := sleepy_preserve_from_heads p E rho hΔ t₀ hs r
          earlyBound c cover source honest
        exact Bool.or_eq_true_iff.mpr (Or.inl ((Option.some.inj (hd.symm.trans raw)) ▸ hp))
      · obtain ⟨forward, _⟩ := synchronous_transfer_relays p E rho hΔ hs.acceptedRelay s
          (sync s) gateBound
        have compatible : Block.Compatible b c := by
          apply timely_compatible_confirmation p E rho hs.execution.toScheduleWellFormed
            s v source hv honest _ c b
            (savedTimely_candidate_at_early p E rho hs.execution.toScheduleWellFormed
              (j + 1) v s c saved) raw
          intro w hw k obj t ht accepted other ho missing
          obtain ⟨t', ht', k', hk'⟩ := forward w hw k obj t ht accepted other ho missing
          refine ⟨t', ht'.trans_le ?_, k', hk'⟩
          change 4 * p.Δ * (s : Time) + 3 * p.Δ ≤ 4 * p.Δ * (s : Time) + 6 * p.Δ
          linarith [p.deltaPos]
        simpa only [Block.Compatible, Block.compatible, Bool.or_comm] using compatible
      · exact Bool.or_eq_true_iff.mpr (Or.inr
          (timely_prefix_of_head_coverage p E rho hs.execution
            (sleepy_quorum_above_faults p E rho t₀ hs) (j + 1) v s b c saved
            (genuine_heads_before_early p E rho hΔ t₀ hs i reader last he h r s b
              source honest raw hrs hs')))
  rcases Bool.or_eq_true_iff.mp comp with hcb | hbc
  · exact Bool.or_eq_true_iff.mpr (Or.inl (GridCO.prefix_trans a c b hp hcb))
  · exact GridCO.ancestors_compatible a b c hp hbc

/-- A disabled early/gate tick adds only raw sources above the cap.
The new raw result is comparable with every retained authority source. -/
theorem cleanRunPath_chain_at_early_disabled
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (i : Nat) (reader : V) (last : Slot)
    (he : rho.events[i]? = some (.tick reader (earlyTime p last)))
    (h : JointCleanInvariant p E rho i)
    (disabled : capBroken p (Run.stateBefore (sapc p) rho i reader) = true) :
    CleanPath (cleanRunPath p rho (i + 1)) := by
  set_option backward.isDefEq.respectTransparency false in
  have nocap : ¬ FaultBound (sapc p) (pcFaultCap p) rho := by
    intro cap
    have active := capBroken_false_before p E rho hs.execution cap reader i
    rw [disabled] at active
    cases active
  have timele (j : Nat) (hj : j < i + 1) (v : V) (t : Time)
      (tick : rho.events[j]? = some (.tick v t)) : t ≤ earlyTime p last := by
    by_contra hn
    have idx := eventIndex_lt_of_time_lt hs.execution.toScheduleWellFormed he tick
      (lt_of_not_ge hn)
    omega
  let Raw := fun b => ∃ r, r < last ∧ ∃ v ∈ rho.honest,
    SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some b
  have sourceCases (b : Block) (src : CleanRunSource p rho (i + 1) b) :
      cleanRunPath p rho i b ∨ Raw b := by
    have prior (j : Nat) (hj : j < i + 1) (v : V) (t : Time)
        (tick : rho.events[j]? = some (.tick v t))
        (active : capBroken p (Run.stateBefore (sapc p) rho j v) = false) : j < i := by
      by_contra hn
      have eq : j = i := by omega
      subst j
      have node := congrArg Event.node (Option.some.inj (he.symm.trans tick))
      change reader = v at node
      subst v
      rw [disabled] at active
      cases active
    cases src with
    | genuine j hj v hv r b tick raw =>
      have time := timele j hj v _ tick
      have bound : r < last := by
        by_contra hn
        have cast : (last : Time) ≤ r := by exact_mod_cast le_of_not_gt hn
        change 4 * p.Δ * (r : Time) + 6 * p.Δ ≤
          4 * p.Δ * (last : Time) + 2 * p.Δ at time
        nlinarith [p.deltaPos]
      rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed tick] at raw
      exact Or.inr ⟨r, bound, v, hv, raw⟩
    | timely _ _ cap _ => exact (nocap cap).elim
    | gate j hj v hv r c tick active selected =>
      exact Or.inl (Or.inr ⟨c.target,
        .gate j (prior j hj v _ tick active) v hv r c tick active selected,
        GridCO.block_preceq_self _⟩)
    | head j hj v hv r c tick active selected =>
      have active' := active
      rw [capBroken_clock] at active'
      exact Or.inl (Or.inr ⟨c.target,
        .head j (prior j hj v _ tick active') v hv r c tick active selected,
        GridCO.block_preceq_self _⟩)
    | proposal j hj v hv r c tick active selected =>
      have active' := active
      rw [capBroken_clock] at active'
      exact Or.inl (Or.inr ⟨c.target,
        .proposal j (prior j hj v _ tick active') v hv r c tick active selected,
        GridCO.block_preceq_self _⟩)
  have mixed (b c : Block) (hb : cleanRunPath p rho i b) (hc : Raw c) :
      Block.Compatible b c := by
    obtain ⟨r, hr, v, hv, raw⟩ := hc
    exact genuine_compatible_run_path_before_early p E rho hΔ t₀ hs nocap
      i reader last he h r hr v hv c raw b hb
  have rawPair (b c : Block) (hb : Raw b) (hc : Raw c) : Block.Compatible b c := by
    obtain ⟨r, hr, v, hv, rawB⟩ := hb
    obtain ⟨s, hs', w, hw, rawC⟩ := hc
    rcases lt_trichotomy r s with hrs | rfl | hsr
    · obtain ⟨d, hd, hp⟩ := (clean_history_before_early p E rho hΔ t₀ hs
        i reader last he h s hs').1 r hrs v hv b rawB w hw
      exact Bool.or_eq_true_iff.mpr (Or.inl ((Option.some.inj (hd.symm.trans rawC)) ▸ hp))
    · have sync : E.t_GST ≤ earlyTime p r := by
        rw [hs.gst_zero]
        change 0 ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
        nlinarith [p.deltaPos, Int.natCast_nonneg r]
      have bound : gateTime p r ≤ rho.horizon := by
        apply le_trans _ (hs.execution.in_horizon _ (List.mem_of_getElem? he)).2
        have cast : (r : Time) + 1 ≤ last := by exact_mod_cast hr
        change 4 * p.Δ * (r : Time) + 6 * p.Δ ≤
          4 * p.Δ * (last : Time) + 2 * p.Δ
        nlinarith [p.deltaPos]
      exact synchronous_sameLabel p E rho hs.execution hΔ hs.acceptedRelay r sync bound
        v w hv hw b c rawB rawC
    · obtain ⟨d, hd, hp⟩ := (clean_history_before_early p E rho hΔ t₀ hs
        i reader last he h r hr).1 s hsr w hw c rawC v hv
      exact Bool.or_eq_true_iff.mpr (Or.inr ((Option.some.inj (hd.symm.trans rawB)) ▸ hp))
  have pair (b c : Block) (hb : CleanRunSource p rho (i + 1) b)
      (hc : CleanRunSource p rho (i + 1) c) : Block.Compatible b c := by
    rcases sourceCases b hb with hb | hb <;> rcases sourceCases c hc with hc | hc
    · exact h.facts.chain.comparable b c hb hc
    · exact mixed b c hb hc
    · simpa only [Block.Compatible, Block.compatible, Bool.or_comm] using mixed c b hc hb
    · exact rawPair b c hb hc
  refine ⟨Or.inl rfl, cleanRunPath_closed p rho (i + 1), ?_⟩
  intro a b ha hb
  rcases ha with rfl | ⟨c, hc, hp⟩
  · exact Bool.or_eq_true_iff.mpr (Or.inl (GridCO.genesis_prefix b))
  rcases hb with rfl | ⟨d, hd, hq⟩
  · exact Bool.or_eq_true_iff.mpr (Or.inr (GridCO.genesis_prefix a))
  rcases Bool.or_eq_true_iff.mp (pair c d hc hd) with hcd | hdc
  · exact GridCO.ancestors_compatible a b d (GridCO.prefix_trans a c d hp hcd) hq
  · exact GridCO.ancestors_compatible a b c hp (GridCO.prefix_trans b d c hq hdc)

/-- Source comparability completes the early/gate step. Raw ordering and
continuation use the shared history proof in either mode. -/
theorem jointClean_early_tick_of_chain {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (i : Nat) (reader : V) (last : Slot)
    (he : rho.events[i]? = some (.tick reader (earlyTime p last)))
    (h : JointCleanInvariant p E rho i)
    (chain : CleanPath (cleanRunPath p rho (i + 1))) :
    JointCleanInvariant p E rho (i + 1) := by
  have timele (j : Nat) (hj : j < i + 1) (v : V) (t : Time)
      (tick : rho.events[j]? = some (.tick v t)) : t ≤ earlyTime p last := by
    by_contra hn
    have idx := eventIndex_lt_of_time_lt hs.execution.toScheduleWellFormed he tick
      (lt_of_not_ge hn)
    omega
  have gateLabel (j : Nat) (hj : j < i + 1) (v : V) (r : Slot)
      (tick : rho.events[j]? = some (.tick v (gateTime p r))) : r < last := by
    have time := timele j hj v _ tick
    by_contra hn
    have cast : (last : Time) ≤ r := by exact_mod_cast le_of_not_gt hn
    change 4 * p.Δ * (r : Time) + 6 * p.Δ ≤
      4 * p.Δ * (last : Time) + 2 * p.Δ at time
    nlinarith [p.deltaPos]
  constructor
  · apply cleanPathFacts_of_chain_and_transfer p E rho hs.execution
      (sleepy_quorum_above_faults p E rho t₀ hs) (i + 1)
      chain
    intro j hj v hv r b tick raw k hk w hw s hrs head
    have time := timele k hk w _ head
    have bound : s ≤ last := by
      by_contra hn
      have cast : (last : Time) + 1 ≤ s := by exact_mod_cast lt_of_not_ge hn
      change 4 * p.Δ * (s : Time) + p.Δ ≤
        4 * p.Δ * (last : Time) + 2 * p.Δ at time
      nlinarith [p.deltaPos]
    rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed tick] at raw
    rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed head]
    exact genuine_heads_before_early p E rho hΔ t₀ hs
      i reader last he h r s b v hv raw hrs bound w hw
  · intro j hj k hk v hv w hw r s b c hrs tick head raw result
    rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed tick] at raw
    rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed head] at result
    obtain ⟨d, hd, hp⟩ := (clean_history_before_early p E rho hΔ t₀ hs
      i reader last he h s (gateLabel k hk w s head)).1 r hrs v hv b raw w hw
    exact (Option.some.inj (hd.symm.trans result)) ▸ hp

/-- The complete disabled early/gate step retains ordered raw history,
old PC authority, and the pending result from the preceding mixed HEAD. -/
theorem jointClean_early_tick_disabled {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (i : Nat) (reader : V) (last : Slot)
    (he : rho.events[i]? = some (.tick reader (earlyTime p last)))
    (h : JointCleanInvariant p E rho i)
    (disabled : capBroken p (Run.stateBefore (sapc p) rho i reader) = true) :
    JointCleanInvariant p E rho (i + 1) :=
  jointClean_early_tick_of_chain p E rho hΔ t₀ hs i reader last he h
    (cleanRunPath_chain_at_early_disabled p E rho hΔ t₀ hs i reader last he h disabled)

end AvailableChain.SAPC
end
