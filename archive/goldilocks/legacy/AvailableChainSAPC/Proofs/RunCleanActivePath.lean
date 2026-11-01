module
public import AvailableChainSAPC.Proofs.RunCleanAuthority

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- At an active tick above the cap, each PC authority source has an
eligible timely witness. New and old authority uses share the same
continuation argument. Stored unused timely saves are not path sources. -/
theorem cleanRunPath_chain_at_active_tick
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (nocap : ¬ FaultBound (sapc p) (pcFaultCap p) rho)
    (i : Nat) (reader : V) (t : Time)
    (he : rho.events[i]? = some (.tick reader t))
    (h : JointCleanInvariant p E rho i)
    (active : capBroken p (Run.stateBefore (sapc p) rho i reader) = false) :
    CleanPath (cleanRunPath p rho (i + 1)) := by
  set_option backward.isDefEq.respectTransparency false in
  have honest := hs.execution.honest_only _ (List.mem_of_getElem? he)
  change reader ∈ rho.honest at honest
  have ha := sleepy_quorum_above_faults p E rho t₀ hs
  have horizon := (hs.execution.in_horizon _ (List.mem_of_getElem? he)).2
  have timele (j : Nat) (hj : j < i + 1) (v : V) (u : Time)
      (tick : rho.events[j]? = some (.tick v u)) : u ≤ t := by
    by_contra hn
    have idx := eventIndex_lt_of_time_lt hs.execution.toScheduleWellFormed he tick
      (lt_of_not_ge hn)
    omega
  let Raw := fun r b => ∃ v ∈ rho.honest,
    SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some b
  let Timely := fun r b => HonestTimelySource p rho i r b ∧ gateTime p r ≤ t
  let Source := fun b => (∃ r, gateTime p r ≤ t ∧ Raw r b) ∨ ∃ r, Timely r b
  have sources (b : Block) (src : CleanRunSource p rho (i + 1) b) : Source b := by
    have pc (j : Nat) (hj : j < i + 1) (v : V) (u : Time)
        (tick : rho.events[j]? = some (.tick v u)) (c : PC p.n)
        (valid : pcValid p (Run.stateBefore (sapc p) rho j v) c = true) : Source c.target := by
      obtain ⟨w, hw, k, hk, ht, saved⟩ := validPC_prior_timely p E rho hs.execution ha j v c valid
      exact Or.inr ⟨c.slot, ⟨w, hw, k, by omega, ht, saved⟩,
        (validPC_gate_le_tick p E rho hΔ hs.execution ha j v u tick c valid).trans
          (timele j hj v u tick)⟩
    cases src with
    | genuine j hj v hv r b tick raw =>
      rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed tick] at raw
      exact Or.inl ⟨r, timele j hj v _ tick, v, hv, raw⟩
    | timely _ _ cap _ => exact (nocap cap).elim
    | gate j hj v _ _ c tick _ selected =>
      exact pc j hj v _ tick c (installedPC_valid_before p rho v j c selected)
    | proposal j hj v _ _ c tick _ selected =>
      rw [clock_bestPC] at selected
      exact pc j hj v _ tick c (installedPC_valid_before p rho v j c selected)
    | head j hj v _ _ c tick _ selected =>
      have valid := certificates_valid_at_fold p (rho.events.take j) v
      have hc := selectedPC_valid p _ (clock_frozenPC_valid p _ _ valid.2 valid.1) _ c selected
      rw [pcValid_eq_of_data p _ _ (clock_blocks p _ _) (clock_archive p _ _)] at hc
      exact pc j hj v _ tick c hc
  have sync (r : Slot) : E.t_GST ≤ earlyTime p r := by
    rw [hs.gst_zero]
    change 0 ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have headBeforeGate (r : Slot) : voteTime p r < gateTime p r := by
    change 4 * p.Δ * (r : Time) + p.Δ < 4 * p.Δ * (r : Time) + 6 * p.Δ
    linarith [p.deltaPos]
  have heads (r s : Slot) (b : Block) (src : Timely r b) (hrs : r < s)
      (time : voteTime p s < t) :
      ∀ v ∈ rho.honest, Block.Preceq b (headData p rho s v).target :=
    timely_continues_before_active_input p E rho hΔ t₀ hs i _ he h reader honest active
      s r b src.1 src.2 hrs time
  have rawPair (r s : Slot) (b c : Block) (hr : gateTime p r ≤ t) (hs' : gateTime p s ≤ t)
      (hb : Raw r b) (hc : Raw s c) : Block.Compatible b c := by
    obtain ⟨v, hv, rawB⟩ := hb
    obtain ⟨w, hw, rawC⟩ := hc
    rcases lt_trichotomy r s with hrs | rfl | hsr
    · obtain ⟨d, hd, hp⟩ := (clean_history_before_tick p E rho hΔ t₀ hs
        i reader t he h s hs').1 r hrs v hv b rawB w hw
      exact Bool.or_eq_true_iff.mpr (Or.inl ((Option.some.inj (hd.symm.trans rawC)) ▸ hp))
    · exact synchronous_sameLabel p E rho hs.execution hΔ hs.acceptedRelay r (sync r)
        (hr.trans horizon) v w hv hw b c rawB rawC
    · obtain ⟨d, hd, hp⟩ := (clean_history_before_tick p E rho hΔ t₀ hs
        i reader t he h r hr).1 s hsr w hw c rawC v hv
      exact Bool.or_eq_true_iff.mpr (Or.inr ((Option.some.inj (hd.symm.trans rawB)) ▸ hp))
  have timelyPair (r s : Slot) (b c : Block) (hb : Timely r b) (hc : Timely s c) :
      Block.Compatible b c := by
    rcases lt_trichotomy r s with hrs | rfl | hsr
    · obtain ⟨v, _, j, _, _, saved⟩ := hc.1
      exact Bool.or_eq_true_iff.mpr (Or.inl (timely_prefix_of_head_coverage p E rho
        hs.execution ha (j + 1) v s b c saved
        (heads r s b hb hrs ((headBeforeGate s).trans_le hc.2))))
    · exact GridCO.ancestors_compatible b c _
        (timely_next_heads_of_active_input p E rho hΔ t₀ hs i _ he h r b hb.1 hb.2
          reader honest active reader honest)
        (timely_next_heads_of_active_input p E rho hΔ t₀ hs i _ he h r c hc.1 hc.2
          reader honest active reader honest)
    · obtain ⟨v, _, j, _, _, saved⟩ := hb.1
      exact Bool.or_eq_true_iff.mpr (Or.inr (timely_prefix_of_head_coverage p E rho
        hs.execution ha (j + 1) v r c b saved
        (heads s r c hc hsr ((headBeforeGate r).trans_le hb.2))))
  have mixed (r s : Slot) (b c : Block) (hr : gateTime p r ≤ t)
      (hb : Raw r b) (hc : Timely s c) : Block.Compatible b c := by
    obtain ⟨v, hv, raw⟩ := hb
    obtain ⟨w, hw, j, _, _, saved⟩ := hc.1
    rcases lt_trichotomy r s with hrs | rfl | hsr
    · apply Bool.or_eq_true_iff.mpr
      apply Or.inl
      apply timely_prefix_of_head_coverage p E rho hs.execution ha (j + 1) w s b c saved
      intro u hu
      cases s with
      | zero => exact (Nat.not_lt_zero r hrs).elim
      | succ s =>
        have bound := ((GridCO.gateTime_le_iff p.engine s (s + 1)).mpr (Nat.le_succ s)).trans hc.2
        have history := clean_history_before_tick p E rho hΔ t₀ hs i reader t he h s bound
        rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hrs) with rfl | hlt
        · exact history.2 v hv b raw u hu
        · obtain ⟨d, hd, hp⟩ := history.1 r hlt v hv b raw v hv
          exact GridCO.prefix_trans b d _ hp (history.2 v hv d hd u hu)
    · obtain ⟨forward, _⟩ := synchronous_transfer_relays p E rho hΔ hs.acceptedRelay r
        (sync r) (hr.trans horizon)
      apply timely_compatible_confirmation p E rho hs.execution.toScheduleWellFormed
        r w v hw hv _ c b
        (savedTimely_candidate_at_early p E rho hs.execution.toScheduleWellFormed
          (j + 1) w r c saved) raw
      intro u hu k obj time ht accepted other ho missing
      obtain ⟨t', ht', k', hk'⟩ := forward u hu k obj time ht accepted other ho missing
      refine ⟨t', ht'.trans_le ?_, k', hk'⟩
      change 4 * p.Δ * (r : Time) + 3 * p.Δ ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
      linarith [p.deltaPos]
    · have earlyBound : earlyTime p r ≤ rho.horizon := by
        apply le_trans _ (hr.trans horizon)
        change 4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
        linarith [p.deltaPos]
      obtain ⟨d, hd, hp⟩ := sleepy_preserve_from_heads p E rho hΔ t₀ hs r earlyBound c
        (heads s r c hc hsr ((headBeforeGate r).trans_le hr)) v hv
      exact Bool.or_eq_true_iff.mpr (Or.inr ((Option.some.inj (hd.symm.trans raw)) ▸ hp))
  have pair (b c : Block) (hb : CleanRunSource p rho (i + 1) b)
      (hc : CleanRunSource p rho (i + 1) c) : Block.Compatible b c := by
    rcases sources b hb with ⟨r, hr, hb⟩ | ⟨r, hb⟩ <;>
      rcases sources c hc with ⟨s, hs', hc⟩ | ⟨s, hc⟩
    · exact rawPair r s b c hr hs' hb hc
    · exact mixed r s b c hr hb hc
    · simpa only [Block.Compatible, Block.compatible, Bool.or_comm] using mixed s r c b hs' hc hb
    · exact timelyPair r s b c hb hc
  refine ⟨Or.inl rfl, cleanRunPath_closed p rho (i + 1), ?_⟩
  intro a b ha hb
  rcases ha with rfl | ⟨c, hc, hp⟩
  · exact Bool.or_eq_true_iff.mpr (Or.inl (GridCO.genesis_prefix b))
  rcases hb with rfl | ⟨d, hd, hq⟩
  · exact Bool.or_eq_true_iff.mpr (Or.inr (GridCO.genesis_prefix a))
  rcases Bool.or_eq_true_iff.mp (pair c d hc hd) with hcd | hdc
  · exact GridCO.ancestors_compatible a b d (GridCO.prefix_trans a c d hp hcd) hq
  · exact GridCO.ancestors_compatible a b c hp (GridCO.prefix_trans b d c hq hdc)

end AvailableChain.SAPC
end
