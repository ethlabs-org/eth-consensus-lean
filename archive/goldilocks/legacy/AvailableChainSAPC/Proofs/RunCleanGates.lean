module
public import AvailableChainSAPC.Proofs.RunCleanFacts
public import AvailableChainSAPC.Proofs.QuorumGenuine

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- All HEAD inputs needed by the label induction precede this early
cutoff. Restriction of the current invariant supplies them. The preceding
gate may be the current event; its result is not assumed as a source. -/
theorem clean_history_before_early_capped {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (i : Nat) (reader : V) (last : Slot)
    (he : rho.events[i]? = some (.tick reader (earlyTime p last)))
    (h : JointCleanInvariant p E rho i) (r : Slot) (hr : r < last) :
    GridCO.GenuineExtends (fun v => v ∈ rho.honest)
      (fun s v => SA.confirmation p
        (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s) r ∧
    GridCO.GenuineContinues (fun v => v ∈ rho.honest)
      (fun s v => SA.confirmation p
        (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s)
      (fun s v => (headData p rho (s + 1) v).target) r := by
  have hbound : gateTime p r ≤ earlyTime p last := by
    have hlt : (r : Time) + 1 ≤ last := by exact_mod_cast hr
    change 4 * p.Δ * (r : Time) + 6 * p.Δ ≤ 4 * p.Δ * (last : Time) + 2 * p.Δ
    nlinarith [p.deltaPos]
  apply clean_genuine_history_capped_of_head_invariants p E rho hΔ t₀ hs cap r
    (hbound.trans (hs.execution.in_horizon _ (List.mem_of_getElem? he)).2)
  intro s hsr j v _ ht
  have htime : voteTime p (s + 1) < earlyTime p last := by
    have hlt : (s : Time) + 1 ≤ last := by exact_mod_cast hsr.trans_lt hr
    change 4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ <
      4 * p.Δ * (last : Time) + 2 * p.Δ
    push_cast
    nlinarith [p.deltaPos]
  exact h.restrict_capped hs.execution cap
    (eventIndex_lt_of_time_lt hs.execution.toScheduleWellFormed ht he htime).le

/-- Timely sources at an earlier label cover every later HEAD through
this early cutoff. The source's own tick proves it precedes that HEAD. -/
theorem timely_heads_before_early_capped {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (i : Nat) (reader : V) (last : Slot)
    (he : rho.events[i]? = some (.tick reader (earlyTime p last)))
    (h : JointCleanInvariant p E rho i) (r s : Slot) (b : Block)
    (source : HonestTimelySource p rho (i + 1) r b) (hrs : r < s) (hsl : s ≤ last)
    (v : V) (hv : v ∈ rho.honest) : Block.Preceq b (headData p rho s v).target := by
  have htime : voteTime p s < earlyTime p last := by
    have hle : (s : Time) ≤ last := by exact_mod_cast hsl
    change 4 * p.Δ * (s : Time) + p.Δ < 4 * p.Δ * (last : Time) + 2 * p.Δ
    nlinarith [p.deltaPos]
  have hpub : PublicTime E (voteTime p s) := by
    refine ⟨4 * s + 1, ?_⟩
    change 4 * p.Δ * (s : Time) + p.Δ = _
    rw [hΔ]
    push_cast
    ring
  have hn : 0 ≤ voteTime p s := by
    change 0 ≤ 4 * p.Δ * (s : Time) + p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg s]
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp (hs.execution.tick_total v hv _ hpub hn
    (htime.le.trans (hs.execution.in_horizon _ (List.mem_of_getElem? he)).2))
  have hki := eventIndex_lt_of_time_lt hs.execution.toScheduleWellFormed hk he htime
  obtain ⟨w, hw, j, _, ht, saved⟩ := source
  have hearly : earlyTime p r < voteTime p s := by
    have hlt : (r : Time) + 1 ≤ s := by exact_mod_cast hrs
    change 4 * p.Δ * (r : Time) + 2 * p.Δ < 4 * p.Δ * (s : Time) + p.Δ
    nlinarith [p.deltaPos]
  have hjk := eventIndex_lt_of_time_lt hs.execution.toScheduleWellFormed ht hk hearly
  exact timely_continues_of_run_invariant p E rho hΔ t₀ hs cap k v s hk
    (h.restrict_capped hs.execution cap hki.le) r b ⟨w, hw, j, hjk, ht, saved⟩
    s hrs (le_refl _) v hv

/-- Earlier raw results cover the HEAD at a later preparation label.
This includes the pending gate immediately before the new early save. -/
theorem genuine_heads_before_early_capped {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
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
    have history := clean_history_before_early_capped p E rho hΔ t₀ hs cap
      i reader last he h s ((Nat.lt_succ_self s).trans_le hsl)
    rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hrs) with rfl | hlt
    · exact history.2 source hsource b raw v hv
    · obtain ⟨c, hc, hp⟩ := history.1 r hlt source hsource b raw source hsource
      exact GridCO.prefix_trans b c _ hp (history.2 source hsource c hc v hv)

/-- The two source kinds added at an early/gate tick are comparable.
The proof uses actual HEAD continuation, not accessibility of a proposal. -/
theorem cleanRunPath_chain_at_early_capped {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (i : Nat) (reader : V) (last : Slot)
    (he : rho.events[i]? = some (.tick reader (earlyTime p last)))
    (h : JointCleanInvariant p E rho i) : CleanPath (cleanRunPath p rho (i + 1)) := by
  have timele (j : Nat) (hj : j < i + 1) (v : V) (t : Time)
      (ht : rho.events[j]? = some (.tick v t)) : t ≤ earlyTime p last := by
    by_contra hn
    have hi := eventIndex_lt_of_time_lt hs.execution.toScheduleWellFormed he ht
      (lt_of_not_ge hn)
    omega
  have horizon := (hs.execution.in_horizon _ (List.mem_of_getElem? he)).2
  have gatebound (r : Slot) (hr : r < last) : gateTime p r ≤ rho.horizon := by
    apply le_trans _ horizon
    have hle : (r : Time) + 1 ≤ last := by exact_mod_cast hr
    change 4 * p.Δ * (r : Time) + 6 * p.Δ ≤ 4 * p.Δ * (last : Time) + 2 * p.Δ
    nlinarith [p.deltaPos]
  have sync (r : Slot) : E.t_GST ≤ earlyTime p r := by
    rw [hs.gst_zero]
    change 0 ≤ 4 * p.Δ * (r : Time) + 2 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  let rawSource := fun r b => ∃ v ∈ rho.honest,
    SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some b
  have rawPair (r s : Slot) (hr : r < last) (hs' : s < last) (b c : Block)
      (hb : rawSource r b) (hc : rawSource s c) : Block.Compatible b c := by
    obtain ⟨v, hv, hb⟩ := hb
    obtain ⟨w, hw, hc⟩ := hc
    rcases lt_trichotomy r s with hrs | rfl | hsr
    · obtain ⟨d, hd, hp⟩ := (clean_history_before_early_capped p E rho hΔ t₀ hs cap
        i reader last he h s hs').1 r hrs v hv b hb w hw
      have eq := Option.some.inj (hd.symm.trans hc)
      exact Bool.or_eq_true_iff.mpr (Or.inl (eq ▸ hp))
    · exact synchronous_sameLabel p E rho hs.execution hΔ hs.acceptedRelay r
        (sync r) (gatebound r hr) v w hv hw b c hb hc
    · obtain ⟨d, hd, hp⟩ := (clean_history_before_early_capped p E rho hΔ t₀ hs cap
        i reader last he h r hr).1 s hsr w hw c hc v hv
      have eq := Option.some.inj (hd.symm.trans hb)
      exact Bool.or_eq_true_iff.mpr (Or.inr (eq ▸ hp))
  have timelyPair (r s : Slot) (hr : r ≤ last) (hs' : s ≤ last) (b c : Block)
      (hb : HonestTimelySource p rho (i + 1) r b)
      (hc : HonestTimelySource p rho (i + 1) s c) : Block.Compatible b c := by
    rcases lt_trichotomy r s with hrs | rfl | hsr
    · obtain ⟨v, _, j, _, _, saved⟩ := hc
      exact Bool.or_eq_true_iff.mpr (Or.inl (timely_prefix_of_head_coverage p E rho
        hs.execution (capped_quorum_above_faults p rho cap) (j + 1) v s b c saved
        (timely_heads_before_early_capped p E rho hΔ t₀ hs cap
          i reader last he h r s b hb hrs hs')))
    · obtain ⟨v, _, j, _, _, savedB⟩ := hb
      obtain ⟨w, _, k, _, _, savedC⟩ := hc
      have eq := savedTimely_unique p E rho hs.execution cap (j + 1) (k + 1)
        v w r b c savedB savedC
      rw [eq]
      exact Bool.or_eq_true_iff.mpr (Or.inl (GridCO.block_preceq_self c))
    · obtain ⟨v, _, j, _, _, saved⟩ := hb
      exact Bool.or_eq_true_iff.mpr (Or.inr (timely_prefix_of_head_coverage p E rho
        hs.execution (capped_quorum_above_faults p rho cap) (j + 1) v r c b saved
        (timely_heads_before_early_capped p E rho hΔ t₀ hs cap
          i reader last he h s r c hc hsr hr)))
  have mixed (r s : Slot) (hr : r < last) (hs' : s ≤ last) (b c : Block)
      (hb : rawSource r b) (hc : HonestTimelySource p rho (i + 1) s c) :
      Block.Compatible b c := by
    obtain ⟨v, hv, raw⟩ := hb
    rcases lt_trichotomy r s with hrs | rfl | hsr
    · obtain ⟨w, _, j, _, _, saved⟩ := hc
      exact Bool.or_eq_true_iff.mpr (Or.inl (timely_prefix_of_head_coverage p E rho
        hs.execution (capped_quorum_above_faults p rho cap) (j + 1) w s b c saved
        (genuine_heads_before_early_capped p E rho hΔ t₀ hs cap
          i reader last he h r s b v hv raw hrs hs')))
    · obtain ⟨w, hw, j, _, _, saved⟩ := hc
      obtain ⟨forward, _⟩ := synchronous_transfer_relays p E rho hΔ hs.acceptedRelay r
        (sync r) (gatebound r hr)
      have hfg : freezeTime p r ≤ gateTime p r := by
        change 4 * p.Δ * (r : Time) + 3 * p.Δ ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
        linarith [p.deltaPos]
      apply timely_compatible_confirmation p E rho hs.execution.toScheduleWellFormed
        r w v hw hv _ c b
        (savedTimely_candidate_at_early p E rho hs.execution.toScheduleWellFormed
          (j + 1) w r c saved) raw
      intro u hu k obj t ht accepted z hz missing
      obtain ⟨t', ht', k', hk'⟩ := forward u hu k obj t ht accepted z hz missing
      exact ⟨t', ht'.trans_le hfg, k', hk'⟩
    · have hearly : earlyTime p r ≤ rho.horizon := by
        apply le_trans _ (gatebound r hr)
        change 4 * p.Δ * (r : Time) + 2 * p.Δ ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
        linarith [p.deltaPos]
      obtain ⟨d, hd, hp⟩ := sleepy_preserve_from_heads p E rho hΔ t₀ hs r hearly c
        (timely_heads_before_early_capped p E rho hΔ t₀ hs cap
          i reader last he h s r c hc hsr hr.le) v hv
      have eq := Option.some.inj (hd.symm.trans raw)
      exact Bool.or_eq_true_iff.mpr (Or.inr (eq ▸ hp))
  let source := fun b => (∃ r, r < last ∧ rawSource r b) ∨
    ∃ r, r ≤ last ∧ HonestTimelySource p rho (i + 1) r b
  have sources (b : Block) (hb : cleanRunPath p rho (i + 1) b) :
      b = .genesis ∨ ∃ c, source c ∧ Block.Preceq b c := by
    rcases (cleanRunPath_capped_sources p E rho hs.execution cap (i + 1) b).mp hb with
      hg | ⟨j, hj, v, hv, r, c, ht, hc, hp⟩ | ⟨r, c, src, hp⟩
    · exact Or.inl hg
    · have htime := timele j hj v _ ht
      have hr : r < last := by
        by_contra hn
        have hle : (last : Time) ≤ r := by exact_mod_cast le_of_not_gt hn
        change 4 * p.Δ * (r : Time) + 6 * p.Δ ≤
          4 * p.Δ * (last : Time) + 2 * p.Δ at htime
        nlinarith [p.deltaPos]
      rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed ht] at hc
      exact Or.inr ⟨c, Or.inl ⟨r, hr, v, hv, hc⟩, hp⟩
    · obtain ⟨v, hv, j, hj, ht, saved⟩ := src
      have htime := timele j hj v _ ht
      have hr : r ≤ last := by
        by_contra hn
        have hlt : (last : Time) < r := by exact_mod_cast lt_of_not_ge hn
        change 4 * p.Δ * (r : Time) + 2 * p.Δ ≤
          4 * p.Δ * (last : Time) + 2 * p.Δ at htime
        nlinarith [p.deltaPos]
      exact Or.inr ⟨c, Or.inr ⟨r, hr, v, hv, j, hj, ht, saved⟩, hp⟩
  have pairs (b c : Block) (hb : source b) (hc : source c) : Block.Compatible b c := by
    rcases hb with ⟨r, hr, hb⟩ | ⟨r, hr, hb⟩ <;>
      rcases hc with ⟨s, hs', hc⟩ | ⟨s, hs', hc⟩
    · exact rawPair r s hr hs' b c hb hc
    · exact mixed r s hr hs' b c hb hc
    · simpa only [Block.Compatible, Block.compatible, Bool.or_comm] using
        mixed s r hs' hr c b hc hb
    · exact timelyPair r s hr hs' b c hb hc
  refine ⟨Or.inl rfl, cleanRunPath_closed p rho (i + 1), ?_⟩
  intro b c hb hc
  rcases sources b hb with rfl | ⟨B, hB, hbB⟩
  · exact Bool.or_eq_true_iff.mpr (Or.inl (GridCO.genesis_prefix c))
  rcases sources c hc with rfl | ⟨C, hC, hcC⟩
  · exact Bool.or_eq_true_iff.mpr (Or.inr (GridCO.genesis_prefix b))
  rcases Bool.or_eq_true_iff.mp (pairs B C hB hC) with hBC | hCB
  · exact GridCO.ancestors_compatible b c C (GridCO.prefix_trans b B C hbB hBC) hcC
  · exact GridCO.ancestors_compatible b c B hbB (GridCO.prefix_trans c C B hcC hCB)

/-- The whole capped early/gate step. Raw gate results and timely saves
are added together; ordered history and continuation include the HEAD
which already ran before this gate. -/
theorem jointClean_early_tick_capped {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (i : Nat) (reader : V) (last : Slot)
    (he : rho.events[i]? = some (.tick reader (earlyTime p last)))
    (h : JointCleanInvariant p E rho i) : JointCleanInvariant p E rho (i + 1) := by
  have timele (j : Nat) (hj : j < i + 1) (v : V) (t : Time)
      (ht : rho.events[j]? = some (.tick v t)) : t ≤ earlyTime p last := by
    by_contra hn
    have hi := eventIndex_lt_of_time_lt hs.execution.toScheduleWellFormed he ht
      (lt_of_not_ge hn)
    omega
  have gateLabel (j : Nat) (hj : j < i + 1) (v : V) (r : Slot)
      (ht : rho.events[j]? = some (.tick v (gateTime p r))) : r < last := by
    have htime := timele j hj v _ ht
    by_contra hn
    have hle : (last : Time) ≤ r := by exact_mod_cast le_of_not_gt hn
    change 4 * p.Δ * (r : Time) + 6 * p.Δ ≤
      4 * p.Δ * (last : Time) + 2 * p.Δ at htime
    nlinarith [p.deltaPos]
  constructor
  · apply cleanPathFacts_capped_of_chain_and_transfer p E rho hs.execution cap (i + 1)
      (cleanRunPath_chain_at_early_capped p E rho hΔ t₀ hs cap i reader last he h)
    intro j hj v hv r b ht raw k hk w hw s hrs head
    have htime := timele k hk w _ head
    have hsl : s ≤ last := by
      by_contra hn
      have hlt : (last : Time) + 1 ≤ s := by exact_mod_cast lt_of_not_ge hn
      change 4 * p.Δ * (s : Time) + p.Δ ≤
        4 * p.Δ * (last : Time) + 2 * p.Δ at htime
      nlinarith [p.deltaPos]
    rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed ht] at raw
    rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed head]
    exact genuine_heads_before_early_capped p E rho hΔ t₀ hs cap
      i reader last he h r s b v hv raw hrs hsl w hw
  · intro j hj k hk v hv w hw r s b c hrs htj htk hb hc
    rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed htj] at hb
    rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed htk] at hc
    obtain ⟨d, hd, hp⟩ := (clean_history_before_early_capped p E rho hΔ t₀ hs cap
      i reader last he h s (gateLabel k hk w s htk)).1 r hrs v hv b hb w hw
    exact (Option.some.inj (hd.symm.trans hc)) ▸ hp

/-- Gate r and early cutoff r+1 are one clock event. -/
theorem jointClean_gate_tick_capped {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (i : Nat) (reader : V) (r : Slot)
    (he : rho.events[i]? = some (.tick reader (gateTime p r)))
    (h : JointCleanInvariant p E rho i) : JointCleanInvariant p E rho (i + 1) := by
  have eq : gateTime p r = earlyTime p (r + 1) := by
    change 4 * p.Δ * (r : Time) + 6 * p.Δ =
      4 * p.Δ * ((r + 1 : Nat) : Time) + 2 * p.Δ
    push_cast
    ring
  exact jointClean_early_tick_capped p E rho hΔ t₀ hs cap i reader (r + 1) (eq ▸ he) h

end AvailableChain.SAPC
end
