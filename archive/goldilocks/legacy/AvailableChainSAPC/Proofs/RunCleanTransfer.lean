module
public import AvailableChainSAPC.Proofs.RunCleanHeads
public import AvailableChainSAPC.Proofs.CleanService

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- The strict input of an earlier or simultaneous HEAD is within the
current event prefix, for every reader, including sleeping readers. -/
theorem head_input_prefix_le {V : Type}
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (i : Nat) (v : V) (r s : Slot)
    (he : rho.events[i]? = some (.tick v (voteTime p r))) (hle : s ≤ r) :
    (rho.events.filter (fun e => decide (e.time ≤ voteTime p s - 1))).length ≤ i := by
  classical
  by_contra hn
  have ht := (index_lt_read_length_iff hs (voteTime p s - 1) he).mp (Nat.lt_of_not_ge hn)
  have hsr : (s : Time) ≤ r := by exact_mod_cast hle
  change 4 * p.Δ * (r : Time) + p.Δ ≤ 4 * p.Δ * (s : Time) + p.Δ - 1 at ht
  nlinarith [p.deltaPos]

/-- Both roots at an earlier HEAD lie on the current path. The proof
uses earlier state fields of this invariant, not an assumed invariant
at every earlier event. -/
theorem head_roots_on_run_path {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (i : Nat) (v : V) (r : Slot)
    (he : rho.events[i]? = some (.tick v (voteTime p r)))
    (h : JointCleanInvariant p E rho i) (s : Slot) (hle : s ≤ r)
    (reader : V) (hr : reader ∈ rho.honest) :
    cleanRunPath p rho i (GridCO.liveRoot (headState p rho s reader).base) ∧
      ∀ c, selectedPC p (headState p rho s reader) s = some c →
        cleanRunPath p rho i c.target := by
  set_option backward.isDefEq.respectTransparency false in
  let k := (rho.events.filter (fun e => decide (e.time ≤ voteTime p s - 1))).length
  have hk : k ≤ i := head_input_prefix_le p E rho hx.toScheduleWellFormed i v r s he hle
  have input : Run.stateBeforeTime (sapc p) rho (voteTime p s) reader =
      Run.stateBefore (sapc p) rho k reader :=
    congrFun (time_input_eq_event_prefix p E rho hx.toScheduleWellFormed _) reader
  constructor
  · apply CleanStateOnPath.liveRoot h.facts.chain
    rw [headState, input, clock_eq_preGate_of_no_gate p _ _ (voteTime_ne_gateTime p s)]
    exact (clockPreGate_clean p _ _ (h.facts.states k hk reader hr)).1
  · intro c hc
    rw [headState, input] at hc
    exact cleanRunPath_mono p rho hk
      (selectedPC_on_cleanRunPath p E rho hx cap k reader _ s c hc)

/-- Timely targets continue through the earlier HEADs of this prefix.
The base step uses q transfer; later steps reuse SA batch preservation
and genuine transfer. No new continuation field is added to the invariant. -/
theorem timely_continues_of_run_invariant {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (i : Nat) (v : V) (last : Slot)
    (he : rho.events[i]? = some (.tick v (voteTime p last)))
    (h : JointCleanInvariant p E rho i)
    (r : Slot) (b : Block) (source : HonestTimelySource p rho i r b) :
    ∀ s, r < s → s ≤ last → ∀ reader ∈ rho.honest,
      Block.Preceq b (headData p rho s reader).target := by
  set_option backward.isDefEq.respectTransparency false in
  have hb : cleanRunPath p rho i b :=
    Or.inr ⟨b, .timely r b cap source, GridCO.block_preceq_self b⟩
  obtain ⟨origin, ho, j, _, _, saved⟩ := source
  have sync (s : Slot) : E.t_GST ≤ earlyTime p s := by
    rw [hs.gst_zero]
    change 0 ≤ 4 * p.Δ * (s : Time) + 2 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg s]
  have horizon := (hs.execution.in_horizon _ (List.mem_of_getElem? he)).2
  have heads (s : Slot) (hsr : r + 1 ≤ s) : s ≤ last →
      ∀ reader ∈ rho.honest, Block.Preceq b (headData p rho s reader).target := by
    induction s, hsr using Nat.le_induction with
    | base =>
      intro hlast reader hr
      have roots := head_roots_on_run_path p E rho hs.execution cap i v last he h
        (r + 1) hlast reader hr
      have htime : voteTime p (r + 1) ≤ rho.horizon := by
        apply le_trans _ horizon
        have hle : ((r + 1 : Nat) : Time) ≤ last := by exact_mod_cast hlast
        change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ ≤
          4 * p.Δ * (last : Time) + p.Δ
        nlinarith [p.deltaPos]
      have ha : capBroken p (headState p rho (r + 1) reader) = false := by
        rw [headState, capBroken_clock]
        exact capBroken_false_beforeTime p E rho hs.execution cap reader _
      exact synchronous_timely_active_head_covers p E rho hs.execution hΔ hs.acceptedRelay
        r (sync r) origin reader ho hr htime b
        (savedTimely_candidate_at_early p E rho hs.execution.toScheduleWellFormed
          (j + 1) origin r b saved) ha (h.facts.chain.comparable _ _ roots.1 hb)
    | succ s hsr ih =>
      intro hlast reader hr
      have hfreeze : freezeTime p s ≤ rho.horizon := by
        apply le_trans _ horizon
        have hle : ((s + 1 : Nat) : Time) ≤ last := by exact_mod_cast hlast
        change 4 * p.Δ * (s : Time) + 3 * p.Δ ≤ 4 * p.Δ * (last : Time) + p.Δ
        push_cast at hle
        nlinarith [p.deltaPos]
      have hearly : earlyTime p s ≤ rho.horizon := by
        apply le_trans _ hfreeze
        change 4 * p.Δ * (s : Time) + 2 * p.Δ ≤ 4 * p.Δ * (s : Time) + 3 * p.Δ
        linarith [p.deltaPos]
      obtain ⟨c, hc, hp⟩ := sleepy_preserve_from_heads p E rho hΔ t₀ hs s hearly b
        (ih (Nat.le_of_succ_le hlast)) reader hr
      have roots := head_roots_on_run_path p E rho hs.execution cap i v last he h
        (s + 1) hlast reader hr
      exact synchronous_local_genuine_head_covers p E rho hs.execution hΔ hs.acceptedRelay
        s (sync s) hfreeze reader hr b c hc hp
        (h.facts.chain.comparable _ _ roots.1 hb)
        (fun cert selected => h.facts.chain.comparable _ _ (roots.2 cert selected) hb)
  intro s hrs
  exact heads s (Nat.succ_le_of_lt hrs)

/-- The selected PC at the next HEAD is below the pending raw result.
This discharges the capped PC transfer input from the chronological
invariant at that HEAD, without assuming that the future raw gate has
already entered the path. -/
theorem selectedPC_prefix_pending_genuine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (i : Nat) (reader : V) (r : Slot)
    (he : rho.events[i]? = some (.tick reader (voteTime p (r + 1))))
    (h : JointCleanInvariant p E rho i)
    (source : V) (hsource : source ∈ rho.honest) (b : Block)
    (raw : SA.confirmation p
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r = some b)
    (c : PC p.n) (selected : selectedPC p (headState p rho (r + 1) reader) (r + 1) = some c) :
    Block.Preceq c.target b := by
  set_option backward.isDefEq.respectTransparency false in
  have ha := capped_quorum_above_faults p rho cap
  have hslot := selectedPC_slot_lt_at_nextHead p E rho hs.execution ha reader r c selected
  have selected' : selectedPC p
      (clock p (Run.stateBefore (sapc p) rho i reader) (voteTime p (r + 1))) (r + 1) =
        some c := by
    rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed he]
    exact selected
  have valid := certificates_valid_at_fold p (rho.events.take i) reader
  have hc := selectedPC_valid p _ (clock_frozenPC_valid p _ _ valid.2 valid.1) _ c selected'
  rw [pcValid_eq_of_data p _ _ (clock_blocks p _ _) (clock_archive p _ _)] at hc
  obtain ⟨v, hv, j, hj, ht, saved⟩ := validPC_prior_timely p E rho hs.execution ha i reader c hc
  have timely : HonestTimelySource p rho i c.slot c.target :=
    ⟨v, hv, j, by omega, ht, saved⟩
  have coverage := timely_continues_of_run_invariant p E rho hΔ t₀ hs cap i reader (r + 1)
    he h c.slot c.target timely r hslot (Nat.le_succ r)
  have hearly : earlyTime p r ≤ rho.horizon := by
    apply le_trans _ (hs.execution.in_horizon _ (List.mem_of_getElem? he)).2
    change 4 * p.Δ * (r : Time) + 2 * p.Δ ≤
      4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast
    linarith [p.deltaPos]
  obtain ⟨d, hd, hp⟩ := sleepy_preserve_from_heads p E rho hΔ t₀ hs r hearly c.target
    coverage source hsource
  have eq : d = b := Option.some.inj (hd.symm.trans raw)
  exact eq ▸ hp

/-- Connect the capped PC step to the existing SA/Grid CO induction.
The remaining chronological induction must supply the HEAD invariants;
there is no whole-run SA projection or additional contract premise. -/
theorem clean_genuine_history_capped_of_head_invariants
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (cap : FaultBound (sapc p) (pcFaultCap p) rho)
    (r : Slot) (hh : gateTime p r ≤ rho.horizon)
    (heads : ∀ s, s ≤ r → ∀ i reader, reader ∈ rho.honest →
      rho.events[i]? = some (.tick reader (voteTime p (s + 1))) →
      JointCleanInvariant p E rho i) :
    GridCO.GenuineExtends (fun v => v ∈ rho.honest)
      (fun s v => SA.confirmation p
        (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s) r ∧
    GridCO.GenuineContinues (fun v => v ∈ rho.honest)
      (fun s v => SA.confirmation p
        (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s)
      (fun s v => (headData p rho (s + 1) v).target) r := by
  apply clean_genuine_history_of_pc p E rho hΔ t₀ hs r hh
  intro s hsr _ source hsource b raw reader hr cert _ selected
  have hgate := ((GridCO.gateTime_le_iff p.engine s r).mpr hsr).trans hh
  have hpub : PublicTime E (voteTime p (s + 1)) := by
    refine ⟨4 * (s + 1) + 1, ?_⟩
    change 4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ = _
    rw [hΔ]
    push_cast
    ring
  have hn : 0 ≤ voteTime p (s + 1) := by
    change 0 ≤ 4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg (s + 1)]
  have hhead : voteTime p (s + 1) ≤ rho.horizon := by
    apply le_trans _ hgate
    change 4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ ≤
      4 * p.Δ * (s : Time) + 6 * p.Δ
    push_cast
    linarith [p.deltaPos]
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (hs.execution.tick_total reader hr _ hpub hn hhead)
  exact Bool.or_eq_true_iff.mpr (Or.inl
    (selectedPC_prefix_pending_genuine p E rho hΔ t₀ hs cap i reader s hi
      (heads s hsr i reader hr hi) source hsource b raw cert selected))

end AvailableChain.SAPC
end
