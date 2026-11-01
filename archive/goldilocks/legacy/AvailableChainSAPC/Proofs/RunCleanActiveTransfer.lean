module
public import AvailableChainSAPC.Proofs.RunCleanUncapped
public import AvailableChainSAPC.Proofs.QuorumGenuine

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- An active input supplies first transfer for every eligible timely
source. Induction on the HEAD label then supplies continuation. Finite
roots use their raw sources; selected PCs use earlier honest preparations.
No fault cap or path-membership premise for the timely target is needed. -/
theorem timely_continues_before_active_input
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (i : Nat) (e : Event V (sapc p).Object) (he : rho.events[i]? = some e)
    (h : JointCleanInvariant p E rho i)
    (observer : V) (ho : observer ∈ rho.honest)
    (active : capBroken p (Run.stateBefore (sapc p) rho i observer) = false)
    (s r : Slot) (b : Block) (source : HonestTimelySource p rho i r b)
    (hgate : gateTime p r ≤ e.time) (hrs : r < s) (htime : voteTime p s < e.time)
    (reader : V) (hr : reader ∈ rho.honest) :
    Block.Preceq b (headData p rho s reader).target := by
  set_option backward.isDefEq.respectTransparency false in
  have ha := sleepy_quorum_above_faults p E rho t₀ hs
  have horizon := (hs.execution.in_horizon _ (List.mem_of_getElem? he)).2
  have sync (a : Slot) : E.t_GST ≤ earlyTime p a := by
    rw [hs.gst_zero]
    change 0 ≤ 4 * p.Δ * (a : Time) + 2 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg a]
  have headTick (a : Slot) (ht : voteTime p a < e.time) (v : V) (hv : v ∈ rho.honest) :
      ∃ k < i, rho.events[k]? = some (.tick v (voteTime p a)) := by
    have pub : PublicTime E (voteTime p a) := by
      refine ⟨4 * a + 1, ?_⟩
      change 4 * p.Δ * (a : Time) + p.Δ = _
      rw [hΔ]
      push_cast
      ring
    have nonneg : 0 ≤ voteTime p a := by
      change 0 ≤ 4 * p.Δ * (a : Time) + p.Δ
      nlinarith [p.deltaPos, Int.natCast_nonneg a]
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp
      (hs.execution.tick_total v hv _ pub nonneg (ht.le.trans horizon))
    exact ⟨k, eventIndex_lt_of_time_lt hs.execution.toScheduleWellFormed hk he ht, hk⟩
  have headTime (a z : Slot) (hle : a ≤ z) : voteTime p a ≤ voteTime p z := by
    have cast : (a : Time) ≤ z := by exact_mod_cast hle
    change 4 * p.Δ * (a : Time) + p.Δ ≤ 4 * p.Δ * (z : Time) + p.Δ
    nlinarith [p.deltaPos]
  induction s using Nat.strong_induction_on generalizing r b reader with
  | h s ih =>
    cases s with
    | zero => exact (Nat.not_lt_zero r hrs).elim
    | succ s =>
      by_cases eq : r = s
      · subst r
        exact timely_next_heads_of_active_input p E rho hΔ t₀ hs i e he h s b source
          hgate observer ho active reader hr
      have hrs' : r < s := lt_of_le_of_ne (Nat.le_of_lt_succ hrs) eq
      have earlier : voteTime p s < e.time := (headTime s (s + 1) (Nat.le_succ s)).trans_lt htime
      have coverage := ih s (Nat.lt_succ_self s) r b source hgate hrs' earlier
      have earlyBound : earlyTime p s ≤ rho.horizon := by
        apply le_trans _ (htime.le.trans horizon)
        change 4 * p.Δ * (s : Time) + 2 * p.Δ ≤
          4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ
        push_cast
        linarith [p.deltaPos]
      have freezeBound : freezeTime p s ≤ rho.horizon := by
        apply le_trans _ (htime.le.trans horizon)
        change 4 * p.Δ * (s : Time) + 3 * p.Δ ≤
          4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ
        push_cast
        linarith [p.deltaPos]
      obtain ⟨c, raw, hpending⟩ := sleepy_preserve_from_heads p E rho hΔ t₀ hs s
        earlyBound b coverage reader hr
      have roots : Block.Compatible (GridCO.liveRoot (headState p rho (s + 1) reader).base) b := by
        rcases (GridCO.liveRoot_is_deepest (headState p rho (s + 1) reader).base).1 with hg | hm
        · rw [hg]
          exact Bool.or_eq_true_iff.mpr (Or.inl (GridCO.genesis_prefix b))
        obtain ⟨⟨a, g, d⟩, hm, ht⟩ := List.mem_filterMap.mp hm
        dsimp only at ht
        split at ht
        · have rootEq := Option.some.inj ht
          obtain ⟨u, z, hus, hz, hp⟩ := nextHead_target_genuine_origin p E rho
            hs.execution.toScheduleWellFormed s reader a g d hm
          have gateTimeLt : gateTime p u < e.time := by
            apply lt_trans _ htime
            have cast : (u : Time) + 1 ≤ s := by exact_mod_cast hus
            change 4 * p.Δ * (u : Time) + 6 * p.Δ <
              4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ
            push_cast
            nlinarith [p.deltaPos]
          have compatible : Block.Compatible z b := by
            rcases lt_trichotomy u r with hur | rfl | hru
            · obtain ⟨v, hv, j, _, _, saved⟩ := source
              apply Bool.or_eq_true_iff.mpr
              apply Or.inl
              apply timely_prefix_of_head_coverage p E rho hs.execution ha (j + 1) v r z b saved
              intro w hw
              have pub : PublicTime E (gateTime p u) := by
                refine ⟨4 * u + 6, ?_⟩
                change 4 * p.Δ * (u : Time) + 6 * p.Δ = _
                rw [hΔ]
                push_cast
                ring
              have nonneg : 0 ≤ gateTime p u := by
                change 0 ≤ 4 * p.Δ * (u : Time) + 6 * p.Δ
                nlinarith [p.deltaPos, Int.natCast_nonneg u]
              obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp
                (hs.execution.tick_total reader hr _ pub nonneg (gateTimeLt.le.trans horizon))
              have hmi := eventIndex_lt_of_time_lt hs.execution.toScheduleWellFormed
                hm he gateTimeLt
              obtain ⟨k, hki, hk⟩ := headTick r
                ((headTime r s hrs'.le).trans_lt earlier) w hw
              have raw' : SA.confirmation p (Run.stateBefore (sapc p) rho m reader).base u =
                  some z := by
                rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed hm]
                exact hz
              have cover := h.facts.transferred m hmi reader hr u z hm raw'
                k hki w hw r hur hk
              rw [stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed hk] at cover
              exact cover
            · obtain ⟨v, hv, j, _, _, saved⟩ := source
              obtain ⟨forward, _⟩ := synchronous_transfer_relays p E rho hΔ hs.acceptedRelay u
                (sync u) (gateTimeLt.le.trans horizon)
              apply timely_compatible_confirmation p E rho hs.execution.toScheduleWellFormed
                u v reader hv hr _ b z
                (savedTimely_candidate_at_early p E rho hs.execution.toScheduleWellFormed
                  (j + 1) v u b saved) hz
              intro w hw k obj t ht accepted other honest missing
              obtain ⟨t', ht', k', hk'⟩ := forward w hw k obj t ht accepted other honest missing
              refine ⟨t', ht'.trans_le ?_, k', hk'⟩
              change 4 * p.Δ * (u : Time) + 3 * p.Δ ≤ 4 * p.Δ * (u : Time) + 6 * p.Δ
              linarith [p.deltaPos]
            · have headCover := ih u (hus.trans_le (Nat.le_succ s)) r b source hgate hru
                ((headTime u s hus.le).trans_lt earlier)
              have earlyU : earlyTime p u ≤ rho.horizon := by
                apply le_trans _ (gateTimeLt.le.trans horizon)
                change 4 * p.Δ * (u : Time) + 2 * p.Δ ≤ 4 * p.Δ * (u : Time) + 6 * p.Δ
                linarith [p.deltaPos]
              obtain ⟨z', hz', hp'⟩ := sleepy_preserve_from_heads p E rho hΔ t₀ hs u
                earlyU b headCover reader hr
              exact Bool.or_eq_true_iff.mpr (Or.inr ((Option.some.inj (hz'.symm.trans hz)) ▸ hp'))
          rw [← rootEq]
          rcases Bool.or_eq_true_iff.mp compatible with hzb | hbz
          · exact Bool.or_eq_true_iff.mpr (Or.inl (GridCO.prefix_trans a z b hp hzb))
          · exact GridCO.ancestors_compatible a b z hp hbz
        · contradiction
      apply synchronous_local_genuine_activePC_head_covers p E rho hs.execution hΔ
        hs.acceptedRelay s (sync s) freezeBound reader hr b c raw hpending roots
      intro _ cert selected
      have slot := selectedPC_slot_lt_at_nextHead p E rho hs.execution ha reader s cert selected
      obtain ⟨k, hki, hk⟩ := headTick (s + 1) htime reader hr
      have selected' := selected
      rw [headState, ← stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed hk]
        at selected'
      have valid := certificates_valid_at_fold p (rho.events.take k) reader
      have valid' := selectedPC_valid p _
        (clock_frozenPC_valid p _ _ valid.2 valid.1) _ cert selected'
      rw [pcValid_eq_of_data p _ _ (clock_blocks p _ _) (clock_archive p _ _)] at valid'
      have src := (h.facts.certificates k hki.le reader hr cert valid').1
      obtain ⟨v, hv, j, hj, tick, saved⟩ := src
      have src : HonestTimelySource p rho i cert.slot cert.target :=
        ⟨v, hv, j, hj.trans hki, tick, saved⟩
      have certGate : gateTime p cert.slot ≤ e.time := by
        apply le_trans _ htime.le
        have cast : (cert.slot : Time) + 1 ≤ s := by exact_mod_cast slot
        change 4 * p.Δ * (cert.slot : Time) + 6 * p.Δ ≤
          4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ
        push_cast
        nlinarith [p.deltaPos]
      rcases lt_trichotomy cert.slot r with hcr | eq | hrc
      · obtain ⟨w, _, m, _, _, savedB⟩ := source
        exact Bool.or_eq_true_iff.mpr (Or.inl
          (timely_prefix_of_head_coverage p E rho hs.execution ha (m + 1) w r cert.target b
            savedB (ih r hrs cert.slot cert.target src certGate hcr
              ((headTime r s hrs'.le).trans_lt earlier))))
      · have certCover := timely_next_heads_of_active_input p E rho hΔ t₀ hs i e he h
          cert.slot cert.target src certGate observer ho active reader hr
        have bCover := timely_next_heads_of_active_input p E rho hΔ t₀ hs i e he h
          r b source hgate observer ho active reader hr
        rw [eq] at certCover
        exact GridCO.ancestors_compatible cert.target b _ certCover bCover
      · exact Bool.or_eq_true_iff.mpr (Or.inr
          (timely_prefix_of_head_coverage p E rho hs.execution ha (j + 1) v cert.slot b cert.target
            saved (ih cert.slot (slot.trans_le (Nat.le_succ s)) r b source hgate hrc
              ((headTime cert.slot s slot.le).trans_lt earlier))))

/-- At an active HEAD, the selected PC is below the pending genuine
result. The strict ack bound and uncapped timely continuation discharge
this PC input of the shared SA history induction. -/
theorem selectedPC_prefix_pending_genuine_of_active
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (i : Nat) (reader : V) (hr : reader ∈ rho.honest) (r : Slot)
    (he : rho.events[i]? = some (.tick reader (voteTime p (r + 1))))
    (h : JointCleanInvariant p E rho i)
    (active : capBroken p (headState p rho (r + 1) reader) = false)
    (source : V) (hsource : source ∈ rho.honest) (b : Block)
    (raw : SA.confirmation p
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r = some b)
    (c : PC p.n)
    (selected : selectedPC p (headState p rho (r + 1) reader) (r + 1) = some c) :
    Block.Preceq c.target b := by
  set_option backward.isDefEq.respectTransparency false in
  have ha := sleepy_quorum_above_faults p E rho t₀ hs
  have slot := selectedPC_slot_lt_at_nextHead p E rho hs.execution ha reader r c selected
  have selected' := selected
  rw [headState, ← stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed he]
    at selected'
  have valid := certificates_valid_at_fold p (rho.events.take i) reader
  have hc := selectedPC_valid p _ (clock_frozenPC_valid p _ _ valid.2 valid.1) _ c selected'
  rw [pcValid_eq_of_data p _ _ (clock_blocks p _ _) (clock_archive p _ _)] at hc
  have timely := (h.facts.certificates i (le_refl _) reader hr c hc).1
  rw [headState, capBroken_clock,
    ← stateBefore_tick_eq_stateBeforeTime hs.execution.toScheduleWellFormed he] at active
  have hgate : gateTime p c.slot ≤ voteTime p (r + 1) := by
    have cast : (c.slot : Time) + 1 ≤ r := by exact_mod_cast slot
    change 4 * p.Δ * (c.slot : Time) + 6 * p.Δ ≤
      4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast
    nlinarith [p.deltaPos]
  have ht : voteTime p r < voteTime p (r + 1) := by
    change 4 * p.Δ * (r : Time) + p.Δ <
      4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast
    linarith [p.deltaPos]
  have coverage := timely_continues_before_active_input p E rho hΔ t₀ hs i _ he h
    reader hr active r c.slot c.target timely hgate slot ht
  have earlyBound : earlyTime p r ≤ rho.horizon := by
    apply le_trans _ (hs.execution.in_horizon _ (List.mem_of_getElem? he)).2
    change 4 * p.Δ * (r : Time) + 2 * p.Δ ≤
      4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    push_cast
    linarith [p.deltaPos]
  obtain ⟨d, hd, hp⟩ := sleepy_preserve_from_heads p E rho hΔ t₀ hs r earlyBound c.target
    coverage source hsource
  exact (Option.some.inj (hd.symm.trans raw)) ▸ hp

/-- The shared SA/Grid CO induction now needs only earlier chronological
HEAD invariants, without the cap. Disabled HEADs use the SA projection;
active HEADs use the selected-PC prefix theorem. -/
theorem clean_genuine_history_of_head_invariants
    {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
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
  intro s hsr _ source hsource b raw reader hr cert active selected
  have hgate := ((GridCO.gateTime_le_iff p.engine s r).mpr hsr).trans hh
  have pub : PublicTime E (voteTime p (s + 1)) := by
    refine ⟨4 * (s + 1) + 1, ?_⟩
    change 4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ = _
    rw [hΔ]
    push_cast
    ring
  have nonneg : 0 ≤ voteTime p (s + 1) := by
    change 0 ≤ 4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg (s + 1)]
  have bound : voteTime p (s + 1) ≤ rho.horizon := by
    apply le_trans _ hgate
    change 4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ ≤
      4 * p.Δ * (s : Time) + 6 * p.Δ
    push_cast
    linarith [p.deltaPos]
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp
    (hs.execution.tick_total reader hr _ pub nonneg bound)
  exact Bool.or_eq_true_iff.mpr (Or.inl
    (selectedPC_prefix_pending_genuine_of_active p E rho hΔ t₀ hs i reader hr s hi
      (heads s hsr i reader hr hi) active source hsource b raw cert selected))

/-- The raw history and its pending HEAD continuation at an early/gate
input follow from that input's invariant. This includes disabled readers
whose preceding HEAD was in mixed mode. -/
theorem clean_history_before_tick {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
    (i : Nat) (reader : V) (t : Time)
    (he : rho.events[i]? = some (.tick reader t))
    (h : JointCleanInvariant p E rho i) (r : Slot) (bound : gateTime p r ≤ t) :
    GridCO.GenuineExtends (fun v => v ∈ rho.honest)
      (fun s v => SA.confirmation p
        (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s) r ∧
    GridCO.GenuineContinues (fun v => v ∈ rho.honest)
      (fun s v => SA.confirmation p
        (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s)
      (fun s v => (headData p rho (s + 1) v).target) r := by
  apply clean_genuine_history_of_head_invariants p E rho hΔ t₀ hs r
    (bound.trans (hs.execution.in_horizon _ (List.mem_of_getElem? he)).2)
  intro s hsr j v _ tick
  have time : voteTime p (s + 1) < t := by
    apply lt_of_lt_of_le _ bound
    have cast : (s : Time) ≤ r := by exact_mod_cast hsr
    change 4 * p.Δ * ((s + 1 : Nat) : Time) + p.Δ <
      4 * p.Δ * (r : Time) + 6 * p.Δ
    push_cast
    nlinarith [p.deltaPos]
  exact h.restrict hs.execution (sleepy_quorum_above_faults p E rho t₀ hs)
    (eventIndex_lt_of_time_lt hs.execution.toScheduleWellFormed tick he time).le


/-- The raw history and its pending HEAD continuation at an early/gate
input follow from that input's invariant. This includes disabled readers
whose preceding HEAD was in mixed mode. -/
theorem clean_history_before_early {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (t₀ : Time) (hs : SleepyRegime (sapc p) E (sapcInterface p).toInterface rho t₀)
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
  have bound : gateTime p r ≤ earlyTime p last := by
    have cast : (r : Time) + 1 ≤ last := by exact_mod_cast hr
    change 4 * p.Δ * (r : Time) + 6 * p.Δ ≤ 4 * p.Δ * (last : Time) + 2 * p.Δ
    nlinarith [p.deltaPos]
  exact clean_history_before_tick p E rho hΔ t₀ hs i reader _ he h r bound

end AvailableChain.SAPC
end
