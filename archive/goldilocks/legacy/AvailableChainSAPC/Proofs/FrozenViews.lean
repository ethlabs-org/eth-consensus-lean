module
public import AvailableChainSAPC.Proofs.BaseViews

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- The base freeze is unchanged by PC saves, release, and the guarded
gate. The updated local clock is explicit for arbitrary input states. -/
theorem clock_base_frozen (p : Params) {n : Nat} (st : State n) (t : Time) :
    (clock p st t).base.frozen =
      let r := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
      if 0 ≤ t - 3 * p.Δ && t == freezeTime p r then
        st.base.frozen ++ [(r, GridCO.freezeView p.engine { st.base with now := t } r)]
      else st.base.frozen := by
  unfold clock
  dsimp only
  split_ifs <;> simp only [gate, gateWithPC_frozen, saveTimely]
  all_goals (try split_ifs) <;> rfl

theorem clock_base_frozen_origin (p : Params) {n : Nat} (st : State n) (t : Time)
    (r : Slot) (view : List (GridCO.Wire n) × List (GridCO.Wire n) × List Block)
    (hm : (r, view) ∈ (clock p st t).base.frozen) :
    (r, view) ∈ st.base.frozen ∨ t = freezeTime p r ∧
      view = GridCO.freezeView p.engine { st.base with now := t } r := by
  rw [clock_base_frozen] at hm
  dsimp only at hm
  split at hm
  · rename_i ht
    rcases List.mem_append.mp hm with hold | hnew
    · exact Or.inl hold
    · have he := List.mem_singleton.mp hnew
      have hr := congrArg Prod.fst he
      have hv := congrArg Prod.snd he
      dsimp only at hr hv
      refine Or.inr ⟨?_, ?_⟩
      · simpa only [← hr, beq_iff_eq] using (Bool.and_eq_true_iff.mp ht).2
      · simpa only [← hr] using hv
  · exact Or.inl hm

/-- A saved ordinary view has an actual local freeze source. It cannot
come from a later PC receipt or from a replayed early save. -/
theorem base_frozen_origin_before {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (index : Nat) (v : V) (r : Slot)
    (view : List (GridCO.Wire p.n) × List (GridCO.Wire p.n) × List Block)
    (hm : (r, view) ∈ (Run.stateBefore (sapc p) rho index v).base.frozen) :
    ∃ j < index, rho.events[j]? = some (.tick v (freezeTime p r)) ∧
      view = GridCO.freezeView p.engine (Run.stateBefore (sapc p) rho j v).base r := by
  obtain ⟨j, hj, t, ht, htime, hv⟩ := clock_field_origin (P := sapc p)
    (fun st => st.base.frozen) rfl (process_base_frozen p)
    (fun st t row => t = freezeTime p row.1 ∧
      row.2 = GridCO.freezeView p.engine { st.base with now := t } row.1)
    (fun st t row hm => clock_base_frozen_origin p st t row.1 row.2 hm)
    rho index v (r, view) hm
  subst t
  refine ⟨j, hj, ht, hv.trans ?_⟩
  exact GridCO.freezeView_eq_of_receiptData p.engine
    { (Run.stateBefore (sapc p) rho j v).base with now := freezeTime p r }
    (Run.stateBefore (sapc p) rho j v).base rfl (base_receiptStamped_at_fold p _ v) r

theorem stateBefore_base_frozen_prefix {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) {i j : Nat} (hij : i ≤ j) (v : V) :
    (Run.stateBefore (sapc p) rho i v).base.frozen <+:
      (Run.stateBefore (sapc p) rho j v).base.frozen := by
  set_option backward.isDefEq.respectTransparency false in
  apply stateBefore_field_prefix (P := sapc p) (fun st => st.base.frozen) ?_ ?_ rho hij v
  · intro st t
    change st.base.frozen <+: (clock p st t).base.frozen
    rw [clock_base_frozen]
    dsimp only
    split <;> simp
  · intro st o
    change st.base.frozen <+: (process p st o).base.frozen
    rw [process_base_frozen]

theorem base_frozenAt_after_freeze {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (r : Slot) (v : V) (hv : v ∈ rho.honest)
    (cut : Time) (hc : freezeTime p r < cut) (hh : freezeTime p r ≤ rho.horizon) :
    GridCO.frozenAt (Run.stateBeforeTime (sapc p) rho cut v).base r =
      some (GridCO.freezeView p.engine
        (Run.stateBeforeTime (sapc p) rho (freezeTime p r) v).base r) := by
  set_option backward.isDefEq.respectTransparency false in
  have hpub : PublicTime E (freezeTime p r) := by
    refine ⟨4 * r + 3, ?_⟩
    change 4 * p.Δ * (r : Time) + 3 * p.Δ = _
    rw [hΔ]
    push_cast
    ring
  have hzero : 0 ≤ freezeTime p r := by
    change 0 ≤ 4 * p.Δ * (r : Time) + 3 * p.Δ
    have := p.deltaPos
    positivity
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (hs.tick_total v hv _ hpub hzero hh)
  have hstate := stateBefore_tick_eq_stateBeforeTime hs hi
  let view := GridCO.freezeView p.engine
    (Run.stateBeforeTime (sapc p) rho (freezeTime p r) v).base r
  have hpost : (r, view) ∈ (Run.stateBefore (sapc p) rho (i + 1) v).base.frozen := by
    rw [stateBefore_succ_event hi]
    simp only [World.step, Function.update_self]
    change (r, view) ∈ (clock p _ (freezeTime p r)).base.frozen
    rw [clock_base_frozen]
    have he := GridCO.freezeView_eq_of_receiptData p.engine
      { (Run.stateBefore (sapc p) rho i v).base with now := freezeTime p r }
      (Run.stateBefore (sapc p) rho i v).base rfl (base_receiptStamped_at_fold p _ v) r
    have ht : freezeTime p r - 3 * p.Δ = 4 * p.Δ * (r : Time) := by
      change 4 * p.Δ * (r : Time) + 3 * p.Δ - 3 * p.Δ = _
      ring
    have hd : 4 * p.Δ ≠ 0 := ne_of_gt (by linarith [p.deltaPos])
    simp only [ht, Int.mul_ediv_cancel_left _ hd, Int.toNat_natCast]
    have hp : 0 ≤ 4 * p.Δ * (r : Time) := by
      have := p.deltaPos
      positivity
    simp only [hp, decide_true, beq_self_eq_true, Bool.and_self, ↓reduceIte]
    apply List.mem_append_right
    apply List.mem_singleton.mpr
    exact Prod.ext rfl (by simpa only [hstate] using he.symm)
  have hil : i < (rho.events.filter (fun e => decide (e.time ≤ cut - 1))).length :=
    (index_lt_read_length_iff hs (cut - 1) hi).mpr (Int.le_sub_one_iff.mpr hc)
  rw [time_input_eq_event_prefix p E rho hs]
  have hm := (stateBefore_base_frozen_prefix p rho (Nat.succ_le_of_lt hil) v).subset hpost
  unfold GridCO.frozenAt
  cases hf : (Run.stateBefore (sapc p) rho
      (rho.events.filter (fun e => decide (e.time ≤ cut - 1))).length v).base.frozen.find?
      (fun row => row.1 == r) with
  | none => have h := List.find?_eq_none.mp hf _ hm; simp at h
  | some row =>
      have he : row.1 = r := by simpa using List.find?_some hf
      obtain ⟨j, _, hj, hview⟩ := base_frozen_origin_before p rho _ v row.1 row.2
        (List.mem_of_find?_eq_some hf)
      rw [he] at hj hview
      rw [stateBefore_tick_eq_stateBeforeTime hs hj] at hview
      exact congrArg some hview

end AvailableChain.SAPC
end
