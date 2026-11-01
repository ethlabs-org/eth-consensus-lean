module
public import AvailableChainSAPC.Proofs.GateRead
public import AvailableChainSA.Proofs.SlowWindow

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

theorem process_genuine (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    (process p st o).base.genuine = st.base.genuine := by
  apply process_base_invariant p (fun acc => acc.genuine = st.base.genuine)
  · intro acc obj ha
    unfold GridCO.admitVote
    split
    · dsimp only; split <;> exact ha
    · exact ha
  · intro acc obj b ha
    unfold GridCO.admitProposal
    dsimp only
    split_ifs <;> exact ha
  · rfl

/-- A new save has its own clock gate as source, even when the raw result
is empty or either gate guard rejects it. -/
theorem clock_genuine_origin (p : Params) {n : Nat} (st : State n) (t : Time)
    (r : Slot) (C : Option Block) (hm : (r, C) ∈ (clock p st t).base.genuine) :
    (r, C) ∈ st.base.genuine ∨ t = gateTime p r ∧
      C = SA.confirmation p (clockPreGate p st t).base r := by
  rw [clock_eq_gate_prestate] at hm
  dsimp only at hm
  split at hm
  · rename_i gateEq
    rw [gate_genuine] at hm
    rcases @GridCO.recordGenuine_origin GridCO.slowLeasePolicy n _ _ r _ C hm with
      old | ⟨eq, raw⟩
    · exact Or.inl (by simpa only [clockPreGate_base, GridCO.clockPreGate_genuine] using old)
    · subst r
      exact Or.inr ⟨by simpa using (Bool.and_eq_true_iff.mp gateEq).2, raw⟩
  · exact Or.inl (by simpa only [clockPreGate_base, GridCO.clockPreGate_genuine] using hm)

theorem clock_genuine_prefix (p : Params) {n : Nat} (st : State n) (t : Time) :
    st.base.genuine <+: (clock p st t).base.genuine := by
  rw [clock_eq_gate_prestate]
  dsimp only
  split
  · rw [gate_genuine]
    unfold GridCO.recordGenuine
    split
    · simp only [clockPreGate_base, GridCO.clockPreGate_genuine]
      exact List.prefix_append _ _
    · simp only [clockPreGate_base, GridCO.clockPreGate_genuine]
      exact List.prefix_refl _
  · simp only [clockPreGate_base, GridCO.clockPreGate_genuine]
    exact List.prefix_refl _

/-- The common clock-source theorem identifies each saved raw result.
This is a statement about the actual gate input, not a replay of receipts. -/
theorem run_genuine_origin {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (index : Nat) (v : V) (r : Slot) (C : Option Block)
    (hm : (r, C) ∈ (Run.stateBefore (sapc p) rho index v).base.genuine) :
    ∃ j < index, rho.events[j]? = some (.tick v (gateTime p r)) ∧
      C = SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r := by
  set_option backward.isDefEq.respectTransparency false in
  obtain ⟨j, hj, t, tick, time, raw⟩ := clock_field_origin (P := sapc p)
    (fun st => st.base.genuine) rfl (process_genuine p)
    (fun st t row => t = gateTime p row.1 ∧
      row.2 = SA.confirmation p (clockPreGate p st t).base row.1)
    (fun st t row hm => clock_genuine_origin p st t row.1 row.2 hm) rho index v (r, C) hm
  dsimp only at time raw
  subst t
  refine ⟨j, hj, tick, ?_⟩
  rw [clockPreGate_base] at raw
  have data := @GridCO.confirmation_eq_of_receiptData GridCO.slowLeasePolicy p.engine p.n
    _ (Run.stateBefore (sapc p) rho j v).base
    (GridCO.clockPreGate_receiptData p.engine _ (gateTime p r))
    (base_receiptStamped_at_fold p _ v) r
  have source := raw.trans data
  rw [stateBefore_tick_eq_stateBeforeTime hs tick] at source
  exact source

theorem time_input_savedGenuine_origin {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (cut : Time) (v : V) (r : Slot) (C : Option Block)
    (saved : GridCO.savedGenuine (Run.stateBeforeTime (sapc p) rho cut v).base r = some C) :
    gateTime p r < cut ∧
      C = SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r := by
  unfold GridCO.savedGenuine at saved
  obtain ⟨row, found, eq⟩ := Option.map_eq_some_iff.mp saved
  have label : row.1 = r := by simpa using List.find?_some found
  have pair : row = (r, C) := Prod.ext label eq
  have member := pair ▸ List.mem_of_find?_eq_some found
  rw [time_input_eq_event_prefix p E rho hs] at member
  obtain ⟨j, hj, tick, raw⟩ := run_genuine_origin p E rho hs _ v r C member
  exact ⟨Int.le_sub_one_iff.mp ((index_lt_read_length_iff hs (cut - 1) tick).mp hj), raw⟩

/-- Every completed gate has its exact immutable save at later inputs.
Sleeping readers have the same public clock obligation. -/
theorem time_input_savedGenuine {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ)
    (cut : Time) (v : V) (hv : v ∈ rho.honest) (r : Slot)
    (hlt : gateTime p r < cut) (hh : gateTime p r ≤ rho.horizon) :
    GridCO.savedGenuine (Run.stateBeforeTime (sapc p) rho cut v).base r =
      some (SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r) := by
  set_option backward.isDefEq.respectTransparency false in
  cases saved : GridCO.savedGenuine (Run.stateBeforeTime (sapc p) rho cut v).base r with
  | some C => exact congrArg some (time_input_savedGenuine_origin p E rho hs cut v r C saved).2
  | none =>
    have publicTime : PublicTime E (gateTime p r) := by
      refine ⟨4 * r + 6, ?_⟩
      change 4 * p.Δ * (r : Time) + 6 * p.Δ = _
      rw [hΔ]
      push_cast
      ring
    have nonneg : 0 ≤ gateTime p r := by
      change 0 ≤ 4 * p.Δ * (r : Time) + 6 * p.Δ
      nlinarith [p.deltaPos, Int.natCast_nonneg r]
    obtain ⟨i, tick⟩ := List.mem_iff_getElem?.mp (hs.tick_total v hv _ publicTime nonneg hh)
    let st := Run.stateBeforeTime (sapc p) rho (gateTime p r) v
    have empty : GridCO.savedGenuine st.base r = none := by
      cases he : GridCO.savedGenuine st.base r with
      | none => rfl
      | some C =>
        exact (lt_irrefl _ (time_input_savedGenuine_origin p E rho hs _ v r C he).1).elim
    have post : (r, SA.confirmation p st.base r) ∈
        (Run.stateBefore (sapc p) rho (i + 1) v).base.genuine := by
      rw [stateBefore_succ_event tick]
      simp only [World.step, Function.update_self]
      change _ ∈ (clock p _ _).base.genuine
      rw [stateBefore_tick_eq_stateBeforeTime hs tick, clock_at_gate, gate_genuine]
      have data := @GridCO.confirmation_eq_of_receiptData GridCO.slowLeasePolicy p.engine p.n
        _ st.base (GridCO.clockPreGate_receiptData p.engine st.base (gateTime p r))
        (base_receiptStamped_at_fold p _ v) r
      simp only [clockPreGate_base, GridCO.recordGenuine, GridCO.savedGenuine,
        GridCO.clockPreGate_genuine]
      change _ ∈ (if true && !(GridCO.savedGenuine st.base r).isSome then _ else _)
      rw [empty]
      simp only [Option.isSome_none, Bool.not_false, Bool.and_self, ↓reduceIte,
        List.mem_append, List.mem_singleton, Prod.mk.injEq, true_and]
      exact Or.inr data.symm
    let finish := (rho.events.filter (fun e => decide (e.time ≤ cut - 1))).length
    have hif : i + 1 ≤ finish := Nat.succ_le_of_lt
      ((index_lt_read_length_iff hs (cut - 1) tick).mpr (Int.le_sub_one_iff.mpr hlt))
    have grows :=  stateBefore_field_prefix (P := sapc p) (fun st => st.base.genuine)
      (clock_genuine_prefix p) (fun st o => by
        change st.base.genuine <+: (process p st o).base.genuine
        rw [process_genuine])
      rho hif v
    have member := grows.subset post
    have noneAt := saved
    rw [time_input_eq_event_prefix p E rho hs] at noneAt
    have nofind : ((Run.stateBefore (sapc p) rho finish v).base.genuine.find?
        (fun row => row.1 == r)) = none := by
      simpa only [GridCO.savedGenuine, Option.map_eq_none_iff] using noneAt
    have bad := List.find?_eq_none.mp nofind _ member
    simp at bad

/-- Actual covering raw results fill the slow window. Missing labels and
PC-vetoed stable writes are treated exactly as in SA. -/
theorem slowEligible_of_input_covers {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hs : ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ)
    (v : V) (hv : v ∈ rho.honest) (r : Slot) (B : Block)
    (hlen : p.k ≤ r + 1) (hh : gateTime p r ≤ rho.horizon)
    (results : ∀ s, s < r → r + 1 ≤ s + p.k → ∃ C,
      SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s = some C ∧
        Block.Preceq B C) :
    SA.slowEligible p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r B = true := by
  apply Bool.and_eq_true_iff.mpr
  refine ⟨decide_eq_true hlen, List.all_eq_true.mpr ?_⟩
  intro j hj
  have hj : j < p.k - 1 := List.mem_range.mp hj
  have hsr : r - (j + 1) < r := by have := p.kLarge; simp only [Slot] at *; omega
  have window : r + 1 ≤ r - (j + 1) + p.k := by simp only [Slot] at *; omega
  obtain ⟨C, raw, below⟩ := results _ hsr window
  have time : gateTime p (r - (j + 1)) < gateTime p r := by
    apply lt_of_not_ge
    intro h
    exact (not_le.mpr hsr) ((GridCO.gateTime_le_iff p.engine _ _).mp h)
  have saved := time_input_savedGenuine p E rho hs hΔ (gateTime p r) v hv
    (r - (j + 1)) time (time.le.trans hh)
  rw [saved, raw]
  exact below

end AvailableChain.SAPC
end
