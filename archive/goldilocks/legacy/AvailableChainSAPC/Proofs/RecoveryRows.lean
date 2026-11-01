module
public import AvailableChainSAPC.Proofs.SlowHistory
public import AvailableChainSAPC.Proofs.RecoveryTransfer
public import AvailableChainKit.Engine.SourceHistory

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- An exact lease has an actual gate source, also when the PC vetoes S. -/
theorem clock_row_source (p : Params) {n : Nat} (st : State n) (t : Time)
    (B : Block) (g : Nat) (d : Time)
    (row : (B, g, d) ∈ (clock p st t).base.obligations) :
    (B, g, d) ∈ st.base.obligations ∨ ∃ r C,
      t = gateTime p r ∧ SA.confirmation p (clockPreGate p st t).base r = some C ∧
      Block.Preceq B C ∧ g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.engine n .block
        (clockPreGate p st t).base r B ∧ d = gateTime p r + lifetime p := by
  rw [clock_eq_gate_prestate] at row
  dsimp only at row
  split at row
  · rename_i gateEq
    rcases gateWithPC_row_origin p _ _ _ B g d row with old | ⟨C, raw, below, admitted, _, deadline⟩
    · exact Or.inl (GridCO.clockPreGate_obligations_subset p.engine st.base t _
        (by simpa only [clockPreGate_base] using old))
    · exact Or.inr ⟨_, C, by simpa using (Bool.and_eq_true_iff.mp gateEq).2,
        raw, below, admitted, deadline⟩
  · exact Or.inl (GridCO.clockPreGate_obligations_subset p.engine st.base t _
      (by simpa only [clockPreGate_base] using row))

/-- The generic engine supplies the source event. Receipt invariance then
moves the raw result and admission test to the strict gate input. -/
theorem run_row_admitted_source {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (index : Nat) (v : V) (B : Block) (g : Nat) (d : Time)
    (row : (B, g, d) ∈ (Run.stateBefore (sapc p) rho index v).base.obligations) :
    ∃ j < index, ∃ r C, rho.events[j]? = some (.tick v (gateTime p r)) ∧
      SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some C ∧
      Block.Preceq B C ∧ g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.engine p.n .block
        (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r B ∧
      d = gateTime p r + lifetime p := by
  set_option backward.isDefEq.respectTransparency false in
  obtain ⟨j, hj, t, tick, r, C, time, raw, below, admitted, deadline⟩ :=
    clock_field_origin (P := sapc p) (fun st => st.base.obligations) rfl (process_obligations p)
      (fun st t row => ∃ r C, t = gateTime p r ∧
        SA.confirmation p (clockPreGate p st t).base r = some C ∧
        Block.Preceq row.1 C ∧ row.2.1 ∈
          @GridCO.admissionLevels GridCO.slowLeasePolicy p.engine p.n .block
            (clockPreGate p st t).base r row.1 ∧ row.2.2 = gateTime p r + lifetime p)
      (fun st t row hm => clock_row_source p st t row.1 row.2.1 row.2.2 hm)
      rho index v (B, g, d) row
  subst t
  rw [clockPreGate_base] at raw admitted
  have stamped : GridCO.ReceiptStamped (Run.stateBefore (sapc p) rho j v).base :=
    base_receiptStamped_at_fold p (rho.events.take j) v
  unfold SA.confirmation at raw
  rw [@GridCO.confirmation_eq_of_receiptData GridCO.slowLeasePolicy p.engine p.n _
    (Run.stateBefore (sapc p) rho j v).base
    (GridCO.clockPreGate_receiptData p.engine _ _) stamped] at raw
  rw [@GridCO.admissionLevels_preGate GridCO.slowLeasePolicy p.engine p.n _ _ stamped] at admitted
  rw [stateBefore_tick_eq_stateBeforeTime hs tick] at raw admitted
  exact ⟨j, hj, r, C, tick, raw, below, admitted, deadline⟩

theorem time_input_row_admitted_source {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (cut : Time) (v : V) (B : Block) (g : Nat) (d : Time)
    (row : (B, g, d) ∈ (Run.stateBeforeTime (sapc p) rho cut v).base.obligations) :
    ∃ r C, gateTime p r < cut ∧
      SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r = some C ∧
      Block.Preceq B C ∧ g ∈ @GridCO.admissionLevels GridCO.slowLeasePolicy p.engine p.n .block
        (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r B ∧
      d = gateTime p r + lifetime p := by
  rw [time_input_eq_event_prefix p E rho hs] at row
  obtain ⟨j, hj, r, C, tick, rest⟩ := run_row_admitted_source p E rho hs _ v B g d row
  exact ⟨r, C, Int.le_sub_one_iff.mp ((index_lt_read_length_iff hs (cut - 1) tick).mp hj), rest⟩

/-- The HEAD clock uses exactly SA's expiry and release filter. -/
theorem head_row_survives_release {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (r : Slot) (v : V) (B : Block) (g : Nat) (d : Time)
    (row : (B, g, d) ∈ (headState p rho (r + 1) v).base.obligations) :
    (B, g, d) ∈ (Run.stateBeforeTime (sapc p) rho (voteTime p (r + 1)) v).base.obligations ∧
      voteTime p (r + 1) < d ∧ GridCO.releaseCount p.engine
        (Run.stateBeforeTime (sapc p) rho (voteTime p (r + 1)) v).base r B < g := by
  set_option backward.isDefEq.respectTransparency false in
  rw [headState, clock_eq_preGate_of_no_gate p _ _ (voteTime_ne_gateTime p (r + 1)),
    clockPreGate_base] at row
  have time : voteTime p (r + 1) = GridCO.releaseTime p.engine r := by
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ = 4 * p.Δ * (r : Time) + 5 * p.Δ
    push_cast; ring
  have eqClock (st : GridCO.State p.n .block) :
      GridCO.clockPreGate p.engine st (voteTime p (r + 1)) =
        @GridCO.clock GridCO.slowLeasePolicy p.engine p.n .block st (voteTime p (r + 1)) := by
    rw [@GridCO.clock_eq_gate_prestate GridCO.slowLeasePolicy]
    dsimp only
    have noGate := voteTime_ne_gateTime p (r + 1)
    split
    · rename_i gateEq
      exact (noGate _ (by simpa using (Bool.and_eq_true_iff.mp gateEq).2)).elim
    · rfl
  rw [eqClock] at row
  have filter := @GridCO.clock_release_obligations GridCO.slowLeasePolicy p.engine p.n
    (Run.stateBeforeTime (sapc p) rho (voteTime p (r + 1)) v).base r
    (base_receiptStamped_at_fold p _ v)
  rw [← time] at filter
  rw [filter] at row
  obtain ⟨old, keep⟩ := List.mem_filter.mp row
  exact ⟨old, by simpa using keep⟩

/-- A full slow window consists of actual raw gates, including vetoed gates. -/
theorem slowEligible_input_covers {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (v : V) (r s : Slot) (B : Block)
    (slow : SA.slowEligible p (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base r B = true)
    (before : s < r) (window : r + 1 ≤ s + p.k) :
    ∃ C, SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s = some C ∧
      Block.Preceq B C := by
  obtain ⟨len, all⟩ := Bool.and_eq_true_iff.mp slow
  have len : p.k ≤ r + 1 := of_decide_eq_true len
  have member : r - s - 1 ∈ List.range (p.k - 1) := by simp; simp only [Slot] at *; omega
  have cover := List.all_eq_true.mp all (r - s - 1) member
  have eq : r - (r - s - 1 + 1) = s := by simp only [Slot] at *; omega
  rw [eq] at cover
  cases saved : GridCO.savedGenuine (Run.stateBeforeTime (sapc p) rho (gateTime p r) v).base s with
  | none => simp [saved] at cover
  | some result =>
    cases result with
    | none => simp [saved] at cover
    | some C =>
      exact ⟨C, (time_input_savedGenuine_origin p E rho hs _ v s _ saved).2.symm,
        by simpa [saved] using! cover⟩

/-- Recent conflicting sources are excluded by same-label safety. Older
sources expire by equality at the final HEAD of a slow window. -/
theorem slow_window_rows_compatible {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (relay : AcceptedObjectRelay (sapc p) E rho)
    (r : Slot) (source : V) (hs : source ∈ rho.honest) (B : Block)
    (slow : SA.slowEligible p
      (Run.stateBeforeTime (sapc p) rho (gateTime p r) source).base r B = true)
    (sync : ∀ s, s < r → r + 1 ≤ s + p.k → E.t_GST ≤ earlyTime p s)
    (horizon : gateTime p r ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (K : Block) (g : Nat) (d : Time)
    (row : (K, g, d) ∈ (headState p rho (r + 1) v).base.obligations) : Block.Compatible K B := by
  obtain ⟨old, live, _⟩ := head_row_survives_release p rho r v K g d row
  obtain ⟨s, C, time, raw, below, _, deadline⟩ := time_input_row_admitted_source p E rho
    hx.toScheduleWellFormed _ v K g d old
  have before : s < r := by
    by_contra hn
    have le := (GridCO.gateTime_le_iff p.engine r s).mpr (Nat.le_of_not_gt hn)
    change 4 * p.Δ * (s : Time) + 6 * p.Δ <
      4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ at time
    change 4 * p.Δ * (r : Time) + 6 * p.Δ ≤ 4 * p.Δ * (s : Time) + 6 * p.Δ at le
    push_cast at time
    linarith [p.deltaPos]
  by_cases window : r + 1 ≤ s + p.k
  · obtain ⟨D, rawD, belowD⟩ := slowEligible_input_covers p E rho hx.toScheduleWellFormed
      source r s B slow before window
    exact GridCO.compatible_prefixes K C B D below belowD
      (synchronous_sameLabel p E rho hx hΔ relay s (sync s before window)
        (((GridCO.gateTime_le_iff p.engine s r).mpr before.le).trans horizon)
        v source hv hs C D raw rawD)
  · have oldSource : (s : Time) + p.k ≤ r := by
      exact_mod_cast (by simp only [Slot] at *; omega : s + p.k ≤ r)
    rw [deadline] at live
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ <
      4 * p.Δ * (s : Time) + 6 * p.Δ + (4 * (p.k : Time) - 1) * p.Δ at live
    push_cast at live
    nlinarith [p.deltaPos]

/-- A later HEAD row is retained from the initial release or comes from
an intervening raw gate. The pending gate at the initial label is included. -/
theorem head_row_source_since {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (r t : Slot) (before : r < t)
    (horizon : voteTime p (r + 1) ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (B : Block) (g : Nat) (d : Time)
    (row : (B, g, d) ∈ (headState p rho (t + 1) v).base.obligations) :
    (B, g, d) ∈ (headState p rho (r + 1) v).base.obligations ∨
      ∃ s C, r ≤ s ∧ s < t ∧
        SA.confirmation p (Run.stateBeforeTime (sapc p) rho (gateTime p s) v).base s = some C ∧
        Block.Preceq B C := by
  set_option backward.isDefEq.respectTransparency false in
  have publicTime : PublicTime E (voteTime p (r + 1)) := by
    refine ⟨4 * (r + 1) + 1, ?_⟩
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ = _
    rw [hΔ]; push_cast; ring
  have positive : 0 ≤ voteTime p (r + 1) := by
    change 0 ≤ 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg (r + 1)]
  obtain ⟨i, tick⟩ := List.mem_iff_getElem?.mp (hs.tick_total v hv _ publicTime positive horizon)
  have stateEq : Run.stateBefore (sapc p) rho (i + 1) v = headState p rho (r + 1) v := by
    rw [stateBefore_succ_event tick]
    simp only [World.step, Function.update_self]
    rw [stateBefore_tick_eq_stateBeforeTime hs tick]
    rfl
  have old := (head_row_survives_release p rho t v B g d row).1
  rw [time_input_eq_event_prefix p E rho hs] at old
  have earlier : voteTime p (r + 1) < voteTime p (t + 1) := by
    have cast : (r : Time) < t := by exact_mod_cast before
    change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ <
      4 * p.Δ * ((t + 1 : Nat) : Time) + p.Δ
    push_cast; nlinarith [p.deltaPos]
  have index := (index_lt_read_length_iff hs (voteTime p (t + 1) - 1) tick).mpr
    (Int.le_sub_one_iff.mpr earlier)
  rcases clock_field_origin_since (P := sapc p) (fun st => st.base.obligations)
      (process_obligations p)
      (fun st u row => ∃ s C, u = gateTime p s ∧
        SA.confirmation p (clockPreGate p st u).base s = some C ∧
        Block.Preceq row.1 C ∧ row.2.1 ∈
          @GridCO.admissionLevels GridCO.slowLeasePolicy p.engine p.n .block
            (clockPreGate p st u).base s row.1 ∧ row.2.2 = gateTime p s + lifetime p)
      (fun st u row hm => clock_row_source p st u row.1 row.2.1 row.2.2 hm)
      rho (i + 1) _ (by omega) v (B, g, d) old with
      prior | ⟨j, lo, hi, u, event, s, C, eq, raw, below, _⟩
  · exact Or.inl (stateEq ▸ prior)
  · subst u
    have timeHi : gateTime p s < voteTime p (t + 1) :=
      Int.le_sub_one_iff.mp ((index_lt_read_length_iff hs _ event).mp hi)
    have timeLo : voteTime p (r + 1) ≤ gateTime p s := by
      by_contra hn
      have := eventIndex_lt_of_time_lt hs event tick (lt_of_not_ge hn)
      omega
    have castLo : (r : Time) ≤ s := by
      change 4 * p.Δ * ((r + 1 : Nat) : Time) + p.Δ ≤
        4 * p.Δ * (s : Time) + 6 * p.Δ at timeLo
      push_cast at timeLo
      by_contra hn
      have diff : (s : Time) + 1 ≤ r := Int.add_one_le_iff.mpr (lt_of_not_ge hn)
      nlinarith [p.deltaPos]
    have castHi : (s : Time) < t := by
      change 4 * p.Δ * (s : Time) + 6 * p.Δ <
        4 * p.Δ * ((t + 1 : Nat) : Time) + p.Δ at timeHi
      push_cast at timeHi
      nlinarith [p.deltaPos]
    have stamped : GridCO.ReceiptStamped (Run.stateBefore (sapc p) rho j v).base :=
      base_receiptStamped_at_fold p _ v
    rw [clockPreGate_base] at raw
    unfold SA.confirmation at raw
    rw [@GridCO.confirmation_eq_of_receiptData GridCO.slowLeasePolicy p.engine p.n _
      (Run.stateBefore (sapc p) rho j v).base
      (GridCO.clockPreGate_receiptData p.engine _ _) stamped] at raw
    rw [stateBefore_tick_eq_stateBeforeTime hs event] at raw
    exact Or.inr ⟨s, C, by exact_mod_cast castLo, by exact_mod_cast castHi, raw, below⟩

end AvailableChain.SAPC
end
