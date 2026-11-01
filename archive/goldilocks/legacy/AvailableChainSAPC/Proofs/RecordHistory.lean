module
public import AvailableChainSAPC.Proofs.PendingAuthority
public import AvailableChainSAPC.Proofs.GateRead

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- Only a genuine gate can change the stable record. -/
theorem clock_stable_cases (p : Params) {n : Nat} (st : State n) (t : Time)
    (stamped : GridCO.ReceiptStamped st.base) :
    stable (clock p st t) = stable st ∨ ∃ r,
      t = gateTime p r ∧ SA.confirmation p st.base r = some (stable (clock p st t)) := by
  have preStable : (clockPreGate p st t).base.stableRecord = stable st := by
    change _ = st.base.stableRecord
    rw [clockPreGate_base, GridCO.clockPreGate_stable]
  rw [clock_eq_gate_prestate]
  dsimp only
  split
  · rename_i gateEq
    have time : t = gateTime p ((t - 6 * p.Δ) / (4 * p.Δ)).toNat := by
      simpa using (Bool.and_eq_true_iff.mp gateEq).2
    rcases (gateWithPC_records p (clockPreGate p st t).base _
      (if capBroken p (clockPreGate p st t) then none else (clockPreGate p st t).bestPC)).1
      with old | ⟨b, raw, eq⟩
    · exact Or.inl (old.trans preStable)
    · rw [clockPreGate_base] at raw
      have raw' := (@GridCO.confirmation_eq_of_receiptData GridCO.slowLeasePolicy p.engine n
        _ st.base (GridCO.clockPreGate_receiptData p.engine st.base t) stamped _).symm.trans raw
      by_cases keep : Block.preceq b (clockPreGate p st t).base.stableRecord = true
      · rw [GridCO.advance, ite_eq_left keep] at eq
        exact Or.inl (eq.trans preStable)
      · rw [GridCO.advance, ite_eq_right keep] at eq
        exact Or.inr ⟨_, time, raw'.trans (congrArg some eq.symm)⟩
  · exact Or.inl preStable

theorem clock_stable_of_no_gate (p : Params) {n : Nat} (st : State n) (t : Time)
    (noGate : ∀ r, t ≠ gateTime p r) : stable (clock p st t) = stable st := by
  rw [clock_eq_preGate_of_no_gate p st t noGate]
  change (clockPreGate p st t).base.stableRecord = st.base.stableRecord
  rw [clockPreGate_base, GridCO.clockPreGate_stable]

/-- The record is genesis or an actual raw result from an earlier gate. -/
theorem run_stable_origin {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (index : Nat) (v : V) :
    stable (Run.stateBefore (sapc p) rho index v) = .genesis ∨ ∃ j < index, ∃ r,
      rho.events[j]? = some (.tick v (gateTime p r)) ∧
      SA.confirmation p (Run.stateBefore (sapc p) rho j v).base r =
        some (stable (Run.stateBefore (sapc p) rho index v)) := by
  set_option backward.isDefEq.respectTransparency false in
  induction index with
  | zero => exact Or.inl rfl
  | succ i ih =>
    cases he : rho.events[i]? with
    | none =>
      simp only [Run.stateBefore, List.take_add_one, he, Option.toList_none, List.append_nil]
      exact ih.imp_right (by rintro ⟨j, hj, rest⟩; exact ⟨j, by omega, rest⟩)
    | some e =>
      have old (eq : stable (Run.stateBefore (sapc p) rho (i + 1) v) =
          stable (Run.stateBefore (sapc p) rho i v)) :
          stable (Run.stateBefore (sapc p) rho (i + 1) v) = .genesis ∨
            ∃ j < i + 1, ∃ r, rho.events[j]? = some (.tick v (gateTime p r)) ∧
              SA.confirmation p (Run.stateBefore (sapc p) rho j v).base r =
                some (stable (Run.stateBefore (sapc p) rho (i + 1) v)) := by
        rw [eq]
        exact ih.imp_right (by rintro ⟨j, hj, rest⟩; exact ⟨j, by omega, rest⟩)
      cases e with
      | deliver w obj t =>
        apply old
        rw [stateBefore_succ_event he]
        by_cases eq : v = w
        · subst w; simp only [World.step, sapc, Function.update_self, process_stable]
        · simp only [World.step, Function.update_of_ne eq]
      | tick w t =>
        by_cases eq : v = w
        · subst w
          rcases clock_stable_cases p (Run.stateBefore (sapc p) rho i v) t
              (base_receiptStamped_at_fold p _ v) with same | ⟨r, time, raw⟩
          · apply old
            rw [stateBefore_succ_event he]
            simpa only [World.step, Function.update_self] using! same
          · right
            refine ⟨i, Nat.lt_succ_self i, r, time ▸ he, ?_⟩
            rw [stateBefore_succ_event he]
            simpa only [World.step, Function.update_self] using! raw
        · apply old
          simp only [stateBefore_succ_event he, World.step, Function.update_of_ne eq]

theorem read_stable_before_first_gate {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) (t : Time) (ht : t < gateTime p 0) (v : V) :
    stable (Run.readAt (sapc p) rho t v) = .genesis := by
  change stable ((rho.events.filter (fun e => decide (e.time ≤ t))).foldl
    World.step World.init v) = stable ((World.init : World V (sapc p)) v)
  apply GridCO.fold_field_unchanged (P := sapc p) stable (process_stable p) _ ?_ World.init v
  intro e he st
  apply clock_stable_of_no_gate p st e.time
  intro r eq
  have bound : e.time ≤ t := of_decide_eq_true (List.mem_filter.mp he).2
  have first := (GridCO.gateTime_le_iff p.engine 0 r).mpr (Nat.zero_le r)
  exact (not_le_of_gt ht) (first.trans (by simpa only [eq] using bound))

theorem read_stable_eq_latest_gate {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (t : Time) (hlo : gateTime p r ≤ t) (hhi : t < gateTime p (r + 1)) (v : V) :
    stable (Run.readAt (sapc p) rho t v) =
      stable (Run.readAt (sapc p) rho (gateTime p r) v) := by
  apply GridCO.read_field_eq_of_no_clock_change stable (process_stable p) E rho hs _ _ hlo
  intro time lo hi st
  apply clock_stable_of_no_gate p st time
  intro s eq
  have hrs : r < s := by
    by_contra hn
    have bound := (GridCO.gateTime_le_iff p.engine s r).mpr (Nat.le_of_not_gt hn)
    exact (not_le_of_gt lo) (eq ▸ bound)
  have bound := (GridCO.gateTime_le_iff p.engine (r + 1) s).mpr hrs
  exact (not_le_of_gt hhi) (bound.trans (by simpa only [eq] using hi))

/-- A prefix of a stable read transfers to every later healthy HEAD.
The read's exact raw source supplies the label bound. -/
theorem healthy_stable_heads {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hΔ : E.Δ = p.Δ)
    (hx : ExecutionValid (sapc p) E rho)
    (roots : RootInjective E (sapcInterface p).toInterface rho)
    (cut : Time) (net : HealthyPrefixDelivery (sapc p) E rho cut)
    (relay : HealthyAcceptedObjectRelay (sapc p) E rho cut)
    (majority : ∀ t, 0 ≤ t → t < cut → AwakeMajority E rho t)
    (r : Slot) (hearly : earlyTime p r ≤ cut) (hh : earlyTime p r ≤ rho.horizon)
    (T : Time) (before : T < gateTime p r) (v : V) (hv : v ∈ rho.honest) (B : Block)
    (below : Block.Preceq B (stable (Run.readAt (sapc p) rho T v))) :
    ∀ w ∈ rho.honest, Block.Preceq B (headData p rho r w).target := by
  rw [readAt_eq_stateBefore hx.toScheduleWellFormed] at below
  have origin := run_stable_origin p rho
    (rho.events.filter (fun e => decide (e.time ≤ T))).length v
  rcases origin with gen | ⟨j, hj, s, tick, raw⟩
  · rw [gen] at below
    have eq : B = .genesis := by simpa [Block.Preceq, Block.preceq] using below
    subst B
    exact fun _ _ => GridCO.genesis_prefix _
  · have time := (index_lt_read_length_iff hx.toScheduleWellFormed T tick).mp hj
    have hsr : s < r := by
      by_contra hn
      have bound := (GridCO.gateTime_le_iff p.engine r s).mpr (Nat.le_of_not_gt hn)
      exact (not_le_of_gt before) (bound.trans time)
    rw [stateBefore_tick_eq_stateBeforeTime hx.toScheduleWellFormed tick] at raw
    intro w hw
    exact GridCO.prefix_trans _ _ _ below
      (healthy_genuine_heads p E rho hΔ hx roots cut net relay majority r hearly hh s hsr
        v hv _ raw w hw)

end AvailableChain.SAPC
end
