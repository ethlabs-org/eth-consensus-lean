module
public import AvailableChainFGSAProofs.Proofs.Shared.Reads
public import AvailableChainFGSAClaims.Statements.Regimes

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- A nonempty executed read supplies the enabled gate at the same tick. -/
theorem clean_gate_enabled_of_result {j : Nat} {v : V} {s : Slot} {C : Block}
    (hS : V2.D.ScheduleWellFormed E rho) (ht : IsGateTick p c rho j v s)
    (hC : gateResultAt p c E rho j = some (some C)) :
    enabledGateAt p c E rho j v s := by
  have h := fgsa_gate_raw_of_nonempty p c E rho hS ht
    ((gateResultAt_eq_gateResult p c E rho hS ht).symm.trans hC)
  have hs : p.slotOf (SA.gateTime p.toParams s) = s + 1 :=
    (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho j v) _).2.symm.trans
      (fgsa_gate_slot (c := c) (V2.D.Run.stateBefore E rho j v) s)
  have hg : joinedAtTime p (storeAt p c E rho j v).restartTime
      (SA.gateTime p.toParams s) = true := h.1
  refine ⟨ht, ?_⟩
  change (match (storeAt p c E rho j v).restartTime with
    | none => True | some w => w ≤ slotStartZ p (s : Int))
  cases hr : (storeAt p c E rho j v).restartTime with
  | none => trivial
  | some w =>
    rw [hr] at hg
    change decide (w ≤ 4 * p.Δ * ((p.slotOf (SA.gateTime p.toParams s) : Int) - 1)) =
      true at hg
    change w ≤ 4 * p.Δ * (s : Int)
    simpa only [hs, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
      decide_eq_true_eq] using hg

/-- The executed gate result includes the join test at this gate. -/
theorem clean_gate_executed {j : Nat} {v : V} {s : Slot}
    (hsch : V2.D.ScheduleWellFormed E rho) (ht : IsGateTick p c rho j v s) :
    gateResultAt p c E rho j = some
      (if joinedAtTime p (storeAt p c E rho j v).restartTime (SA.gateTime p.toParams s)
      then SA.Root.confirmationFrom p.toParams (eraseFG (storeAt p c E rho j v).fg.F)
        (actView (clockPre p (storeAt p c E rho j v) (SA.gateTime p.toParams s))) s
      else none) := by
  rw [gateResultAt_eq_gateResult p c E rho hsch ht,
    gateResult_eq_saved p c E rho hsch ht]
  exact fgsa_gate_saved_guarded E rho hsch ht

/-- An enabled gate exposes the raw result of its pre-gate store. -/
theorem clean_gate_raw_enabled {j : Nat} {v : V} {s : Slot}
    (hsch : V2.D.ScheduleWellFormed E rho)
    (ht : enabledGateAt p c E rho j v s) :
    gateResultAt p c E rho j = some (SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (storeAt p c E rho j v) (SA.gateTime p.toParams s)).fg.F)
      (actView (clockPre p (storeAt p c E rho j v) (SA.gateTime p.toParams s))) s) := by
  have hj : joinedAtTime p (storeAt p c E rho j v).restartTime
      (SA.gateTime p.toParams s) = true := fgsa_gate_joined_of_enabled E rho ht
  rw [clean_gate_executed hsch ht.1]
  simp only [hj, ite_true, clockPre_fg]

/-- A nonempty executed result supplies both the join guard and the raw equation. -/
theorem clean_gate_nonempty_raw {j : Nat} {v : V} {s : Slot} {C : Block}
    (hsch : V2.D.ScheduleWellFormed E rho) (ht : IsGateTick p c rho j v s)
    (hC : gateResultAt p c E rho j = some (some C)) :
    enabledGateAt p c E rho j v s ∧
    SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (storeAt p c E rho j v) (SA.gateTime p.toParams s)).fg.F)
      (actView (clockPre p (storeAt p c E rho j v) (SA.gateTime p.toParams s))) s =
        some C := by
  have h := fgsa_gate_raw_of_nonempty p c E rho hsch ht
    ((gateResultAt_eq_gateResult p c E rho hsch ht).symm.trans hC)
  exact ⟨clean_gate_enabled_of_result hsch ht hC, h.2⟩

/-- The stored gate-time join test is equivalent to the enabled-gate guard. -/
theorem clean_gate_join_test_iff {j : Nat} {v : V} {s : Slot}
    (ht : IsGateTick p c rho j v s) :
    joinedAtTime p (storeAt p c E rho j v).restartTime (SA.gateTime p.toParams s) = true ↔
      enabledGateAt p c E rho j v s := by
  constructor
  · intro hj
    have hs : p.slotOf (SA.gateTime p.toParams s) = s + 1 :=
      (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho j v) _).2.symm.trans
        (fgsa_gate_slot (c := c) (V2.D.Run.stateBefore E rho j v) s)
    refine ⟨ht, ?_⟩
    change (match (storeAt p c E rho j v).restartTime with
      | none => True | some w => w ≤ slotStartZ p (s : Int))
    cases hr : (storeAt p c E rho j v).restartTime with
    | none => trivial
    | some w =>
      rw [hr] at hj
      change decide (w ≤ 4 * p.Δ * ((p.slotOf (SA.gateTime p.toParams s) : Int) - 1)) =
        true at hj
      change w ≤ 4 * p.Δ * (s : Int)
      simpa only [hs, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
        decide_eq_true_eq] using hj
  · exact fgsa_gate_joined_of_enabled E rho

/-- A suppressed gate has an empty executed result. -/
theorem clean_gate_unjoined {j : Nat} {v : V} {s : Slot}
    (hsch : V2.D.ScheduleWellFormed E rho) (ht : IsGateTick p c rho j v s)
    (hJ : ¬ enabledGateAt p c E rho j v s) :
    gateResultAt p c E rho j = some none := by
  have hj : joinedAtTime p (storeAt p c E rho j v).restartTime
      (SA.gateTime p.toParams s) = false :=
    Bool.eq_false_iff.mpr (fun h => hJ ((clean_gate_join_test_iff ht).mp h))
  rw [clean_gate_executed hsch ht]
  simp only [hj, Bool.false_eq_true, ite_false]

/-- A restart leaves a marker at least as late as that restart until this event cut. -/
theorem clean_restart_marker_after (hS : V2.D.ScheduleWellFormed E rho)
    {k i : Nat} {x : V} {u : Time} (hk : rho.events[k]? = some (.restart x u))
    (hki : k < i) :
    ∃ w, (storeAt p c E rho i x).restartTime = some w ∧ u ≤ w := by
  let Q : Node p → Prop := fun nd => ∃ w, nd.st.restartTime = some w ∧ u ≤ w
  refine V2.D.Engine.stateBefore_step_induction E rho Q (Nat.succ_le_of_lt hki) x ?_ ?_
  · intro j e hkj _ he hx ⟨w, hw, huw⟩
    cases e with
    | restart y t =>
      change y = x at hx
      subst y
      have hkt : u ≤ t := by
        obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
        obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp he
        have hs := List.pairwise_iff_getElem.mp hS.sorted k j hkl hjl (by omega)
        rw [hke, hje] at hs
        exact V2.D.Engine.time_le_of_key_le _ _ hs
      refine ⟨t, ?_, hkt⟩
      simp only [V2.D.World.step, Function.update_self]
      exact acRestart_restartTime p _ t
    | tick y t =>
      change y = x at hx
      subst y
      refine ⟨w, ?_, huw⟩
      simp only [V2.D.World.step, Function.update_self]
      rw [tick_st (p := p) (c := c) E rho (V2.D.Run.stateBefore E rho j x) x t,
        fgsa_clock_restartTime]
      exact hw
    | deliver y o t =>
      change y = x at hx
      subst y
      refine ⟨w, ?_, huw⟩
      simp only [V2.D.World.step, Function.update_self]
      change (FGSA.process p (storeAt p c E rho j x) (toWire p o)).restartTime = some w
      rwa [fgsa_process_restartTime]
  · refine ⟨u, ?_, le_rfl⟩
    rw [V2.D.Engine.state_after_restart hk]
    exact acRestart_restartTime p _ u

/-- An enabled honest gate is awake from the start of its label through its tick. -/
theorem clean_enabledGate_awakeClosed (hV : V2.D.ExecutionValid E rho)
    {j : Nat} {x : V} {s : Slot} (hx : x ∈ rho.honest)
    (hG : enabledGateAt p c E rho j x s) :
    AwakeClosed E x (slotStartZ p (s : Int)) (SA.gateTime p.toParams s) := by
  intro t ht0 hst htg
  have hA := hV.tick_awake x _ (List.mem_of_getElem? hG.1)
  cases ha : E.awake x t with
  | true => rfl
  | false =>
    obtain ⟨w, htw, hwg, hW⟩ := V2.D.Engine.wake_between htg ha hA
    have hw0 : 0 < w := lt_of_le_of_lt ht0 htw
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp (hV.wake_restart x hx w hw0
      (hwg.trans (hV.in_horizon _ (List.mem_of_getElem? hG.1)).2) hW)
    have hkj := V2.D.Engine.restart_index_lt_event hV.toScheduleWellFormed hk hG.1 hwg
      (by change (0 : Nat) < 1; omega)
    obtain ⟨u, hu, hwu⟩ := clean_restart_marker_after hV.toScheduleWellFormed hk hkj
    have hb := hG.2
    change (match (storeAt p c E rho j x).restartTime with
      | none => True | some w => w ≤ slotStartZ p (s : Int)) at hb
    rw [hu] at hb
    exact (not_lt_of_ge (hwu.trans hb) (hst.trans_lt htw)).elim

/-- The label interval of an enabled gate contains no later local wake restart. -/
theorem clean_enabledGate_restartFreeTime (hV : V2.D.ExecutionValid E rho)
    (hR : V2.D.RestartsAtWakes E rho) {j : Nat} {x : V} {s : Slot}
    (hx : x ∈ rho.honest) (hG : enabledGateAt p c E rho j x s) :
    RestartFreeTime rho x (slotStartZ p (s : Int)) (SA.gateTime p.toParams s) := by
  intro w hsw hwg hm
  have hw := (hR x w hm).2.2
  have h0 : 0 ≤ slotStartZ p (s : Int) := by
    change 0 ≤ 4 * p.Δ * (s : Int)
    have := p.deltaPos
    positivity
  have ha := clean_enabledGate_awakeClosed hV hx hG (w - 1)
    (by dsimp [Time] at *; omega) (by dsimp [Time] at *; omega)
    (by dsimp [Time] at *; omega)
  rw [ha] at hw
  cases hw

/-- Joinedness at this gate supplies its stored restart cutoff. -/
theorem clean_enabledGate_of_joinedAt (hS : V2.D.ScheduleWellFormed E rho)
    {j : Nat} {x : V} {s : Slot} (ht : IsGateTick p c rho j x s)
    (hJ : joinedAt p E rho x (s + 1) (SA.gateTime p.toParams s)) :
    enabledGateAt p c E rho j x s := by
  refine ⟨ht, ?_⟩
  have hb := fgsa_restartTime_bound E rho j x (slotStartZ p (s : Int)) (by
    intro k w hkj hk
    obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp ht
    have hs := List.pairwise_iff_getElem.mp hS.sorted k j hkl hjl hkj
    rw [hke, hje] at hs
    have hw := hJ.2.2 w (hS.in_horizon _ (List.mem_of_getElem? hk)).1
      (V2.D.Engine.time_le_of_key_le _ _ hs) (List.mem_of_getElem? hk)
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hw)
  change (match (storeAt p c E rho j x).restartTime with
    | none => True | some w => w ≤ slotStartZ p (s : Int))
  cases hr : (storeAt p c E rho j x).restartTime with
  | none => trivial
  | some w => exact hb w hr

/-- The joined-majority denominator supplies a joined honest node at this exact time. -/
theorem clean_joined_witness [Fintype V] {t : Time}
    (hP : (Gen.V2.Duty.faulty rho).card < (joinedHonest p E rho t).card) :
    ∃ z, z ∈ rho.honest ∧ joinedAt p E rho z (slotAt p t) t := by
  classical
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hP)
  exact ⟨z, (Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2⟩

/-- T10: choose an enabled intermediate gate from the earlier joined population. -/
theorem clean_joined_gate_witness [Fintype V] {ΔF b₀ : Time}
    (h : HealthyPrefixSleep₂ p c E rho b₀ ΔF) (s : Slot)
    (hcut : SA.gateTime p.toParams s < b₀) :
    ∃ z j, z ∈ rho.honest ∧ enabledGateAt p c E rho j z s ∧
      AwakeClosed E z (slotStartZ p (s : Int)) (SA.gateTime p.toParams s) := by
  have h0 : 0 ≤ SA.gateTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have := p.deltaPos
    positivity
  obtain ⟨z, hz, hJ⟩ := clean_joined_witness (h.joinedPartBefore _ h0 hcut)
  have hslot : slotAt p (SA.gateTime p.toParams s) = s + 1 :=
    (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho 0 z) _).2.symm.trans
      (fgsa_gate_slot (c := c) (V2.D.Run.stateBefore E rho 0 z) s)
  rw [hslot] at hJ
  have hp : V2.PublicTime E (SA.gateTime p.toParams s) := by
    refine ⟨4 * s + 6, ?_⟩
    rw [h.base.delta]
    change 4 * p.Δ * (s : Int) + 6 * p.Δ = ((4 * s + 6 : Nat) : Int) * p.Δ
    push_cast
    ring
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (h.base.valid.tick_total z hz _ hp h0
    (hcut.le.trans h.cut.2) hJ.1)
  have hG := clean_enabledGate_of_joinedAt h.base.valid.toScheduleWellFormed hj hJ
  exact ⟨z, j, hz, hG, clean_enabledGate_awakeClosed h.base.valid hz hG⟩

end AvailableChain.FGSA.Run
end
