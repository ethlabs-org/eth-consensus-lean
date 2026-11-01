module
-- shake keep reason: source declarations
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.Interfaces -- shake: keep
public import AvailableChainFGSAProofs.Proofs.Shared.AnchorService
public import AvailableChainFGSAProofs.Proofs.Shared.Reads

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- A nonempty executed read supplies the enabled gate at the same tick. -/
theorem wcg_gate_enabled_of_result {j : Nat} {v : V} {s : Slot} {C : Block}
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

/-- W3-J supplies the stored pre-gate test for the gate-write law. -/
theorem wcg_gate_pre_joined {j : Nat} {x : V} {s : Slot}
    (hG : enabledGateAt p c E rho j x s) :
    joinedNow p (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)) = true := by
  rw [clockPre_joined]
  exact fgsa_gate_joined_of_enabled E rho hG

/-- W3-G exposes the raw result only at an enabled gate. -/
theorem wcg_gate_raw_enabled {j : Nat} {x : V} {s : Slot}
    (hS : V2.D.ScheduleWellFormed E rho) (hG : enabledGateAt p c E rho j x s) :
    gateResultAt p c E rho j = some (SA.Root.confirmationFrom p.toParams
      (eraseFG (storeAt p c E rho j x).fg.F)
      (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s) := by
  rw [gateResultAt_eq_gateResult p c E rho hS hG.1,
    gateResult_eq_saved p c E rho hS hG.1]
  exact fgsa_gate_saved_result E rho hS hG.1 (fgsa_gate_joined_of_enabled E rho hG)

/-- WC plan §6.5; DC a gate is after the completed cut exactly when its label is later. -/
theorem wcg_gate_cut_iff (hsch : V2.D.ScheduleWellFormed E rho)
    {w : HealingWitness} {iStar j : Nat} {x : V} {s : Slot}
    (hs : WCSeed p c E rho w iStar) (ht : IsGateTick p c rho j x s) :
    iStar ≤ j ↔ w.u < s := by
  have hc := V2.D.Engine.filter_eq_take hsch (cutPred (SA.gateTime p.toParams w.u)) (by
    intro e f hle hf
    exact decide_eq_true (hle.trans (of_decide_eq_true hf)))
  constructor
  · intro hj
    by_contra hn
    have hle : (s : Int) ≤ w.u := Int.ofNat_le.mpr (Nat.le_of_not_gt hn)
    have htime : SA.gateTime p.toParams s ≤ SA.gateTime p.toParams w.u := by
      change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ 4 * p.Δ * (w.u : Int) + 6 * p.Δ
      nlinarith [p.deltaPos]
    have hf := V2.D.Engine.filter_false_of_index_ge hsch
      (cutPred (SA.gateTime p.toParams w.u)) (by
        intro e f hle hf
        exact decide_eq_true (hle.trans (of_decide_eq_true hf)))
      (show afterTicksIdx rho (SA.gateTime p.toParams w.u) ≤ j from hs.cut ▸ hj) ht
    have hh : cutPred (SA.gateTime p.toParams w.u)
        (.tick x (SA.gateTime p.toParams s) : V2.Event V (fgsa p c).Object) = true :=
      decide_eq_true (Prod.Lex.toLex_le_toLex.mpr
        (htime.lt_or_eq.imp id (fun he => ⟨he, le_rfl⟩)))
    rw [hh] at hf
    cases hf
  · intro hslabel
    by_contra hn
    have hj : j < afterTicksIdx rho (SA.gateTime p.toParams w.u) :=
      hs.cut ▸ Nat.lt_of_not_ge hn
    have hm : V2.Event.tick x (SA.gateTime p.toParams s) ∈
        rho.events.filter (cutPred (SA.gateTime p.toParams w.u)) := by
      rw [hc]
      apply List.mem_of_getElem? (i := j)
      change (rho.events.take (afterTicksIdx rho (SA.gateTime p.toParams w.u)))[j]? = _
      rw [List.getElem?_take_of_lt hj]
      exact ht
    have hk := of_decide_eq_true (List.mem_filter.mp hm).2
    have hh : SA.gateTime p.toParams s ≤ SA.gateTime p.toParams w.u := by
      rcases Prod.Lex.toLex_le_toLex.mp hk with h | ⟨h, _⟩
      · exact h.le
      · exact h.le
    have hcast : (w.u : Int) < s := Int.ofNat_lt.mpr hslabel
    change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ 4 * p.Δ * (w.u : Int) + 6 * p.Δ at hh
    nlinarith [p.deltaPos]


omit [DecidableEq V] in
private theorem wcg_prefixTime_unfold (i : Nat) : prefixTime rho i =
    ((rho.events.take i).getLast?.map (fun e => e.time)).getD 0 := rfl

omit [DecidableEq V] in
/-- Every event in a finite prefix is at or before its final event time. -/
theorem wcg_event_before_prefixTime (hS : V2.D.ScheduleWellFormed E rho)
    {i j : Nat} {e : V2.Event V (fgsa p c).Object}
    (hi : i ≤ rho.events.length) (hj : j < i) (he : rho.events[j]? = some e) :
    e.time ≤ prefixTime rho i := by
  have hlast : i - 1 < rho.events.length := by omega
  let f := rho.events[i - 1]
  have hf : rho.events[i - 1]? = some f := List.getElem?_eq_getElem hlast
  have ht : e.time ≤ f.time := by
    rcases (show j ≤ i - 1 by omega).lt_or_eq with hlt | rfl
    · obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp he
      have hk := List.pairwise_iff_getElem.mp hS.sorted j (i - 1) hjl hlast hlt
      rw [hje] at hk
      exact V2.D.Engine.time_le_of_key_le _ _ hk
    · have heq : e = f := Option.some.inj (he.symm.trans hf)
      rw [heq]
  rw [wcg_prefixTime_unfold, List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left hi,
    List.getElem?_take_of_lt (by omega), hf]
  exact ht

/-- A confirmed reader with an early marker has its own enabled covered gate. -/
theorem wcg_confirmedReader_early_gate (hV : V2.D.ExecutionValid E rho)
    (hdelta : E.Δ = p.Δ) {i : Nat} {y : V} {r : Slot}
    (hy : confirmedReaderIdx p c E rho y i)
    (hhor : SA.gateTime p.toParams r ≤ rho.horizon)
    (ht : SA.gateTime p.toParams r ≤ prefixTime rho i)
    (hcut : afterTicksIdx rho (SA.gateTime p.toParams r) ≤ i)
    (hmarker : ∀ w, (storeAt p c E rho i y).restartTime = some w →
      w ≤ slotStartZ p (r : Int)) :
    ∃ k < i, enabledGateAt p c E rho k y r := by
  have hS := hV.toScheduleWellFormed
  have hbound (j : Nat) (u : Time) (hj : j < i)
      (he : rho.events[j]? = some (.restart y u)) : u ≤ slotStartZ p (r : Int) := by
    obtain ⟨w, hw, huw⟩ := fgsa_restartTime_ge E rho hS he hj
    exact huw.trans (hmarker w hw)
  have hsg : slotStartZ p (r : Int) ≤ SA.gateTime p.toParams r := by
    change 4 * p.Δ * (r : Int) ≤ 4 * p.Δ * (r : Int) + 6 * p.Δ
    linarith [p.deltaPos]
  have h0 : 0 ≤ SA.gateTime p.toParams r := by
    change 0 ≤ 4 * p.Δ * (r : Int) + 6 * p.Δ
    have := p.deltaPos
    positivity
  have hAw : E.awake y (SA.gateTime p.toParams r) = true := by
    by_contra hn
    have hfalse := Bool.eq_false_iff.mpr hn
    obtain ⟨u, hgu, hut, hW⟩ := V2.D.Engine.wake_between ht hfalse hy.1.2.1
    obtain ⟨j, hj, he⟩ := hy.2 u (h0.trans_lt hgu) hut hW
    exact (not_lt.mpr ((hbound j u hj he).trans hsg)) hgu
  have hclock : ((4 * r + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams r := by
    change ((4 * r + 6 : Nat) : Int) * p.Δ = 4 * p.Δ * (r : Int) + 6 * p.Δ
    push_cast
    ring
  obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hS hdelta y hy.1.1 (4 * r + 6)
    (hclock ▸ hhor) (hclock ▸ hAw)
  rw [hclock] at hk
  have hkc : k < afterTicksIdx rho (SA.gateTime p.toParams r) := by
    by_contra hn
    have hf := V2.D.Engine.filter_false_of_index_ge hS
      (cutPred (SA.gateTime p.toParams r)) (by
        intro e f hk hf
        exact decide_eq_true (hk.trans (of_decide_eq_true hf)))
      (Nat.le_of_not_gt hn) hk
    have htrue : cutPred (SA.gateTime p.toParams r)
        (.tick y (SA.gateTime p.toParams r) : V2.Event V (fgsa p c).Object) = true :=
      decide_eq_true le_rfl
    rw [htrue] at hf
    cases hf
  have hki := hkc.trans_le hcut
  refine ⟨k, hki, hk, ?_⟩
  have hb := fgsa_restartTime_bound E rho k y (slotStartZ p (r : Int)) (by
    intro j u hj he
    exact hbound j u (hj.trans hki) he)
  cases hw : (storeAt p c E rho k y).restartTime with
  | none => trivial
  | some w => exact hb w hw

/-- A completed result supplies its own enabled gate. -/
theorem wcg_result_enabled {w : HealingWitness} {iStar i j : Nat} {x : V}
    {s : Slot} {B : Block} (hr : WCResult p c E rho w iStar i j x s B)
    (hS : V2.D.ScheduleWellFormed E rho) : enabledGateAt p c E rho j x s :=
  wcg_gate_enabled_of_result hS hr.event hr.value

/-- Joinedness at this gate supplies its stored restart cutoff. -/
theorem wcg_enabledGate_of_joinedAt (hS : V2.D.ScheduleWellFormed E rho)
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

/-- Keep the all-time joined count until the intermediate gate actor is chosen. -/
theorem wcg_joined_gate_witness [Fintype V] (hV : V2.D.ExecutionValid E rho)
    (hdelta : E.Δ = p.Δ) (s : Slot)
    (hP : (Gen.V2.Duty.faulty rho).card <
      (joinedHonest p E rho (SA.gateTime p.toParams s)).card)
    (hh : SA.gateTime p.toParams s ≤ rho.horizon) :
    ∃ z j, z ∈ rho.honest ∧ enabledGateAt p c E rho j z s ∧
      AwakeClosed E z (slotStartZ p (s : Int)) (SA.gateTime p.toParams s) := by
  classical
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hP)
  obtain ⟨hz, hJ⟩ := Finset.mem_filter.mp hz
  have hslot : slotAt p (SA.gateTime p.toParams s) = s + 1 :=
    (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho 0 z) _).2.symm.trans
      (fgsa_gate_slot (c := c) (V2.D.Run.stateBefore E rho 0 z) s)
  rw [hslot] at hJ
  have h0 : 0 ≤ SA.gateTime p.toParams s := by
    change 0 ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ
    have := p.deltaPos
    positivity
  have hp : V2.PublicTime E (SA.gateTime p.toParams s) := by
    refine ⟨4 * s + 6, ?_⟩
    rw [hdelta]
    change 4 * p.Δ * (s : Int) + 6 * p.Δ = ((4 * s + 6 : Nat) : Int) * p.Δ
    push_cast
    ring
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (hV.tick_total z hz _ hp h0 hh hJ.1)
  have hG := wcg_enabledGate_of_joinedAt hV.toScheduleWellFormed hj hJ
  exact ⟨z, j, hz, hG, fgsa_enabledGate_awakeClosed hV hz hG⟩

end AvailableChain.FGSA.Run
end
