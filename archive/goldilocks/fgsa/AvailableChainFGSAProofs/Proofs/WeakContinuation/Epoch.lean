module
public import AvailableChainFGSAProofs.Statements.WeakContinuation
public import AvailableChainFGSAProofs.Proofs.Shared.Reads

public section

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- A nonempty executed read supplies the enabled gate at the same tick. -/
theorem wc_gate_enabled_of_result {j : Nat} {v : V} {s : Slot} {C : Block}
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

/-- A restart leaves a marker at least as late as that restart until this event cut. -/
private theorem wc_restart_marker_after (hS : V2.D.ScheduleWellFormed E rho)
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
theorem wc_enabledGate_awakeClosed (hV : V2.D.ExecutionValid E rho)
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
    obtain ⟨u, hu, hwu⟩ := wc_restart_marker_after hV.toScheduleWellFormed hk hkj
    have hb := hG.2
    change (match (storeAt p c E rho j x).restartTime with
      | none => True | some w => w ≤ slotStartZ p (s : Int)) at hb
    rw [hu] at hb
    exact (not_lt_of_ge (hwu.trans hb) (hst.trans_lt htw)).elim

/-- The label interval of an enabled gate contains no later local wake restart. -/
theorem wc_enabledGate_restartFreeTime (hV : V2.D.ExecutionValid E rho)
    (hR : V2.D.RestartsAtWakes E rho) {j : Nat} {x : V} {s : Slot}
    (hx : x ∈ rho.honest) (hG : enabledGateAt p c E rho j x s) :
    RestartFreeTime rho x (slotStartZ p (s : Int)) (SA.gateTime p.toParams s) := by
  intro w hsw hwg hm
  have hw := (hR x w hm).2.2
  have h0 : 0 ≤ slotStartZ p (s : Int) := by
    change 0 ≤ 4 * p.Δ * (s : Int)
    have := p.deltaPos
    positivity
  have ha := wc_enabledGate_awakeClosed hV hx hG (w - 1)
    (by dsimp [Time] at *; omega) (by dsimp [Time] at *; omega)
    (by dsimp [Time] at *; omega)
  rw [ha] at hw
  cases hw

/-- Joinedness at this gate supplies its stored restart cutoff. -/
theorem wc_enabledGate_of_joinedAt (hS : V2.D.ScheduleWellFormed E rho)
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

/-- A completed nonempty WC result supplies its enabled origin gate. -/
theorem WCResult.enabled {w : HealingWitness} {iStar i j : Nat} {x : V}
    {s : Slot} {B : Block} (hr : WCResult p c E rho w iStar i j x s B)
    (hS : V2.D.ScheduleWellFormed E rho) : enabledGateAt p c E rho j x s :=
  wc_gate_enabled_of_result hS hr.event hr.value

/-- W3-G exposes the raw result only at an enabled gate. -/
theorem wc_gate_raw_enabled {j : Nat} {x : V} {s : Slot}
    (hS : V2.D.ScheduleWellFormed E rho) (hG : enabledGateAt p c E rho j x s) :
    gateResultAt p c E rho j = some (SA.Root.confirmationFrom p.toParams
      (eraseFG (storeAt p c E rho j x).fg.F)
      (actView (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s))) s) := by
  rw [gateResultAt_eq_gateResult p c E rho hS hG.1,
    gateResult_eq_saved p c E rho hS hG.1]
  exact fgsa_gate_saved_result E rho hS hG.1 (fgsa_gate_joined_of_enabled E rho hG)

/-- W3-J supplies the stored pre-gate test for the gate-write law. -/
theorem wc_gate_pre_joined {j : Nat} {x : V} {s : Slot}
    (hG : enabledGateAt p c E rho j x s) :
    joinedNow p (clockPre p (storeAt p c E rho j x) (SA.gateTime p.toParams s)) = true := by
  rw [clockPre_joined]
  exact fgsa_gate_joined_of_enabled E rho hG

/-- W3-G saves an empty executed result when the stored join test is false. -/
theorem wc_gate_suppressed {j : Nat} {x : V} {s : Slot}
    (hS : V2.D.ScheduleWellFormed E rho) (ht : IsGateTick p c rho j x s)
    (hJ : joinedAtTime p (storeAt p c E rho j x).restartTime
      (SA.gateTime p.toParams s) = false) : gateResultAt p c E rho j = some none := by
  rw [gateResultAt_eq_gateResult p c E rho hS ht,
    gateResult_eq_saved p c E rho hS ht]
  exact fgsa_gate_saved_unjoined E rho hS ht hJ

/-- Keep the all-time joined count until the intermediate gate actor is chosen. -/
theorem wc_joined_gate_witness [Fintype V] (hV : V2.D.ExecutionValid E rho)
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
  have hG := wc_enabledGate_of_joinedAt hV.toScheduleWellFormed hj hJ
  exact ⟨z, j, hz, hG, wc_enabledGate_awakeClosed hV hz hG⟩

/-- Source and suffix counts are joined at the inclusive source boundary. -/
theorem wc_joined_participation_split [Fintype V] {a cut t : Time}
    (hsource : ∀ r, a < r → r ≤ cut →
      (Gen.V2.Duty.faulty rho).card < (joinedHonest p E rho r).card)
    (hsuffix : ∀ r, cut < r → r ≤ rho.horizon →
      (Gen.V2.Duty.faulty rho).card < (joinedHonest p E rho r).card)
    (hat : a < t) (hth : t ≤ rho.horizon) :
    (Gen.V2.Duty.faulty rho).card < (joinedHonest p E rho t).card := by
  by_cases ht : t ≤ cut
  · exact hsource t hat ht
  · exact hsuffix t (lt_of_not_ge ht) hth

/-- N4 uses this receiver's event-index epoch, bounded by its enabled gate. -/
theorem wc_enabledGate_service_epoch (hV : V2.D.ExecutionValid E rho)
    (hR : V2.D.RestartsAtWakes E rho) {j : Nat} {x : V} {s : Slot}
    (hx : x ∈ rho.honest) (hG : enabledGateAt p c E rho j x s)
    {a freeze : Time} (ha : slotStartZ p (s : Int) ≤ a) (haf : a < freeze)
    (hf : freeze ≤ SA.gateTime p.toParams s) :
    V2.D.restartFree rho x (V2.D.Run.actionCut rho a) (V2.D.Run.idxBefore rho freeze) := by
  apply Gen.V2.Duty.restartFree_actionCut_idxBefore hV.toScheduleWellFormed haf
  intro k t ht hat htf
  exact wc_enabledGate_restartFreeTime hV hR hx hG t (ha.trans_lt hat)
    (htf.le.trans hf) (List.mem_of_getElem? ht)

/-- WC plan §6.5; DC a gate is after the completed cut exactly when its label is later. -/
theorem wc_gate_cut_iff (hsch : V2.D.ScheduleWellFormed E rho)
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


/-- A later awake epoch supplies a later enabled gate for the same reader.
The old result is ordered below that result, without an old awake premise. -/
theorem wc_currentEpoch_result {w : HealingWitness} {iStar i j : Nat} {x y : V}
    {s : Slot} {B : Block} {t wake : Time}
    (hS : V2.D.ScheduleWellFormed E rho) (hs : WCSeed p c E rho w iStar)
    (inv : WCInv p c E rho w iStar i)
    (hr : WCResult p c E rho w iStar i j x s B)
    (hy : confirmedReaderAtIdx p c E rho y i t)
    (hw : (storeAt p c E rho i y).restartTime = some wake)
    (hlate : slotStartZ p ((s + 1 : Nat) : Int) < wake) :
    ∃ k r C, s < r ∧ WCResult p c E rho w iStar i k y r C ∧
      Block.Preceq B C ∧ AwakeClosed E y (slotStartZ p (r : Int)) t ∧
      RestartFreeTime rho y (slotStartZ p (r : Int)) t := by
  have hc := hy.2.2
  rw [hw] at hc
  obtain ⟨r, k, hwr, _hrt, hki, hG, hA, hR⟩ := hc
  have hsr : s < r := by
    have ht := hlate.trans_le hwr
    change 4 * p.Δ * ((s + 1 : Nat) : Int) < 4 * p.Δ * (r : Int) at ht
    have hd := p.deltaPos
    have hcast : (s : Int) + 1 < r := by push_cast at ht; nlinarith
    exact Nat.lt_of_succ_lt (Int.ofNat_lt.mp (by exact_mod_cast hcast))
  have hlabel := hr.label.trans hsr
  have hk := (wc_gate_cut_iff hS hs hG.1).mpr hlabel
  obtain ⟨C, hC, _hQ, _hp⟩ := inv.nonempty k y r hk hki hy.1 hG hlabel
  have hresult : WCResult p c E rho w iStar i k y r C :=
    ⟨hy.1, hk, hki, hlabel, hG.1, hC⟩
  exact ⟨k, r, C, hsr, hresult, inv.ordered j k x y s r B C hr hresult hsr, hA, hR⟩

/-- Choose the earlier gate actor before transferring to the joined voter.
This witness serves T49, T53 and T57 without keeping the voter awake at that gate. -/
theorem wc_joined_retrospective_witness [Fintype V]
    (hV : V2.D.ExecutionValid E rho) (hdelta : E.Δ = p.Δ)
    {w : HealingWitness} {iStar i j : Nat} {x y : V} {s r : Slot} {B : Block}
    (hs : WCSeed p c E rho w iStar) (inv : WCInv p c E rho w iStar i)
    (hr : WCResult p c E rho w iStar i j x s B) (hsr : s < r)
    (hy : y ∈ rho.honest)
    (hJ : joinedAt p E rho y (r + 1) (SA.voteTime p.toParams (r + 1)))
    (hP : (Gen.V2.Duty.faulty rho).card <
      (joinedHonest p E rho (SA.gateTime p.toParams r)).card)
    (hh : SA.gateTime p.toParams r ≤ rho.horizon)
    (hcompleted : ∀ k z, IsGateTick p c rho k z r → k < i) :
    ∃ z k l, z ∈ rho.honest ∧ enabledGateAt p c E rho k z r ∧ l < k ∧
      WCHeadRead p c E rho l y (r + 1) B := by
  obtain ⟨z, k, hz, hG, _hA⟩ := wc_joined_gate_witness hV hdelta r hP hh
  have hlabel := hr.label.trans hsr
  have hk := (wc_gate_cut_iff hV.toScheduleWellFormed hs hG.1).mpr hlabel
  have hki := hcompleted k z hG.1
  obtain ⟨C, hC, _hQ, _hp⟩ := inv.nonempty k z r hk hki hz hG hlabel
  have hresult : WCResult p c E rho w iStar i k z r C :=
    ⟨hz, hk, hki, hlabel, hG.1, hC⟩
  have hBC := inv.ordered j k x z s r B C hr hresult hsr
  obtain ⟨l, hl, hhead⟩ := inv.retrospective k z r C hresult y hy hJ
  refine ⟨z, k, l, hz, hG, hl, hhead.event,
    block_preceq_trans hBC hhead.covers, ?_, hhead.receipts⟩
  intro A hAB
  exact hhead.path A (block_preceq_trans hAB hBC)

omit [DecidableEq V] in
private theorem wc_prefixTime_unfold (i : Nat) : prefixTime rho i =
    ((rho.events.take i).getLast?.map (fun e => e.time)).getD 0 := rfl

omit [DecidableEq V] in
/-- Every event in a finite prefix is at or before its final event time. -/
theorem wc_event_before_prefixTime (hS : V2.D.ScheduleWellFormed E rho)
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
  rw [wc_prefixTime_unfold, List.getLast?_eq_getElem?, List.length_take, Nat.min_eq_left hi,
    List.getElem?_take_of_lt (by omega), hf]
  exact ht

/-- A confirmed reader with an early marker has its own enabled covered gate. -/
theorem wc_confirmedReader_early_gate (hV : V2.D.ExecutionValid E rho)
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
    obtain ⟨w, hw, huw⟩ := wc_restart_marker_after hS he hj
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

/-- A public confirmed reader supplies its original gate in the same awake epoch. -/
theorem wc_confirmedReader_public_gate (hV : V2.D.ExecutionValid E rho)
    (hdelta : E.Δ = p.Δ) {i : Nat} {y : V} {r : Slot} {t : Time}
    (hy : confirmedReaderAtIdx p c E rho y i t)
    (hWakes : WakesAppliedAtIdx E rho y i t)
    (hhor : SA.gateTime p.toParams r ≤ rho.horizon)
    (ht : SA.gateTime p.toParams r ≤ t)
    (hcut : afterTicksIdx rho (SA.gateTime p.toParams r) ≤ i)
    (hmarker : ∀ w, (storeAt p c E rho i y).restartTime = some w →
      w ≤ slotStartZ p (r : Int)) :
    ∃ k < i, enabledGateAt p c E rho k y r := by
  have hS := hV.toScheduleWellFormed
  have hbound (j : Nat) (u : Time) (hj : j < i)
      (he : rho.events[j]? = some (.restart y u)) : u ≤ slotStartZ p (r : Int) := by
    obtain ⟨w, hw, huw⟩ := wc_restart_marker_after hS he hj
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
    obtain ⟨u, hgu, hut, hW⟩ := V2.D.Engine.wake_between ht hfalse hy.2.1
    obtain ⟨j, hj, he⟩ := hWakes u (h0.trans_lt hgu) hut hW
    exact (not_lt.mpr ((hbound j u hj he).trans hsg)) hgu
  have hclock : ((4 * r + 6 : Nat) : Time) * p.Δ = SA.gateTime p.toParams r := by
    change ((4 * r + 6 : Nat) : Int) * p.Δ = 4 * p.Δ * (r : Int) + 6 * p.Δ
    push_cast
    ring
  obtain ⟨k, hk, _⟩ := fgsa_tick_total E rho hS hdelta y hy.1 (4 * r + 6)
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

/-- Receipt anchors at max(send,GST) meet the unchanged deadline exactly. -/
theorem wc_receipt_anchor_deadline (send gst a : Time)
    (hsa : send ≤ a) (ha : a ≤ max send gst) :
    max a gst + p.Δ = max send gst + p.Δ := by
  have h : max a gst = max send gst := by
    apply le_antisymm
    · exact max_le ha (le_max_right _ _)
    · exact max_le (hsa.trans (le_max_left _ _)) (le_max_right _ _)
  rw [h]

/-- An anchor after the old maximum cannot meet the old receipt deadline. -/
theorem wc_receipt_anchor_late (send gst a : Time) (ha : max send gst < a) :
    ¬ max a gst + p.Δ ≤ max send gst + p.Δ := by
  have h := le_max_left a gst
  dsimp [Time] at *
  omega

end AvailableChain.FGSA.Run
end
