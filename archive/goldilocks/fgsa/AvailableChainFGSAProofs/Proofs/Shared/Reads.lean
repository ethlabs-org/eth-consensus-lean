module
public import AvailableChainFGSAClaims.Statements.Reads
public import AvailableChainFGSARun.Statements.Interface
public import AvailableChainFGSAProofs.Proofs.Shared.CatchUp

public section

/-! Post-gate cut proofs (P3 F0.1). -/

namespace AvailableChain.FGSA.Run

variable {V : Type} {In : Type} {P : V2.ProtocolSpecD In}
    (E : Generic.Env V) (rho : V2.D.Run V P)

private theorem cut_downward (t : Time) :
    ∀ e f : V2.Event V P.Object, e.key ≤ f.key →
      cutPred t f = true → cutPred t e = true := by
  intro e f hk hf
  exact decide_eq_true (hk.trans (of_decide_eq_true hf))

variable [DecidableEq V]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The post-gate cut is an event-prefix state. -/
theorem afterTicks_eq_stateBefore (hs : V2.D.ScheduleWellFormed E rho) (t : Time) :
    afterTicks E rho t = V2.D.Run.stateBefore E rho (afterTicksIdx rho t) := by
  exact congrArg (fun events => events.foldl (V2.D.World.step E rho) V2.D.World.init)
    (V2.D.Engine.filter_eq_take hs (cutPred t) (cut_downward t))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Later ticks at the cut belong to other nodes. No restart premise is needed. -/
theorem afterTicks_node (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t)) :
    afterTicks E rho t v =
      (V2.D.tick E rho (V2.D.Run.stateBefore E rho i v) v t).1 := by
  have hf := V2.D.Engine.filter_eq_take hs (cutPred t) (cut_downward t)
  have hcut : cutPred t (V2.Event.tick v t : V2.Event V P.Object) = true :=
    decide_eq_true le_rfl
  have hic : i < afterTicksIdx rho t := by
    by_contra hn
    have hfalse := V2.D.Engine.filter_false_of_index_ge hs (cutPred t)
      (cut_downward t) (Nat.le_of_not_gt hn) hi
    rw [hcut] at hfalse
    contradiction
  rw [afterTicks_eq_stateBefore E rho hs t]
  calc
    V2.D.Run.stateBefore E rho (afterTicksIdx rho t) v =
        V2.D.Run.stateBefore E rho (i + 1) v := by
      apply V2.D.Engine.stateBefore_other_node E rho (Nat.succ_le_of_lt hic)
      intro j e hij hjc hj hnode
      have hm : e ∈ rho.events.filter (cutPred t) := by
        rw [hf]
        apply List.mem_of_getElem? (i := j)
        change (rho.events.take (afterTicksIdx rho t))[j]? = some e
        rw [List.getElem?_take_of_lt hjc]
        exact hj
      have hecut : e.key ≤ toLex (t, 1) :=
        of_decide_eq_true (List.mem_filter.mp hm).2
      obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
      obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
      have hk := (List.pairwise_iff_getElem.mp hs.sorted) i j hil hjl (by omega)
      rw [hie, hje] at hk
      change toLex (t, 1) ≤ toLex (e.time, e.phase) at hk
      change toLex (e.time, e.phase) ≤ toLex (t, 1) at hecut
      have hpair : (e.time, e.phase) = (t, 1) :=
        congrArg ofLex (le_antisymm hecut hk)
      have ht : e.time = t := congrArg Prod.fst hpair
      have hp : e.phase = 1 := congrArg Prod.snd hpair
      have he : e = .tick v t := by
        cases e with
        | restart u a => change (0 : Nat) = 1 at hp; contradiction
        | tick u a => change u = v at hnode; change a = t at ht; rw [hnode, ht]
        | deliver u o a => change (2 : Nat) = 1 at hp; contradiction
      have hji : j = i :=
        (List.Nodup.getElem_inj_iff hs.nodup).mp (by rw [hje, hie, he])
      omega
    _ = _ := (V2.D.Run.step_tick_eq E rho hi).1

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Without restarts, the tick input is the strict-before-time read. -/
theorem afterTicks_eq_tick_preTick (hs : V2.D.ScheduleWellFormed E rho)
    (hnr : V2.D.NoRestart rho) {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t)) :
    afterTicks E rho t v =
      (V2.D.tick E rho (V2.D.Run.stateBeforeTime E rho t v) v t).1 := by
  rw [afterTicks_node E rho hs hi, V2.D.Engine.stateBefore_tick_eq_stateBeforeTime hs hnr hi]

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The strict-before index is before the cut, and the inclusive index is after it. -/
theorem preIdx_le_afterTicksIdx (hs : V2.D.ScheduleWellFormed E rho) (t : Time) :
    (rho.events.filter (fun e => decide (e.time < t))).length ≤ afterTicksIdx rho t ∧
    afterTicksIdx rho t ≤ (rho.events.filter (fun e => decide (e.time ≤ t))).length := by
  have _ := hs.sorted
  constructor
  · change _ ≤ (rho.events.filter (cutPred t)).length
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro e _ he
    exact decide_eq_true (Prod.Lex.toLex_le_toLex.mpr (Or.inl (of_decide_eq_true he)))
  · change (rho.events.filter (cutPred t)).length ≤ _
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro e _ he
    rcases Prod.Lex.toLex_le_toLex.mp (of_decide_eq_true he) with h | ⟨h, _⟩
    · exact decide_eq_true (le_of_lt h)
    · exact decide_eq_true (le_of_eq h)

omit [DecidableEq V] in
/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The post-gate index increases with time. -/
theorem afterTicksIdx_mono (rho : V2.D.Run V P) {t u : Time} (htu : t ≤ u) :
    afterTicksIdx rho t ≤ afterTicksIdx rho u := by
  change (rho.events.filter (cutPred t)).length ≤ (rho.events.filter (cutPred u)).length
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro e _ he
  have htu' : toLex (t, (1 : Nat)) ≤ toLex (u, 1) :=
    Prod.Lex.toLex_le_toLex.mpr (htu.lt_or_eq.imp id (fun h => ⟨h, le_rfl⟩))
  exact decide_eq_true ((of_decide_eq_true he).trans htu')

end AvailableChain.FGSA.Run


namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

local instance (w : Option Time) (cut : Time) :
    Decidable (match w with | none => True | some t => t ≤ cut) := by
  cases w <;> dsimp <;> infer_instance

variable (p : Params) {In : Type} (c : AppCodec In)
    {V : Type} [DecidableEq V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
A scheduled tick event has the same index as the tick reader.
DC: SAME event-index uniqueness; shared by the HEAD and exact-service proofs. -/
theorem fgsa_tickIdx_of_event (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {t : Time} (hi : rho.events[i]? = some (.tick x t)) :
    V2.D.Run.tickIdx? rho x t = some i := by
  have hil := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨j, hj⟩ : ∃ j, V2.D.Run.tickIdx? rho x t = some j := by
    rw [V2.D.Run.tickIdx?, ← Option.isSome_iff_exists, List.findIdx?_isSome, List.any_eq_true]
    refine ⟨rho.events[i], List.getElem_mem hil, ?_⟩
    rw [(List.getElem?_eq_some_iff.mp hi).2]
    simp
  have hji := fgsa_tick_unique E rho hs (V2.D.Run.tickIdx?_spec hj) hi
  exact hji ▸ hj

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The time read equals the new-label value saved by the scheduled gate.
T7.6 uses `gateStep_fresh` on `actView (clockPre ...)`; `clockPre_fg` fixes F. -/
theorem gateResult_eq_saved (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {s : Slot} (hi : IsGateTick p c rho i x s) :
    gateResult p c E rho x s =
      GridCO.savedGenuine
        (((fgsa p c).clock (V2.D.Run.stateBefore E rho i x)
          (SA.gateTime p.toParams s)).st.base) s := by
  classical
  have ht := fgsa_tickIdx_of_event p c E rho hs hi
  rw [gateResult_def, gateIn_def, preTick_def, ht]
  dsimp only [Option.map_some]
  have hrtime : (clockPre p (V2.D.Run.stateBefore E rho i x).st
      (SA.gateTime p.toParams s)).restartTime =
      (V2.D.Run.stateBefore E rho i x).st.restartTime := by
    unfold clockPre
    dsimp only
    split_ifs <;> rfl
  rw [clockPre_fg, hrtime]
  have hslot : p.slotOf (SA.gateTime p.toParams s) = s + 1 :=
    (fgsa_postClock_slot (c := c) (V2.D.Run.stateBefore E rho i x) _).2.symm.trans
      (fgsa_gate_slot (c := c) (V2.D.Run.stateBefore E rho i x) s)
  have hg := fgsa_gate_saved_guarded E rho hs hi
  change GridCO.savedGenuine
    (((fgsa p c).clock (V2.D.Run.stateBefore E rho i x)
      (SA.gateTime p.toParams s)).st.base) s = _ at hg
  cases hr : (V2.D.Run.stateBefore E rho i x).st.restartTime with
  | none =>
    rw [hr] at hg
    change GridCO.savedGenuine _ _ = some (SA.Root.confirmationFrom p.toParams
      (eraseFG (V2.D.Run.stateBefore E rho i x).st.fg.F)
      (actView (clockPre p (V2.D.Run.stateBefore E rho i x).st
        (SA.gateTime p.toParams s))) s) at hg
    simpa only [hr, decide_true, ite_true] using hg.symm
  | some w =>
    rw [hr] at hg
    change GridCO.savedGenuine _ _ = some (if
      decide (w ≤ 4 * p.Δ * ((p.slotOf (SA.gateTime p.toParams s) : Int) - 1)) then
        _ else none) at hg
    simp only [hslot, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hg
    by_cases hw : w ≤ 4 * p.Δ * (s : Int)
    · simpa only [hr, hw, decide_true, ite_true] using hg.symm
    · simpa only [hr, hw, decide_false, Bool.false_eq_true, ite_false] using hg.symm




/-- An executed nonempty result supplies the joined raw branch at the same tick. -/
theorem fgsa_gate_raw_of_nonempty (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {s : Slot} {B : Block} (hi : IsGateTick p c rho i x s)
    (h : gateResult p c E rho x s = some (some B)) :
    joinedAtTime p (V2.D.Run.stateBefore E rho i x).st.restartTime
      (SA.gateTime p.toParams s) = true ∧
    SA.Root.confirmationFrom p.toParams
      (eraseFG (clockPre p (V2.D.Run.stateBefore E rho i x).st
        (SA.gateTime p.toParams s)).fg.F)
      (actView (clockPre p (V2.D.Run.stateBefore E rho i x).st
        (SA.gateTime p.toParams s))) s = some B := by
  have hg := fgsa_gate_saved_guarded E rho hs hi
  have hsave := (gateResult_eq_saved p c E rho hs hi).symm.trans h
  change GridCO.savedGenuine (FGSA.clock p (V2.D.Run.stateBefore E rho i x).st
    (SA.gateTime p.toParams s)).base s = some (some B) at hsave
  dsimp only at hg
  rw [hsave] at hg
  cases hj : joinedAtTime p (V2.D.Run.stateBefore E rho i x).st.restartTime
      (SA.gateTime p.toParams s) with
  | false => simp only [hj, Bool.false_eq_true, ite_false, Option.some.injEq] at hg; cases hg
  | true =>
    simp only [hj, ite_true, Option.some.injEq] at hg
    exact ⟨rfl, by simpa only [clockPre_fg] using hg.symm⟩

private theorem fgsa_read_gate_label (s : Slot) :
    ((SA.gateTime p.toParams s - 6 * p.Δ) / (4 * p.Δ)).toNat = s := by
  have ht : SA.gateTime p.toParams s - 6 * p.Δ = 4 * p.Δ * (s : Int) := by
    change 4 * p.Δ * (s : Int) + 6 * p.Δ - 6 * p.Δ = _
    ring
  have hDelta : (0 : Int) < p.Δ := p.deltaPos
  have hn : (4 * p.Δ : Int) ≠ 0 := by omega
  rw [ht, Int.mul_ediv_cancel_left _ hn, Int.toNat_natCast]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The clock test holds exactly at gate times. -/
theorem isGateTime_iff (p : Params) (t : Time) :
    isGateTime p t = true ↔ ∃ s : Slot, SA.gateTime p.toParams s = t := by
  constructor
  · intro h
    have hh : 0 ≤ t - 6 * p.Δ ∧
        t = SA.gateTime p.toParams ((t - 6 * p.Δ) / (4 * p.Δ)).toNat := by
      simpa only [isGateTime_def, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using h
    exact ⟨_, hh.2.symm⟩
  · rintro ⟨s, rfl⟩
    have hn : 0 ≤ SA.gateTime p.toParams s - 6 * p.Δ := by
      change 0 ≤ 4 * p.Δ * (s : Int) + 6 * p.Δ - 6 * p.Δ
      have := p.deltaPos
      nlinarith [Int.natCast_nonneg s]
    simp only [isGateTime_def, fgsa_read_gate_label, hn, decide_true,
      beq_self_eq_true, Bool.and_self]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Index and time forms of the raw gate result agree. -/
theorem gateResultAt_eq_gateResult (hs : V2.D.ScheduleWellFormed E rho)
    {j : Nat} {x : V} {s : Slot} (hj : IsGateTick p c rho j x s) :
    gateResultAt p c E rho j = gateResult p c E rho x s := by
  have ht := fgsa_tickIdx_of_event p c E rho hs hj
  have hg := (isGateTime_iff p (SA.gateTime p.toParams s)).mpr ⟨s, rfl⟩
  -- Reduce the index match without exporting its equation lemmas.
  change (match rho.events[j]? with
    | some (.tick y t) => if isGateTime p t then
        some (if (match (FGSA.clockPre p (V2.D.Run.stateBefore E rho j y).st t).restartTime
          with
          | none => True
          | some w => w ≤ 4 * p.Δ * (((t - 6 * p.Δ) / (4 * p.Δ)).toNat : Int)) then
          SA.Root.confirmationFrom p.toParams
          (eraseFG (FGSA.clockPre p (V2.D.Run.stateBefore E rho j y).st t).fg.F)
          (FGSA.actView (FGSA.clockPre p (V2.D.Run.stateBefore E rho j y).st t))
          ((t - 6 * p.Δ) / (4 * p.Δ)).toNat else none)
      else none
    | _ => none) = _
  rw [show rho.events[j]? = some (.tick x (SA.gateTime p.toParams s)) from hj]
  dsimp only
  rw [hg, ite_eq_left rfl, fgsa_read_gate_label, gateResult_def, gateIn_def, preTick_def, ht]
  rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The next-vote time read is the HEAD computation at that tick's index. -/
theorem vHead_eq_headAtIdx (hs : V2.D.ScheduleWellFormed E rho)
    {k : Nat} {y : V} {s : Slot}
    (hk : rho.events[k]? = some (.tick y (SA.voteTime p.toParams (s + 1)))) :
    vHead p c E rho y s = some (headAtIdx p c E rho k (s + 1)) := by
  have ht := fgsa_tickIdx_of_event p c E rho hs hk
  rw [vHead_def, postClock_def, preTick_def, ht]
  change _ = some (match rho.events[k]? with
    | some (.tick x t) => FGSA.headVote p ((fgsa p c).clock
        (V2.D.Run.stateBefore E rho k x) t).st (s + 1)
    | _ => .genesis)
  rw [hk]
  rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The action source uses the fast-write row of round `r`, with no fallback. -/
theorem actionSourceFG_eq_round (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {r : Nat}
    (hi : rho.events[i]? = some (.tick x (p.actionTime r))) :
    let st := ((fgsa p c).clock (V2.D.Run.stateBefore E rho i x) (p.actionTime r)).st
    actionSourceFG p c E rho x r = some
      (deepest ((fullTree p st).filter (fun B =>
        decide (eraseFG B ∈ (fastWriteAt st (r * p.R)).getD []) &&
          match leaseOf st (eraseFG B) with
          | some d => decide (st.base.now < d)
          | none => false))) := by
  intro st
  have ht := fgsa_tickIdx_of_event p c E rho hs hi
  rw [actionSourceFG_def, postClock_def, preTick_def, ht]
  change some (deepest ((fullTree p st).filter (fun B =>
    decide (eraseFG B ∈ (fastWriteAt st (p.round (st.slot p) * p.R)).getD []) &&
      match leaseOf st (eraseFG B) with
      | some d => decide (st.base.now < d)
      | none => false))) = _
  rw [(fgsa_action_slot_round (c := c) (V2.D.Run.stateBefore E rho i x) r).2]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
An index witness implies finalization in the strict-before state. -/
theorem acceptsFinalBefore_of_idx (hnr : V2.D.NoRestart rho)
    (hs : V2.D.ScheduleWellFormed E rho) {x : V} {X : FGBlock (Fin p.n)} {d : Time}
    (h : ∃ i ≤ rho.events.length,
      (∀ k < i, ∃ e, rho.events[k]? = some e ∧ e.time < d) ∧
      FGBlock.Preceq X (storeAt p c E rho i x).fg.F) :
    AcceptsFinalBefore p c E rho x X d :=
  (Gen.V2.Duty.holdsBefore_iff_exists_idx hnr hs (fgsa_monoAlong_preceq_F p c X)).mpr h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 22:1382–1384; FirstFinality plan §8. DC: SAME prefix coverage.
Without restarts, acceptance before a deadline holds before any later deadline. -/
theorem acceptsFinalBefore_mono_deadline (hnr : V2.D.NoRestart rho)
    (hs : V2.D.ScheduleWellFormed E rho) {x : V} {X : FGBlock (Fin p.n)}
    {d d' : Time} (hdd : d ≤ d') (h : AcceptsFinalBefore p c E rho x X d) :
    AcceptsFinalBefore p c E rho x X d' := by
  obtain ⟨i, hi, hbefore, hX⟩ :=
    (Gen.V2.Duty.holdsBefore_iff_exists_idx hnr hs
      (fgsa_monoAlong_preceq_F p c X)).mp h
  apply acceptsFinalBefore_of_idx p c E rho hnr hs
  refine ⟨i, hi, ?_, hX⟩
  intro k hk
  obtain ⟨e, he, ht⟩ := hbefore k hk
  exact ⟨e, he, ht.trans_le hdd⟩

/-- Acceptance of a descendant before a deadline also accepts each ancestor. -/
theorem acceptsFinalBefore_mono_ancestor (hnr : V2.D.NoRestart rho)
    (hs : V2.D.ScheduleWellFormed E rho) {x : V} {X U : FGBlock (Fin p.n)}
    {d d' : Time} (hXU : FGBlock.Preceq X U) (hdd : d ≤ d')
    (h : AcceptsFinalBefore p c E rho x U d) : AcceptsFinalBefore p c E rho x X d' := by
  obtain ⟨i, hi, hbefore, hU⟩ :=
    (Gen.V2.Duty.holdsBefore_iff_exists_idx hnr hs (fgsa_monoAlong_preceq_F p c U)).mp h
  apply acceptsFinalBefore_of_idx p c E rho hnr hs
  refine ⟨i, hi, ?_, KitFG.preceq_trans hXU hU⟩
  intro k hk
  obtain ⟨e, he, ht⟩ := hbefore k hk
  exact ⟨e, he, ht.trans_le hdd⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
The stable read at the post-gate cut is the post-clock stable read. -/
theorem stable_afterTicks (hs : V2.D.ScheduleWellFormed E rho) (hnr : V2.D.NoRestart rho)
    {i : Nat} {v : V} {t : Time} (hi : rho.events[i]? = some (.tick v t)) :
    (fgsaInterface p c).stable (afterTicks E rho t v) =
      (fgsaInterface p c).stable ((fgsa p c).clock (V2.D.Run.stateBeforeTime E rho t v) t) := by
  rw [afterTicks_eq_tick_preTick E rho hs hnr hi]
  exact (fgsaOutputs p c).stable_tick E rho _ v t

end AvailableChain.FGSA.Run

end
