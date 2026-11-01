module
public import AvailableChainFGSAProofs.Proofs.WeakContinuationGrowth.EventReplay
public import AvailableChainFGSAProofs.Statements.WeakContinuation

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E E' : Generic.Env V} {source rho : V2.D.Run V (fgsa p c)}

/-- Local store replay uses the completed-gate index of each run. -/
theorem wcg_cut_storeReplay (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hs : V2.D.ScheduleWellFormed E source) (hr : V2.D.ScheduleWellFormed E' rho)
    (x : V) (hx : x ∈ rho.honest) {t : Time} (ht : t ≤ source.horizon) :
    storeAt p c E' rho (afterTicksIdx rho t) x =
      storeAt p c E source (afterTicksIdx source t) x := by
  have he := wcg_afterTicksReplay ha x hx ht
  rw [afterTicks_eq_stateBefore E' rho hr, afterTicks_eq_stateBefore E source hs] at he
  exact congrArg (fun st => st.st) he

/-- Retained validators keep the seed's state fields at their own cut.
Historical origin fields of WCSeed require separate index and quorum proofs. -/
theorem wcg_seed_state (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hsource : V2.D.ScheduleWellFormed E source)
    (hrho : V2.D.ScheduleWellFormed E' rho) {w : HealingWitness} {iSource : Nat}
    (hs : WCSeed p c E source w iSource)
    (hend : SA.gateTime p.toParams w.u ≤ source.horizon) :
    let iRho := afterTicksIdx rho (SA.gateTime p.toParams w.u)
    ∀ x ∈ rho.honest,
      S_at p c E' rho iRho x = w.QStar ∧
      w.M + 1 ≤ (storeAt p c E' rho iRho x).fg.h_max ∧
      Block.Preceq (F_at p c E' rho iRho x) w.QStar ∧
      ∀ row ∈ (storeAt p c E' rho iRho x).base.obligations,
        (storeAt p c E' rho iRho x).base.now < row.2.2 → Block.Preceq row.1 w.QStar := by
  intro iRho x hx
  have he : storeAt p c E' rho iRho x = storeAt p c E source iSource x := by
    rw [hs.cut]
    exact wcg_cut_storeReplay ha hsource hrho x hx hend
  have hm := ha.honest hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (storeAt p c E' rho iRho x).base.stableRecord = w.QStar
    rw [he]
    exact hs.refreshed x hm
  · rw [he]
    exact hs.height x hm
  · change Block.Preceq (eraseFG (storeAt p c E' rho iRho x).fg.F) w.QStar
    rw [he]
    exact hs.finalBelow x hm
  · rw [he]
    exact hs.liveTargets x hm

omit [DecidableEq V] in
private theorem cut_downward (t : Time) :
    ∀ e f : V2.Event V (fgsa p c).Object, e.key ≤ f.key →
      cutPred t f = true → cutPred t e = true := by
  intro e f hef hf
  exact decide_eq_true (hef.trans (of_decide_eq_true hf))

omit [DecidableEq V] in
/-- Every tick through the cut occurs before the completed-gate index. -/
theorem wcg_tick_before_cut (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {x : V} {t d : Time} (he : rho.events[i]? = some (.tick x t))
    (ht : t ≤ d) : i < afterTicksIdx rho d := by
  by_contra h
  have hf := V2.D.Engine.filter_false_of_index_ge hs (cutPred d)
    (cut_downward d) (Nat.le_of_not_gt h) he
  have hc : cutPred d (.tick x t : V2.Event V (fgsa p c).Object) = true := by
    apply decide_eq_true
    exact Prod.Lex.toLex_le_toLex.mpr (ht.lt_or_eq.imp id (fun h => ⟨h, le_rfl⟩))
  rw [hc] at hf
  cases hf

omit [DecidableEq V] in
/-- An event before the cut has time at most the cut time. -/
theorem wcg_time_before_cut (hs : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {e : V2.Event V (fgsa p c).Object} {d : Time}
    (he : rho.events[i]? = some e) (hi : i < afterTicksIdx rho d) : e.time ≤ d := by
  have hm : e ∈ rho.events.filter (cutPred d) := by
    rw [V2.D.Engine.filter_eq_take hs (cutPred d) (cut_downward d)]
    apply List.mem_of_getElem? (i := i)
    change (rho.events.take (afterTicksIdx rho d))[i]? = some e
    rw [List.getElem?_take_of_lt hi]
    exact he
  have hkey := of_decide_eq_true (List.mem_filter.mp hm).2
  rcases Prod.Lex.toLex_le_toLex.mp hkey with h | ⟨h, _⟩
  · exact le_of_lt h
  · exact le_of_eq h

/-- Optional pre-tick reads agree, including the case of an absent tick. -/
theorem wcg_preTickReplay (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hs : V2.D.ScheduleWellFormed E source) (hr : V2.D.ScheduleWellFormed E' rho)
    (x : V) (hx : x ∈ rho.honest) {t : Time} (ht : t ≤ source.horizon) :
    preTick E' rho x t = preTick E source x t := by
  rw [preTick_def, preTick_def]
  cases hk : rho.tickIdx? x t with
  | none =>
    cases hj : source.tickIdx? x t with
    | none => rfl
    | some j =>
      obtain ⟨k, he, _⟩ := wcg_tickEventReplay ha hs hr hx ht
        (V2.D.Run.tickIdx?_spec hj)
      have := fgsa_tickIdx_of_event p c E' rho hr he
      rw [hk] at this
      cases this
  | some k =>
    obtain ⟨j, hj, he⟩ := wcg_tickSourceReplay ha hs hr hx ht
      (V2.D.Run.tickIdx?_spec hk)
    rw [fgsa_tickIdx_of_event p c E source hs hj]
    exact congrArg some he

private def replay_guardDecidable (w : Option Time) (cut : Time) :
    Decidable (match w with | none => True | some t => t ≤ cut) := by
  cases w <;> dsimp <;> infer_instance

private def replay_gateAt (p : Params) {In : Type} (c : AppCodec In)
    {V : Type} [DecidableEq V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (j : Nat) : Option (Option Block) :=
  match rho.events[j]? with
  | some (.tick x t) =>
      if isGateTime p t then
        let st := FGSA.clockPre p (rho.stateBefore E j x).st t
        letI := replay_guardDecidable st.restartTime
          (4 * p.Δ * (((t - 6 * p.Δ) / (4 * p.Δ)).toNat : Int))
        some (if (match st.restartTime with
          | none => True
          | some w => w ≤ (4 * p.Δ * (((t - 6 * p.Δ) / (4 * p.Δ)).toNat : Int)))
          then SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (FGSA.actView st)
            ((t - 6 * p.Δ) / (4 * p.Δ)).toNat else none)
      else none
  | _ => none

private def replay_headAt (p : Params) {In : Type} (c : AppCodec In)
    {V : Type} [DecidableEq V] (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (j : Nat) (s : Slot) : Block :=
  match rho.events[j]? with
  | some (.tick x t) => headVote p ((fgsa p c).clock (rho.stateBefore E j x) t).st s
  | _ => .genesis

private theorem replay_gateAt_eq (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (j : Nat) : gateResultAt p c E rho j = replay_gateAt p c E rho j := rfl

private theorem replay_headAt_eq (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (j : Nat) (s : Slot) : headAtIdx p c E rho j s = replay_headAt p c E rho j s := rfl

/-- Matched ticks have the same raw gate result and deterministic HEAD. -/
theorem wcg_tickReads {j k : Nat} {x : V} {t : Time}
    (hj : source.events[j]? = some (.tick x t))
    (hk : rho.events[k]? = some (.tick x t))
    (he : rho.stateBefore E' k x = source.stateBefore E j x) :
    gateResultAt p c E' rho k = gateResultAt p c E source j ∧
    ∀ s, headAtIdx p c E' rho k s = headAtIdx p c E source j s := by
  simp only [replay_gateAt_eq, replay_headAt_eq]
  unfold replay_gateAt replay_headAt
  rw [hk, hj]
  dsimp only
  rw [he]
  exact ⟨rfl, fun _ => rfl⟩

/-- The gate guard transfers at the matched occurrence. -/
theorem wcg_tickPassed {j k : Nat} {x : V} {t : Time}
    (hj : source.events[j]? = some (.tick x t))
    (hk : rho.events[k]? = some (.tick x t))
    (he : rho.stateBefore E' k x = source.stateBefore E j x)
    (hp : gatePassedAt p c E source j) : gatePassedAt p c E' rho k := by
  obtain ⟨y, s, hy, hp⟩ := hp
  have hxy : y = x ∧ SA.gateTime p.toParams s = t := by
    exact V2.Event.tick.inj (Option.some.inj (hy.1.symm.trans hj))
  obtain ⟨hxy, ht⟩ := hxy
  subst y
  have hstore : storeAt p c E' rho k x = storeAt p c E source j x :=
    congrArg (fun st => st.st) he
  refine ⟨x, s, ⟨?_, ?_⟩, ?_⟩
  · change rho.events[k]? = _
    rw [ht]
    exact hk
  · rw [hstore]
    exact hy.2
  · simpa only [hstore] using hp

/-- Signed action rows replay at the source index with the same wire. -/
theorem wcg_rowSourceReplay (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hs : V2.D.ScheduleWellFormed E source) (hr : V2.D.ScheduleWellFormed E' rho)
    {k : Nat} {x : V} {r : Nat} {a : RowWire p.n}
    (hrow : HonestRowAt p c E' rho k x r a) (ht : p.actionTime r ≤ source.horizon) :
    ∃ j, HonestRowAt p c E source j x r a := by
  obtain ⟨j, hj, he⟩ := wcg_tickSourceReplay ha hs hr hrow.1 ht hrow.2.1
  refine ⟨j, ha.honest hrow.1, hj, ?_⟩
  have hem := hrow.2.2
  rw [(V2.D.Run.step_tick_eq E' rho hrow.2.1).2,
    he, wcg_tick_retained ha x hrow.1 _ _ ht] at hem
  rwa [(V2.D.Run.step_tick_eq E source hj).2]

/-- Source and gate getters replay at the original action time. -/
theorem wcg_actionReads (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (hs : V2.D.ScheduleWellFormed E source) (hr : V2.D.ScheduleWellFormed E' rho)
    (x : V) (hx : x ∈ rho.honest) {r : Nat} (ht : p.actionTime r ≤ source.horizon) :
    actionSourceFG p c E' rho x r = actionSourceFG p c E source x r ∧
    gateResult p c E' rho x (r * p.R) = gateResult p c E source x (r * p.R) := by
  constructor
  · rw [actionSourceFG_def, actionSourceFG_def, postClock_def, postClock_def,
      wcg_preTickReplay ha hs hr x hx ht]
  · have ht' : SA.gateTime p.toParams (r * p.R) ≤ source.horizon := ht
    rw [gateResult_def, gateResult_def, gateIn_def, gateIn_def,
      wcg_preTickReplay ha hs hr x hx ht']

end AvailableChain.FGSA.Run
end
