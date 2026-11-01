module
public import AvailableChainFGSAClaims.Statements.WeakContinuationGrowth

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} {c : AppCodec In} [DecidableEq V]
    {E E' : Generic.Env V} {source rho : V2.D.Run V (fgsa p c)}

private def localStep (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (x : V) (st : (fgsa p c).State) : V2.Event V (fgsa p c).Object → (fgsa p c).State
  | .restart v t => if v = x then (fgsa p c).restore ((fgsa p c).durable st) t else st
  | .tick v t => if v = x then (V2.D.tick E rho st v t).1 else st
  | .deliver v o _ => if v = x then (fgsa p c).process st o else st

private theorem step_local (world : V2.D.World V (fgsa p c)) (x : V)
    (e : V2.Event V (fgsa p c).Object) :
    V2.D.World.step E rho world e x = localStep E rho x (world x) e := by
  cases e with
  | restart v t =>
    change Function.update world v _ x = if v = x then _ else _
    by_cases h : v = x
    · subst v; simp
    · rw [ite_eq_right h, Function.update_of_ne (Ne.symm h)]
  | tick v t =>
    change Function.update world v _ x = if v = x then _ else _
    by_cases h : v = x
    · subst v; simp
    · rw [ite_eq_right h, Function.update_of_ne (Ne.symm h)]
  | deliver v o t =>
    change Function.update world v _ x = if v = x then _ else _
    by_cases h : v = x
    · subst v; simp
    · rw [ite_eq_right h, Function.update_of_ne (Ne.symm h)]

private theorem fold_local (events : List (V2.Event V (fgsa p c).Object))
    (world : V2.D.World V (fgsa p c)) (x : V) :
    (events.foldl (V2.D.World.step E rho) world) x =
      events.foldl (localStep E rho x) (world x) := by
  induction events generalizing world with
  | nil => rfl
  | cons e es ih =>
    change (es.foldl _ (V2.D.World.step E rho world e)) x = es.foldl _ _
    rw [ih, step_local]

private theorem localStep_other (x : V) (st : (fgsa p c).State)
    (e : V2.Event V (fgsa p c).Object) (h : e.node ≠ x) :
    localStep E rho x st e = st := by
  cases e with
  | restart v t => exact ite_eq_right h
  | tick v t => exact ite_eq_right h
  | deliver v o t => exact ite_eq_right h

private theorem fold_filter_local (events : List (V2.Event V (fgsa p c).Object))
    (st : (fgsa p c).State) (x : V) :
    events.foldl (localStep E rho x) st =
      (events.filter (fun e => decide (e.node = x))).foldl (localStep E rho x) st := by
  induction events generalizing st with
  | nil => rfl
  | cons e es ih =>
    by_cases h : e.node = x
    · simp only [List.foldl_cons, List.filter_cons, h, decide_true,
        ite_true]
      exact ih _
    · simp only [List.foldl_cons, List.filter_cons, h, decide_false, Bool.false_eq_true,
        ite_false]
      rw [localStep_other x st e h]
      exact ih _

theorem wcg_tick_retained (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (x : V) (hx : x ∈ rho.honest) (st : (fgsa p c).State)
    (t : Time) (ht : t ≤ source.horizon) :
    V2.D.tick E' rho st x t = V2.D.tick E source st x t := by
  have hseats : ∀ l, rho.ownSeats l x = source.ownSeats l x := by
    intro l
    change (List.finRange _).filter (fun i => decide (rho.seatOf l i = x)) =
      (List.finRange _).filter (fun i => decide (source.seatOf l i = x))
    rw [ha.seats]
  change (let st' := (fgsa p c).clock st t
          let released := if E'.awake x t then _ else []
          ((released.filter _).foldl _ st', released)) =
         (let st' := (fgsa p c).clock st t
          let released := if E.awake x t then _ else []
          ((released.filter _).foldl _ st', released))
  simp only [ha.awake x hx t ht, ha.inputs x hx t ht, hseats]

/-- DC local replay: a time-bounded filter can discard arbitrary events at
other validators. It does not identify the two global event positions. -/
theorem wcg_filtered_replay (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (x : V) (hx : x ∈ rho.honest)
    (test : V2.Event V (fgsa p c).Object → Bool)
    (htest : ∀ e, test e = true → e.time ≤ source.horizon) :
    ((rho.events.filter test).foldl (V2.D.World.step E' rho) V2.D.World.init) x =
      ((source.events.filter test).foldl (V2.D.World.step E source) V2.D.World.init) x := by
  simp only [fold_local]
  rw [fold_filter_local (E := E') (rho := rho) (rho.events.filter test),
    fold_filter_local (E := E) (rho := source) (source.events.filter test)]
  have hfilter : (rho.events.filter test).filter (fun e => decide (e.node = x)) =
      (source.events.filter test).filter (fun e => decide (e.node = x)) := by
    have hf := congrArg (List.filter test) (ha.events x hx)
    have normalize (es : List (V2.Event V (fgsa p c).Object)) :
        (es.filter (fun e => decide (e.node = x ∧ e.time ≤ source.horizon))).filter test =
          (es.filter test).filter (fun e => decide (e.node = x)) := by
      simp only [List.filter_filter]
      apply List.filter_congr
      intro e _
      by_cases ht : test e = true
      · have he := htest e ht
        simp [ht, he]
      · have he : test e = false := Bool.eq_false_iff.mpr ht
        simp [he]
    simpa only [normalize] using hf
  rw [hfilter]
  apply List.foldl_ext
  intro st e he
  have he' := List.mem_filter.mp he
  have hn := of_decide_eq_true he'.2
  have ht := htest e (List.mem_filter.mp he'.1).2
  cases e with
  | restart v t => rfl
  | deliver v o t => rfl
  | tick v t =>
    change v = x at hn
    subst v
    change (if x = x then (V2.D.tick E' rho st x t).1 else st) =
      (if x = x then (V2.D.tick E source st x t).1 else st)
    rw [ite_eq_left rfl, ite_eq_left rfl, wcg_tick_retained ha x hx st t ht]

/-- Inclusive public reads agree at each retained validator through T. -/
theorem wcg_readReplay (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (x : V) (hx : x ∈ rho.honest) {t : Time} (ht : t ≤ source.horizon) :
    rho.readAt E' t x = source.readAt E t x :=
  wcg_filtered_replay ha x hx _ (fun _ he => (of_decide_eq_true he).trans ht)

/-- Completed-gate worlds agree locally; the cut indices remain run-specific. -/
theorem wcg_afterTicksReplay (ha : RetainedAgreesThrough₂ p c E source E' rho)
    (x : V) (hx : x ∈ rho.honest) {t : Time} (ht : t ≤ source.horizon) :
    afterTicks E' rho t x = afterTicks E source t x := by
  apply wcg_filtered_replay ha x hx
  intro e he
  rcases Prod.Lex.toLex_le_toLex.mp (of_decide_eq_true he) with h | ⟨h, _⟩
  · exact h.le.trans ht
  · exact h.le.trans ht

end AvailableChain.FGSA.Run
end
