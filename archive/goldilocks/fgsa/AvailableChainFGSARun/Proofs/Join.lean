module
public import AvailableChainFGSARun.Proofs.FGSource
public import AvailableChainFGSARun.Proofs.Acceptance
public import AvailableChainKitV2.DutySleep -- shake: keep (re-export)

public section

namespace AvailableChain.FGSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

private theorem join_reconcile_restartTime (st : State p.n) :
    (reconcile st).restartTime = st.restartTime := by
  unfold reconcile
  rw [normalizeS_fields]

/-- Processing keeps the last restart marker. -/
theorem fgsa_process_restartTime (st : State p.n) (o : Wire p.n) :
    (FGSA.process p st o).restartTime = st.restartTime := by
  unfold FGSA.process
  cases hd : o.decode with
  | none => rfl
  | some m =>
    cases m with
    | vote s i b => rfl
    | row i body =>
      change (admitRow p st ⟨o.auth, body⟩).restartTime = st.restartTime
      rcases admitRow_eq p st ⟨o.auth, body⟩ with h | h <;> rw [h]
    | block s N =>
      change (admitBlock p st s N).restartTime = st.restartTime
      cases hn : namedParentHeld st N with
      | false => rw [admitBlock_refused p st s N (Or.inl hn)]
      | true =>
        cases hp : parentFG st N.erase with
        | none => rw [admitBlock_refused p st s N (Or.inr (Or.inl hp))]
        | some B =>
          cases ha : blockAccepted p st s N B with
          | false => rw [admitBlock_refused p st s N (Or.inr (Or.inr ⟨B, hp, ha⟩))]
          | true =>
            obtain ⟨pool, he, -⟩ := admitBlock_accepted_eq p st s N B hn hp ha
            rw [he]
            dsimp only
            split
            · rfl
            · exact join_reconcile_restartTime _

/-- A bound on all prior local restarts bounds the stored marker. -/
theorem fgsa_restartTime_bound (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))
    (i : Nat) (v : V) (b : Time)
    (hR : ∀ j w, j < i → rho.events[j]? = some (.restart v w) → w ≤ b) :
    ∀ w, (V2.D.Run.stateBefore E rho i v).st.restartTime = some w → w ≤ b := by
  let Q : Node p → Prop := fun nd => ∀ w, nd.st.restartTime = some w → w ≤ b
  refine V2.D.Engine.stateBefore_step_induction E rho Q (Nat.zero_le i) v ?_ ?_
  · intro k e _ hki he hv hQ
    cases e with
    | restart u t =>
      change u = v at hv
      subst u
      simp only [V2.D.World.step, Function.update_self]
      intro w hw
      change (acRestart p (V2.D.Run.stateBefore E rho k v).st t).restartTime = some w at hw
      rw [acRestart_restartTime] at hw
      cases Option.some.inj hw
      exact hR k t hki he
    | tick u t =>
      change u = v at hv
      subst u
      intro w hw
      simp only [V2.D.World.step, Function.update_self] at hw
      rw [tick_st (c := c) E rho (V2.D.Run.stateBefore E rho k v) v t,
        fgsa_clock_restartTime] at hw
      exact hQ w hw
    | deliver u o t =>
      change u = v at hv
      subst u
      intro w hw
      simp only [V2.D.World.step, Function.update_self] at hw
      change (FGSA.process p (V2.D.Run.stateBefore E rho k v).st (toWire p o)).restartTime =
        some w at hw
      rw [fgsa_process_restartTime] at hw
      exact hQ w hw
  · intro w hw
    cases hw

/-- The explicit restart clause of environment joinedness gives the store test. -/
theorem fgsa_joinedNow_of_joinedEnv (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hS : V2.D.ScheduleWellFormed E rho)
    {i : Nat} {v : V} {t : Time} (hi : rho.events[i]? = some (.tick v t))
    (hJ : ∀ w, 0 ≤ w → w ≤ t → V2.Event.restart v w ∈ rho.events →
      w ≤ 4 * p.Δ * ((p.slotOf t : Int) - 1)) :
    joinedNow p ((fgsa p c).clock (V2.D.Run.stateBefore E rho i v) t).st = true := by
  have hbound := fgsa_restartTime_bound E rho i v
    (4 * p.Δ * ((p.slotOf t : Int) - 1)) (by
      intro j w hji he
      obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp he
      obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
      have hk := List.pairwise_iff_getElem.mp hS.sorted j i hjl hil hji
      rw [hje, hie] at hk
      exact hJ w (hS.in_horizon _ (List.mem_of_getElem? he)).1
        (V2.D.Engine.time_le_of_key_le _ _ hk) (List.mem_of_getElem? he))
  change joinedNow p (FGSA.clock p (V2.D.Run.stateBefore E rho i v).st t) = true
  unfold joinedNow
  rw [fgsa_clock_restartTime, (clock_vn _ t).2]
  cases hr : (V2.D.Run.stateBefore E rho i v).st.restartTime with
  | none => rfl
  | some w => exact decide_eq_true (hbound w hr)

/-- The marker and gate-time clauses of caught-up imply the store join test. -/
theorem fgsa_joinedNow_of_caughtUp (nd : Node p) (t : Time)
    (hC : ∀ w, nd.st.restartTime = some w →
      ∃ (s : Slot), w ≤ 4 * p.Δ * (s : Int) ∧ SA.gateTime p.toParams s ≤ t) :
    joinedNow p ((fgsa p c).clock nd t).st = true := by
  change joinedNow p (FGSA.clock p nd.st t) = true
  unfold joinedNow
  rw [fgsa_clock_restartTime, (clock_vn _ t).2]
  cases hr : nd.st.restartTime with
  | none => rfl
  | some w =>
    obtain ⟨s, hw, ht⟩ := hC w hr
    have hd : (0 : Int) < p.Δ := p.deltaPos
    have hthreshold : 4 * p.Δ * ((s + 1 : Nat) : Int) ≤ t := by
      change 4 * p.Δ * (s : Int) + 6 * p.Δ ≤ t at ht
      push_cast
      nlinarith
    have ht0 : 0 ≤ t := (by positivity : 0 ≤ 4 * p.Δ * ((s + 1 : Nat) : Int)).trans
      hthreshold
    have hs := (fgsa_slot_threshold_iff p t ht0 (s + 1)).2 hthreshold
    apply decide_eq_true
    have hsc : (s : Int) + 1 ≤ (p.slotOf t : Int) := by exact_mod_cast hs
    nlinarith

/-- The stored join test follows from the environment's awake closed interval.
RestartsAtWakes excludes extra restarts during that interval. -/
theorem fgsa_joinedNow_of_awakeClosed (E : Generic.Env V)
    (rho : V2.D.Run V (fgsa p c)) (hS : V2.D.ScheduleWellFormed E rho)
    (hR : V2.D.RestartsAtWakes E rho) {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t))
    (hA : V2.D.AwakeOnClosed E v (4 * p.Δ * ((p.slotOf t : Int) - 1)) t) :
    joinedNow p ((fgsa p c).clock (V2.D.Run.stateBefore E rho i v) t).st = true := by
  let b := 4 * p.Δ * ((p.slotOf t : Int) - 1)
  have hbound := fgsa_restartTime_bound E rho i v b (by
    intro j w hji he
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp he
    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
    have hk := List.pairwise_iff_getElem.mp hS.sorted j i hjl hil hji
    rw [hje, hie] at hk
    have htime := V2.D.Engine.time_le_of_key_le _ _ hk
    have hw := (hR v w (List.mem_of_getElem? he)).2.2
    by_contra hn
    have ha := hA (w - 1) (by dsimp [b, Time] at *; omega)
      (by change w ≤ t at htime; dsimp [Time] at *; omega)
    rw [ha] at hw
    cases hw)
  change joinedNow p (FGSA.clock p (V2.D.Run.stateBefore E rho i v).st t) = true
  unfold joinedNow
  rw [fgsa_clock_restartTime, (clock_vn _ t).2]
  cases hr : (V2.D.Run.stateBefore E rho i v).st.restartTime with
  | none => rfl
  | some w => exact decide_eq_true (hbound w hr)

end AvailableChain.FGSA.Run
end
