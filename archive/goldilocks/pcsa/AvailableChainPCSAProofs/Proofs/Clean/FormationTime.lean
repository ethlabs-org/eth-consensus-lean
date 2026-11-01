module
public import AvailableChainPCSAProofs.Proofs.Clean.FormationSource
public import AvailableChainPCSAProofs.Proofs.Foundations.StampRun

public section

/-! Local clock and receipt-time bounds for Formation. -/

namespace AvailableChain.PCSA.Run

variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In} {m : FGMode}

/-- Every local clock before an indexed event is at most that event's time. -/
theorem pcsa_formation_now_before_event (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : V2.D.ScheduleWellFormed E rho)
    (j : Nat) (e : V2.Event V (Obj p)) (he : rho.events[j]? = some e) (x : V) :
    (V2.D.Run.stateBefore E rho j x).st.base.now ≤ e.time := by
  have hzero : 0 ≤ e.time := (h.in_horizon e (List.mem_of_getElem? he)).1
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => nd.st.base.now ≤ e.time) (Nat.zero_le j) x ?_ hzero
  intro k f _ hkj hf hn hc
  cases f with
  | restart y t =>
    change y = x at hn
    subst y
    change (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.now ≤ e.time
    rw [Function.update_self]
    exact hzero
  | tick y t =>
    change y = x at hn
    subst y
    have ht : t ≤ e.time := by
      have hk := (List.getElem?_eq_some_iff.mp hf).1
      have hj := (List.getElem?_eq_some_iff.mp he).1
      have hh := (List.pairwise_iff_getElem.mp h.sorted) k j hk hj hkj
      rw [(List.getElem?_eq_some_iff.mp hf).2, (List.getElem?_eq_some_iff.mp he).2] at hh
      exact V2.D.Engine.time_le_of_key_le _ _ hh
    change (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.now ≤ e.time
    rw [Function.update_self]
    have hs := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k x) x t
    have hh : (clock p (V2.D.Run.stateBefore E rho k x).st t).base.now ≤ e.time := by
      rw [pcsa_clock_now]
      exact ht
    exact hs.symm ▸ hh
  | deliver y o t =>
    change y = x at hn
    subst y
    change (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.now ≤ e.time
    rw [Function.update_self]
    change (process p (V2.D.Run.stateBefore E rho k x).st (toWire p o)).base.now ≤ e.time
    rw [pcsa_process_now]
    exact hc

/-- Sorted ticks and deliveries make the local clock monotone without restart. -/
theorem pcsa_formation_now_mono (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (h : V2.D.ScheduleWellFormed E rho)
    (hNR : V2.D.NoRestart rho) (i j : Nat) (hij : i ≤ j) (x : V) :
    (V2.D.Run.stateBefore E rho i x).st.base.now ≤
      (V2.D.Run.stateBefore E rho j x).st.base.now := by
  refine V2.D.Engine.stateBefore_step_induction E rho
    (fun nd : Node p => (V2.D.Run.stateBefore E rho i x).st.base.now ≤ nd.st.base.now)
    hij x ?_ (le_refl _)
  intro k e _ _ he hn hc
  cases e with
  | restart y t => exact (hNR k y t he).elim
  | tick y t =>
    change y = x at hn
    subst y
    have ht := hc.trans (pcsa_formation_now_before_event E rho h k (.tick x t) he x)
    change (V2.D.Run.stateBefore E rho i x).st.base.now ≤
      (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.now
    rw [Function.update_self]
    have hs := pcsa_tick_st E rho (V2.D.Run.stateBefore E rho k x) x t
    have hh : (V2.D.Run.stateBefore E rho i x).st.base.now ≤
        (clock p (V2.D.Run.stateBefore E rho k x).st t).base.now := by
      rw [pcsa_clock_now]
      exact ht
    exact hs.symm ▸ hh
  | deliver y o t =>
    change y = x at hn
    subst y
    change (V2.D.Run.stateBefore E rho i x).st.base.now ≤
      (Function.update (V2.D.Run.stateBefore E rho k) x _ x).st.base.now
    rw [Function.update_self]
    change (V2.D.Run.stateBefore E rho i x).st.base.now ≤
      (process p (V2.D.Run.stateBefore E rho k x).st (toWire p o)).base.now
    rw [pcsa_process_now]
    exact hc

/-- The local clock immediately after a tick records its exact time. -/
theorem pcsa_formation_now_after_tick (E : Generic.Env V)
    (rho : V2.D.Run V (pcsaWith m p c)) (j : Nat) (x : V) (t : Time)
    (hj : rho.events[j]? = some (.tick x t)) :
    (V2.D.Run.stateBefore E rho (j + 1) x).st.base.now = t := by
  have hs := congrArg (fun nd : Node p => nd.st.base.now) (V2.D.Run.step_tick_eq E rho hj).1
  exact hs.trans (congrArg (fun st : State p.n => st.base.now)
    (pcsa_tick_st E rho (V2.D.Run.stateBefore E rho j x) x t) |>.trans
      (pcsa_clock_now p _ t))

end AvailableChain.PCSA.Run
end
