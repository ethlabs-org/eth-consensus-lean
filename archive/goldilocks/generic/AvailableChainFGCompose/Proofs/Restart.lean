module
public import AvailableChainFGCompose.Statements.Restart
public import AvailableChainFGCompose.Proofs.SourceHead

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {V In : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V P)

/-- DC: SAME. Event-prefix tree membership survives every restore. -/
theorem tf_cumulative_all (L : FGCoreLaws R) (K : FGTreeKeepLaws R) {i j : Nat}
    (hij : i ≤ j) (x : V) : TFAt R E rho i x ⊆ TFAt R E rho j x := by
  intro B hB
  exact V2.D.Engine.stateBefore_stable_restore (fun nd => B ∈ (R.core nd).fg.TF)
    (fun st t h => by simpa only [L.clock_fg] using h)
    (fun st o h => L.process_tf st o h)
    (fun st o h => by simpa only [L.own_core] using h)
    E rho hij x (fun st t h => K.restart_keep st t h) hB

/-- DC: SAME. A held HEAD remains held at each later event cut. -/
theorem head_held_from_all (L : FGCoreLaws R) (HL : FGHeadLaws R E rho)
    (hs : V2.D.ScheduleWellFormed E rho) (K : FGTreeKeepLaws R)
    {s : Slot} {t : Time} {X : FGBlock (Fin n)} {x : V}
    (hh : (postClock E rho x t).map (fun nd => R.headVote nd s) = some (R.erase X))
    (k : Nat) (cut : Time) (ht : t ≤ cut) (hk : afterTicksIdx rho cut ≤ k) :
    X ∈ TFAt R E rho k x := by
  obtain ⟨i, hi, hX⟩ := head_held R E rho L HL hh
  exact tf_cumulative_all R E rho L K
    ((tick_lt_afterTicks E rho hs hi ht).le.trans hk) x hX

/-- DC: INTENTIONAL. Equal-time restarts can change the state, but keep TF equal.
Keep alone does not suffice: restore could add a block at the tick time. -/
theorem tf_before_tick_eq_beforeTime (hs : V2.D.ScheduleWellFormed E rho)
    (T : FGTreeRestoreLaws R) {i : Nat} {x : V} {t : Time}
    (hi : rho.events[i]? = some (.tick x t)) :
    TFAt R E rho i x = (R.core (V2.D.Run.stateBeforeTime E rho t x)).fg.TF := by
  let q := fun e : V2.Event V P.Object => decide (e.time < t)
  have hdown : ∀ e f : V2.Event V P.Object, e.key ≤ f.key → q f = true → q e = true := by
    intro e f hk hft
    exact decide_eq_true ((V2.D.Engine.time_le_of_key_le _ _ hk).trans_lt
      (of_decide_eq_true hft))
  have hf := V2.D.Engine.filter_eq_take hs q hdown
  have hni : (rho.events.filter q).length ≤ i := by
    by_contra hc
    have hlt : i < (rho.events.filter q).length := by omega
    have hm : V2.Event.tick x t ∈ rho.events.filter q := by
      rw [hf]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hlt]; exact hi)
    exact lt_irrefl t (of_decide_eq_true (List.mem_filter.mp hm).2)
  have hbase : V2.D.Run.stateBefore E rho (rho.events.filter q).length x =
      V2.D.Run.stateBeforeTime E rho t x := by
    exact congrArg (fun es : List (V2.Event V P.Object) =>
      (es.foldl (V2.D.World.step E rho) V2.D.World.init) x) hf.symm
  apply V2.D.Engine.stateBefore_step_induction E rho
    (fun nd => (R.core nd).fg.TF = (R.core (V2.D.Run.stateBeforeTime E rho t x)).fg.TF)
    hni x ?_ (by rw [hbase])
  intro j e hj hji hget hnode hTF
  have hl : t ≤ e.time := by
    have := V2.D.Engine.filter_false_of_index_ge hs q
      hdown hj hget
    simpa [q] using this
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hget
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have hk : e.key ≤ (V2.Event.tick x t : V2.Event V P.Object).key := by
    simpa [hje, hie] using (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hji
  have ht : e.time = t := le_antisymm (V2.D.Engine.time_le_of_key_le _ _ hk) hl
  cases e with
  | restart u t' =>
      change u = x at hnode
      subst u
      simpa only [V2.D.World.step, Function.update_self, T.restart_eq] using hTF
  | tick u t' =>
      change u = x at hnode
      change t' = t at ht
      have heq : (V2.Event.tick u t' : V2.Event V P.Object) = .tick x t := by rw [hnode, ht]
      have : j = i := (List.Nodup.getElem_inj_iff hs.nodup).mp (by rw [hje, hie, heq])
      omega
  | deliver u o t' =>
      change t' = t at ht
      subst t'
      simp [V2.Event.key, V2.Event.time, V2.Event.phase, Prod.Lex.toLex_le_toLex] at hk

/-- DC: SAME. Restore equality supplies the strict-before carrier read. -/
theorem chainRows_of_head_all (L : FGCoreLaws R) (HL : FGHeadLaws R E rho)
    (hs : V2.D.ScheduleWellFormed E rho) (T : FGTreeRestoreLaws R)
    {s : Slot} {t : Time} {X : FGBlock (Fin n)} {x : V} (hx : x ∈ rho.honest)
    (hh : (postClock E rho x t).map (fun nd => R.headVote nd s) = some (R.erase X))
    (cut : Time) (hcut : t < cut) : ChainRowsBefore R E rho X cut := by
  obtain ⟨i, hi, hX⟩ := head_held R E rho L HL hh
  intro W hW _row _hrow
  refine ⟨x, t, hx, hcut, ?_⟩
  have hanc := ancestor_closed_of_parent_closed _ (HL.parent_closed i x) X hX W hW
  rw [Gen.V2.Duty.HoldsBefore_def]
  rw [← tf_before_tick_eq_beforeTime R E rho hs T hi]
  exact hanc

end AvailableChain.FGCompose
end
