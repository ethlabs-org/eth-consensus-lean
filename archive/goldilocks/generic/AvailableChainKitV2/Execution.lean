module
public import AvailableChainEngineV2.Conditions.Schedule
public import AvailableChainEngineV2.Laws.SelfDelivery

@[expose] public section

/-! Schedule lemmas over engine v2 (plan 2a, Task 4). The texts are those of
v1 `AvailableChainKit/Engine/Execution.lean` over v2 runs: `Run.stateBefore`
takes the environment, and events have a restart phase before the tick
phase. v1 `stateBefore_succ_event` is `Run.stateBefore_succ` of engine v2. -/

namespace AvailableChain.V2.Engine

open AvailableChain

private theorem filter_eq_takeWhile {α : Type} {R : α → α → Prop} {p : α → Bool}
    (hdc : ∀ a b, R a b → p b = true → p a = true)
    (xs : List α) (hs : xs.Pairwise R) : xs.filter p = xs.takeWhile p := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      obtain ⟨ha, hs⟩ := List.pairwise_cons.mp hs
      by_cases hp : p a = true
      · rw [List.filter_cons_of_pos hp, List.takeWhile_cons_of_pos hp, ih hs]
      · rw [List.filter_cons_of_neg hp, List.takeWhile_cons_of_neg hp]
        exact List.filter_eq_nil_iff.mpr (fun b hb hpb => hp (hdc a b (ha b hb) hpb))

section Schedule
variable {V : Type} {In : Type} {P : ProtocolSpec In} {E : Generic.Env V} {rho : Run V P}

/-- Strict event-time order implies strict index order in a valid schedule. -/
theorem eventIndex_lt_of_time_lt (hs : ScheduleWellFormed E rho)
    {i j : Nat} {e f : Event V P.Object}
    (hi : rho.events[i]? = some e) (hj : rho.events[j]? = some f)
    (ht : e.time < f.time) : i < j := by
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
  by_contra hn
  rcases Nat.lt_or_ge j i with hji | hij
  · have hk := (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hji
    rw [hje, hie] at hk
    have ht' : f.time ≤ e.time := by
      rcases Prod.Lex.toLex_le_toLex.mp hk with h | ⟨h, _⟩
      · exact le_of_lt h
      · exact le_of_eq h
    exact (not_le.mpr ht) ht'
  · have he : e = f := by
      have : i = j := by omega
      subst j
      exact Option.some.inj (hi.symm.trans hj)
    simp [he] at ht

theorem time_le_of_key_le (e f : Event V P.Object)
    (h : e.key ≤ f.key) : e.time ≤ f.time := by
  rcases Prod.Lex.toLex_le_toLex.mp h with h | ⟨h, _⟩
  · exact le_of_lt h
  · exact le_of_eq h

theorem filter_eq_take (hs : ScheduleWellFormed E rho)
    (q : Event V P.Object → Bool)
    (hdc : ∀ e f, e.key ≤ f.key → q f = true → q e = true) :
    rho.events.filter q = rho.events.take (rho.events.filter q).length := by
  apply List.prefix_iff_eq_take.mp
  rw [filter_eq_takeWhile hdc _ hs.sorted]
  exact List.takeWhile_prefix _

theorem filter_false_of_index_ge (hs : ScheduleWellFormed E rho)
    (q : Event V P.Object → Bool)
    (hdc : ∀ e f, e.key ≤ f.key → q f = true → q e = true)
    {j : Nat} {e : Event V P.Object}
    (hj : (rho.events.filter q).length ≤ j) (hget : rho.events[j]? = some e) :
    q e = false := by
  set n := (rho.events.filter q).length
  have hf := filter_eq_take hs q hdc
  have hn : (rho.events.drop n).filter q = [] := by
    have h1 : rho.events.filter q = (rho.events.take n).filter q ++
        (rho.events.drop n).filter q := by
      conv_lhs => rw [← List.take_append_drop n rho.events]
      rw [List.filter_append]
    have h2 : (rho.events.take n).filter q = rho.events.filter q := by
      rw [← hf, List.filter_filter]
      simp only [Bool.and_self]
    rw [h2] at h1
    exact List.self_eq_append_right.mp h1
  have hm : e ∈ rho.events.drop n := by
    apply List.mem_of_getElem? (i := j - n)
    rw [List.getElem?_drop, Nat.add_sub_of_le hj]
    exact hget
  by_contra hc
  have : e ∈ (rho.events.drop n).filter q := List.mem_filter.mpr ⟨hm, by simpa using hc⟩
  simp [hn] at this

private theorem downward_lt (t : Time) :
    ∀ e f : Event V P.Object, e.key ≤ f.key →
      decide (f.time < t) = true → decide (e.time < t) = true := by
  intro e f hk hf
  exact decide_eq_true (lt_of_le_of_lt (time_le_of_key_le e f hk) (of_decide_eq_true hf))

theorem index_lt_read_length_iff (hs : ScheduleWellFormed E rho)
    (t : Time) {i : Nat} {e : Event V P.Object}
    (hi : rho.events[i]? = some e) :
    i < (rho.events.filter (fun f => decide (f.time ≤ t))).length ↔ e.time ≤ t := by
  let q := fun f : Event V P.Object => decide (f.time ≤ t)
  have hdown : ∀ a b, a.key ≤ b.key → q b = true → q a = true := by
    intro a b hk hb
    exact decide_eq_true (le_trans (time_le_of_key_le _ _ hk) (of_decide_eq_true hb))
  constructor
  · intro hl
    have hm : e ∈ rho.events.filter q := by
      rw [filter_eq_take hs q hdown]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hl]; exact hi)
    exact of_decide_eq_true (List.mem_filter.mp hm).2
  · intro ht
    by_contra hn
    have hf := filter_false_of_index_ge hs q hdown (Nat.le_of_not_gt hn) hi
    simp [q, ht] at hf

theorem read_length_mono (a b : Time) (hab : a ≤ b) :
    (rho.events.filter (fun e => decide (e.time ≤ a))).length ≤
      (rho.events.filter (fun e => decide (e.time ≤ b))).length := by
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro e _ he
  exact decide_eq_true (le_trans (of_decide_eq_true he) hab)

/-- A local tick at or before a delivery precedes that delivery in the list.
This includes equal times, because ticks have the earlier event phase. -/
theorem tick_index_lt_delivery (E : Generic.Env V) (rho : Run V P)
    (hs : ScheduleWellFormed E rho)
    {i j : Nat} {v w : V} {o : P.Object} {a t : Time}
    (hi : rho.events[i]? = some (.tick v a))
    (hj : rho.events[j]? = some (.deliver w o t)) (hat : a ≤ t) : i < j := by
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
  by_contra hn
  rcases Nat.lt_or_ge j i with hji | hij
  · have hk := (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hji
    rw [hje, hie] at hk
    have hbad : t < a := by
      simpa [Event.key, Event.time, Event.phase, Prod.Lex.toLex_le_toLex] using hk
    exact (not_lt.mpr hat) hbad
  · have he : i = j := by omega
    subst j
    simp [hi] at hj

variable [DecidableEq V]

/-- The public read is the event-prefix state after all events at its time. -/
theorem readAt_eq_stateBefore (hs : ScheduleWellFormed E rho) (t : Time) :
    Run.readAt E rho t = Run.stateBefore E rho
      (rho.events.filter (fun e => decide (e.time ≤ t))).length := by
  unfold Run.readAt Run.stateBefore
  exact congrArg (fun events => events.foldl (World.step E rho) World.init)
    (filter_eq_take hs (fun e => decide (e.time ≤ t)) (by
    intro e f hk hf
    exact decide_eq_true (le_trans (time_le_of_key_le _ _ hk) (of_decide_eq_true hf))))

/-- Other nodes' events do not change a reader's state (DC N4): if no event
with an index in `[a, b)` is at `v`, the state of `v` is the same before `a`
and before `b`. It is `Run.stateBefore_eq_of_node_ne` of engine v2. -/
theorem stateBefore_other_node (E : Generic.Env V) (rho : Run V P) {v : V} {a b : Nat}
    (hab : a ≤ b)
    (h : ∀ k e, a ≤ k → k < b → rho.events[k]? = some e → e.node ≠ v) :
    Run.stateBefore E rho b v = Run.stateBefore E rho a v :=
  Run.stateBefore_eq_of_node_ne E rho hab h

/-- The tick reads the state strictly before its public time. Equal-time
steps before it belong to other nodes, or are restarts of the ticking node;
`NoRestart` excludes the latter (a restart of `v` at time `t` comes before
the tick and is in `stateBefore` only). -/
theorem stateBefore_tick_eq_stateBeforeTime (hs : ScheduleWellFormed E rho)
    (hnr : NoRestart rho) {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t)) :
    Run.stateBefore E rho i v = Run.stateBeforeTime E rho t v := by
  let q := fun e : Event V P.Object => decide (e.time < t)
  have hf := filter_eq_take hs q (downward_lt t)
  have hni : (rho.events.filter q).length ≤ i := by
    by_contra hc
    have hlt : i < (rho.events.filter q).length := by omega
    have hm : Event.tick v t ∈ rho.events.filter q := by
      rw [hf]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hlt]; exact hi)
    have ht := of_decide_eq_true (List.mem_filter.mp hm).2
    exact lt_irrefl t ht
  change _ = ((rho.events.filter q).foldl (World.step E rho) World.init) v
  rw [hf]
  apply stateBefore_other_node E rho hni
  intro j e hj hji hget hnode
  have hl : t ≤ e.time := by
    have := filter_false_of_index_ge hs q (downward_lt t) hj hget
    simpa [q] using this
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hget
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have hk : e.key ≤ (Event.tick v t : Event V P.Object).key := by
    simpa [hje, hie] using (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hji
  have ht : e.time = t := le_antisymm (time_le_of_key_le _ _ hk) hl
  have he : e = .tick v t := by
    cases e with
    | restart u t' =>
        simp only [Event.node] at hnode
        subst hnode
        exact absurd hget (hnr j u t')
    | tick u t' => simp only [Event.node] at hnode; simp only [Event.time] at ht; rw [hnode, ht]
    | deliver u o t' =>
        simp only [Event.time] at ht
        subst t'
        simp [Event.key, Event.time, Event.phase, Prod.Lex.toLex_le_toLex] at hk
  have : j = i := (List.Nodup.getElem_inj_iff hs.nodup).mp (by rw [hje, hie, he])
  omega

omit [DecidableEq V] in
/-- The action cut includes exactly earlier events and restarts at the anchor. -/
theorem index_lt_actionCut_iff (hs : ScheduleWellFormed E rho)
    {i : Nat} {e : Event V P.Object} (hi : rho.events[i]? = some e) (a : Time) :
    i < Run.actionCut rho a ↔ e.time < a ∨ (e.time = a ∧ e.phase = 0) := by
  let q := fun e : Event V P.Object =>
    decide (e.time < a ∨ (e.time = a ∧ e.phase = 0))
  have hd : ∀ e f, e.key ≤ f.key → q f = true → q e = true := by
    intro e f hk hf
    apply decide_eq_true
    have hf' : f.time < a ∨ (f.time = a ∧ f.phase = 0) := of_decide_eq_true hf
    have hk' := Prod.Lex.toLex_le_toLex.mp hk
    dsimp only [Event.key] at hk'
    dsimp [Time] at *
    rcases hk' with h | ⟨h, hp⟩ <;> rcases hf' with ht | ⟨ht, hf⟩ <;> omega
  change i < (rho.events.filter q).length ↔ _
  constructor
  · intro hl
    have hm : e ∈ rho.events.filter q := by
      rw [filter_eq_take hs q hd]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hl]; exact hi)
    exact of_decide_eq_true (List.mem_filter.mp hm).2
  · intro ht
    by_contra hn
    have hf := filter_false_of_index_ge hs q hd (Nat.le_of_not_gt hn) hi
    have htq : q e = true := decide_eq_true ht
    rw [htq] at hf
    cases hf

/-- A tick reads the state after all restarts at its time. -/
theorem stateBefore_tick_eq_stateAfterRestartsAt (hs : ScheduleWellFormed E rho)
    {i : Nat} {v : V} {t : Time} (hi : rho.events[i]? = some (.tick v t)) :
    Run.stateBefore E rho i v = Run.stateAfterRestartsAt E rho t v := by
  have hc : Run.actionCut rho t ≤ i := by
    by_contra hn
    have h := (index_lt_actionCut_iff hs hi t).mp (Nat.lt_of_not_ge hn)
    simp [Event.time, Event.phase] at h
  exact Run.stateBefore_eq_of_node_ne E rho hc (by
    intro j e hj hji he hv
    have hn := (index_lt_actionCut_iff hs he t).not.mp (Nat.not_lt.mpr hj)
    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp he
    have hk := (List.pairwise_iff_getElem.mp hs.sorted) j i hjl hil hji
    rw [hje, hie] at hk
    have ht := time_le_of_key_le _ _ hk
    have het : e.time = t := by dsimp [Event.time, Time] at *; omega
    have heq : e = .tick v t := by
      cases e with
      | restart u t' => exact False.elim (hn (Or.inr ⟨het, rfl⟩))
      | tick u t' => change u = v at hv; change t' = t at het; rw [hv, het]
      | deliver u o t' =>
          change t' = t at het; subst t'
          simp [Event.key, Event.time, Event.phase, Prod.Lex.toLex_le_toLex] at hk
    have : j = i := (List.Nodup.getElem_inj_iff hs.nodup).mp (by rw [hje, hie, heq])
    omega)

end Schedule
end AvailableChain.V2.Engine
end
