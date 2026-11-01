module
public import AvailableChainStatements.Generic.Regimes

@[expose] public section

namespace AvailableChain.Engine

-- These schedule proofs depend only on the fixed engine.

open AvailableChain.Generic AvailableChain.Statements.Generic

/- The following schedule bridges port the list arguments from
verified-consensus Proofs/Protocol/Handlers/{Bridges,TickBridges}.lean.
They use only the common event order and world update semantics. -/

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
variable {V : Type} [DecidableEq V] {seats : Nat} {P : ProtocolSpec seats} {E : Env V}
  {rho : Run V P}

theorem stateBefore_succ_event {i : Nat} {e : Event V P.Object}
    (hi : rho.events[i]? = some e) :
    Run.stateBefore P rho (i + 1) =
      World.step (Run.stateBefore P rho i) e := by
  unfold Run.stateBefore
  rw [List.take_add_one, List.foldl_append, hi]
  rfl

omit [DecidableEq V] in
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

omit [DecidableEq V] in
theorem time_le_of_key_le (e f : Event V P.Object)
    (h : e.key ≤ f.key) : e.time ≤ f.time := by
  rcases Prod.Lex.toLex_le_toLex.mp h with h | ⟨h, _⟩
  · exact le_of_lt h
  · exact le_of_eq h

omit [DecidableEq V] in
theorem filter_eq_take (hs : ScheduleWellFormed E rho)
    (q : Event V P.Object → Bool)
    (hdc : ∀ e f, e.key ≤ f.key → q f = true → q e = true) :
    rho.events.filter q = rho.events.take (rho.events.filter q).length := by
  apply List.prefix_iff_eq_take.mp
  rw [filter_eq_takeWhile hdc _ hs.sorted]
  exact List.takeWhile_prefix _

omit [DecidableEq V] in
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

omit [DecidableEq V] in
private theorem downward_lt (t : Time) :
    ∀ e f : Event V P.Object, e.key ≤ f.key →
      decide (f.time < t) = true → decide (e.time < t) = true := by
  intro e f hk hf
  exact decide_eq_true (lt_of_le_of_lt (time_le_of_key_le e f hk) (of_decide_eq_true hf))

/-- The public read is the event-prefix state after all events at its time. -/
theorem readAt_eq_stateBefore (hs : ScheduleWellFormed E rho) (t : Time) :
    Run.readAt P rho t = Run.stateBefore P rho
      (rho.events.filter (fun e => decide (e.time ≤ t))).length := by
  unfold Run.readAt Run.stateBefore
  exact congrArg (fun events => events.foldl World.step World.init)
    (filter_eq_take hs (fun e => decide (e.time ≤ t)) (by
    intro e f hk hf
    exact decide_eq_true (le_trans (time_le_of_key_le _ _ hk) (of_decide_eq_true hf))))

omit [DecidableEq V] in
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

omit [DecidableEq V] in
theorem read_length_mono (a b : Time) (hab : a ≤ b) :
    (rho.events.filter (fun e => decide (e.time ≤ a))).length ≤
      (rho.events.filter (fun e => decide (e.time ≤ b))).length := by
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  apply List.countP_mono_left
  intro e _ he
  exact decide_eq_true (le_trans (of_decide_eq_true he) hab)

/-- Other nodes' events do not change a reader's state. -/
theorem stateBefore_eq_of_other_nodes (v : V) {m : Nat} (n : Nat) (hm : m ≤ n)
    (h : ∀ j e, m ≤ j → j < n → rho.events[j]? = some e → e.node ≠ v) :
    Run.stateBefore P rho n v = Run.stateBefore P rho m v := by
  induction n with
  | zero => rw [Nat.le_zero.mp hm]
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · have hmn : m ≤ n := by omega
        rw [← ih hmn (fun j e h1 h2 h3 => h j e h1 (by omega) h3)]
        unfold Run.stateBefore
        rw [List.take_add_one, List.foldl_append]
        cases hn : rho.events[n]? with
        | none => simp
        | some e =>
            have hne : e.node ≠ v := h n e hmn (by omega) hn
            simp only [Option.toList, List.foldl_cons, List.foldl_nil]
            cases e <;> exact Function.update_of_ne (Ne.symm hne) _ _
      · rw [Nat.le_antisymm hm hge]

/-- The tick reads the state strictly before its public time. Equal-time
steps before it belong to other nodes. -/
theorem stateBefore_tick_eq_stateBeforeTime (hs : ScheduleWellFormed E rho)
    {i : Nat} {v : V} {t : Time} (hi : rho.events[i]? = some (.tick v t)) :
    Run.stateBefore P rho i v = Run.stateBeforeTime P rho t v := by
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
  change _ = ((rho.events.filter q).foldl World.step World.init) v
  rw [hf]
  apply stateBefore_eq_of_other_nodes v i hni
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
    | tick u t' => simp only [Event.node] at hnode; simp only [Event.time] at ht; rw [hnode, ht]
    | deliver u o t' =>
        simp only [Event.time] at ht
        subst t'
        simp [Event.key, Event.time, Event.phase, Prod.Lex.toLex_le_toLex] at hk
  have : j = i := (List.Nodup.getElem_inj_iff hs.nodup).mp (by rw [hje, hie, he])
  omega

end Schedule
end AvailableChain.Engine
end
