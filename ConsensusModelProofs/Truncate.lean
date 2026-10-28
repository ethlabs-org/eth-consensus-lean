module
public import ConsensusModel.System
public import Mathlib.Tactic

@[expose] public section

/-! # Truncation: valid runs are closed under prefixes (L1)

`Run.truncate rho b` keeps the events at times `≤ b` and sets the horizon to
`b`. Events of a valid run are sorted by time, so the kept events are a prefix
of the event list, and everything the engine computes on that prefix (states,
releases, views) is what it computes in the full run. Hence
(`Run.truncate_valid`) the truncation of a valid run at `b ∈ [0, horizon]` is a
valid run, and (`Run.truncate_prefix`) its L0 trace is the prefix of the full
trace up to `b` (`Trace.PrefixOf`), its views agree with the full run's on its
cuts, its log agrees with the full log at times `≤ b`, and a hash collision in
the truncation is one in the full run. -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : Family O} {E : Env V}

namespace Run

variable (rho : Run F E)

/-- The prefix of a run up to `b`: events with time `≤ b`, horizon `b`. -/
def truncate (b : Time) : Run F E :=
  { rho with horizon := b, events := rho.events.filter (fun e => decide (e.time ≤ b)) }

omit [DecidableEq V] in
/-- On a time-sorted list, the events at times `≤ b` form a prefix, and every
later event is after `b`. -/
theorem filter_time_split (b : Time) :
    ∀ (l : List (Event V (protoOf F E).Object)), l.Pairwise Event.keyLe →
      ∃ ys, l = l.filter (fun e => decide (e.time ≤ b)) ++ ys ∧ ∀ e ∈ ys, b < e.time
  | [], _ => ⟨[], rfl, by simp⟩
  | x :: xs, h => by
    rw [List.pairwise_cons] at h
    by_cases hx : x.time ≤ b
    · obtain ⟨ys, hys, hlt⟩ := filter_time_split b xs h.2
      refine ⟨ys, ?_, hlt⟩
      rw [List.filter_cons_of_pos (by simpa using hx), List.cons_append, ← hys]
    · have hall : ∀ e ∈ xs, b < e.time := by
        intro e he
        have hle : x.time ≤ e.time := by
          rcases h.1 e he with h' | ⟨h', _⟩
          · exact h'.le
          · exact h'.le
        exact lt_of_lt_of_le (lt_of_not_ge hx) hle
      refine ⟨x :: xs, ?_, ?_⟩
      · rw [List.filter_cons_of_neg (by simpa using hx)]
        have : xs.filter (fun e => decide (e.time ≤ b)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro e he
          simpa using hall e he
        rw [this, List.nil_append]
      · intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact lt_of_not_ge hx
        · exact hall e he

variable {rho}

section Prefix

variable {b : Time} {ys : List (Event V (protoOf F E).Object)}
  (hsplit : rho.events = (rho.truncate b).events ++ ys)
include hsplit

omit [DecidableEq V] in
theorem truncate_getElem? {i : Nat} (hi : i < (rho.truncate b).events.length) :
    (rho.truncate b).events[i]? = rho.events[i]? := by
  rw [hsplit, List.getElem?_append_left hi]

theorem truncate_stateBefore {i : Nat} (hi : i ≤ (rho.truncate b).events.length) :
    (rho.truncate b).stateBefore i = rho.stateBefore i := by
  change ((rho.truncate b).events.take i).foldl rho.step rho.initWorld =
    (rho.events.take i).foldl rho.step rho.initWorld
  conv_rhs => rw [hsplit, List.take_append_of_le_length hi]

theorem truncate_releasesAt {i : Nat} (hi : i < (rho.truncate b).events.length) :
    (rho.truncate b).releasesAt i = rho.releasesAt i := by
  unfold releasesAt
  rw [truncate_getElem? hsplit hi, truncate_stateBefore hsplit hi.le]
  rfl

theorem truncate_viewIdx (v : V) {i : Nat} (hi : i ≤ (rho.truncate b).events.length) :
    (rho.truncate b).ViewIdx v i = rho.ViewIdx v i := by
  ext o
  simp only [ViewIdx, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, o₀, hk, h, hc⟩
    have hkl : k < (rho.truncate b).events.length := lt_of_lt_of_le hk hi
    rw [truncate_getElem? hsplit hkl, truncate_releasesAt hsplit hkl] at h
    exact ⟨k, o₀, hk, h, hc⟩
  · rintro ⟨k, o₀, hk, h, hc⟩
    have hkl : k < (rho.truncate b).events.length := lt_of_lt_of_le hk hi
    rw [← truncate_getElem? hsplit hkl, ← truncate_releasesAt hsplit hkl] at h
    exact ⟨k, o₀, hk, h, hc⟩

omit [DecidableEq V] in
/-- An event of the full run at a time `≤ b` lies in the kept prefix. -/
theorem truncate_index_lt (hys : ∀ e ∈ ys, b < e.time) {i : Nat}
    {e : Event V (protoOf F E).Object} (h : rho.events[i]? = some e) (he : e.time ≤ b) :
    i < (rho.truncate b).events.length := by
  by_contra hn
  rw [hsplit, List.getElem?_append_right (by omega)] at h
  exact absurd (hys e (List.mem_of_getElem? h)) (not_lt.mpr he)

theorem truncate_releases_iff (hys : ∀ e ∈ ys, b < e.time) {v : V}
    {o : (protoOf F E).Object} {t : Time} (ht : t ≤ b) :
    (rho.truncate b).releases v o t ↔ rho.releases v o t := by
  constructor
  · rintro ⟨i, hi, ho⟩
    have hil : i < (rho.truncate b).events.length := (List.getElem?_eq_some_iff.mp hi).1
    rw [truncate_getElem? hsplit hil] at hi
    rw [truncate_releasesAt hsplit hil] at ho
    exact ⟨i, hi, ho⟩
  · rintro ⟨i, hi, ho⟩
    have hil := truncate_index_lt hsplit hys hi ht
    rw [← truncate_getElem? hsplit hil] at hi
    rw [← truncate_releasesAt hsplit hil] at ho
    exact ⟨i, hi, ho⟩

omit [DecidableEq V] in
theorem truncate_receives_iff (hys : ∀ e ∈ ys, b < e.time) {v : V}
    {o : (protoOf F E).Object} {t : Time} (ht : t ≤ b) :
    (rho.truncate b).receives v o t ↔ rho.receives v o t := by
  constructor
  · rintro ⟨i, hi⟩
    have hil : i < (rho.truncate b).events.length := (List.getElem?_eq_some_iff.mp hi).1
    rw [truncate_getElem? hsplit hil] at hi
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    have hil := truncate_index_lt hsplit hys hi ht
    rw [← truncate_getElem? hsplit hil] at hi
    exact ⟨i, hi⟩

omit [DecidableEq V] in
theorem truncate_cutTime {i : Nat} (hi : i ≤ (rho.truncate b).events.length) :
    (rho.truncate b).cutTime i = rho.cutTime i := by
  cases i with
  | zero => rfl
  | succ k =>
    simp only [cutTime]
    rw [truncate_getElem? hsplit (by omega)]

end Prefix

omit [DecidableEq V] in
theorem truncate_split (hs : rho.events.Pairwise Event.keyLe) (b : Time) :
    ∃ ys, rho.events = (rho.truncate b).events ++ ys ∧ ∀ e ∈ ys, b < e.time :=
  filter_time_split b rho.events hs

omit [DecidableEq V] in
theorem mem_truncate_events {b : Time} {e : Event V (protoOf F E).Object} :
    e ∈ (rho.truncate b).events ↔ e ∈ rho.events ∧ e.time ≤ b := by
  simp [truncate, List.mem_filter]

/-- The truncation of a valid run at `b ∈ [0, horizon]` is a valid run. -/
theorem truncate_valid (hv : rho.ExecutionValid) {b : Time} (hb : 0 ≤ b)
    (hbh : b ≤ rho.horizon) : (rho.truncate b).ExecutionValid := by
  obtain ⟨ys, hsplit, hys⟩ := rho.truncate_split hv.sorted b
  have hsub : ∀ e, e ∈ (rho.truncate b).events → e ∈ rho.events := fun e he =>
    (mem_truncate_events.mp he).1
  refine ⟨⟨hb, hv.sorted.sublist List.filter_sublist, hv.nodup.filter _, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_⟩, ?_, hv.selValid, ?_⟩
  · intro e he
    exact ⟨(hv.in_horizon e (hsub e he)).1, (mem_truncate_events.mp he).2⟩
  · intro e he
    exact hv.honest_only e (hsub e he)
  · intro v hvh t ht0 htb haw
    exact mem_truncate_events.mpr ⟨hv.tick_total v hvh t ht0 (le_trans htb hbh) haw, htb⟩
  · intro v t he
    exact hv.tick_awake v t (hsub _ he)
  · intro v o t he
    exact hv.deliver_awake v o t (hsub _ he)
  · intro v t he
    exact hv.restart_at_wake v t (hsub _ he)
  · intro v hvh t ht0 htb hw
    exact mem_truncate_events.mpr ⟨hv.wake_restart v hvh t ht0 (le_trans htb hbh) hw, htb⟩
  · intro i w o t hi o' hc u hu hsg
    have hil : i < (rho.truncate b).events.length := (List.getElem?_eq_some_iff.mp hi).1
    rw [truncate_getElem? hsplit hil] at hi
    obtain ⟨j, t', hj, hjt, hjo⟩ := hv.unforgeable i w o t hi o' hc u hu hsg
    have hjl : j < (rho.truncate b).events.length := lt_trans hj hil
    refine ⟨j, t', hj, ?_, ?_⟩
    · rw [truncate_getElem? hsplit hjl]; exact hjt
    · rw [truncate_releasesAt hsplit hjl]; exact hjo
  · intro i w o t hi o' hc k r ha
    have hil : i < (rho.truncate b).events.length := (List.getElem?_eq_some_iff.mp hi).1
    rw [truncate_getElem? hsplit hil] at hi
    exact hv.credentials i w o t hi o' hc k r ha

/-- The truncation at `b` of a valid run is its L0 prefix up to `b` in the
system `sysOf`: the trace is `Trace.PrefixOf` the full trace at `b`, views
agree on the prefix's cuts, the log agrees at times `≤ b`, and a hash
collision in the truncation is one in the full run (`Excuse` transfers). -/
theorem truncate_prefix (hv : rho.ExecutionValid) (b : Time) :
    let r : (sysOf O F V).Run := ⟨E, rho⟩
    let r' : (sysOf O F V).Run := ⟨E, rho.truncate b⟩
    ((sysOf O F V).trace r').PrefixOf ((sysOf O F V).trace r) b ∧
      (∀ v i, i ≤ ((sysOf O F V).trace r').cuts →
        (sysOf O F V).view r' v i = (sysOf O F V).view r v i) ∧
      ((sysOf O F V).log r').AgreesUpTo ((sysOf O F V).log r) b ∧
      ((sysOf O F V).Excuse r' → (sysOf O F V).Excuse r) := by
  obtain ⟨ys, hsplit, hys⟩ := rho.truncate_split hv.sorted b
  have hlen : rho.events.length = (rho.truncate b).events.length + ys.length := by
    rw [hsplit, List.length_append]
  refine ⟨⟨rfl, ?_, ?_, ?_⟩, ?_, ⟨?_, fun _ _ _ => rfl⟩, ?_⟩
  · -- the prefix's cuts end at `endCut b`
    change (rho.truncate b).events.length =
      Nat.findGreatest (fun i => rho.cutTime i ≤ b) rho.events.length
    symm
    rw [Nat.findGreatest_eq_iff]
    refine ⟨by omega, ?_, ?_⟩
    · intro hn
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have hkl : k < (rho.truncate b).events.length := by omega
      rw [← truncate_cutTime hsplit le_rfl, hk]
      simp only [cutTime]
      rw [List.getElem?_eq_getElem hkl]
      exact (mem_truncate_events.mp (List.getElem_mem hkl)).2
    · intro m hm hml hc
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
      have hkl : k < rho.events.length := by omega
      simp only [cutTime] at hc
      rw [List.getElem?_eq_getElem hkl] at hc
      have := truncate_index_lt hsplit hys (List.getElem?_eq_getElem hkl) hc
      omega
  · intro i hi
    exact truncate_cutTime hsplit hi
  · intro g v i hi
    change (protoOf F E).out g ((rho.truncate b).stateBefore i v).st =
      (protoOf F E).out g (rho.stateBefore i v).st
    rw [truncate_stateBefore hsplit hi]
  · intro v i hi
    have hi' : i ≤ (rho.truncate b).events.length := hi
    simp only [sysOf, truncate_viewIdx hsplit v hi']
  · intro v m t ht
    constructor
    · simp only [sysOf, truncate_releases_iff hsplit hys ht]
    · simp only [sysOf, truncate_receives_iff hsplit hys ht]
  · rintro ⟨x, y, hxy, ⟨ox, ⟨vx, hvx, hox⟩, hx⟩, ⟨oy, ⟨vy, hvy, hoy⟩, hy⟩, hh⟩
    have hmono : ∀ w o, o ∈ (rho.truncate b).ViewIdx w (rho.truncate b).events.length →
        o ∈ rho.ViewIdx w rho.events.length := by
      intro w o ho
      rw [truncate_viewIdx hsplit w le_rfl] at ho
      obtain ⟨k, o₀, hk, h, hc⟩ := ho
      exact ⟨k, o₀, by omega, h, hc⟩
    exact ⟨x, y, hxy, ⟨ox, ⟨vx, hvx, hmono vx ox hox⟩, hx⟩,
      ⟨oy, ⟨vy, hvy, hmono vy oy hoy⟩, hy⟩, hh⟩

end Run

end Consensus.Model

end
