module
public import ConsensusLean.Lemmas.Model.Truncate
public import ConsensusLean.Lemmas.Model.Canonical.Events

public section

/-! # Retention: a run read from the faults of one time (L1)

`Run.retain rho d` keeps the events of the nodes honest at `d` and makes the faults constant,
`faultyAt := fun _ => rho.faultyAt d`: every node compromised by `d` is faulty from the start, and
every other node keeps exactly its events. The engine runs each node on its own events only, so
the retained run computes, for every node honest at `d`, the states, releases, receipts and views
of the full run at the corresponding cuts (`retain_stateBefore`, `retainIdx`). Hence:

* (`retain_valid`) the retention at `d ≥ horizon` of a valid run is a valid run with constant
  faults: what the dropped nodes signed while honest becomes adversarial in the retained run;
* (`retain_stateBefore_endCut`) the state of a kept node at the end of every time is unchanged;
* (`retain_delivers`) the network conditions of the full run hold of the retained run;
* (`retain_observed`) an object observed in the retained run is observed in the full run, so
  (`retain_not_hashCollision`) a hash collision of the retained run is one of the full run.

The retained run is a proof device: a claim about kept nodes proved on the retained run, with
the constant-fault machinery, is a claim about the full run. -/

namespace Consensus.Model

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {F : ProtocolFamily O}
    {E : Env V}

namespace Run

variable (rho : Run F E)

/-- An event is kept by the retention at `d` when its node is honest at `d`. -/
def keptAt (d : Time) (e : Event V (protoOf F E).Object) : Bool :=
  decide (e.node ∉ rho.faultyAt d)

/-- **The retention at `d`**: the events of the nodes honest at `d`, with the faults of `d` at
every time. -/
def retain (d : Time) : Run F E :=
  { rho with
    faultyAt := fun _ => rho.faultyAt d
    faultyAt_mono := monotone_const
    events := rho.events.filter (rho.keptAt d) }

/-- The retained index of the full-run cut `i`: the kept events among the first `i`. -/
def retainIdx (d : Time) (i : Nat) : Nat := ((rho.events.take i).filter (rho.keptAt d)).length

variable {rho} {d : Time}

theorem keptAt_iff {e : Event V (protoOf F E).Object} :
    rho.keptAt d e = true ↔ e.node ∉ rho.faultyAt d := by
  simp [keptAt]

theorem retain_events : (rho.retain d).events = rho.events.filter (rho.keptAt d) := by rfl

theorem retain_faultyAt (t : Time) : (rho.retain d).faultyAt t = rho.faultyAt d := by rfl

theorem retain_horizon : (rho.retain d).horizon = rho.horizon := by rfl

theorem retain_hash : (rho.retain d).hash = rho.hash := by rfl

theorem retain_point : (rho.retain d).point = rho.point.retain d := by rfl

/-- The retained run has constant faults. -/
theorem retain_constant : (rho.retain d).point.ConstantFaults := fun _ => rfl

theorem retain_inbox : (rho.retain d).inbox = rho.inbox := by rfl

theorem retain_step : (rho.retain d).step = rho.step := by rfl

theorem retain_initWorld : (rho.retain d).initWorld = rho.initWorld := by rfl

theorem retain_tick : (rho.retain d).tick = rho.tick := by rfl

theorem retain_deliver : (rho.retain d).deliver = rho.deliver := by rfl

theorem mem_retain_events {e : Event V (protoOf F E).Object} :
    e ∈ (rho.retain d).events ↔ e ∈ rho.events ∧ e.node ∉ rho.faultyAt d := by
  rw [retain_events, List.mem_filter, keptAt_iff]

/-! ### Each node runs on its own events -/

/-- An event leaves the other nodes unchanged. -/
theorem step_apply_of_ne (w : V → Node (protoOf F E)) {e : Event V (protoOf F E).Object}
    {v : V} (h : e.node ≠ v) : rho.step w e v = w v := by
  cases e <;> exact Function.update_of_ne (Ne.symm h) _ _

/-- An event's effect on a node reads only that node. -/
theorem step_apply_congr {w w' : V → Node (protoOf F E)} {v : V} (h : w v = w' v)
    (e : Event V (protoOf F E).Object) : rho.step w e v = rho.step w' e v := by
  by_cases hv : e.node = v
  · subst hv
    cases e <;> simp only [step, Event.node, Function.update_self] at h ⊢ <;> rw [h]
  · rw [step_apply_of_ne w hv, step_apply_of_ne w' hv, h]

/-- Dropping events of other nodes leaves a node's state unchanged. -/
theorem foldl_step_filter (p : Event V (protoOf F E).Object → Bool) {v : V} :
    ∀ (l : List (Event V (protoOf F E).Object)), (∀ e ∈ l, e.node = v → p e = true) →
      ∀ (w w' : V → Node (protoOf F E)), w v = w' v →
        (l.foldl rho.step w) v = ((l.filter p).foldl rho.step w') v
  | [], _, _, _, h => h
  | e :: l, hp, w, w', h => by
    have hl : ∀ e ∈ l, e.node = v → p e = true := fun e he => hp e (List.mem_cons_of_mem _ he)
    by_cases he : p e = true
    · rw [List.filter_cons_of_pos he, List.foldl_cons, List.foldl_cons]
      exact foldl_step_filter p l hl _ _ (rho.step_apply_congr h e)
    · rw [List.filter_cons_of_neg he, List.foldl_cons]
      have hne : e.node ≠ v := fun hn => he (hp e List.mem_cons_self hn)
      exact foldl_step_filter p l hl _ _ ((rho.step_apply_of_ne w hne).trans h)

/-! ### The index map -/

theorem retain_take (i : Nat) :
    (rho.retain d).events.take (rho.retainIdx d i) = (rho.events.take i).filter (rho.keptAt d) := by
  have h : rho.events.filter (rho.keptAt d) =
      (rho.events.take i).filter (rho.keptAt d) ++ (rho.events.drop i).filter (rho.keptAt d) := by
    rw [← List.filter_append, List.take_append_drop]
  rw [retain_events, retainIdx, h]
  exact List.take_left' rfl

theorem retainIdx_zero : rho.retainIdx d 0 = 0 := by simp [retainIdx]

theorem retainIdx_succ {i : Nat} {e : Event V (protoOf F E).Object}
    (he : rho.events[i]? = some e) :
    rho.retainIdx d (i + 1) = rho.retainIdx d i + if rho.keptAt d e then 1 else 0 := by
  simp only [retainIdx, List.take_add_one, he, Option.toList_some, List.filter_append,
    List.length_append]
  split_ifs with h <;> simp [h]

theorem retainIdx_succ_of_kept {i : Nat} {e : Event V (protoOf F E).Object}
    (he : rho.events[i]? = some e) (hk : e.node ∉ rho.faultyAt d) :
    rho.retainIdx d (i + 1) = rho.retainIdx d i + 1 := by
  rw [retainIdx_succ he]
  simp [(keptAt_iff).mpr hk]

theorem retainIdx_succ_of_not_kept {i : Nat} {e : Event V (protoOf F E).Object}
    (he : rho.events[i]? = some e) (hk : e.node ∈ rho.faultyAt d) :
    rho.retainIdx d (i + 1) = rho.retainIdx d i := by
  rw [retainIdx_succ he]
  simp [keptAt, hk]

theorem retainIdx_succ_of_none {i : Nat} (he : rho.events[i]? = none) :
    rho.retainIdx d (i + 1) = rho.retainIdx d i := by
  have : rho.events.take (i + 1) = rho.events.take i := by
    rw [List.take_add_one, he]; simp
  simp [retainIdx, this]

theorem retainIdx_succ_le (i : Nat) : rho.retainIdx d (i + 1) ≤ rho.retainIdx d i + 1 := by
  cases he : rho.events[i]? with
  | none => rw [retainIdx_succ_of_none he]; omega
  | some e => rw [retainIdx_succ he]; split_ifs <;> omega

theorem retainIdx_mono {i j : Nat} (hij : i ≤ j) : rho.retainIdx d i ≤ rho.retainIdx d j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    refine ih.trans ?_
    cases he : rho.events[j]? with
    | none => rw [retainIdx_succ_of_none he]
    | some e => rw [retainIdx_succ he]; omega

theorem retainIdx_length : rho.retainIdx d rho.events.length = (rho.retain d).events.length := by
  rw [retainIdx, List.take_length, retain_events]

/-- A kept event of the full run is at its retained index. -/
theorem retain_getElem? {i : Nat} {e : Event V (protoOf F E).Object}
    (he : rho.events[i]? = some e) (hk : e.node ∉ rho.faultyAt d) :
    (rho.retain d).events[rho.retainIdx d i]? = some e := by
  have hs := retainIdx_succ_of_kept (d := d) he hk
  have ht := retain_take (rho := rho) (d := d) (i + 1)
  have hr : (rho.events.take (i + 1)).filter (rho.keptAt d) =
      (rho.events.take i).filter (rho.keptAt d) ++ [e] := by
    rw [List.take_add_one, he, Option.toList_some, List.filter_append]
    simp [(keptAt_iff).mpr hk]
  rw [hs, hr] at ht
  have hl := congrArg (fun l => l[rho.retainIdx d i]?) ht
  rw [List.getElem?_take_of_lt (by omega)] at hl
  rw [hl, List.getElem?_append_right (by rw [retainIdx])]
  rw [retainIdx]
  simp

theorem retainIdx_lt_of_kept {i j : Nat} (hij : i < j) {e : Event V (protoOf F E).Object}
    (he : rho.events[i]? = some e) (hk : e.node ∉ rho.faultyAt d) :
    rho.retainIdx d i < rho.retainIdx d j := by
  have hs := retainIdx_succ_of_kept (d := d) he hk
  exact lt_of_lt_of_le (show rho.retainIdx d i < rho.retainIdx d (i + 1) by omega)
    (retainIdx_mono (rho := rho) (d := d) hij)

/-- Every retained event is a kept event of the full run at a preimage index. -/
theorem retain_getElem?_preimage {j : Nat} {e : Event V (protoOf F E).Object}
    (he : (rho.retain d).events[j]? = some e) :
    ∃ i, rho.events[i]? = some e ∧ rho.retainIdx d i = j ∧ e.node ∉ rho.faultyAt d := by
  classical
  have hj : j < (rho.retain d).events.length := (List.getElem?_eq_some_iff.mp he).1
  have hex : ∃ i, j < rho.retainIdx d (i + 1) :=
    ⟨rho.events.length, by
      rw [retainIdx_succ_of_none (List.getElem?_eq_none le_rfl), retainIdx_length]
      exact hj⟩
  let i := Nat.find hex
  have hi : j < rho.retainIdx d (i + 1) := Nat.find_spec hex
  have hlo : rho.retainIdx d i ≤ j := by
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · rw [h0, retainIdx_zero]; omega
    · have := Nat.find_min hex (show i - 1 < i by omega)
      rw [show i - 1 + 1 = i by omega] at this
      omega
  have heq : rho.retainIdx d i = j := by
    have := retainIdx_succ_le (rho := rho) (d := d) i
    omega
  cases hei : rho.events[i]? with
  | none =>
    rw [retainIdx_succ_of_none hei] at hi
    omega
  | some e' =>
    have hk : e'.node ∉ rho.faultyAt d := by
      intro hn
      rw [retainIdx_succ_of_not_kept hei hn] at hi
      omega
    have := retain_getElem? (d := d) hei hk
    rw [heq, he] at this
    cases this
    exact ⟨i, hei, heq, hk⟩

/-! ### States, releases and receipts of kept nodes -/

/-- **A kept node's state at a cut is its state at the retained cut.** -/
theorem retain_stateBefore {v : V} (hv : v ∉ rho.faultyAt d) (i : Nat) :
    (rho.retain d).stateBefore (rho.retainIdx d i) v = rho.stateBefore i v := by
  change ((rho.retain d).events.take (rho.retainIdx d i)).foldl (rho.retain d).step
      (rho.retain d).initWorld v = (rho.events.take i).foldl rho.step rho.initWorld v
  rw [retain_take, retain_step, retain_initWorld]
  refine (foldl_step_filter (rho := rho) _ _ ?_ _ _ rfl).symm
  intro e _ he
  rw [keptAt_iff, he]
  exact hv

/-- A kept event releases what it releases in the full run. -/
theorem retain_releasesAt {i : Nat} {e : Event V (protoOf F E).Object}
    (he : rho.events[i]? = some e) (hk : e.node ∉ rho.faultyAt d) :
    (rho.retain d).releasesAt (rho.retainIdx d i) = rho.releasesAt i := by
  have hg := retain_getElem? (d := d) he hk
  unfold releasesAt
  rw [hg, he]
  cases e with
  | tick v t => simp only [Event.node] at hk; dsimp only; rw [retain_stateBefore hk]; rfl
  | deliver v o t => simp only [Event.node] at hk; dsimp only; rw [retain_stateBefore hk]; rfl
  | restart v t => rfl

theorem retain_sendsAt {v : V} (hv : v ∉ rho.faultyAt d) {i : Nat} {t : Time}
    (hs : rho.SendsAt v i t) : (rho.retain d).SendsAt v (rho.retainIdx d i) t := by
  rcases hs with h | ⟨o, h⟩
  · exact Or.inl (retain_getElem? h hv)
  · exact Or.inr ⟨o, retain_getElem? h hv⟩

theorem retain_releases_iff {v : V} (hv : v ∉ rho.faultyAt d) {o : (protoOf F E).Object}
    {t : Time} : (rho.retain d).releases v o t ↔ rho.releases v o t := by
  constructor
  · rintro ⟨j, hs, ho⟩
    obtain ⟨e, he, hn, ht⟩ := hs.exists_event
    obtain ⟨i, hi, rfl, hk⟩ := retain_getElem?_preimage he
    refine ⟨i, ?_, by rwa [← retain_releasesAt hi hk]⟩
    rcases hs with h | ⟨p, h⟩
    · rw [h] at he; cases he; exact Or.inl hi
    · rw [h] at he; cases he; exact Or.inr ⟨p, hi⟩
  · rintro ⟨i, hs, ho⟩
    obtain ⟨e, he, hn, -⟩ := hs.exists_event
    exact ⟨_, retain_sendsAt hv hs, by rwa [retain_releasesAt he (hn ▸ hv)]⟩

theorem retain_receives_iff {w : V} (hw : w ∉ rho.faultyAt d) {o : (protoOf F E).Object}
    {t : Time} : (rho.retain d).receives w o t ↔ rho.receives w o t := by
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨i, hi, -, -⟩ := retain_getElem?_preimage hj
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨_, retain_getElem? hi hw⟩

/-- A kept node's view at a cut is its view at the retained cut. -/
theorem retain_viewIdx {v : V} (hv : v ∉ rho.faultyAt d) (i : Nat) :
    (rho.retain d).ViewIdx v (rho.retainIdx d i) = rho.ViewIdx v i := by
  unfold ViewIdx
  rw [retain_stateBefore hv]

/-! ### Validity -/

/-- **The retention at `d ≥ horizon` of a valid run is a valid run.** The releases of a dropped
node while it was honest become adversarial deliveries, which `Unforgeable` allows of a signer
faulty in the retained run. -/
theorem retain_valid (hv : rho.ExecutionValid) (hd : rho.horizon ≤ d) :
    (rho.retain d).ExecutionValid := by
  have hsub : ∀ e, e ∈ (rho.retain d).events → e ∈ rho.events := fun e he =>
    (mem_retain_events.mp he).1
  have hF : ∀ v t, t ≤ rho.horizon → v ∉ rho.faultyAt d → v ∉ rho.faultyAt t :=
    fun v t ht hv' hf => hv' (rho.faultyAt_mono (ht.trans hd) hf)
  refine ⟨hv.horizon_nonneg, hv.sorted.sublist List.filter_sublist, hv.nodup.filter _, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, hv.selValid, ?_⟩
  · exact fun e he => hv.in_horizon e (hsub e he)
  · exact fun e he => (mem_retain_events.mp he).2
  · intro v t ht0 hth hvh haw
    exact mem_retain_events.mpr ⟨hv.tick_total v t ht0 hth (hF v t hth hvh) haw, hvh⟩
  · exact fun v t he => hv.tick_awake v t (hsub _ he)
  · exact fun v o t he => hv.deliver_awake v o t (hsub _ he)
  · exact fun v t he => hv.restart_at_wake v t (hsub _ he)
  · intro v t ht0 hth hvh hw
    exact mem_retain_events.mpr ⟨hv.wake_restart v t ht0 hth (hF v t hth hvh) hw, hvh⟩
  · intro j w o t hj o' hc u hu hsg
    obtain ⟨i, hi, rfl, -⟩ := retain_getElem?_preimage hj
    have ht : t ≤ rho.horizon := (hv.in_horizon _ (List.mem_of_getElem? hi)).2
    obtain ⟨k, t', hk, hks, hko⟩ := hv.unforgeable i w o t hi o' hc u hu (hF u t ht hsg)
    obtain ⟨e, he, hn, -⟩ := hks.exists_event
    refine ⟨rho.retainIdx d k, t', retainIdx_lt_of_kept hk he (hn ▸ hsg),
      retain_sendsAt (rho := rho) hsg hks, ?_⟩
    rwa [retain_releasesAt he (hn ▸ hsg)]
  · intro j w o t hj o' hc k r ha
    obtain ⟨i, hi, -, -⟩ := retain_getElem?_preimage hj
    exact hv.credentials i w o t hi o' hc k r ha

/-! ### The end of a time -/

omit [DecidableEq V] in
/-- On a time-sorted run, the cut at the end of `t` follows the events at times `≤ t`. -/
theorem findGreatest_cutTime (hs : rho.events.Pairwise Event.keyLe) (t : Time) :
    Nat.findGreatest (fun i => rho.cutTime i ≤ t) rho.events.length =
      (rho.events.filter (fun e => decide (e.time ≤ t))).length := by
  obtain ⟨ys, hsplit, hys⟩ := rho.truncate_split hs t
  have hlen : rho.events.length = (rho.truncate t).events.length + ys.length := by
    rw [hsplit, List.length_append]
  rw [show (rho.events.filter (fun e => decide (e.time ≤ t))).length =
    (rho.truncate t).events.length by rw [truncate_eq], Nat.findGreatest_eq_iff]
  refine ⟨by omega, ?_, ?_⟩
  · intro hn
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hkl : k < (rho.truncate t).events.length := by omega
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

/-- The retained cut at the end of `t` is the retained index of the full cut at the end of `t`. -/
theorem retain_findGreatest (hs : rho.events.Pairwise Event.keyLe) (t : Time) :
    Nat.findGreatest (fun i => (rho.retain d).cutTime i ≤ t) (rho.retain d).events.length =
      rho.retainIdx d (Nat.findGreatest (fun i => rho.cutTime i ≤ t) rho.events.length) := by
  rw [findGreatest_cutTime (hs.sublist List.filter_sublist), findGreatest_cutTime hs, retainIdx]
  obtain ⟨ys, hsplit, -⟩ := rho.truncate_split hs t
  have htake : rho.events.take (rho.events.filter (fun e => decide (e.time ≤ t))).length =
      rho.events.filter (fun e => decide (e.time ≤ t)) := by
    rw [truncate_eq] at hsplit
    have h := List.take_left' (l₁ := rho.events.filter (fun e => decide (e.time ≤ t))) (l₂ := ys)
      rfl
    rwa [← hsplit] at h
  rw [htake, retain_events, List.filter_filter, List.filter_filter]
  congr 2
  funext e
  exact Bool.and_comm _ _

/-- **A kept node's state at the end of a time is unchanged by the retention.** -/
theorem retain_stateBefore_endCut (hs : rho.events.Pairwise Event.keyLe) {v : V}
    (hv : v ∉ rho.faultyAt d) (t : Time) :
    (rho.retain d).stateBefore
        (Nat.findGreatest (fun i => (rho.retain d).cutTime i ≤ t) (rho.retain d).events.length) v =
      rho.stateBefore (Nat.findGreatest (fun i => rho.cutTime i ≤ t) rho.events.length) v := by
  rw [retain_findGreatest hs, retain_stateBefore hv]

/-! ### Observation and the network -/

/-- **An object observed in the retained run at `d ≥ horizon` is observed in the full run.** -/
theorem retain_observed (hv : rho.ExecutionValid) (hd : rho.horizon ≤ d)
    {o : (protoOf F E).Object} (ho : o ∈ (rho.retain d).Observed) : o ∈ rho.Observed := by
  obtain ⟨v, j, hj, hh, hov⟩ := ho
  change v ∉ rho.faultyAt d at hh
  have hpre : ∃ i ≤ rho.events.length, rho.retainIdx d i = j := by
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · exact ⟨0, Nat.zero_le _, retainIdx_zero⟩
    · obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.mp (show
        (rho.retain d).events[j - 1]? ≠ none by
          rw [List.getElem?_eq_getElem (by omega)]; simp)
      obtain ⟨i, hi, hij, hk⟩ := retain_getElem?_preimage he
      refine ⟨i + 1, (List.getElem?_eq_some_iff.mp hi).1, ?_⟩
      rw [retainIdx_succ_of_kept hi hk]
      omega
  obtain ⟨i, hil, rfl⟩ := hpre
  refine ⟨v, i, hil, ?_, by rwa [← retain_viewIdx hh]⟩
  change v ∉ rho.faultyAt (rho.cutTime i)
  intro hf
  apply hh
  refine rho.faultyAt_mono ?_ hf
  cases i with
  | zero => exact (hv.horizon_nonneg.trans hd)
  | succ k =>
    simp only [cutTime]
    cases he : rho.events[k]? with
    | none => exact (hv.horizon_nonneg.trans hd)
    | some e => exact (hv.in_horizon e (List.mem_of_getElem? he)).2.trans hd

/-- A hash collision of the retained run at `d ≥ horizon` is one of the full run. -/
theorem retain_not_hashCollision (hv : rho.ExecutionValid) (hd : rho.horizon ≤ d)
    (hc : ¬ rho.HashCollision) : ¬ (rho.retain d).HashCollision := by
  rintro ⟨x, y, hxy, ⟨ox, hox, hx⟩, ⟨oy, hoy, hy⟩, hh⟩
  exact hc ⟨x, y, hxy, ⟨ox, retain_observed hv hd hox, hx⟩,
    ⟨oy, retain_observed hv hd hoy, hy⟩, hh⟩

/-- A send of a valid run is at a time of `[0, horizon]`. -/
theorem releases_time (hv : rho.ExecutionValid) {v : V} {o : (protoOf F E).Object} {t : Time}
    (h : rho.releases v o t) : 0 ≤ t ∧ t ≤ rho.horizon := by
  obtain ⟨i, hs, -⟩ := h
  obtain ⟨e, he, -, rfl⟩ := hs.exists_event
  exact hv.in_horizon e (List.mem_of_getElem? he)

/-- **Delivery transfers to the retention at `d ≥ horizon`**, for deadlines at or after their
start: every node the retained run counts as honest is honest in the full run at every time up to
the horizon, and sends, receipts and inboxes of kept nodes are unchanged. -/
theorem retain_delivers (hv : rho.ExecutionValid) (hd : rho.horizon ≤ d) {dl dlF : Time → Time}
    {cut : Time} (hdl : ∀ a, a ≤ dl a) (h : rho.log.Delivers rho.point dl dlF cut) :
    (rho.retain d).log.Delivers (rho.retain d).point dl dlF cut := by
  have hF : ∀ v t, t ≤ rho.horizon → v ∉ rho.faultyAt d → v ∉ rho.faultyAt t :=
    fun v t ht hv' hf => hv' (rho.faultyAt_mono (ht.trans hd) hf)
  have hheld : ∀ w m e, w ∉ rho.faultyAt d →
      rho.log.Held rho.point w m e → (rho.retain d).log.Held (rho.retain d).point w m e := by
    rintro w m e hw ⟨t', ht', hsr, hn⟩
    refine ⟨t', ht', ?_, hn⟩
    rcases hsr with hs | hr
    · exact Or.inl ((retain_releases_iff hw).mpr hs)
    · exact Or.inr ((retain_receives_iff hw).mpr hr)
  constructor
  · intro v m t hs hvh hr w a hta hdc hdh hw haw
    have hs' : rho.releases v m t := (retain_releases_iff hvh).mp hs
    exact hheld w m _ hw (h.msgs v m t hs' (hF v t (releases_time hv hs').2 hvh) hr w a hta hdc
      hdh (hF w _ hdh hw) haw)
  · intro v m t hs hvh hr w a hta hdc hdh hw haw
    have hs' : rho.releases v m t := (retain_releases_iff hvh).mp hs
    exact hheld w m _ hw (h.fgAtts v m t hs' (hF v t (releases_time hv hs').2 hvh) hr w a hta hdc
      hdh (hF w _ hdh hw) haw)
  · intro u x τ hτ hu hua hx w a hτa hdc hdh hw haw
    exact h.txs u x τ hτ (hF u τ ((hτa.trans (hdl a)).trans hdh) hu) hua hx w a hτa hdc hdh
      (hF w _ hdh hw) haw

end Run

end Consensus.Model

end
