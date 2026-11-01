module
public import AvailableChainFGSARun.Proofs.Receipts -- shake: keep (re-export)
public import AvailableChainFGSARun.Proofs.Hooks -- shake: keep (re-export)
public import AvailableChainEngineV2.Laws.Duty.SelfDelivery -- shake: keep (re-export)

/-! Self-delivery of the own FG row (own-row analysis, Option 1; spec
`on_tick` ends with `attest`, and `on_attestation` is the delivery handler).

The FG action tick records the released row in Λ only; the row enters the
sender's store through a delivery event. This module shows that the
same-time self-delivery of an emitted row, appended after the last event of
the sender, is a valid continuation of a valid run (`EmitOk` for the row,
with freshness from send-once and unforgeable signatures), and that the
per-object delivery premises survive the append. The regime record
`Base₂` is handled in `AvailableChainFGSAProofs.Proofs.Shared.SelfDelivery`.
No statement, claim, manifest or fixture changes. -/

public section
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG
variable {p : Params} {In V : Type} [DecidableEq V] {c : AppCodec In}

/-! ### Append laws of the duty engine (generic in the protocol)

TODO (review m2): these laws and the cut laws below are generic in `P`; their home is
`AvailableChainEngineV2/Laws/Duty/SelfDelivery.lean` under `V2.D.Run` (where
`getElem?_snoc_cases` is the local `hcases` of `ExecutionValid.snoc_selfDelivery`). The
move is deferred: an edit of that L1 module invalidates the whole downstream build. -/

section Snoc
variable {In' : Type} {P : V2.ProtocolSpecD In'} {E : Generic.Env V} {rho : V2.D.Run V P}
  {e : V2.Event V P.Object}

omit [DecidableEq V] in
/-- [own-row Option 1; DC N3] An index of the appended run is an old index or the new one. -/
theorem getElem?_snoc_cases {k : Nat} {f : V2.Event V P.Object}
    (hk : ({ rho with events := rho.events ++ [e] } : V2.D.Run V P).events[k]? = some f) :
    (k < rho.events.length ∧ rho.events[k]? = some f) ∨
      (k = rho.events.length ∧ f = e) := by
  by_cases hlt : k < rho.events.length
  · exact Or.inl ⟨hlt, by rw [← V2.D.Run.getElem?_snoc_of_lt hlt]; exact hk⟩
  · change (rho.events ++ [e])[k]? = some f at hk
    have hk' : k < (rho.events ++ [e]).length := (List.getElem?_eq_some_iff.mp hk).1
    have hkn : k = rho.events.length := by simp at hk'; omega
    subst hkn
    have hdn : (rho.events ++ [e])[rho.events.length]? = some e := by simp
    rw [hdn] at hk
    exact Or.inr ⟨rfl, (Option.some.inj hk).symm⟩

/-- [own-row Option 1; DC N3] Past the new event, the state is the final state. -/
theorem stateBefore_snoc_of_ge {k : Nat} (hk : rho.events.length + 1 ≤ k) :
    V2.D.Run.stateBefore E ({ rho with events := rho.events ++ [e] } : V2.D.Run V P) k =
      V2.D.Run.stateBefore E ({ rho with events := rho.events ++ [e] } : V2.D.Run V P)
        (rho.events.length + 1) := by
  simp only [V2.D.Run.stateBefore]
  rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp)]

/-- [own-row Option 1; DC N3] The state after the new event is one step from the old final
state. -/
theorem stateBefore_snoc_last :
    V2.D.Run.stateBefore E ({ rho with events := rho.events ++ [e] } : V2.D.Run V P)
      (rho.events.length + 1) =
      V2.D.World.step E rho (V2.D.Run.stateBefore E rho rho.events.length) e := by
  have hdn : ({ rho with events := rho.events ++ [e] } : V2.D.Run V P).events[rho.events.length]? =
      some e := by simp
  rw [V2.D.Run.stateBefore_succ E _ hdn, V2.D.Run.stateBefore_snoc_of_le le_rfl]
  rfl

/-- [own-row Option 1; DC N3] The time-indexed state after an append: one more step when the
new event is before the time. -/
theorem stateBeforeTime_snoc (T : Time) :
    V2.D.Run.stateBeforeTime E ({ rho with events := rho.events ++ [e] } : V2.D.Run V P) T =
      if e.time < T then V2.D.World.step E rho (V2.D.Run.stateBeforeTime E rho T) e
      else V2.D.Run.stateBeforeTime E rho T := by
  change ((rho.events ++ [e]).filter (fun f => decide (f.time < T))).foldl
    (V2.D.World.step E rho) V2.D.World.init = _
  rw [List.filter_append, List.foldl_append]
  by_cases h : e.time < T
  · simp [h]
    rfl
  · simp [h]
    rfl

/-- [own-row Option 1; DC N3] A delivery append adds no emission. -/
theorem emits_snoc_deliver_iff {v u : V} {o₀ o : P.Object} {t₀ t : Time} :
    V2.D.Run.emits E ({ rho with events := rho.events ++ [.deliver v o₀ t₀] } : V2.D.Run V P)
      u o t ↔ V2.D.Run.emits E rho u o t := by
  constructor
  · rintro ⟨k, hk, ho⟩
    rcases getElem?_snoc_cases hk with ⟨hlt, hk'⟩ | ⟨-, h⟩
    · exact ⟨k, hk', by rw [V2.D.Run.emitsAt_snoc_of_lt hlt] at ho; exact ho⟩
    · cases h
  · exact V2.D.Run.emits_snoc

/-- [own-row Option 1; DC N3] Old handler calls survive an append. -/
theorem handlesAt_snoc_of_lt {k : Nat} (hk : k < rho.events.length) {w : V} {o : P.Object}
    {t : Time} (h : V2.D.Run.handlesAt E rho k w o t) :
    V2.D.Run.handlesAt E ({ rho with events := rho.events ++ [e] } : V2.D.Run V P) k w o t := by
  obtain ⟨o', hk', hh⟩ := h
  exact ⟨o', by rw [V2.D.Run.getElem?_snoc_of_lt hk]; exact hk',
    by rw [V2.D.Run.stateBefore_snoc_of_le (Nat.le_of_lt hk)]; exact hh⟩

/-- [own-row Option 1; DC N3] A handler call index of the old run is below its length. -/
theorem handlesAt_lt_length {k : Nat} {w : V} {o : P.Object} {t : Time}
    (h : V2.D.Run.handlesAt E rho k w o t) : k < rho.events.length := by
  obtain ⟨_, hk, -⟩ := h
  exact (List.getElem?_eq_some_iff.mp hk).1

/-- [own-row Option 1; DC N3] A handler call of the appended run is an old call or a call of
the new event. -/
theorem handlesAt_snoc_cases {k : Nat} {w : V} {o : P.Object} {t : Time}
    (h : V2.D.Run.handlesAt E ({ rho with events := rho.events ++ [e] } : V2.D.Run V P)
      k w o t) :
    (k < rho.events.length ∧ V2.D.Run.handlesAt E rho k w o t) ∨
      (k = rho.events.length ∧ ∃ o', e = .deliver w o' t ∧
        P.handles (V2.D.Run.stateBefore E rho rho.events.length w) o' o) := by
  obtain ⟨o', hk, hh⟩ := h
  rcases getElem?_snoc_cases hk with ⟨hlt, hk'⟩ | ⟨rfl, he⟩
  · exact Or.inl ⟨hlt, o', hk',
      by rw [V2.D.Run.stateBefore_snoc_of_le (Nat.le_of_lt hlt)] at hh; exact hh⟩
  · exact Or.inr ⟨rfl, o', he.symm,
      by rw [V2.D.Run.stateBefore_snoc_of_le le_rfl] at hh; exact hh⟩

/-- [own-row Option 1; DC N3] An acceptance of the appended run is an old acceptance or a
call of the new event. -/
theorem acceptsAt_snoc_cases {k : Nat} {w : V} {o : P.Object} {t : Time}
    (h : V2.D.Run.acceptsAt E ({ rho with events := rho.events ++ [e] } : V2.D.Run V P)
      k w o t) :
    (k < rho.events.length ∧ V2.D.Run.acceptsAt E rho k w o t) ∨
      (k = rho.events.length ∧ ∃ o', e = .deliver w o' t ∧
        P.handles (V2.D.Run.stateBefore E rho rho.events.length w) o' o) := by
  obtain ⟨hh, hb, ha⟩ := h
  rcases handlesAt_snoc_cases hh with ⟨hlt, hh'⟩ | hnew
  · refine Or.inl ⟨hlt, hh', ?_, ?_⟩
    · rw [V2.D.Run.stateBefore_snoc_of_le (Nat.le_of_lt hlt)] at hb; exact hb
    · rw [V2.D.Run.stateBefore_snoc_of_le hlt] at ha; exact ha
  · exact Or.inr hnew

omit [DecidableEq V] in
/-- [own-row Option 1; DC N3] A delivery append keeps `NoRestart`. -/
theorem noRestart_snoc_deliver {v : V} {o : P.Object} {t : Time} (h : V2.D.NoRestart rho) :
    V2.D.NoRestart ({ rho with events := rho.events ++ [.deliver v o t] } : V2.D.Run V P) := by
  intro k u s hk
  rcases getElem?_snoc_cases hk with ⟨-, hk'⟩ | ⟨-, hk'⟩
  · exact h k u s hk'
  · cases hk'

end Snoc

/-! ### The cut at the action time (generic in the protocol)

The run `rho` cut at `n` with horizon `t` has the first `n` events, where `n` is the number
of events with key at most `(t, 1)` (`hcut`; `exists_cut` supplies it for a sorted run). In a
sorted run these are the events before the deliveries at `t`. The cut run keeps the engine
premises, and the same-time self-delivery of a row released at `t` appends to it: `hkey`
and `hlast` of the append laws hold by construction (`cut_key_le`, `cut_lastEvent`). -/

section Cut
variable {In' : Type} {P : V2.ProtocolSpecD In'} {E : Generic.Env V} {rho : V2.D.Run V P}
  {n : Nat} {t : Time}

omit [DecidableEq V] in
/-- [own-row Option 1; DC N3] A sorted event list has a cut index for every key bound. -/
theorem exists_cut (hs : rho.events.Pairwise (fun e f => V2.Event.key e ≤ V2.Event.key f))
    (b : Lex (Time × Nat)) :
    ∃ n, ∀ (k : Nat) (e : V2.Event V P.Object), rho.events[k]? = some e →
      (k < n ↔ e.key ≤ b) := by
  suffices h : ∀ l : List (V2.Event V P.Object),
      l.Pairwise (fun e f => V2.Event.key e ≤ V2.Event.key f) →
      ∃ n, ∀ k e, l[k]? = some e → (k < n ↔ V2.Event.key e ≤ b) from h _ hs
  intro l hl
  induction l with
  | nil => exact ⟨0, fun k e hk => by simp at hk⟩
  | cons a l ih =>
    obtain ⟨hal, hl'⟩ := List.pairwise_cons.mp hl
    obtain ⟨n, hn⟩ := ih hl'
    by_cases ha : a.key ≤ b
    · refine ⟨n + 1, fun k e hk => ?_⟩
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        exact ⟨fun _ => ha, fun _ => Nat.succ_pos n⟩
      | succ k =>
        simp only [List.getElem?_cons_succ] at hk
        exact Nat.succ_lt_succ_iff.trans (hn k e hk)
    · refine ⟨0, fun k e hk => ⟨fun h => absurd h (Nat.not_lt_zero _), fun he => ?_⟩⟩
      exfalso
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        exact ha he
      | succ k =>
        simp only [List.getElem?_cons_succ] at hk
        exact ha (le_trans (hal e (List.mem_of_getElem? hk)) he)

omit [DecidableEq V] in
/-- [own-row Option 1; DC N3] A tick key is below the cut bound iff its time is at most `t`. -/
theorem tick_key_le {u : V} {s : Time} :
    (V2.Event.tick u s : V2.Event V P.Object).key ≤ toLex (t, 1) ↔ s ≤ t := by
  unfold V2.Event.key
  rw [Prod.Lex.toLex_le_toLex]
  change s < t ∨ s = t ∧ 1 ≤ 1 ↔ s ≤ t
  constructor
  · rintro (h | ⟨rfl, -⟩)
    · exact le_of_lt h
    · exact le_rfl
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, le_rfl⟩

omit [DecidableEq V] in
/-- [own-row Option 1; DC N3] A delivery key is below the cut bound iff its time is below
`t`. -/
theorem deliver_key_le {u : V} {o : P.Object} {s : Time} :
    (V2.Event.deliver u o s : V2.Event V P.Object).key ≤ toLex (t, 1) ↔ s < t := by
  unfold V2.Event.key
  rw [Prod.Lex.toLex_le_toLex]
  change s < t ∨ s = t ∧ 2 ≤ 1 ↔ s < t
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact h
    · exact absurd h (by decide)
  · exact Or.inl

omit [DecidableEq V] in
/-- [own-row Option 1; DC N3] An event below the cut bound is at time at most `t`. -/
theorem cut_time_le_of_key_le {e : V2.Event V P.Object} (h : e.key ≤ toLex (t, 1)) :
    e.time ≤ t := by
  unfold V2.Event.key at h
  rcases Prod.Lex.toLex_le_toLex.mp h with h | ⟨h, -⟩
  · exact le_of_lt h
  · exact le_of_eq h

omit [DecidableEq V] in
/-- [own-row Option 1; DC N3] An event above the cut bound is at time at least `t`. -/
theorem le_time_of_not_key_le {e : V2.Event V P.Object} (h : ¬ e.key ≤ toLex (t, 1)) :
    t ≤ e.time := by
  by_contra hlt
  exact h (by unfold V2.Event.key; exact Prod.Lex.toLex_le_toLex.mpr (Or.inl (lt_of_not_ge hlt)))

omit [DecidableEq V] in
/-- [own-row Option 1; DC N3] The events of the cut run are the old events below `n`. -/
theorem getElem?_cut_iff {k : Nat} {e : V2.Event V P.Object} :
    (rho.events.take n)[k]? = some e ↔ k < n ∧ rho.events[k]? = some e := by
  rw [List.getElem?_take]
  by_cases h : k < n <;> simp [h]

/-- [own-row Option 1; DC N3] States at or before the cut are the old states. -/
theorem stateBefore_cut_of_le {k : Nat} (hk : k ≤ n) :
    V2.D.Run.stateBefore E ({ rho with events := rho.events.take n, horizon := t } :
      V2.D.Run V P) k = V2.D.Run.stateBefore E rho k := by
  change ((rho.events.take n).take k).foldl (V2.D.World.step E rho) V2.D.World.init = _
  rw [List.take_take, Nat.min_eq_left hk]
  rfl

/-- [own-row Option 1; DC N3] States after the cut are the old state at the cut. -/
theorem stateBefore_cut_of_ge {k : Nat} (hk : n ≤ k) :
    V2.D.Run.stateBefore E ({ rho with events := rho.events.take n, horizon := t } :
      V2.D.Run V P) k = V2.D.Run.stateBefore E rho n := by
  change ((rho.events.take n).take k).foldl (V2.D.World.step E rho) V2.D.World.init = _
  rw [List.take_take, Nat.min_eq_right hk]
  rfl

/-- [own-row Option 1; DC N3] Ticks before the cut release the same objects. -/
theorem emitsAt_cut_of_lt {k : Nat} (hk : k < n) :
    V2.D.Run.emitsAt E ({ rho with events := rho.events.take n, horizon := t } :
      V2.D.Run V P) k = V2.D.Run.emitsAt E rho k := by
  delta V2.D.Run.emitsAt
  rw [List.getElem?_take_of_lt hk, stateBefore_cut_of_le (Nat.le_of_lt hk)]
  rfl

/-- [own-row Option 1; DC N3] The emissions of the cut run are the old emissions at times at
most `t`. -/
theorem emits_cut_iff
    (hcut : ∀ k e, rho.events[k]? = some e → (k < n ↔ e.key ≤ toLex (t, 1)))
    {u : V} {o : P.Object} {s : Time} :
    V2.D.Run.emits E ({ rho with events := rho.events.take n, horizon := t } : V2.D.Run V P)
      u o s ↔ s ≤ t ∧ V2.D.Run.emits E rho u o s := by
  constructor
  · rintro ⟨k, hk, ho⟩
    obtain ⟨hkn, hk'⟩ := getElem?_cut_iff.mp hk
    refine ⟨tick_key_le.mp ((hcut k _ hk').mp hkn), k, hk', ?_⟩
    rw [emitsAt_cut_of_lt hkn] at ho
    exact ho
  · rintro ⟨hs, k, hk, ho⟩
    have hkn : k < n := (hcut k _ hk).mpr (tick_key_le.mpr hs)
    exact ⟨k, getElem?_cut_iff.mpr ⟨hkn, hk⟩, by rw [emitsAt_cut_of_lt hkn]; exact ho⟩

/-- [own-row Option 1; DC N3] The time-indexed state of the cut run at a time at most `t` is
the old one: every event before that time is below the cut. -/
theorem stateBeforeTime_cut
    (hcut : ∀ k e, rho.events[k]? = some e → (k < n ↔ e.key ≤ toLex (t, 1)))
    {D : Time} (hD : D ≤ t) :
    V2.D.Run.stateBeforeTime E ({ rho with events := rho.events.take n, horizon := t } :
      V2.D.Run V P) D = V2.D.Run.stateBeforeTime E rho D := by
  change ((rho.events.take n).filter (fun e => decide (e.time < D))).foldl
    (V2.D.World.step E rho) V2.D.World.init =
    (rho.events.filter (fun e => decide (e.time < D))).foldl (V2.D.World.step E rho)
      V2.D.World.init
  conv_rhs => rw [← List.take_append_drop n rho.events]
  rw [List.filter_append, List.foldl_append]
  have hnil : (rho.events.drop n).filter (fun e => decide (e.time < D)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro e he
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
    rw [List.getElem?_drop] at hj
    have hkey : ¬ e.key ≤ toLex (t, 1) := fun h => by
      have := (hcut _ _ hj).mpr h
      omega
    simp only [decide_eq_true_eq]
    exact not_lt.mpr (le_trans hD (le_time_of_not_key_le hkey))
  rw [hnil, List.foldl_nil]

/-- [own-row Option 1; DC N3] Handler calls before the cut survive it. -/
theorem handlesAt_cut_of_lt {k : Nat} (hk : k < n) {w : V} {o : P.Object} {s : Time}
    (h : V2.D.Run.handlesAt E rho k w o s) :
    V2.D.Run.handlesAt E ({ rho with events := rho.events.take n, horizon := t } :
      V2.D.Run V P) k w o s := by
  obtain ⟨o', hk', hh⟩ := h
  exact ⟨o', getElem?_cut_iff.mpr ⟨hk, hk'⟩,
    by rw [stateBefore_cut_of_le (Nat.le_of_lt hk)]; exact hh⟩

/-- [own-row Option 1; DC N3] A handler call of the cut run is an old call below the cut. -/
theorem handlesAt_cut {k : Nat} {w : V} {o : P.Object} {s : Time}
    (h : V2.D.Run.handlesAt E ({ rho with events := rho.events.take n, horizon := t } :
      V2.D.Run V P) k w o s) :
    k < n ∧ V2.D.Run.handlesAt E rho k w o s := by
  obtain ⟨o', hk, hh⟩ := h
  obtain ⟨hkn, hk'⟩ := getElem?_cut_iff.mp hk
  exact ⟨hkn, o', hk', by rw [stateBefore_cut_of_le (Nat.le_of_lt hkn)] at hh; exact hh⟩

/-- [own-row Option 1; DC N3] An acceptance of the cut run is an old acceptance below the
cut. -/
theorem acceptsAt_cut {k : Nat} {w : V} {o : P.Object} {s : Time}
    (h : V2.D.Run.acceptsAt E ({ rho with events := rho.events.take n, horizon := t } :
      V2.D.Run V P) k w o s) :
    k < n ∧ V2.D.Run.acceptsAt E rho k w o s := by
  obtain ⟨hh, hb, ha⟩ := h
  obtain ⟨hkn, hh'⟩ := handlesAt_cut hh
  refine ⟨hkn, hh', ?_, ?_⟩
  · rw [stateBefore_cut_of_le (Nat.le_of_lt hkn)] at hb; exact hb
  · rw [stateBefore_cut_of_le hkn] at ha; exact ha

omit [DecidableEq V] in
/-- [own-row Option 1; DC N3] The cut keeps `NoRestart`. -/
theorem noRestart_cut (h : V2.D.NoRestart rho) :
    V2.D.NoRestart ({ rho with events := rho.events.take n, horizon := t } : V2.D.Run V P) :=
  fun k u s hk => h k u s (getElem?_cut_iff.mp hk).2

omit [DecidableEq V] in
/-- [own-row Option 1; DC N3] Every event of the cut run has key at most `(t, 2)`: the
`hkey` premise of the append laws. -/
theorem cut_key_le
    (hcut : ∀ k e, rho.events[k]? = some e → (k < n ↔ e.key ≤ toLex (t, 1))) :
    ∀ e ∈ ({ rho with events := rho.events.take n, horizon := t } : V2.D.Run V P).events,
      e.key ≤ toLex (t, 2) := by
  intro e he
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp he
  obtain ⟨hkn, hk'⟩ := getElem?_cut_iff.mp hk
  exact le_trans ((hcut k e hk').mp hkn)
    (Prod.Lex.toLex_le_toLex.mpr (Or.inr ⟨rfl, Nat.le_succ 1⟩))

omit [DecidableEq V] in
/-- [own-row Option 1; DC N3] After the tick of `v` at `t`, the cut run has no event of `v`:
the `hlast` premise of the append laws. The later events have key `(t, 1)`, so they are
ticks at `t`; a second tick of `v` at `t` contradicts `nodup`. -/
theorem cut_lastEvent (hS : V2.D.ScheduleWellFormed E rho)
    (hcut : ∀ k e, rho.events[k]? = some e → (k < n ↔ e.key ≤ toLex (t, 1)))
    {i : Nat} {v : V} (hi : rho.events[i]? = some (.tick v t)) :
    ∀ k e, i < k →
      ({ rho with events := rho.events.take n, horizon := t } : V2.D.Run V P).events[k]? =
        some e → e.node ≠ v := by
  intro k e hik hk hnode
  obtain ⟨hkn, hk'⟩ := getElem?_cut_iff.mp hk
  have hkey : e.key ≤ toLex (t, 1) := (hcut k e hk').mp hkn
  have hilen : i < rho.events.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨hkl, hkv⟩ := List.getElem?_eq_some_iff.mp hk'
  have hs := List.pairwise_iff_getElem.mp hS.sorted i k hilen hkl hik
  rw [hkv, (List.getElem?_eq_some_iff.mp hi).2] at hs
  have heq : e.key = toLex (t, 1) := le_antisymm hkey hs
  unfold V2.Event.key at heq
  have h2 := congrArg ofLex heq
  simp only [ofLex_toLex, Prod.mk.injEq] at h2
  cases e with
  | restart u s => simp [V2.Event.phase] at h2
  | deliver u o s => simp [V2.Event.phase] at h2
  | tick u s =>
    change u = v at hnode
    subst hnode
    have hst : s = t := by
      have := h2.1
      exact this
    have hki : k = i := (hS.nodup.getElem_inj_iff (hi := hkl) (hj := hilen)).mp
      (by rw [hkv, (List.getElem?_eq_some_iff.mp hi).2, hst])
    omega

/-- [own-row Option 1; DC N3] The cut run of a valid run is valid: the schedule fields by
sublist and the key bound, the delivery fields by the old indices, the signature fields by
`emits_cut_iff` (an emission before a cut delivery is before `t`). -/
theorem executionValid_cut (hvalid : V2.D.ExecutionValid E rho)
    (hcut : ∀ k e, rho.events[k]? = some e → (k < n ↔ e.key ≤ toLex (t, 1)))
    (ht0 : 0 ≤ t) (hth : t ≤ rho.horizon) :
    V2.D.ExecutionValid E ({ rho with events := rho.events.take n, horizon := t } :
      V2.D.Run V P) := by
  have hsub : (rho.events.take n).Sublist rho.events := List.take_sublist n _
  have hmem : ∀ e ∈ rho.events.take n, e.key ≤ toLex (t, 1) := fun e he => by
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp he
    obtain ⟨hkn, hk'⟩ := getElem?_cut_iff.mp hk
    exact (hcut k e hk').mp hkn
  refine { toScheduleWellFormed := ?_, toDeliveryWellFormed := ?_,
           toUnforgeableSignatures := ?_, toSleepWellFormed := ?_ }
  · refine ⟨ht0, hvalid.sorted.sublist hsub, hvalid.nodup.sublist hsub, ?_, ?_, ?_, ?_⟩
    · intro e he
      exact ⟨(hvalid.in_horizon e (hsub.subset he)).1, cut_time_le_of_key_le (hmem e he)⟩
    · intro e he
      exact hvalid.honest_only e (hsub.subset he)
    · intro u s he
      exact hvalid.tick_public u s (hsub.subset he)
    · intro u hu s hs h0 hh ha
      obtain ⟨k, hk⟩ :=
        List.mem_iff_getElem?.mp (hvalid.tick_total u hu s hs h0 (le_trans hh hth) ha)
      have hkn : k < n := (hcut k _ hk).mpr (tick_key_le.mpr hh)
      exact List.mem_iff_getElem?.mpr ⟨k, getElem?_cut_iff.mpr ⟨hkn, hk⟩⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro k u o s hk
      exact hvalid.wire k u o s (getElem?_cut_iff.mp hk).2
    · intro k u o s hk
      obtain ⟨hkn, hk'⟩ := getElem?_cut_iff.mp hk
      rw [stateBefore_cut_of_le (Nat.le_of_lt hkn)]
      exact hvalid.deps k u o s hk'
    · intro k u o s hk
      obtain ⟨hkn, hk'⟩ := getElem?_cut_iff.mp hk
      rw [stateBefore_cut_of_le (Nat.le_of_lt hkn)]
      exact hvalid.fresh k u o s hk'
  · refine ⟨?_, ?_⟩
    · rintro u o s ⟨k, hk⟩ w hw hhold
      obtain ⟨hkn, hk'⟩ := getElem?_cut_iff.mp hk
      obtain ⟨t', ht', he⟩ := hvalid.unforgeable u o s ⟨k, hk'⟩ w hw hhold
      have hst : s < t := deliver_key_le.mp ((hcut k _ hk').mp hkn)
      exact ⟨t', ht', (emits_cut_iff hcut).mpr ⟨le_trans ht' (le_of_lt hst), he⟩⟩
    · rintro u o s ⟨k, hk⟩ o' hc w hw hhold
      obtain ⟨hkn, hk'⟩ := getElem?_cut_iff.mp hk
      obtain ⟨t', ht', he⟩ := hvalid.carried u o s ⟨k, hk'⟩ o' hc w hw hhold
      have hst : s < t := deliver_key_le.mp ((hcut k _ hk').mp hkn)
      exact ⟨t', ht', (emits_cut_iff hcut).mpr ⟨le_trans ht' (le_of_lt hst), he⟩⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro u time h
      exact hvalid.tick_awake u time (hsub.subset h)
    · intro u o time h
      exact hvalid.deliver_awake u o time (hsub.subset h)
    · intro u time h
      exact hvalid.restart_awake u time (hsub.subset h)
    · intro u hu time h0 hh hw
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp
        (hvalid.wake_restart u hu time h0 (hh.trans hth) hw)
      have hkey : (V2.Event.restart u time : V2.Event V P.Object).key ≤ toLex (t, 1) := by
        change toLex (time, 0) ≤ toLex (t, 1)
        apply Prod.Lex.toLex_le_toLex.mpr
        rcases lt_or_eq_of_le hh with h | rfl
        · exact Or.inl h
        · exact Or.inr ⟨rfl, by change (0 : Nat) ≤ 1; exact Nat.zero_le 1⟩
      exact List.mem_of_getElem? (getElem?_cut_iff.mpr ⟨(hcut k _ hk).2 hkey, hk⟩)

omit [DecidableEq V] in
/-- [own-row Option 1; DC N3] The key bound `(t, 2)` survives an appended delivery at `t`:
the `hkey` premise for a further self-delivery. -/
theorem hkey_snoc_deliver {v : V} {o : P.Object}
    (hkey : ∀ e ∈ rho.events, e.key ≤ toLex (t, 2)) :
    ∀ e ∈ ({ rho with events := rho.events ++ [.deliver v o t] } : V2.D.Run V P).events,
      e.key ≤ toLex (t, 2) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hkey e he
  · rw [List.mem_singleton.mp he]
    exact le_refl (toLex (t, 2))

omit [DecidableEq V] in
/-- [own-row Option 1; DC N3] An appended delivery to another node keeps "no later event of
`u`": the `hlast` premise for a further self-delivery. -/
theorem hlast_snoc_of_ne {i : Nat} {u v : V} {o : P.Object}
    (hlast : ∀ k e, i < k → rho.events[k]? = some e → e.node ≠ u) (hne : v ≠ u) :
    ∀ k e, i < k →
      ({ rho with events := rho.events ++ [.deliver v o t] } : V2.D.Run V P).events[k]? =
        some e → e.node ≠ u := by
  intro k e hik hk
  rcases getElem?_snoc_cases hk with ⟨-, hk'⟩ | ⟨-, rfl⟩
  · exact hlast k e hik hk'
  · exact hne

/-- [own-row Option 1; DC Generic/Conditions.lean:134] A prefix delivery premise holds at
every earlier cut. -/
theorem healthyPrefixDeliveryBy_of_le {delayOf : P.Object → Time} {b₀ b : Time}
    (hb : b ≤ b₀)
    (h : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho delayOf b₀) :
    Gen.V2.Duty.HealthyPrefixDeliveryBy E rho delayOf b where
  broadcast_emitted u hu o t he w hw a hta ha had hc hh hr hx :=
    h.broadcast_emitted u hu o t he w hw a hta ha had (hc.trans hb) hh hr hx
  relay_accepted u hu k o t he w hw a hta ha had hc hh hr hx :=
    h.relay_accepted u hu k o t he w hw a hta ha had (hc.trans hb) hh hr hx

end Cut

/-! ### FG-SA facts about the own row -/

variable {E : Generic.Env V} {rho : V2.D.Run V (fgsa p c)}

/-- [own-row Option 1; DC N4] A store wire with a row payload keeps the proposals: the
handler is `admitRow` or the identity. -/
theorem process_row_proposals (st : State p.n) (a : Auth Label p.n) (body : RowPayload) :
    (FGSA.process p st ⟨a, .row body⟩).proposals = st.proposals := by
  unfold FGSA.process
  cases hd : Wire.decode (⟨a, .row body⟩ : Wire p.n) with
  | none => rfl
  | some m =>
    cases m with
    | vote s i b => cases decode_eq_vote.mp hd
    | block s N => cases decode_eq_block.mp hd
    | row i body' =>
      change (admitRow p st ⟨a, body'⟩).proposals = st.proposals
      rcases admitRow_eq p st ⟨a, body'⟩ with h | h <;> rw [h]

/-- [own-row Option 1; DC N4] An FG row delivery adds no named body. -/
theorem process_ofRow_namedBodies (st : State p.n) (a : RowWire p.n) :
    (FGSA.process p st (toWire p (ofRow p a))).namedBodies = st.namedBodies := by
  rw [toWire_ofRow]
  simp only [State.namedBodies, process_row_proposals]

/-- [own-row Option 1; DC NamedRootCollisionFree] The named scope of a run with an appended
row delivery is the named scope of the run. -/
theorem namedProposalInRun_snoc_row {v : V} {a : RowWire p.n} {t : Time}
    {A : NamedProposal p.n}
    (h : NamedProposalInRun p c E
      ({ rho with events := rho.events ++ [.deliver v (ofRow p a) t] }) A) :
    NamedProposalInRun p c E rho A := by
  obtain ⟨B, hB, hAB⟩ := h
  refine ⟨B, ?_, hAB⟩
  rcases hB with ⟨x, o, s, hmem, hpay⟩ | ⟨x, hx, k, hk⟩
  · rcases List.mem_append.mp hmem with hmem | hmem
    · exact Or.inl ⟨x, o, s, hmem, hpay⟩
    · obtain ⟨-, rfl, -⟩ := V2.Event.deliver.inj (List.mem_singleton.mp hmem)
      change Msg.row a.payload = Msg.proposal B at hpay
      cases hpay
  · refine Or.inr ⟨x, hx, ?_⟩
    by_cases hk' : k ≤ rho.events.length
    · exact ⟨k, by rw [V2.D.Run.stateBefore_snoc_of_le hk'] at hk; exact hk⟩
    · refine ⟨rho.events.length, ?_⟩
      rw [stateBefore_snoc_of_ge (by omega), stateBefore_snoc_last] at hk
      simp only [V2.D.World.step] at hk
      by_cases hxv : x = v
      · subst hxv
        rw [Function.update_self] at hk
        change B ∈ (FGSA.process p (V2.D.Run.stateBefore E rho rho.events.length x).st
          (toWire p (ofRow p a))).namedBodies at hk
        rw [process_ofRow_namedBodies] at hk
        exact hk
      · rw [Function.update_of_ne hxv] at hk
        exact hk

/-- [own-row Option 1; DC NamedRootCollisionFree] `NamedRootCollisionFree` survives an
appended row delivery: the scope does not grow. -/
theorem namedRootCollisionFree_snoc_row {v : V} {a : RowWire p.n} {t : Time}
    (h : NamedRootCollisionFree p c E rho) :
    NamedRootCollisionFree p c E
      ({ rho with events := rho.events ++ [.deliver v (ofRow p a) t] }) where
  root_injective B C hB hC :=
    h.root_injective B C (namedProposalInRun_snoc_row hB) (namedProposalInRun_snoc_row hC)

/-- [own-row Option 1; DC N4] A delivery append keeps every exclusion of the time-indexed
state (`excludesS_process`). -/
theorem excludes_stateBeforeTime_snoc {v w : V} {o₀ o : Obj p} {t₀ T : Time}
    (h : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho T w) o = true) :
    (fgsa p c).excludes (V2.D.Run.stateBeforeTime E
      ({ rho with events := rho.events ++ [.deliver v o₀ t₀] }) T w) o = true := by
  rw [stateBeforeTime_snoc]
  split
  · simp only [V2.D.World.step]
    by_cases hw : w = v
    · subst hw
      rw [Function.update_self]
      exact excludesS_process _ _ _ h
    · rw [Function.update_of_ne hw]
      exact h
  · exact h

/-- [own-row Option 1; DC N4] The contrapositive: an object not excluded after the append
was not excluded before. -/
theorem excludes_stateBeforeTime_snoc_false {v w : V} {o₀ o : Obj p} {t₀ T : Time}
    (h : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E
      ({ rho with events := rho.events ++ [.deliver v o₀ t₀] }) T w) o = false) :
    (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho T w) o = false := by
  cases hb : (fgsa p c).excludes (V2.D.Run.stateBeforeTime E rho T w) o with
  | false => rfl
  | true =>
    rw [excludes_stateBeforeTime_snoc (v := v) (o₀ := o₀) (t₀ := t₀) hb] at h
    cases h

/-- [own-row Option 1; spec `attest`, `on_attestation`; DC N4] The own row is fresh: a row
released by the FG action tick of `v` at index `i` is not in the row pool of `v` before
that tick. A pool row has an earlier handler call (`rowPool_provenance`); under
`UnforgeableSignatures` its honest holder `v` emitted it at or before that delivery; the
fixed FG seat emits each content once (`fgsa_emitOnceUnder`), so that emission is the tick
at `i`; the schedule order then puts the delivery before the emission time. -/
theorem fgsa_emitted_row_fresh (hvalid : V2.D.ExecutionValid E rho) {i : Nat} {v : V}
    {t : Time} (hi : rho.events[i]? = some (.tick v t)) {j : Fin p.n} {body : RowPayload}
    (ho : ofRow p ⟨.seat .fg j, body⟩ ∈ V2.D.Run.emitsAt E rho i) :
    (⟨.seat .fg j, body⟩ : RowWire p.n) ∉ (V2.D.Run.stateBefore E rho i v).st.rowPool := by
  intro hm
  obtain ⟨-, hseat, -⟩ := (fgsa_emitsAt_row E rho i v t hi j body).mp ho
  have hv : v ∈ rho.honest := hvalid.honest_only _ (List.mem_of_getElem? hi)
  have hilen : i < rho.events.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨k, tk, hki, ⟨o', hk, hhand⟩, -⟩ := rowPool_provenance E rho i v _ hm
  have hhold : V2.D.Run.holder rho (ofRow p ⟨.seat .fg j, body⟩).auth = some v := by
    rw [ofRow_auth]
    exact congrArg some hseat
  have hproc : V2.D.Run.processes rho v o' tk := ⟨k, hk⟩
  have hem : ∃ t', t' ≤ tk ∧ V2.D.Run.emits E rho v (ofRow p ⟨.seat .fg j, body⟩) t' := by
    rcases (fgsaHooks p c).handles_carries _ _ _ hhand with heq | hc
    · rw [← heq]
      exact hvalid.unforgeable v o' tk hproc v hv (by rw [heq]; exact hhold)
    · exact hvalid.carried v o' tk hproc _ hc v hv hhold
  obtain ⟨t', ht', i', hi', ho'⟩ := hem
  have hii : i' = i :=
    fgsa_emitOnceUnder E rho hvalid j (by rw [hseat]; exact hv) (.row body) i' i t' t
      (by rw [hseat]; exact hi') (by rw [hseat]; exact hi) ho' ho
  subst hii
  rw [hi] at hi'
  obtain ⟨-, rfl⟩ := V2.Event.tick.inj (Option.some.inj hi')
  obtain ⟨hkl, hkv⟩ := List.getElem?_eq_some_iff.mp hk
  have hs := List.pairwise_iff_getElem.mp hvalid.sorted k i' hkl hilen hki
  rw [hkv, (List.getElem?_eq_some_iff.mp hi).2] at hs
  unfold V2.Event.key at hs
  rcases Prod.Lex.toLex_le_toLex.mp hs with hlt | ⟨-, hph⟩
  · change tk < t at hlt
    exact (lt_irrefl _ (lt_of_le_of_lt ht' hlt)).elim
  · change (2 : Nat) ≤ 1 at hph
    omega

/-- [own-row Option 1; DC N4] `EmitOk` for a released FG row: the wire check from
`honest_emit_wellFormed`, no dependencies (`depsS`), freshness from
`fgsa_emitted_row_fresh`, and a row carries nothing (`carriesS`). -/
theorem fgsa_emitOk_row (hvalid : V2.D.ExecutionValid E rho) {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t)) {j : Fin p.n} {body : RowPayload}
    (ho : ofRow p ⟨.seat .fg j, body⟩ ∈ V2.D.Run.emitsAt E rho i) :
    V2.D.EmitOk E rho (V2.D.Run.stateBefore E rho i v) v t (ofRow p ⟨.seat .fg j, body⟩) := by
  obtain ⟨hawake, -, -⟩ := (fgsa_emitsAt_row E rho i v t hi j body).mp ho
  have hv : v ∈ rho.honest := hvalid.honest_only _ (List.mem_of_getElem? hi)
  have hd : (toWire p (ofRow p ⟨.seat .fg j, body⟩)).decode = some (.row j body) := by
    rw [toWire_ofRow]
    exact decode_eq_row.mpr rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact honest_emit_wellFormed E rho hvalid.toDeliveryWellFormed hvalid.toScheduleWellFormed
      i v t hi hv hawake _ ho
  · change depsS p (V2.D.tick E rho (V2.D.Run.stateBefore E rho i v) v t).1.st
      (ofRow p ⟨.seat .fg j, body⟩) = true
    unfold depsS
    rw [hd]
  · change processedS p (FGSA.clock p (V2.D.Run.stateBefore E rho i v).st t)
      (ofRow p ⟨.seat .fg j, body⟩) = false
    unfold processedS
    rw [hd, clock_rowPool]
    exact decide_eq_false (fgsa_emitted_row_fresh hvalid hi ho)
  · intro o' h
    exact h

/-- [own-row Option 1; DC N4] Every object released at an FG seat is a row with `EmitOk`. -/
theorem fgsa_emitOk_fg (hvalid : V2.D.ExecutionValid E rho) {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (.tick v t)) {j : Fin p.n} {m : Msg p.n}
    (ho : (⟨.seat (.base .fg) j, m⟩ : Obj p) ∈ V2.D.Run.emitsAt E rho i) :
    V2.D.EmitOk E rho (V2.D.Run.stateBefore E rho i v) v t ⟨.seat (.base .fg) j, m⟩ := by
  have ho' := ho
  rw [(V2.D.Run.step_tick_eq E rho hi).2] at ho'
  obtain ⟨body, rfl⟩ := fgsa_tick_fg_row E rho _ v t j m ho'
  exact fgsa_emitOk_row hvalid hi ho

/-- [own-row Option 1; DC N3] The same-time self-delivery of a released FG row, appended
after the last event of the sender, keeps `ExecutionValid`. Scope: `hkey` restricts the run
to events at or before `(t, 2)`, so with `tick_total` the run ends at the action time `t`;
`executionValid_ownRow_run` removes the restriction through the cut. -/
theorem executionValid_snoc_selfDelivery (hvalid : V2.D.ExecutionValid E rho) {i : Nat}
    {v : V} {t : Time} (hkey : ∀ e ∈ rho.events, e.key ≤ toLex (t, 2))
    (hi : rho.events[i]? = some (.tick v t))
    (hlast : ∀ k e, i < k → rho.events[k]? = some e → e.node ≠ v)
    {j : Fin p.n} {body : RowPayload}
    (ho : ofRow p ⟨.seat .fg j, body⟩ ∈ V2.D.Run.emitsAt E rho i) :
    V2.D.ExecutionValid E
      ({ rho with events := rho.events ++ [.deliver v (ofRow p ⟨.seat .fg j, body⟩) t] }) :=
  hvalid.snoc_selfDelivery (fgsaHooks p c) hkey hi hlast ho (fgsa_emitOk_row hvalid hi ho)

private theorem service_snoc {w : V} {o : Obj p} {a d : Time}
    {u : V} {obj : Obj p} {time : Time}
    (h : V2.D.DeliveryService E rho w o a d) :
    V2.D.DeliveryService E ({ rho with events := rho.events ++ [.deliver u obj time] })
      w o a d := by
  rcases h with ⟨k, hk, hp⟩ | ⟨t', ha, hd, j, hj⟩
  · left
    have hlen : k ≤ rho.events.length := hk.trans (List.length_filter_le _ _)
    refine ⟨k, ?_, ?_⟩
    · exact hk.trans (by
        change (rho.events.filter _).length ≤ ((rho.events ++ [_]).filter _).length
        rw [List.filter_append, List.length_append]
        omega)
    · rwa [V2.D.Run.stateBefore_snoc_of_le hlen]
  · right
    exact ⟨t', ha, hd, j, handlesAt_snoc_of_lt (handlesAt_lt_length hj) hj⟩

omit [DecidableEq V] in
private theorem actionCut_cut_eq {n : Nat} {t a : Time}
    (hcut : ∀ k e, rho.events[k]? = some e → (k < n ↔ e.key ≤ toLex (t, 1)))
    (ha : a < t) :
    V2.D.Run.actionCut ({ rho with events := rho.events.take n, horizon := t }) a =
      V2.D.Run.actionCut rho a := by
  change ((rho.events.take n).filter _).length = (rho.events.filter _).length
  conv_rhs => rw [← List.take_append_drop n rho.events]
  rw [List.filter_append, List.length_append]
  have hnil : (rho.events.drop n).filter
      (fun e => decide (e.time < a ∨ (e.time = a ∧ e.phase = 0))) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
    rw [List.getElem?_drop] at hj
    have hn : ¬ e.key ≤ toLex (t, 1) := by
      intro h
      have := (hcut _ _ hj).2 h
      omega
    have ht := le_time_of_not_key_le hn
    simp only [decide_eq_true_eq]
    rintro (h | ⟨h, _⟩) <;> dsimp [Time] at * <;> omega
  rw [hnil, List.length_nil, Nat.add_zero]

private theorem service_cut {n : Nat} {t a d : Time}
    (hcut : ∀ k e, rho.events[k]? = some e → (k < n ↔ e.key ≤ toLex (t, 1)))
    (had : a < d) (hdt : d ≤ t) {w : V} {o : Obj p}
    (h : V2.D.DeliveryService E rho w o a d) :
    V2.D.DeliveryService E ({ rho with events := rho.events.take n, horizon := t })
      w o a d := by
  rcases h with ⟨k, hk, hp⟩ | ⟨time, ha, hd, j, hj⟩
  · left
    have he := actionCut_cut_eq hcut (had.trans_le hdt)
    have hlen : V2.D.Run.actionCut rho a ≤ n := by
      rw [← he]
      exact (List.length_filter_le _ _).trans (by
        rw [List.length_take]
        exact Nat.min_le_left _ _)
    refine ⟨k, by rwa [he], ?_⟩
    rwa [stateBefore_cut_of_le (hk.trans hlen)]
  · right
    have hcall := hj
    obtain ⟨parent, he, _⟩ := hj
    have hjn : j < n := (hcut j _ he).2 (deliver_key_le.mpr (hd.trans_le hdt))
    exact ⟨time, ha, hd, j, handlesAt_cut_of_lt hjn hcall⟩

/-! ### Delivery regimes survive the append -/

/-- [own-row Option 1; DC Generic/Conditions.lean:110] `PartialSynchronyBy` survives the
same-time self-delivery of a released object that carries nothing. Old obligations keep
their witnesses; the obligations of the new acceptance are the broadcast obligations of the
emission, with the same deadline. Scope: the lemma itself has no run-end premise, but its
use in the append laws (`hkey`) is for a run whose events are all at or before `(t, 2)`. -/
theorem partialSynchronyBy_snoc_selfDelivery {delayOf : Obj p → Time}
    (h : Gen.V2.Duty.PartialSynchronyBy E rho delayOf) {i : Nat} {v : V} {t : Time} {o : Obj p}
    (hi : rho.events[i]? = some (.tick v t)) (ho : o ∈ V2.D.Run.emitsAt E rho i)
    (hnc : ∀ o', (fgsa p c).carries o o' → False) :
    Gen.V2.Duty.PartialSynchronyBy E
      ({ rho with events := rho.events ++ [.deliver v o t] }) delayOf where
  broadcast_emitted u hu o' t' he w hw a hta ha had hc hh hr hx := by
    exact service_snoc (h.broadcast_emitted u hu o' t' (emits_snoc_deliver_iff.mp he) w hw
      a hta ha had hc hh hr (excludes_stateBeforeTime_snoc_false hx))
  relay_accepted u hu k o' t' hacc w hw a hta ha had hc hh hr hx := by
    rcases acceptsAt_snoc_cases hacc with ⟨hlt, hacc'⟩ | ⟨rfl, o'', heq, hcall⟩
    · exact service_snoc (h.relay_accepted u hu k o' t' hacc' w hw a hta ha had hc hh hr
        (excludes_stateBeforeTime_snoc_false hx))
    · obtain ⟨rfl, rfl, rfl⟩ := V2.Event.deliver.inj heq
      rcases (fgsaHooks p c).handles_carries _ _ _ hcall with rfl | hcarried
      · exact service_snoc (h.broadcast_emitted v hu o t ⟨i, hi, ho⟩ w hw
          a hta ha had hc hh hr (excludes_stateBeforeTime_snoc_false hx))
      · exact (hnc _ hcarried).elim

/-- [own-row Option 1; DC Generic/Conditions.lean:134] `HealthyPrefixDeliveryBy` survives
the same-time self-delivery of a released object that carries nothing. Scope: as for
`partialSynchronyBy_snoc_selfDelivery`. -/
theorem healthyPrefixDeliveryBy_snoc_selfDelivery {delayOf : Obj p → Time} {cut : Time}
    (h : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho delayOf cut) {i : Nat} {v : V} {t : Time}
    {o : Obj p} (hi : rho.events[i]? = some (.tick v t)) (ho : o ∈ V2.D.Run.emitsAt E rho i)
    (hnc : ∀ o', (fgsa p c).carries o o' → False) :
    Gen.V2.Duty.HealthyPrefixDeliveryBy E
      ({ rho with events := rho.events ++ [.deliver v o t] }) delayOf cut where
  broadcast_emitted u hu o' t' he w hw a hta ha had hc hh hr hx := by
    exact service_snoc (h.broadcast_emitted u hu o' t' (emits_snoc_deliver_iff.mp he) w hw
      a hta ha had hc hh hr (excludes_stateBeforeTime_snoc_false hx))
  relay_accepted u hu k o' t' hacc w hw a hta ha had hc hh hr hx := by
    rcases acceptsAt_snoc_cases hacc with ⟨hlt, hacc'⟩ | ⟨rfl, o'', heq, hcall⟩
    · exact service_snoc (h.relay_accepted u hu k o' t' hacc' w hw a hta ha had hc hh hr
        (excludes_stateBeforeTime_snoc_false hx))
    · obtain ⟨rfl, rfl, rfl⟩ := V2.Event.deliver.inj heq
      rcases (fgsaHooks p c).handles_carries _ _ _ hcall with rfl | hcarried
      · exact service_snoc (h.broadcast_emitted v hu o t ⟨i, hi, ho⟩ w hw
          a hta ha had hc hh hr (excludes_stateBeforeTime_snoc_false hx))
      · exact (hnc _ hcarried).elim

/-! ### The cut for FG-SA: scope and delivery regimes, and the spec-like run -/

/-- [own-row Option 1; DC NamedRootCollisionFree] The named scope of the cut run is in the
named scope of the run. -/
theorem namedProposalInRun_cut {n : Nat} {t : Time} {A : NamedProposal p.n}
    (h : NamedProposalInRun p c E ({ rho with events := rho.events.take n, horizon := t }) A) :
    NamedProposalInRun p c E rho A := by
  obtain ⟨B, hB, hAB⟩ := h
  refine ⟨B, ?_, hAB⟩
  rcases hB with ⟨x, o, s, hmem, hpay⟩ | ⟨x, hx, k, hk⟩
  · exact Or.inl ⟨x, o, s, (List.take_sublist n _).subset hmem, hpay⟩
  · refine Or.inr ⟨x, hx, ?_⟩
    by_cases hk' : k ≤ n
    · exact ⟨k, by rw [stateBefore_cut_of_le hk'] at hk; exact hk⟩
    · exact ⟨n, by rw [stateBefore_cut_of_ge (by omega)] at hk; exact hk⟩

/-- [own-row Option 1; DC NamedRootCollisionFree] `NamedRootCollisionFree` survives the cut. -/
theorem namedRootCollisionFree_cut {n : Nat} {t : Time} (h : NamedRootCollisionFree p c E rho) :
    NamedRootCollisionFree p c E ({ rho with events := rho.events.take n, horizon := t }) where
  root_injective B C hB hC :=
    h.root_injective B C (namedProposalInRun_cut hB) (namedProposalInRun_cut hC)

/-- [own-row Option 1; DC Generic/Conditions.lean:110] `PartialSynchronyBy` survives the cut:
a deadline within the cut horizon `t` is within the old horizon, the state at that deadline
is the old one, and the old witness delivery is before `t`, so below the cut. -/
theorem partialSynchronyBy_cut {n : Nat} {t : Time} {delayOf : Obj p → Time}
    (hcut : ∀ k e, rho.events[k]? = some e → (k < n ↔ e.key ≤ toLex (t, 1)))
    (hth : t ≤ rho.horizon) (h : Gen.V2.Duty.PartialSynchronyBy E rho delayOf) :
    Gen.V2.Duty.PartialSynchronyBy E
      ({ rho with events := rho.events.take n, horizon := t }) delayOf where
  broadcast_emitted u hu o time he w hw a hta ha had hc hh hr hx := by
    obtain ⟨_, he'⟩ := (emits_cut_iff hcut).mp he
    rw [stateBeforeTime_cut hcut hh] at hx
    exact service_cut hcut had hh (h.broadcast_emitted u hu o time he' w hw a hta ha had
      (hc.trans hth) (hh.trans hth) hr hx)
  relay_accepted u hu k o time hacc w hw a hta ha had hc hh hr hx := by
    obtain ⟨_, hacc'⟩ := acceptsAt_cut hacc
    rw [stateBeforeTime_cut hcut hh] at hx
    exact service_cut hcut had hh (h.relay_accepted u hu k o time hacc' w hw a hta ha had
      (hc.trans hth) (hh.trans hth) hr hx)

/-- [own-row Option 1; DC Generic/Conditions.lean:134] `HealthyPrefixDeliveryBy` survives
the cut when the prefix cut is at most `t`. -/
theorem healthyPrefixDeliveryBy_cut {n : Nat} {t : Time} {delayOf : Obj p → Time} {b₀ : Time}
    (hcut : ∀ k e, rho.events[k]? = some e → (k < n ↔ e.key ≤ toLex (t, 1)))
    (_hb : b₀ ≤ t) (hth : t ≤ rho.horizon)
    (h : Gen.V2.Duty.HealthyPrefixDeliveryBy E rho delayOf b₀) :
    Gen.V2.Duty.HealthyPrefixDeliveryBy E
      ({ rho with events := rho.events.take n, horizon := t }) delayOf b₀ where
  broadcast_emitted u hu o time he w hw a hta ha had hc hh hr hx := by
    obtain ⟨_, he'⟩ := (emits_cut_iff hcut).mp he
    rw [stateBeforeTime_cut hcut hh] at hx
    exact service_cut hcut had hh (h.broadcast_emitted u hu o time he' w hw a hta ha had
      hc (hh.trans hth) hr hx)
  relay_accepted u hu k o time hacc w hw a hta ha had hc hh hr hx := by
    obtain ⟨_, hacc'⟩ := acceptsAt_cut hacc
    rw [stateBeforeTime_cut hcut hh] at hx
    exact service_cut hcut had hh (h.relay_accepted u hu k o time hacc' w hw a hta ha had
      hc (hh.trans hth) hr hx)

/-- [own-row Option 1; DC N3] The spec-like run of an arbitrary valid run: cut after the
ticks at the action time `t` (horizon `t`), then the same-time self-delivery of the row
that the tick of `v` at `t` released. It is `ExecutionValid`. `exists_cut` supplies `n`. -/
theorem executionValid_ownRow_run (hvalid : V2.D.ExecutionValid E rho) {n i : Nat} {v : V}
    {t : Time} (hcut : ∀ k e, rho.events[k]? = some e → (k < n ↔ e.key ≤ toLex (t, 1)))
    (hi : rho.events[i]? = some (.tick v t)) {j : Fin p.n} {body : RowPayload}
    (ho : ofRow p ⟨.seat .fg j, body⟩ ∈ V2.D.Run.emitsAt E rho i) :
    V2.D.ExecutionValid E
      ({ rho with events := rho.events.take n ++ [.deliver v (ofRow p ⟨.seat .fg j, body⟩) t],
                  horizon := t }) := by
  obtain ⟨ht0, hth⟩ := hvalid.in_horizon _ (List.mem_of_getElem? hi)
  have hin : i < n := (hcut i _ hi).mpr (tick_key_le.mpr le_rfl)
  exact executionValid_snoc_selfDelivery (executionValid_cut hvalid hcut ht0 hth)
    (cut_key_le hcut) (getElem?_cut_iff.mpr ⟨hin, hi⟩)
    (cut_lastEvent hvalid.toScheduleWellFormed hcut hi)
    (by rw [emitsAt_cut_of_lt hin]; exact ho)

/-- [own-row Option 1; DC N4] A released FG row carries nothing. -/
theorem fgsa_row_noCarried (a : RowWire p.n) (o' : Obj p)
    (h : (fgsa p c).carries (ofRow p a) o') : False := h

end AvailableChain.FGSA.Run
end
