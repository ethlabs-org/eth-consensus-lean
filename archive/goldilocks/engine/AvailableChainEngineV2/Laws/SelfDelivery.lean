module
public import AvailableChainEngineV2.Laws.Hooks

@[expose] public section

/-! Self-delivery at the emission time (plan 2a D4, Task 3; Astra A02, DC N3,
N4). A node can get its own object by a normal delivery at the emission time,
after its tick. `selfDelivery_admissible` shows that such a delivery passes
the delivery checks of `ExecutionValid`; `ExecutionValid.snoc_selfDelivery`
appends it to a valid run. Neither claims that the handler accepts the
object. -/

namespace AvailableChain.V2

open AvailableChain

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}

/-- The protocol facts that a self-delivery needs about the object `o` that
the tick of `v` at time `t` releases from the state `st` (Astra A02).

* `wire`: `o` is well-formed.
* `deps`: the post-tick state holds the dependencies of `o`.
* `fresh`: the POST-CLOCK state has not processed `o`. The own-record fold
  keeps this (`HooksSound.recordOwn_processed`); a state before the clock is
  not enough, because `clock` can change `processed`.
* `noCarried`: `o` carries no object. So a delivery of `o` needs no
  provenance for carried signatures. This excludes a self-visible object
  that carries signed objects; in FG-SA, the self-visible objects are the FG
  rows, and a row carries nothing. -/
structure EmitOk (E : Generic.Env V) (rho : Run V P) (st : P.State) (v : V) (t : Time)
    (o : P.Object) : Prop where
  wire : P.wellFormed o = true
  deps : P.depsPresent (tick E rho st v t).1 o = true
  fresh : P.processed (P.clock st t) o = false
  noCarried : ∀ o', P.carries o o' → False

/-- The holder of a signed object that a tick of `v` releases is `v`: the
engine signs only with the seats of `v`. -/
theorem Run.holder_of_mem_tick {E : Generic.Env V} {rho : Run V P} {st : P.State} {v : V}
    {t : Time} {o : P.Object} {u : V} (ho : o ∈ (tick E rho st v t).2)
    (hu : Run.holder rho o.auth = some u) : u = v := by
  simp only [tick] at ho
  split at ho
  · rcases List.mem_append.mp ho with ho | ho
    · obtain ⟨ℓ, -, ho⟩ := List.mem_flatMap.mp ho
      obtain ⟨i, hi, hio⟩ := List.mem_filterMap.mp ho
      obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.mp hio
      simp only [Run.holder, Option.some.injEq] at hu
      simp only [Run.ownSeats, List.mem_filter, decide_eq_true_eq] at hi
      rw [← hu, hi.2]
    · obtain ⟨p, -, rfl⟩ := List.mem_map.mp ho
      simp [Run.holder] at hu
  · simp at ho

/-- An event of another node does not change the state of `v`. -/
theorem World.step_apply_of_node_ne (E : Generic.Env V) (rho : Run V P) (w : World V P)
    {e : Event V P.Object} {v : V} (h : e.node ≠ v) : World.step E rho w e v = w v := by
  cases e with
  | restart u _ => exact Function.update_of_ne (Ne.symm h) _ _
  | tick u _ => exact Function.update_of_ne (Ne.symm h) _ _
  | deliver u _ _ => exact Function.update_of_ne (Ne.symm h) _ _

namespace Run

/-- The state of `v` is the same before indices `a ≤ b` when no event of `v`
has an index in `[a, b)` (DC N4). -/
theorem stateBefore_eq_of_node_ne (E : Generic.Env V) (rho : Run V P) {v : V} {a b : Nat}
    (hab : a ≤ b)
    (h : ∀ k e, a ≤ k → k < b → rho.events[k]? = some e → e.node ≠ v) :
    stateBefore E rho b v = stateBefore E rho a v := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
      rw [← ih fun k e hak hkb => h k e hak (Nat.lt_succ_of_lt hkb)]
      cases he : rho.events[b]? with
      | none => simp [stateBefore, List.take_add_one, he]
      | some e =>
          rw [stateBefore_succ E rho he]
          exact World.step_apply_of_node_ne E rho _ (h b e hab (Nat.lt_succ_self b) he)

end Run

/-- Self-delivery is admissible (Astra A02; DC N4). Let the tick event at
index `i` release `o`, and let `EmitOk` hold for `o` at that tick. At an index
`j` where the state of `v` is still its post-tick state (`hstate`; for
example the delivery of `o` to `v` at time `t`, with no event of `v` between),
the delivery of `o` to `v` passes the wire, dependency and freshness checks of
`DeliveryWellFormed`, and it passes the checks of `UnforgeableSignatures`: an
honest holder of the outer signature is `v`, which emits `o` at `t`, and `o`
carries nothing.

The lemma does not claim that the handler accepts `o`, and it does not claim
that the rest of the run stays valid. It needs no premise that `v` is honest
or that `o` is self-visible: the engine signs only with the seats of `v`, and
an unsigned object has no holder. -/
theorem selfDelivery_admissible {E : Generic.Env V} {rho : Run V P} (hH : HooksSound P)
    {i j : Nat} {v : V} {o : P.Object} {t : Time}
    (hi : rho.events[i]? = some (.tick v t)) (ho : o ∈ Run.emitsAt E rho i)
    (hok : EmitOk E rho (Run.stateBefore E rho i v) v t o)
    (hstate : Run.stateBefore E rho j v = Run.stateBefore E rho (i + 1) v) :
    P.wellFormed o = true ∧ P.depsPresent (Run.stateBefore E rho j v) o = true ∧
      P.processed (Run.stateBefore E rho j v) o = false ∧
      (∀ u ∈ rho.honest, Run.holder rho o.auth = some u →
        ∃ t', t' ≤ t ∧ Run.emits E rho u o t') ∧
      (∀ o', P.carries o o' → ∀ u ∈ rho.honest, Run.holder rho o'.auth = some u →
        ∃ t', t' ≤ t ∧ Run.emits E rho u o' t') := by
  obtain ⟨hpost, hemit⟩ := Run.step_tick_eq E rho hi
  rw [hstate, hpost]
  refine ⟨hok.wire, hok.deps, ?_, fun u _ hu => ?_, fun o' hc => (hok.noCarried o' hc).elim⟩
  · rw [hH.processed_tick]; exact hok.fresh
  · rw [hemit] at ho
    rw [Run.holder_of_mem_tick ho hu]
    exact ⟨t, le_rfl, i, hi, by rw [hemit]; exact ho⟩

/-! ### The append form (DC N3) -/

namespace Run

variable {E : Generic.Env V} {rho : Run V P} {e : Event V P.Object}

omit [DecidableEq V] in
/-- Indices of the old run keep their events after an append. -/
theorem getElem?_snoc_of_lt {k : Nat} (hk : k < rho.events.length) :
    ({ rho with events := rho.events ++ [e] } : Run V P).events[k]? = rho.events[k]? :=
  List.getElem?_append_left hk

/-- The tick does not read the event list, so an append does not change it. -/
theorem tick_snoc :
    tick E ({ rho with events := rho.events ++ [e] } : Run V P) = tick E rho :=
  rfl

/-- Prefixes of the old run keep their state after an append. -/
theorem stateBefore_snoc_of_le {k : Nat} (hk : k ≤ rho.events.length) :
    stateBefore E ({ rho with events := rho.events ++ [e] } : Run V P) k =
      stateBefore E rho k := by
  simp only [stateBefore, List.take_append_of_le_length hk]
  rfl

/-- Old ticks release the same objects after an append. -/
theorem emitsAt_snoc_of_lt {k : Nat} (hk : k < rho.events.length) :
    emitsAt E ({ rho with events := rho.events ++ [e] } : Run V P) k = emitsAt E rho k := by
  simp only [emitsAt, getElem?_snoc_of_lt hk, stateBefore_snoc_of_le (Nat.le_of_lt hk)]
  rfl

/-- An emission of the old run is an emission after an append. -/
theorem emits_snoc {u : V} {o : P.Object} {t : Time} (h : emits E rho u o t) :
    emits E ({ rho with events := rho.events ++ [e] } : Run V P) u o t := by
  obtain ⟨k, hk, ho⟩ := h
  have hlt : k < rho.events.length := (List.getElem?_eq_some_iff.mp hk).1
  exact ⟨k, by rw [getElem?_snoc_of_lt hlt]; exact hk, by
    rw [emitsAt_snoc_of_lt hlt]; exact ho⟩

end Run

/-- `EmitOk` does not read the event list. -/
theorem EmitOk.snoc {E : Generic.Env V} {rho : Run V P} {e : Event V P.Object}
    {st : P.State} {v : V} {t : Time} {o : P.Object} (h : EmitOk E rho st v t o) :
    EmitOk E ({ rho with events := rho.events ++ [e] } : Run V P) st v t o :=
  ⟨h.wire, by rw [Run.tick_snoc]; exact h.deps, h.fresh, h.noCarried⟩

/-- The append form of self-delivery (DC N3; Astra re-check 2, M3). Let `rho`
be `ExecutionValid`, with every event key at most `(t, 2)`. Let the event at
index `i` be the tick of `v` at `t`, with no later event of `v`, and let it
release `o` with `EmitOk`. Then `rho` with the delivery of `o` to `v` at `t`
appended is `ExecutionValid`.

`HooksSound P` gives `recordOwn_processed`, which `ExecutionValid` does not
contain: without it, the own record can set `processed` for `o`, and the
appended delivery then fails freshness. The schedule condition of `rho`
gives `v ∈ rho.honest` and `0 ≤ t ≤ rho.horizon` from the tick. -/
theorem ExecutionValid.snoc_selfDelivery {E : Generic.Env V} {rho : Run V P}
    (hvalid : ExecutionValid E rho) (hH : HooksSound P) {i : Nat} {v : V} {t : Time}
    {o : P.Object} (hkey : ∀ e ∈ rho.events, e.key ≤ toLex (t, 2))
    (hi : rho.events[i]? = some (.tick v t))
    (hlast : ∀ k e, i < k → rho.events[k]? = some e → e.node ≠ v)
    (ho : o ∈ Run.emitsAt E rho i)
    (hok : EmitOk E rho (Run.stateBefore E rho i v) v t o) :
    ExecutionValid E ({ rho with events := rho.events ++ [.deliver v o t] } : Run V P) := by
  set d : Event V P.Object := .deliver v o t with hd
  set rho' : Run V P := { rho with events := rho.events ++ [d] } with hrho'
  have hilen : i < rho.events.length := (List.getElem?_eq_some_iff.mp hi).1
  have hmem : Event.tick v t ∈ rho.events := List.mem_of_getElem? hi
  obtain ⟨ht0, hth⟩ := hvalid.in_horizon _ hmem
  have hv : v ∈ rho.honest := hvalid.honest_only _ hmem
  have hlen : rho'.events.length = rho.events.length + 1 := by simp [hrho']
  -- The new event is the last one.
  have hdn : rho'.events[rho.events.length]? = some d := by simp [hrho']
  -- An index of `rho'` is an old index or the new one.
  have hcases : ∀ k f, rho'.events[k]? = some f →
      (k < rho.events.length ∧ rho.events[k]? = some f) ∨
        (k = rho.events.length ∧ f = d) := by
    intro k f hk
    by_cases hlt : k < rho.events.length
    · exact Or.inl ⟨hlt, by rw [← Run.getElem?_snoc_of_lt hlt]; exact hk⟩
    · have hk' : k < rho'.events.length := (List.getElem?_eq_some_iff.mp hk).1
      have hkn : k = rho.events.length := by omega
      subst hkn
      rw [hdn] at hk
      exact Or.inr ⟨rfl, (Option.some.inj hk).symm⟩
  -- The delivery checks at the new index.
  have hstate : Run.stateBefore E rho' rho.events.length v =
      Run.stateBefore E rho' (i + 1) v := by
    refine Run.stateBefore_eq_of_node_ne E rho' hilen fun k f hik hkn hkf => ?_
    rw [Run.getElem?_snoc_of_lt hkn] at hkf
    exact hlast k f (by omega) hkf
  have hi' : rho'.events[i]? = some (.tick v t) := by
    rw [Run.getElem?_snoc_of_lt hilen]; exact hi
  have ho' : o ∈ Run.emitsAt E rho' i := by rw [Run.emitsAt_snoc_of_lt hilen]; exact ho
  have hok' : EmitOk E rho' (Run.stateBefore E rho' i v) v t o := by
    rw [Run.stateBefore_snoc_of_le (Nat.le_of_lt hilen)]; exact hok.snoc
  obtain ⟨hwire, hdeps, hfresh, hprov, hcarr⟩ := selfDelivery_admissible hH hi' ho' hok' hstate
  refine { toScheduleWellFormed := ?_, toDeliveryWellFormed := ?_,
           toUnforgeableSignatures := ?_, toSleepWellFormed := ?_ }
  · refine ⟨hvalid.horizon_nonneg, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact List.pairwise_append.mpr ⟨hvalid.sorted, List.pairwise_singleton _ _,
        fun a ha b hb => by rw [List.mem_singleton.mp hb]; exact hkey a ha⟩
    · refine List.nodup_append.mpr ⟨hvalid.nodup, List.nodup_singleton _, ?_⟩
      intro a ha b hb hab
      rw [List.mem_singleton.mp hb] at hab
      subst hab
      obtain ⟨k, hk⟩ := List.getElem?_of_mem ha
      rcases lt_trichotomy k i with hki | hki | hki
      · -- An earlier delivery at `(t, 2)` cannot come before the tick at `(t, 1)`.
        obtain ⟨hkl, hkv⟩ := List.getElem?_eq_some_iff.mp hk
        have hs := List.pairwise_iff_getElem.mp hvalid.sorted k i hkl hilen hki
        rw [hkv, (List.getElem?_eq_some_iff.mp hi).2] at hs
        exact absurd hs (by simp [hd, Event.key, Event.time, Event.phase,
          Prod.Lex.toLex_le_toLex])
      · rw [hki, hi] at hk; exact absurd hk (by simp)
      · exact hlast k _ hki hk rfl
    · intro f hf
      rcases List.mem_append.mp hf with hf | hf
      · exact hvalid.in_horizon f hf
      · rw [List.mem_singleton.mp hf]; exact ⟨ht0, hth⟩
    · intro f hf
      rcases List.mem_append.mp hf with hf | hf
      · exact hvalid.honest_only f hf
      · rw [List.mem_singleton.mp hf]; exact hv
    · intro u s hf
      rcases List.mem_append.mp hf with hf | hf
      · exact hvalid.tick_public u s hf
      · exact absurd (List.mem_singleton.mp hf) (by simp [hd])
    · intro u hu s hs h0 hh ha
      exact List.mem_append_left _ (hvalid.tick_total u hu s hs h0 hh ha)
  · refine ⟨?_, ?_, ?_⟩
    · intro k u p s hk
      rcases hcases k _ hk with ⟨-, hk⟩ | ⟨-, hk⟩
      · exact hvalid.wire k u p s hk
      · obtain ⟨-, rfl, -⟩ := Event.deliver.inj hk; exact hwire
    · intro k u p s hk
      rcases hcases k _ hk with ⟨hlt, hk'⟩ | ⟨rfl, hk'⟩
      · rw [Run.stateBefore_snoc_of_le (Nat.le_of_lt hlt)]; exact hvalid.deps k u p s hk'
      · obtain ⟨rfl, rfl, -⟩ := Event.deliver.inj hk'; exact hdeps
    · intro k u p s hk
      rcases hcases k _ hk with ⟨hlt, hk'⟩ | ⟨rfl, hk'⟩
      · rw [Run.stateBefore_snoc_of_le (Nat.le_of_lt hlt)]; exact hvalid.fresh k u p s hk'
      · obtain ⟨rfl, rfl, -⟩ := Event.deliver.inj hk'; exact hfresh
  · refine ⟨?_, ?_⟩
    · rintro u p s ⟨k, hk⟩ w hw hhold
      rcases hcases k _ hk with ⟨-, hk'⟩ | ⟨-, hk'⟩
      · obtain ⟨t', ht', he⟩ := hvalid.unforgeable u p s ⟨k, hk'⟩ w hw hhold
        exact ⟨t', ht', Run.emits_snoc he⟩
      · obtain ⟨-, rfl, rfl⟩ := Event.deliver.inj hk'; exact hprov w hw hhold
    · rintro u p s ⟨k, hk⟩ p' hc w hw hhold
      rcases hcases k _ hk with ⟨-, hk'⟩ | ⟨-, hk'⟩
      · obtain ⟨t', ht', he⟩ := hvalid.carried u p s ⟨k, hk'⟩ p' hc w hw hhold
        exact ⟨t', ht', Run.emits_snoc he⟩
      · obtain ⟨-, rfl, rfl⟩ := Event.deliver.inj hk'; exact hcarr p' hc w hw hhold
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro u s hf
      rcases List.mem_append.mp hf with hf | hf
      · exact hvalid.tick_awake u s hf
      · exact absurd (List.mem_singleton.mp hf) (by simp [hd])
    · intro u p s hf
      rcases List.mem_append.mp hf with hf | hf
      · exact hvalid.deliver_awake u p s hf
      · obtain ⟨rfl, rfl, rfl⟩ := Event.deliver.inj (List.mem_singleton.mp hf)
        exact hvalid.tick_awake _ _ hmem
    · intro u s hf
      rcases List.mem_append.mp hf with hf | hf
      · exact hvalid.restart_awake u s hf
      · exact absurd (List.mem_singleton.mp hf) (by simp [hd])
    · intro u hu s h0 hh hw
      exact List.mem_append_left _ (hvalid.wake_restart u hu s h0 hh hw)

end AvailableChain.V2

end
