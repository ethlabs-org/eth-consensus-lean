module
public import ConsensusLean.Instances.Goldilocks.Results.Spec.NodeCanonicalTrace
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeDeliveryOrigin
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeInventorySchedule
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeStateAgreement
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Relay
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Structural laws of canonical replay -/

namespace Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

open Blocks Shape Node

variable {V : Type} [Fintype V] {E : Env V}
variable {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
variable {F : ChainShapeFamily O I} {p : Params} {hN : p.n = Fintype.card V}
variable {hn : 1 ≤ Fintype.card V}
variable {A : NodeAC (paramsAtCount p (Fintype.card V) hN hn)}
variable (e : Encoding F E p hN hn A) (rho : Model.Run (compiled F) E)

/-- Clamping to the horizon preserves monotonicity of compromise. -/
theorem honestKeysAt_antitone : Antitone (honestKeysAt rho) := by
  intro s t hst y hy
  rw [mem_honestKeysAt_iff] at hy ⊢
  exact fun hf => hy (rho.faultyAt_mono (min_le_min_right _ hst) hf)

/-- The genesis block has the distinguished genesis digest. -/
theorem genesis_root_ok :
    ((paramsAtCount p (Fintype.card V) hN hn).genesisBlock A.genesisPayload).RootOk
      (digestOf e rho) := by
  simp only [Block.RootOk, Params.genesisBlock, digestOf_eq]

variable [DecidableEq V]

/-- The trace starts from the initialized AC state when the adapter starts FG at genesis
with an empty attestation record. -/
theorem init (y : Fin (Fintype.card V))
    (hfg : (initial e rho y).fg = Store.init A.genesisPayload)
    (hrecord : (initial e rho y).record = FG.Record.empty) :
    (simTrace e rho).init y = Node.initWith A (initial e rho y).ac := by
  rw [simTrace_init_eq, ← initial_eq]
  rcases h : initial e rho y with ⟨fg, ac, record⟩
  rw [h] at hfg hrecord
  cases hfg
  cases hrecord
  rfl

/-- Every labelled cut lies in the finite event expansion. -/
theorem finite (T : Time) :
    {k | (simTrace e rho).label k ≠ none ∧ (simTrace e rho).time k ≤ T}.Finite := by
  apply (Set.finite_Iio (allCuts e rho).length).subset
  intro k hk
  have hl := hk.1
  simpa [simTrace_label] using hl

private theorem event_of_cut {k : Nat} {r : CutRec A}
    (hr : (allCuts e rho)[k]? = some r) :
    ∃ i ev, rho.events[i]? = some ev ∧ cutMap e rho i ≤ k ∧
      k < cutMap e rho (i + 1) ∧ (simTrace e rho).time k = ev.time ∧
      (simTrace e rho).node k = rho.ownKey ev.node ∧ r ∈ eventCuts e rho i := by
  rw [allCuts_eq] at hr
  obtain ⟨i, hi, hlo, hhi, hmem⟩ := cut_event_range e rho _ _ _ hr
  have hm := List.mem_of_getElem? hmem
  obtain ⟨ht, hy⟩ := eventCut_node_time e rho (List.getElem?_eq_getElem hi) hm
  rw [simTrace_time, simTrace_node, allCuts_eq, hr]
  exact ⟨i, rho.events[i], List.getElem?_eq_getElem hi, hlo, hhi, ht, hy, hm⟩

open Classical in
/-- An engine event covering the given replay cut, or zero outside the expansion. -/
noncomputable def eventOf (k : Nat) : Nat :=
  if h : ∃ i < rho.events.length, cutMap e rho i ≤ k ∧ k < cutMap e rho (i + 1) then
    h.choose
  else 0

open Classical in
/-- The event chosen by `eventOf` is the witness of a covering interval, if one exists. -/
theorem eventOf_eq (k : Nat) : eventOf e rho k =
    if h : ∃ i < rho.events.length, cutMap e rho i ≤ k ∧ k < cutMap e rho (i + 1) then
      h.choose
    else 0 := by rfl

/-- A labelled cut lies in the interval of its selected engine event. -/
theorem eventOf_spec {k : Nat} (hk : (simTrace e rho).label k ≠ none) :
    eventOf e rho k < rho.events.length ∧ cutMap e rho (eventOf e rho k) ≤ k ∧
      k < cutMap e rho (eventOf e rho k + 1) := by
  cases hr : (allCuts e rho)[k]? with
  | none => simp [simTrace_label, hr] at hk
  | some r =>
    obtain ⟨i, ev, he, hlo, hhi, -⟩ := event_of_cut e rho hr
    have h : ∃ j < rho.events.length, cutMap e rho j ≤ k ∧ k < cutMap e rho (j + 1) :=
      ⟨i, (List.getElem?_eq_some_iff.mp he).1, hlo, hhi⟩
    rw [eventOf_eq, dite_eq_left h]
    exact h.choose_spec

/-- A labelled cut has the time of its selected engine event. -/
theorem eventOf_time {k : Nat} {ev} (hk : (simTrace e rho).label k ≠ none)
    (he : rho.events[eventOf e rho k]? = some ev) : (simTrace e rho).time k = ev.time := by
  obtain ⟨_, hlo, hhi⟩ := eventOf_spec e rho hk
  cases hr : (allCuts e rho)[k]? with
  | none => simp [simTrace_label, hr] at hk
  | some r =>
    obtain ⟨i, f, hf, h₁, h₂, ht, -⟩ := event_of_cut e rho hr
    have hi : i = eventOf e rho k :=
      le_antisymm (cutMap_index_le e rho h₁ hhi le_rfl) (cutMap_index_le e rho hlo h₂ le_rfl)
    rw [hi, he] at hf
    exact ht.trans (congrArg Model.Event.time (Option.some.inj hf)).symm

private theorem call_origin {y : Fin (Fintype.card V)} {k : Nat} {c : Cut A}
    (hc : (simTrace e rho).CallAt y k c) :
    ∃ i ev, rho.events[i]? = some ev ∧ cutMap e rho i ≤ k ∧ k < cutMap e rho (i + 1) ∧
      (simTrace e rho).time k = ev.time ∧ ev.node = rho.key y ∧
      ∃ r ∈ eventCuts e rho i, r.label = c := by
  obtain ⟨hn, hl⟩ := hc
  cases hr : (allCuts e rho)[k]? with
  | none => simp [simTrace_label, hr] at hl
  | some r =>
    obtain ⟨i, ev, he, h1, h2, ht, hy, hm⟩ := event_of_cut e rho hr
    have hkey := congrArg rho.key (hy.symm.trans hn)
    rw [Model.Run.ownKey, Equiv.apply_symm_apply] at hkey
    rw [simTrace_label, hr, Option.map_some, Option.some.injEq] at hl
    exact ⟨i, ev, he, h1, h2, ht, hkey, r, hm, hl⟩

private theorem time_bounds (hv : rho.ExecutionValid) (k : Nat) :
    0 ≤ (simTrace e rho).time k ∧ (simTrace e rho).time k ≤ rho.horizon + 1 := by
  cases hr : (allCuts e rho)[k]? with
  | none =>
    rw [simTrace_time, hr, Option.elim_none]
    exact ⟨by linarith only [hv.horizon_nonneg], le_rfl⟩
  | some r =>
    obtain ⟨_, ev, he, _, _, ht, _, _⟩ := event_of_cut e rho hr
    rw [ht]
    have h := hv.in_horizon ev (List.mem_of_getElem? he)
    exact ⟨h.1, by linarith only [h.2]⟩

/-- Labelled and stuttering cuts both have nonnegative time. -/
theorem time_nonneg (hv : rho.ExecutionValid) (k : Nat) : 0 ≤ (simTrace e rho).time k :=
  (time_bounds e rho hv k).1

/-- A trace observation is in the engine's observation horizon. -/
theorem inHorizon_iff (hv : rho.ExecutionValid) (t : Time) :
    (simTrace e rho).InHorizon t ↔ t ≤ rho.horizon := by
  refine ⟨?_, inHorizon_of_le e rho⟩
  rintro ⟨k, hk | ⟨T, hT, h⟩, htk⟩
  · cases hr : (allCuts e rho)[k]? with
    | none => simp [simTrace_label, hr] at hk
    | some r =>
      obtain ⟨_, ev, he, _, _, ht, -⟩ := event_of_cut e rho hr
      exact (ht ▸ htk).trans (hv.in_horizon ev (List.mem_of_getElem? he)).2
  · rw [simTrace_observationHorizon, Option.some.injEq] at hT
    exact hT ▸ h

/-- The adjacent trace times at a mapped post-event cut bound the event time. -/
theorem readPoint_after_event (hv : rho.ExecutionValid) {i : Nat} {ev}
    (he : rho.events[i]? = some ev) :
    (∀ k < cutMap e rho (i + 1), (simTrace e rho).time k ≤ ev.time) ∧
      ev.time ≤ (simTrace e rho).time (cutMap e rho (i + 1)) := by
  have hi := (List.getElem?_eq_some_iff.mp he).1
  have hlen : (allCuts e rho).length = cutMap e rho rho.events.length := by
    rw [allCuts_eq, prefix_cuts]
  constructor
  · intro k hk
    have hkl := hk.trans_le (hlen ▸ cutMap_mono e rho (Nat.succ_le_of_lt hi))
    obtain ⟨j, f, hf, hj, _, ht, -⟩ := event_of_cut e rho (List.getElem?_eq_getElem hkl)
    have hji : j ≤ i := by
      by_contra! h
      exact (not_lt_of_ge ((cutMap_mono e rho h).trans hj)) hk
    rw [ht]
    rcases hji.lt_or_eq with h | rfl
    · rcases keyLe_of_lt rho hv hf he h with h | ⟨h, _⟩ <;> exact h.le
    · rw [he, Option.some.injEq] at hf
      exact hf ▸ le_rfl
  · cases hr : (allCuts e rho)[cutMap e rho (i + 1)]? with
    | none =>
      rw [simTrace_time, hr, Option.elim_none]
      have h := (hv.in_horizon ev (List.mem_of_getElem? he)).2
      linarith only [h]
    | some r =>
      obtain ⟨j, f, hf, _, hj, ht, -⟩ := event_of_cut e rho hr
      have hij : i < j := by
        by_contra! h
        exact (not_lt_of_ge (cutMap_mono e rho (Nat.succ_le_succ h))) hj
      rw [ht]
      rcases keyLe_of_lt rho hv he hf hij with h | ⟨h, _⟩ <;> exact h.le

/-- At a bounded engine cut, the adjacent trace times bound its time. -/
theorem cutMap_time_bounds (hv : rho.ExecutionValid) {i : Nat} (hi : i ≤ rho.events.length) :
    (∀ k < cutMap e rho i, (simTrace e rho).time k ≤ rho.cutTime i) ∧
      rho.cutTime i ≤ (simTrace e rho).time (cutMap e rho i) := by
  cases i with
  | zero =>
    refine ⟨fun k hk => ?_, time_nonneg e rho hv _⟩
    rw [cutMap_zero] at hk
    omega
  | succ i =>
    obtain ⟨ev, he⟩ : ∃ ev, rho.events[i]? = some ev :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    simpa only [Model.Run.cutTime, he, Option.elim_some] using readPoint_after_event e rho hv he

/-- The replay preserves the time order of engine events. -/
theorem time_mono (hv : rho.ExecutionValid) : Monotone (simTrace e rho).time := by
  intro k l hkl
  cases hl : (allCuts e rho)[l]? with
  | none =>
    rw [simTrace_time e rho l, hl]
    exact (time_bounds e rho hv k).2
  | some r =>
    have hk : k < (allCuts e rho).length := hkl.trans_lt (List.getElem?_eq_some_iff.mp hl).1
    obtain ⟨i, ev, he, hstart, _, ht, _, _⟩ :=
      event_of_cut e rho (List.getElem?_eq_getElem hk)
    obtain ⟨j, ev', he', _, hend, ht', _, _⟩ := event_of_cut e rho hl
    have hij : i ≤ j := by
      by_contra! h
      exact (not_lt_of_ge (cutMap_mono e rho (Nat.succ_le_of_lt h)))
        (hstart.trans_lt (hkl.trans_lt hend))
    rw [ht, ht']
    rcases hij.lt_or_eq with h | rfl
    · rcases keyLe_of_lt rho hv he he' h with h | h
      · exact h.le
      · exact h.1.le
    · cases he.symm.trans he'
      exact le_rfl

/-- A call takes place only while its validator is awake. -/
theorem awake_of_call (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)} {k : Nat}
    (hc : (simTrace e rho).IsCall y k) : (simTrace e rho).awake y ((simTrace e rho).time k) := by
  obtain ⟨c, hc⟩ := hc
  obtain ⟨_, ev, he, _, _, ht, hkey, _⟩ := call_origin e rho hc
  have hm := List.mem_of_getElem? he
  rw [simTrace_awake_iff, ht, ← hkey]
  refine ⟨?_, hv.in_horizon ev hm⟩
  cases ev with
  | tick v t => exact hv.tick_awake v t hm
  | deliver v o t => exact hv.deliver_awake v o t hm
  | restart v t => exact (hv.restart_at_wake v t hm).2.1

/-- A restart contributes one restart cut, at its event's node and time. -/
private theorem restart_at {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.restart v t)) :
    (simTrace e rho).RestartAt (rho.ownKey v) (cutMap e rho i) ∧
      (simTrace e rho).time (cutMap e rho i) = t ∧
      cutMap e rho (i + 1) = cutMap e rho i + 1 := by
  let st := e.adapter.node (stateAt e rho v i)
  have hcs : ∃ ℓ : ACLabel A,
      (exec (runProposer rho hn) (digestOf e rho) (rho.ownKey v) st t .restart).2 =
        [.ac ℓ] ∧ ℓ.call = .restart := by
    refine ⟨_, rfl, rfl⟩
  obtain ⟨ℓ, hcs, hc⟩ := hcs
  have hec : eventCuts e rho i =
      [⟨rho.ownKey v, t, Nat.pair i 0, 0, .ac ℓ,
        cutPost (rho.ownKey v) t st (.ac ℓ)⟩] := by
    rw [eventCuts_restart e rho i v t he, groupRecs_eq]
    simp [st, hcs, cutPosts_cons, cutPosts_nil]
  have hr := allCuts_getElem?_add e rho i 0 (List.getElem?_eq_some_iff.mp he).1
    (by rw [hec, List.length_singleton]; exact Nat.one_pos)
  rw [Nat.add_zero, hec] at hr
  refine ⟨⟨ℓ, ⟨?_, ?_⟩, hc⟩, ?_, ?_⟩
  · rw [simTrace_node, hr]; rfl
  · rw [simTrace_label, hr]; rfl
  · rw [simTrace_time, hr]; rfl
  · rw [cutMap_succ, hec, List.length_singleton]

private theorem exists_wake (f : Time → Bool) {u t : Time} (hu : f u = false) (ht : f t = true)
    (h : u ≤ t) : ∃ w, u < w ∧ w ≤ t ∧ f w = true ∧ f (w - 1) = false := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, t = u + n := ⟨(t - u).toNat, by unfold Time at *; omega⟩
  clear h
  induction n with
  | zero => simp [hu] at ht
  | succ n ih =>
    by_cases hft : f (u + n) = true
    · obtain ⟨w, h1, h2, h3⟩ := ih hft
      exact ⟨w, h1, by push_cast at h2 ⊢; linarith only [h2], h3⟩
    · refine ⟨u + (n + 1 : Nat), by push_cast; linarith only [Int.natCast_nonneg n], le_rfl, ht,
        ?_⟩
      have : u + ((n + 1 : Nat) : Int) - 1 = u + n := by unfold Time at *; omega
      rw [this]
      simpa using hft

/-- An honest node observed awake after a sleep has a restart between the two observations. -/
theorem restart_at_wake (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)} {u v : Time}
    (hy : y ∈ honestKeysAt rho v) (hu : 0 ≤ u) (huv : u < v)
    (hs : ¬ (simTrace e rho).awake y u) (hw : (simTrace e rho).awake y v) :
    ∃ k, (simTrace e rho).RestartAt y k ∧ u < (simTrace e rho).time k ∧
      (simTrace e rho).time k ≤ v := by
  obtain ⟨hwv, -, hvh⟩ := (simTrace_awake_iff e rho y v).mp hw
  have hwu : E.awake (rho.key y) u = false := by
    by_contra h
    exact hs ((simTrace_awake_iff e rho y u).mpr ⟨by simpa using h, hu, huv.le.trans hvh⟩)
  obtain ⟨w, huw, hwv', hw1, hw2⟩ := exists_wake _ hwu hwv huv.le
  rw [mem_honestKeysAt_iff, min_eq_left hvh] at hy
  obtain ⟨i, he⟩ := List.mem_iff_getElem?.mp
    (hv.wake_restart (rho.key y) w (by linarith only [hu, huw]) (hwv'.trans hvh)
      (fun hf => hy (rho.faultyAt_mono hwv' hf)) ⟨hw1, hw2⟩)
  obtain ⟨hr, ht, -⟩ := restart_at e rho he
  rw [Model.Run.ownKey, Equiv.symm_apply_apply] at hr
  exact ⟨_, hr, ht ▸ huw, ht ▸ hwv'⟩

private theorem index_eq (hv : rho.ExecutionValid)
    {i j : Nat} {ev : Model.Event V (Model.protoOf (compiled F) E).Object}
    (hi : rho.events[i]? = some ev) (hj : rho.events[j]? = some ev) : i = j := by
  obtain ⟨_, hi'⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨_, hj'⟩ := List.getElem?_eq_some_iff.mp hj
  exact hv.nodup.getElem_inj_iff.mp (hi'.trans hj'.symm)

/-- The first cut of a replay group identifies its enclosing engine event and phase. -/
theorem group_origin {y : Fin (Fintype.card V)} {j : Nat} {t : Time} {ev : Node.Event A}
    (hg : (simTrace e rho).GroupAt (runProposer rho hn) (digestOf e rho) y j t ev) :
    ∃ i ev', rho.events[i]? = some ev' ∧ cutMap e rho i ≤ j ∧ j < cutMap e rho (i + 1) ∧
      ev'.node = rho.key y ∧ ev'.time = t ∧ ev.phase = ev'.phase ∧
      ∃ r, (eventCuts e rho i)[j - cutMap e rho i]? = some r ∧ r.pos = 0 := by
  obtain ⟨hne, hg, -⟩ := hg
  obtain ⟨hy, ht, _, hpos, hl⟩ := hg 0 (List.length_pos_of_ne_nil hne)
  rw [Nat.add_zero] at hy ht hpos hl
  cases hr : (allCuts e rho)[j]? with
  | none => simp [simTrace_label, hr] at hl
  | some r =>
    have hr' := hr
    rw [allCuts_eq] at hr'
    obtain ⟨i, hi, h1, h2, hidx⟩ := cut_event_range e rho _ _ _ hr'
    have he := List.getElem?_eq_getElem hi
    have hm := List.mem_of_getElem? hidx
    obtain ⟨ht', hy'⟩ := eventCut_node_time e rho he hm
    rw [simTrace_pos, hr, Option.elim_some] at hpos
    rw [simTrace_label, hr, Option.map_some, Option.some.injEq] at hl
    rw [simTrace_node, hr, Option.elim_some, hy'] at hy
    rw [simTrace_time, hr, Option.elim_some, ht'] at ht
    have hk := congrArg rho.key hy
    rw [Model.Run.ownKey, Equiv.apply_symm_apply] at hk
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
    rw [List.getElem_of_eq hcs] at hl
    change r.label = c at hl
    subst c
    have hp := phase_of_pos_zero e rho he hm hpos hcs
    exact ⟨i, rho.events[i], he, h1, h2, hk, ht, hp, r, hidx, hpos⟩

private theorem delivery_group_source {y : Fin (Fintype.card V)} {j : Nat} {t : Time}
    {ev : Node.Event A} (hg : (simTrace e rho).GroupAt (runProposer rho hn) (digestOf e rho)
      y j t ev) (hp : ev.phase = 2) :
    ∃ (i : Nat) (v : V), ∃ o u w, rho.events[i]? = some (.deliver v o u) ∧
      engineObj e w ∈ o.parts ∧
      canonEvent (receiverCodec e rho v) (Model.digests rho.hash o) w = some ev := by
  obtain ⟨i, source, he, hstart, _, _, _, hphase, r, hr, _⟩ := group_origin e rho hg
  have hrec := allCuts_getElem?_add e rho i (j - cutMap e rho i)
    (List.getElem?_eq_some_iff.mp he).1 (List.getElem?_eq_some_iff.mp hr).1
  rw [Nat.add_sub_cancel' hstart, hr] at hrec
  obtain ⟨hne, hcuts, _⟩ := hg
  obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil hne
  have hl := (hcuts 0 (List.length_pos_of_ne_nil hne)).2.2.2.2
  rw [Nat.add_zero, simTrace_label, hrec, Option.map_some, Option.some.injEq,
    List.getElem_of_eq hcs] at hl
  change r.label = c at hl
  subst c
  cases source with
  | tick v u => simp [Model.Event.phase, hp] at hphase
  | restart v u => simp [Model.Event.phase, hp] at hphase
  | deliver v o u =>
    obtain ⟨w, ev', st, hw, hcanon, hc⟩ := delivery_origin e rho he (List.mem_of_getElem? hr)
    refine ⟨i, v, o, u, w, he, hw, ?_⟩
    suffices ev' = ev by rwa [this] at hcanon
    cases ev with
    | tick x => simp [Node.Event.phase] at hp
    | restart => simp [Node.Event.phase] at hp
    | block b =>
      obtain ⟨acc, hl⟩ := Simulation.exec_block_head _ _ _ _ _ b hcs
      rw [hl] at hc
      cases ev' with
      | tick x => unfold canonEvent at hcanon; split at hcanon <;> cases hcanon
      | restart => simp [exec, Node.restart, acCall] at hc
      | message m => simp [exec, onMessage, acCall] at hc
      | attestation a => simp [exec, onAttestation] at hc
      | block b' =>
        simp only [exec, onBlock] at hc
        split at hc
        · cases hc
        · split at hc <;> simp [acCall] at hc <;> simp [hc.1]
    | attestation a =>
      have hl : r.label = .fg (.attestation a) := by
        simpa only [exec, onAttestation, List.cons.injEq] using (List.cons.inj hcs).1.symm
      rw [hl] at hc
      cases ev' with
      | tick x => unfold canonEvent at hcanon; split at hcanon <;> cases hcanon
      | restart => simp [exec, Node.restart, acCall] at hc
      | message m => simp [exec, onMessage, acCall] at hc
      | block b =>
        simp only [exec, onBlock] at hc
        split at hc
        · cases hc
        · split at hc <;> simp [acCall] at hc
      | attestation a' =>
        simp only [exec, onAttestation, List.mem_singleton, Cut.fg.injEq,
          FGLabel.attestation.injEq] at hc
        rw [hc]
    | message m =>
      have hl : ∃ l : ACLabel A, r.label = .ac l ∧ l.call = .message m := by
        simp only [exec, onMessage, acCall, List.cons.injEq] at hcs
        exact ⟨_, hcs.1.symm, rfl⟩
      obtain ⟨l, hl, hm⟩ := hl
      rw [hl] at hc
      cases ev' with
      | tick x => unfold canonEvent at hcanon; split at hcanon <;> cases hcanon
      | restart => simp [exec, Node.restart, acCall] at hc; subst l; cases hm
      | attestation a => simp [exec, onAttestation] at hc
      | message m' =>
        simp [exec, onMessage, acCall] at hc
        subst l
        cases hm
        rfl
      | block b =>
        simp only [exec, onBlock] at hc
        split at hc
        · cases hc
        · split at hc <;> simp [acCall] at hc
          subst l
          cases hm

omit [DecidableEq V] in
private theorem decoded_block {o : (Model.protoOf (compiled F) E).Object}
    {w : ShapeObj (Fintype.card V) e.skel.Kind I e.Body} {b : A.Blk}
    (hw : engineObj e w ∈ o.parts)
    (hd : decodeBlock e.codec.decode e.codec.carried A.validPayload
      (Model.digests rho.hash o) w = some b) :
    ∃ h cs, w = .mk (.signed b.proposer (.proposer b.slot)) (.item h) cs ∧
      b = blockOf (rho.hash h) h b.proposer b.fgPayload b.acPayload ∧
      e.codec.decode h.info = some (b.fgPayload, b.acPayload) ∧
      (∀ a ∈ b.fgPayload, a.WellFormed) ∧ A.validPayload b := by
  unfold decodeBlock at hd
  split at hd
  · rename_i k s h cs
    split at hd
    · rename_i atts payload d hc hr
      simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hd
      obtain ⟨⟨hs, _, hf, ha⟩, rfl⟩ := hd
      have hh : h ∈ o.parts.filterMap Model.Obj.item? :=
        List.mem_filterMap.mpr ⟨_, hw, (engineObj_item e _).trans rfl⟩
      have hh' : rootOf (Model.digests rho.hash o) h = some (rho.hash h) :=
        Simulation.find?_map_pair rho.hash h _ hh
      rw [hh', Option.some.injEq] at hr
      subst d s
      exact ⟨h, cs, rfl, rfl, hc, hf, ha⟩
    · cases hd
  · cases hd

private theorem block_source {y : Fin (Fintype.card V)} {j : Nat} {t : Time} {b : A.Blk}
    (hg : (simTrace e rho).GroupAt (runProposer rho hn) (digestOf e rho) y j t (.block b)) :
    ∃ (i : Nat) (v : V), ∃ o u w, rho.events[i]? = some (.deliver v o u) ∧
      engineObj e w ∈ o.parts ∧
      decodeBlock e.codec.decode e.codec.carried A.validPayload
        (Model.digests rho.hash o) w = some b := by
  obtain ⟨i, v, o, u, w, he, hw, hc⟩ := delivery_group_source e rho hg rfl
  refine ⟨i, v, o, u, w, he, hw, ?_⟩
  rw [receiverCodec_eq] at hc
  unfold canonEvent at hc
  split at hc <;> cases hc
  assumption

/-- Wire checks on every replayed group follow from the codec's decoding guarantees. -/
theorem wire
    (hcodec : ∀ {h atts payload}, e.codec.decode h = some (atts, payload) →
      e.codec.encode atts payload = h)
    (hmsg : ∀ {io w m}, e.decodeMessage io w = some m → A.validMsg m)
    (hatt : ∀ {w a}, e.codec.attestation w = some a → a.WellFormed)
    {y : Fin (Fintype.card V)} {j : Nat} {t : Time} {ev : Node.Event A}
    (hg : (simTrace e rho).GroupAt (runProposer rho hn) (digestOf e rho) y j t ev) :
    WireOK (digestOf e rho) ev := by
  cases ev with
  | tick x => trivial
  | restart => trivial
  | message m =>
    obtain ⟨_, v, _, _, w, _, _, hc⟩ := delivery_group_source e rho hg rfl
    apply hmsg (io := voteIOAt e rho v) (w := w)
    rw [receiverCodec_eq] at hc
    unfold canonEvent at hc
    split at hc <;> cases hc
    assumption
  | attestation a =>
    obtain ⟨_, _, _, _, w, _, _, hc⟩ := delivery_group_source e rho hg rfl
    apply hatt (w := w)
    rw [receiverCodec_eq] at hc
    unfold canonEvent at hc
    split at hc <;> cases hc
    assumption
  | block b =>
    obtain ⟨_, _, o, _, w, _, hw, hd⟩ := block_source e rho hg
    obtain ⟨h, cs, _, hb, hc, hf, ha⟩ := decoded_block e rho hw hd
    refine ⟨?_, hf, ha⟩
    unfold Block.RootOk
    rw [digestOf_eq, hcodec hc]
    rw [congrArg Block.root hb, congrArg Block.parent hb, congrArg Block.slot hb,
      congrArg Block.input hb]
    obtain ⟨par, pos, input, info⟩ := h
    have hpar (g : Nat) : parentRef g (parentRoot g par) = par := by
      cases par with
      | root => simp [parentRoot, parentRef]
      | digest d =>
        simp only [parentRoot, parentRef]
        have hn : taggedRoot g d ≠ g := by unfold taggedRoot; split_ifs <;> omega
        rw [ite_eq_right hn]
        congr
        unfold rawRoot taggedRoot
        split_ifs <;> omega
    simp only [blockOf]
    generalize (paramsAtCount p (Fintype.card V) hN hn).genesisRoot = g at *
    cases hparent : parentRoot g par with
    | none => cases par <;> simp [parentRoot] at hparent
    | some r =>
      have he := hpar g
      rw [hparent] at he
      change taggedRoot g (rho.hash ⟨par, pos, input, info⟩) =
        taggedRoot g (rho.hash ⟨parentRef g (some r), pos, input, info⟩)
      rw [he]

omit [DecidableEq V] in
private theorem cast_signed_proposer {s q : ChainShape (Model.pubOf E) O.Id I}
    (h : s = q) (k : Fin (Fintype.card V)) (slot : Nat) (header : Header I)
    (cs : List (compile q).Object) :
    (cast (congrArg (fun x => (compile x).Object) h.symm)
      (.mk (.signed k (.proposer slot)) (.item header) cs) : (compile s).Object).auth =
      .signed k (.proposer slot) := by
  cases h
  rfl

omit [DecidableEq V] in
private theorem cast_item_ne_data {s q : ChainShape (Model.pubOf E) O.Id I}
    (h : s = q) (k : Fin (Fintype.card V)) (slot : Nat) (header : Header I)
    (cs : List (compile q).Object) (x : (compile s).Body) :
    (cast (congrArg (fun x => (compile x).Object) h.symm)
      (.mk (.signed k (.proposer slot)) (.item header) cs) : (compile s).Object).msg ≠
      .data x := by
  cases h
  intro hm
  cases hm

/-- Every replayed block group carries the credential of the selected proposer. -/
theorem proposerCredential (hv : rho.ExecutionValid)
    (hsel : ∀ s : Nat, rho.sel (.proposer s) = {runProposer rho hn s})
    {y : Fin (Fintype.card V)} {j : Nat} {t : Time} {b : A.Blk}
    (hg : (simTrace e rho).GroupAt (runProposer rho hn) (digestOf e rho) y j t (.block b)) :
    b.proposer = runProposer rho hn b.slot := by
  obtain ⟨i, v, o, u, w, he, hw, hd⟩ := block_source e rho hg
  obtain ⟨header, cs, rfl, _, _, _, _⟩ := decoded_block e rho hw hd
  have ha := hv.credentials.2 i v o u he _ hw b.proposer (.proposer b.slot) (by
    rw [engineObj_eq]
    exact cast_signed_proposer e.shape_eq _ _ _ _) (fun x hb => by
    rw [engineObj_eq] at hb
    exact absurd hb (cast_item_ne_data e.shape_eq _ _ _ _ x))
  rw [hsel] at ha
  exact Finset.mem_singleton.mp ha

/-- At a fixed time, replay groups preserve the engine's phase order. -/
theorem phase_order (hv : rho.ExecutionValid) {y y' : Fin (Fintype.card V)} {j j' : Nat}
    {t : Time} {ev ev' : Node.Event A}
    (hg : (simTrace e rho).GroupAt (runProposer rho hn) (digestOf e rho) y j t ev)
    (hg' : (simTrace e rho).GroupAt (runProposer rho hn) (digestOf e rho) y' j' t ev')
    (hj : j < j') : ev.phase ≤ ev'.phase := by
  obtain ⟨i, ei, hi, h1, _, _, ht, hp, _⟩ := group_origin e rho hg
  obtain ⟨i', ei', hi', _, h2, _, ht', hp', _⟩ := group_origin e rho hg'
  have hle : i ≤ i' := by
    by_contra! h
    have : cutMap e rho (i' + 1) ≤ cutMap e rho i := cutMap_mono e rho (Nat.succ_le_of_lt h)
    omega
  rw [hp, hp']
  rcases hle.lt_or_eq with h | rfl
  · rcases keyLe_of_lt rho hv hi hi' h with h | h
    · rw [ht, ht'] at h
      exact (lt_irrefl _ h).elim
    · exact h.2
  · cases hi.symm.trans hi'
    exact le_rfl

private theorem tick_origin {y : Fin (Fintype.card V)} {j : Nat} {t : Time}
    (hg : (simTrace e rho).TickAt (runProposer rho hn) (digestOf e rho) y j t) :
    ∃ i, rho.events[i]? = some (.tick (rho.key y) t) ∧ j = cutMap e rho i ∧
      (paramsAtCount p (Fintype.card V) hN hn).IsPublic t := by
  obtain ⟨x, hg⟩ := hg
  obtain ⟨i, ev, he, h1, _, hy, ht, hp, r, hr, hpos⟩ := group_origin e rho hg
  cases ev with
  | restart => simp [Node.Event.phase, Model.Event.phase] at hp
  | deliver => simp [Node.Event.phase, Model.Event.phase] at hp
  | tick v s =>
    change v = rho.key y at hy
    change s = t at ht
    subst v s
    rw [eventCuts_tick e rho i _ t he] at hr
    split at hr
    · rename_i hpublic
      obtain ⟨hm, hrec⟩ := List.getElem?_eq_some_iff.mp hr
      have hidx := congrArg CutRec.pos hrec
      rw [List.getElem_of_eq (groupRecs_eq _ _ _ _ _ _ _), List.getElem_mapIdx] at hidx
      change j - cutMap e rho i = r.pos at hidx
      exact ⟨i, he, by omega, hpublic⟩
    · simp at hr

/-- A tick group starts only at a public time. -/
theorem tick_public {y : Fin (Fintype.card V)} {j : Nat} {t : Time}
    (hg : (simTrace e rho).TickAt (runProposer rho hn) (digestOf e rho) y j t) :
    (paramsAtCount p (Fintype.card V) hN hn).IsPublic t :=
  (tick_origin e rho hg).choose_spec.2.2

/-- A valid run has at most one tick group per node and time. -/
theorem tick_unique (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)} {j j' : Nat} {t : Time}
    (hg : (simTrace e rho).TickAt (runProposer rho hn) (digestOf e rho) y j t)
    (hg' : (simTrace e rho).TickAt (runProposer rho hn) (digestOf e rho) y j' t) : j = j' := by
  obtain ⟨i, he, rfl, _⟩ := tick_origin e rho hg
  obtain ⟨i', he', rfl, _⟩ := tick_origin e rho hg'
  rw [index_eq rho hv he he']

private theorem restart_origin {y : Fin (Fintype.card V)} {k : Nat}
    (hr : (simTrace e rho).RestartAt y k) :
    ∃ i t, rho.events[i]? = some (.restart (rho.key y) t) ∧ k = cutMap e rho i ∧
      (simTrace e rho).time k = t := by
  obtain ⟨l, hc, hl⟩ := hr
  obtain ⟨i, ev, he, h1, h2, ht, hy, r, hm, hlab⟩ := call_origin e rho hc
  obtain ⟨v, t, rfl⟩ := restart_of_mem_eventCuts e rho he hm hlab hl
  change v = rho.key y at hy
  subst v
  have hs := (restart_at e rho he).2.2
  exact ⟨i, t, he, by omega, ht⟩

private theorem earlier_call_before_restart (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} {j i : Nat} {t : Time} {c : Cut A}
    (hc : (simTrace e rho).CallAt y j c) (hj : j < cutMap e rho i)
    (he : rho.events[i]? = some (.restart (rho.key y) t)) :
    (simTrace e rho).time j < t := by
  obtain ⟨k, ev, hk, hlo, _, ht, hy, _⟩ := call_origin e rho hc
  have hki : k < i := by
    by_contra! h
    have := cutMap_mono e rho h
    omega
  rw [ht]
  rcases keyLe_of_lt rho hv hk he hki with h | ⟨hs, hp⟩
  · exact h
  · cases ev with
    | tick => simp [Model.Event.phase] at hp
    | deliver => simp [Model.Event.phase] at hp
    | restart v s =>
      change v = rho.key y at hy
      change s = t at hs
      subst v s
      exact (hki.ne (index_eq rho hv hk he)).elim

/-- The first call after a sleep is the restart at the intervening wake. -/
theorem restart_of_sleep (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)} {i : Nat} {u : Time}
    (hy : y ∈ honestKeysAt rho ((simTrace e rho).time i))
    (hc : (simTrace e rho).IsCall y i) (hu : 0 ≤ u) (hui : u < (simTrace e rho).time i)
    (hs : ¬ (simTrace e rho).awake y u)
    (hprev : ∀ j < i, (simTrace e rho).IsCall y j → (simTrace e rho).time j < u) :
    (simTrace e rho).RestartAt y i := by
  obtain ⟨k, hr, huk, hki⟩ := restart_at_wake e rho hv hy hu hui hs
    (awake_of_call e rho hv hc)
  obtain ⟨ix, t, he, rfl, ht⟩ := restart_origin e rho hr
  have hik : i ≤ cutMap e rho ix := by
    by_contra! h
    obtain ⟨l, hl, _⟩ := hr
    exact (not_lt_of_ge huk.le) (hprev _ h ⟨.ac l, hl⟩)
  have hEq : i = cutMap e rho ix := by
    obtain ⟨c, hcall⟩ := hc
    by_contra h
    have hlt := earlier_call_before_restart e rho hv hcall (lt_of_le_of_ne hik h) he
    exact (not_lt_of_ge (ht ▸ hki)) hlt
  rwa [hEq]

/-- An observed restart has a preceding sleep later than every previous call of its node. -/
theorem sleep_of_restart (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)} {i : Nat}
    (hr : (simTrace e rho).RestartAt y i) :
    ∃ u : Time, 0 ≤ u ∧ u < (simTrace e rho).time i ∧ ¬ (simTrace e rho).awake y u ∧
      ∀ j < i, (simTrace e rho).IsCall y j → (simTrace e rho).time j < u := by
  obtain ⟨ix, t, he, rfl, ht⟩ := restart_origin e rho hr
  obtain ⟨ht0, _, hs⟩ := hv.restart_at_wake _ _ (List.mem_of_getElem? he)
  refine ⟨t - 1, Int.le_sub_one_of_lt ht0, ht ▸ sub_one_lt t, ?_, ?_⟩
  · intro h
    have hw := ((simTrace_awake_iff e rho y _).mp h).1
    rw [hs] at hw
    cases hw
  · rintro j hj ⟨c, hc⟩
    have hlt := earlier_call_before_restart e rho hv hc hj he
    have hw := ((simTrace_awake_iff e rho y _).mp (awake_of_call e rho hv ⟨c, hc⟩)).1
    have hne : (simTrace e rho).time j ≠ t - 1 := by
      intro heq
      rw [heq, hs] at hw
      cases hw
    unfold Time at *
    omega

private theorem length_posts {Q : Params} {N : NodeAC Q} (y : Fin Q.n) (t : Time)
    (cs : List (Cut N)) (st : NodeState N) : (cutPosts y t cs st).length = cs.length := by
  induction cs generalizing st with
  | nil => rw [cutPosts_nil]; rfl
  | cons c cs ih => simp only [cutPosts_cons, List.length_cons, ih]

private theorem range_of_id {i s k : Nat} (hi : i < rho.events.length)
    (hk : (simTrace e rho).event k = Nat.pair i s) :
    cutMap e rho i ≤ k ∧ k < cutMap e rho (i + 1) := by
  cases hr : (allCuts e rho)[k]? with
  | none =>
    rw [simTrace_event, hr, Option.elim_none, Nat.pair_eq_pair] at hk
    omega
  | some r =>
    obtain ⟨j, ev, he, h1, h2, _, _, hm⟩ := event_of_cut e rho hr
    obtain ⟨s', hs⟩ := eventCut_id e rho he hm
    rw [simTrace_event, hr, Option.elim_some, hs, Nat.pair_eq_pair] at hk
    exact hk.1 ▸ ⟨h1, h2⟩

omit [DecidableEq V] in
private theorem length_group {y : Fin (Fintype.card V)} {t : Time} {id : Nat}
    {st : NodeState A} {ev : Node.Event A} :
    (groupRecs (runProposer rho hn) (digestOf e rho) y st t id ev).length =
      (exec (runProposer rho hn) (digestOf e rho) y st t ev).2.length := by
  rw [groupRecs_eq]
  simp only [List.length_mapIdx, List.length_zip, length_posts, min_self]

/-- An encoded group of records with a unique event id is a replay group. -/
theorem groupAt_of_recs (pr : Nat → Fin (Fintype.card V))
    (dg : Digest (List (FG.Att (Fintype.card V))) A.Payload)
    {y : Fin (Fintype.card V)} {j id : Nat} {t : Time}
    {ev : Node.Event A} {st : NodeState A} (hstate : (simTrace e rho).state y j = st)
    (hne : (exec pr dg y st t ev).2 ≠ [])
    (hrec : ∀ k < (groupRecs pr dg y st t id ev).length,
      (allCuts e rho)[j + k]? = (groupRecs pr dg y st t id ev)[k]?)
    (huniq : ∀ k, (simTrace e rho).event k = id → j ≤ k ∧
      k < j + (groupRecs pr dg y st t id ev).length) :
    (simTrace e rho).GroupAt pr dg y j t ev := by
  subst st
  set st := (simTrace e rho).state y j
  set cs := (exec pr dg y st t ev).2
  have hlen : (groupRecs pr dg y st t id ev).length = cs.length := by
    rw [groupRecs_eq, List.length_mapIdx, List.length_zip, length_posts, min_self]
  have hrec' : ∀ k (hk : k < cs.length),
      (allCuts e rho)[j + k]? = some ⟨y, t, id, k, cs[k],
        (cutPosts y t cs st)[k]'(by rwa [length_posts])⟩ := by
    intro k hk
    rw [hrec k (hlen ▸ hk), groupRecs_eq]
    rw [List.getElem?_eq_getElem (by simpa only [List.length_mapIdx, List.length_zip,
      length_posts, min_self] using hk),
      List.getElem_mapIdx, List.getElem_zip]
  have hid : (simTrace e rho).event j = id := by
    have h := hrec' 0 (List.length_pos_of_ne_nil hne)
    rw [Nat.add_zero] at h
    rw [simTrace_event, h]; rfl
  refine ⟨hne, ?_, ?_⟩
  · intro k hk
    have h := hrec' k hk
    rw [simTrace_node, simTrace_time, simTrace_event, simTrace_pos, simTrace_label, h, hid]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intro k hk
    rw [← hlen]
    exact huniq k (hk.trans hid)

/-- A group's recorded state after its first `k` cuts is the corresponding handler fold. -/
theorem state_in_group (pr : Nat → Fin (Fintype.card V))
    (dg : Digest (List (FG.Att (Fintype.card V))) A.Payload)
    {y : Fin (Fintype.card V)} {j id : Nat} {t : Time} {ev : Node.Event A} {st : NodeState A}
    (hcut : ∀ k < (groupRecs pr dg y st t id ev).length,
      (allCuts e rho)[j + k]? = (groupRecs pr dg y st t id ev)[k]?)
    (hstate : (simTrace e rho).state y j = st) :
    ∀ k ≤ (exec pr dg y st t ev).2.length,
      (simTrace e rho).state y (j + k) =
        ((exec pr dg y st t ev).2.take k).foldl (cutPost y t) st := by
  intro k
  induction k with
  | zero => intro _; simpa using hstate
  | succ k ih =>
    intro hk
    have hk' : k < (groupRecs pr dg y st t id ev).length := by
      rw [groupRecs_eq, List.length_mapIdx, List.length_zip, length_posts, min_self]
      omega
    have hr := hcut k hk'
    rw [List.getElem?_eq_getElem hk', List.getElem_of_eq (groupRecs_eq ..),
      List.getElem_mapIdx, List.getElem_zip] at hr
    change (simTrace e rho).state y (j + k).succ = _
    rw [Trace.state.eq_2, ite_eq_left, simTrace_post, hr, Option.elim_some,
      Node.cutPosts_getElem]
    rw [simTrace_node, simTrace_label, hr]
    simp

/-- Replaying a whole handler group reaches the handler's result state. -/
private theorem state_after_group {y : Fin (Fintype.card V)} {j id : Nat} {t : Time}
    {ev : Node.Event A} {st : NodeState A}
    (hcut : ∀ k < (groupRecs (runProposer rho hn) (digestOf e rho) y st t id ev).length,
      (allCuts e rho)[j + k]? = (groupRecs (runProposer rho hn) (digestOf e rho) y st t id ev)[k]?)
    (hstate : (simTrace e rho).state y j = st) :
    (simTrace e rho).state y
      (j + (groupRecs (runProposer rho hn) (digestOf e rho) y st t id ev).length) =
      (exec (runProposer rho hn) (digestOf e rho) y st t ev).1 := by
  rw [length_group e rho, state_in_group e rho _ _ hcut hstate _ le_rfl,
    List.take_length, foldl_cutPost_exec]

private theorem indexed_delivery_group {y : Fin (Fintype.card V)} {t : Time} {i : Nat}
    (C : WireCodec A e.skel.Kind I e.Body)
    (hs : List (Header I × Nat))
    (os : List (ShapeObj (Fintype.card V) e.skel.Kind I e.Body)) :
    ∀ (j sub : Nat) (st : NodeState A),
    (∀ k < (deliverRecs C (runProposer rho hn) (digestOf e rho)
        hs y t i os st sub).length,
      (allCuts e rho)[j + k]? = (deliverRecs C (runProposer rho hn) (digestOf e rho)
        hs y t i os st sub)[k]?) →
    (simTrace e rho).state y j = st →
    ∀ k < (deliverRecs C (runProposer rho hn) (digestOf e rho)
        hs y t i os st sub).length,
      ∃ pre w post ev j' s, os = pre ++ w :: post ∧ canonEvent C hs w = some ev ∧
        let st' := pre.foldl (fun a o => ((canonEvent C hs o).map
          (fun ev => (exec (runProposer rho hn) (digestOf e rho) y a t ev).1)).getD a) st
        let grp := groupRecs (runProposer rho hn) (digestOf e rho) y st' t (Nat.pair i s) ev
        (∀ m < grp.length, (allCuts e rho)[j' + m]? = grp[m]?) ∧
        (simTrace e rho).state y j' = st' ∧ j' ≤ j + k ∧ j + k < j' + grp.length ∧
        ((∀ l s', (simTrace e rho).event l = Nat.pair i s' → sub ≤ s' → j ≤ l ∧
          l < j + (deliverRecs C (runProposer rho hn) (digestOf e rho)
            hs y t i os st sub).length) →
          ∀ l, (simTrace e rho).event l = Nat.pair i s → j' ≤ l ∧ l < j' + grp.length) := by
  induction os with
  | nil =>
    intro j sub st _ _ k hk
    rw [deliverRecs_nil, List.length_nil] at hk
    omega
  | cons o os ih =>
    intro j sub st hcut hstate k hk
    rw [deliverRecs_cons] at hcut hk
    cases he : canonEvent C hs o with
    | none =>
      simp only [he] at hcut hk
      obtain ⟨pre, w, post, ev, j', s, hsplit, hc, hrec, hst, hlo, hhi, hu⟩ :=
        ih j (sub + 1) st hcut hstate k hk
      refine ⟨o :: pre, w, post, ev, j', s, by rw [hsplit]; rfl, hc, ?_⟩
      simp only [List.foldl_cons, he, Option.map_none, Option.getD_none]
      refine ⟨hrec, hst, hlo, hhi, fun huniq => hu fun l s' hl hs' => ?_⟩
      have h := huniq l s' hl (by omega)
      rwa [deliverRecs_cons, he] at h
    | some ev =>
      simp only [he, List.length_append] at hcut hk
      set grp := groupRecs (runProposer rho hn) (digestOf e rho) y st t (Nat.pair i sub) ev
      set next := (exec (runProposer rho hn) (digestOf e rho) y st t ev).1
      set rest :=
        deliverRecs C (runProposer rho hn) (digestOf e rho) hs y t i os next (sub + 1)
      change k < grp.length + rest.length at hk
      change ∀ m < grp.length + rest.length, (allCuts e rho)[j + m]? = (grp ++ rest)[m]? at hcut
      have hg : ∀ m < grp.length, (allCuts e rho)[j + m]? = grp[m]? := fun m hm => by
        rw [hcut m (Nat.lt_of_lt_of_le hm (Nat.le_add_right _ _)), List.getElem?_append_left hm]
      have htail (m : Nat) (hm : m < rest.length) :
          (allCuts e rho)[j + grp.length + m]? = rest[m]? := by
        rw [Nat.add_assoc, hcut _ (Nat.add_lt_add_left hm grp.length),
          List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
      by_cases hkg : k < grp.length
      · refine ⟨[], o, os, ev, j, sub, rfl, he, hg, hstate, Nat.le_add_right j k,
          Nat.add_lt_add_left hkg j, ?_⟩
        intro huniq l hl
        obtain ⟨hlo, hhi⟩ := huniq l sub hl le_rfl
        rw [deliverRecs_cons, he, List.length_append] at hhi
        change l < j + (grp.length + rest.length) at hhi
        change j ≤ l ∧ l < j + grp.length
        refine ⟨hlo, ?_⟩
        by_contra! hge
        have hm : l - (j + grp.length) < rest.length := by omega
        have hr := htail _ hm
        rw [Nat.add_sub_cancel' hge, List.getElem?_eq_getElem hm] at hr
        obtain ⟨s, hs, hid⟩ := deliverRecs_id _ _ _ _ _ _ _ _ _ _ (List.getElem_mem hm)
        rw [simTrace_event, hr, Option.elim_some] at hl
        rw [hid, Nat.pair_eq_pair] at hl
        omega
      · have hnext : (simTrace e rho).state y (j + grp.length) = next := by
          exact state_after_group e rho hg hstate
        have hk' : k - grp.length < rest.length := by omega
        obtain ⟨pre, w, post, ev', j', s, hsplit, hc, hrec, hst, h1, h2, hu⟩ :=
          ih (j + grp.length) (sub + 1) next htail hnext (k - grp.length) hk'
        refine ⟨o :: pre, w, post, ev', j', s, by rw [hsplit]; rfl, hc, ?_⟩
        simp only [List.foldl_cons, he, Option.map_some, Option.getD_some]
        have hindex : j + grp.length + (k - grp.length) = j + k := by omega
        rw [hindex] at h1 h2
        refine ⟨hrec, hst, h1, h2, fun huniq => hu ?_⟩
        intro l s' hl hs'
        have huniq' (l s : Nat) (hl : (simTrace e rho).event l = Nat.pair i s)
            (hs : sub + 1 ≤ s) : j + grp.length ≤ l ∧ l < j + grp.length + rest.length := by
          obtain ⟨hlo, hhi⟩ := huniq l s hl (by omega)
          rw [deliverRecs_cons, he, List.length_append] at hhi
          change l < j + (grp.length + rest.length) at hhi
          refine ⟨?_, by omega⟩
          by_contra! hlt
          have hm : l - j < grp.length := by omega
          have hr := hg _ hm
          rw [Nat.add_sub_cancel' hlo, List.getElem?_eq_getElem hm] at hr
          rw [simTrace_event, hr, Option.elim_some] at hl
          have hid : grp[l - j].event = Nat.pair i sub := by
            dsimp only [grp]
            rw [List.getElem_of_eq (groupRecs_eq ..), List.getElem_mapIdx]
          rw [hid, Nat.pair_eq_pair] at hl
          omega
        exact huniq' l s' hl hs'

/-- At an indexed delivery cut, expose the node replay prefix and the selected handler's
label and pre-state. This does not require global uniqueness of the group's event id. -/
theorem indexed_receipt_state {y : Fin (Fintype.card V)} {t : Time} {i j sub k : Nat}
    (C : WireCodec A e.skel.Kind I e.Body)
    (hs : List (Header I × Nat))
    (os : List (ShapeObj (Fintype.card V) e.skel.Kind I e.Body)) (st : NodeState A)
    (hcut : ∀ m < (deliverRecs C (runProposer rho hn) (digestOf e rho)
        hs y t i os st sub).length,
      (allCuts e rho)[j + m]? = (deliverRecs C (runProposer rho hn) (digestOf e rho)
        hs y t i os st sub)[m]?)
    (hstate : (simTrace e rho).state y j = st) {r : CutRec A}
    (hr : (deliverRecs C (runProposer rho hn) (digestOf e rho)
      hs y t i os st sub)[k]? = some r) :
    ∃ pre w post ev, os = pre ++ w :: post ∧ canonEvent C hs w = some ev ∧
      let st' := pre.foldl (fun a o => ((canonEvent C hs o).map
        (fun ev => (exec (runProposer rho hn) (digestOf e rho) y a t ev).1)).getD a) st
      let cs := (exec (runProposer rho hn) (digestOf e rho) y st' t ev).2
      cs[r.pos]? = some r.label ∧
        (simTrace e rho).state y (j + k) = (cs.take r.pos).foldl (cutPost y t) st' := by
  obtain ⟨pre, w, post, ev, j', s, hm, hc, hrec, hst, hlo, hhi, _⟩ :=
    indexed_delivery_group e rho C hs os j sub st hcut hstate k (List.getElem?_eq_some_iff.mp hr).1
  have hidx : j' + (j + k - j') = j + k := Nat.add_sub_cancel' hlo
  have hpos := hrec (j + k - j') (by omega)
  rw [hidx, hcut _ (List.getElem?_eq_some_iff.mp hr).1, hr] at hpos
  have hlen := (List.getElem?_eq_some_iff.mp hpos.symm).1
  have hstep := state_in_group e rho _ _ hrec hst (j + k - j')
    (by rw [length_group e rho] at hlen; exact hlen.le)
  rw [hidx] at hstep
  rw [List.getElem?_eq_getElem hlen, List.getElem_of_eq (groupRecs_eq ..),
    List.getElem_mapIdx, List.getElem_zip] at hpos
  cases hpos
  exact ⟨pre, w, post, ev, hm, hc, List.getElem?_eq_getElem _, hstep⟩

private theorem delivery_group {y : Fin (Fintype.card V)} {t : Time} {i : Nat}
    (C : WireCodec A e.skel.Kind I e.Body)
    (hs : List (Header I × Nat))
    (os : List (ShapeObj (Fintype.card V) e.skel.Kind I e.Body)) :
    ∀ (j sub : Nat) (st : NodeState A),
    (∀ k < (deliverRecs C (runProposer rho hn) (digestOf e rho)
        hs y t i os st sub).length,
      (allCuts e rho)[j + k]? = (deliverRecs C (runProposer rho hn) (digestOf e rho)
        hs y t i os st sub)[k]?) →
    (simTrace e rho).state y j = st →
    (∀ k s, (simTrace e rho).event k = Nat.pair i s → sub ≤ s → j ≤ k ∧
      k < j + (deliverRecs C (runProposer rho hn) (digestOf e rho)
        hs y t i os st sub).length) →
    ∀ k < (deliverRecs C (runProposer rho hn) (digestOf e rho)
        hs y t i os st sub).length,
      ∃ j' st' id ev, (∀ m < (groupRecs (runProposer rho hn) (digestOf e rho)
          y st' t id ev).length,
        (allCuts e rho)[j' + m]? = (groupRecs (runProposer rho hn) (digestOf e rho)
          y st' t id ev)[m]?) ∧
        (simTrace e rho).state y j' = st' ∧ j' ≤ j + k ∧
        j + k < j' + (groupRecs (runProposer rho hn) (digestOf e rho) y st' t id ev).length ∧
        (∀ l, (simTrace e rho).event l = id → j' ≤ l ∧
          l < j' + (groupRecs (runProposer rho hn) (digestOf e rho) y st' t id ev).length) := by
  intro j sub st hcut hstate huniq k hk
  obtain ⟨_, _, _, ev, j', s, _, _, hrec, hst, hlo, hhi, hu⟩ :=
    indexed_delivery_group e rho C hs os j sub st hcut hstate k hk
  exact ⟨j', _, Nat.pair i s, ev, hrec, hst, hlo, hhi, hu huniq⟩

private theorem records_of_call {due : e.State hn → Bool} (laws : e.Lawful due)
    (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)} {k : Nat} {c : Cut A}
    (hc : (simTrace e rho).CallAt y k c) :
    ∃ j st t id ev, (∀ m < (groupRecs (runProposer rho hn) (digestOf e rho)
          y st t id ev).length,
        (allCuts e rho)[j + m]? = (groupRecs (runProposer rho hn) (digestOf e rho)
          y st t id ev)[m]?) ∧
      (simTrace e rho).state y j = st ∧ j ≤ k ∧
      k < j + (groupRecs (runProposer rho hn) (digestOf e rho) y st t id ev).length ∧
      (∀ l, (simTrace e rho).event l = id → j ≤ l ∧
        l < j + (groupRecs (runProposer rho hn) (digestOf e rho) y st t id ev).length) := by
  obtain ⟨i, ev, he, h1, h2, _, hy, _⟩ := call_origin e rho hc
  have hi := (List.getElem?_eq_some_iff.mp he).1
  have hcut : ∀ m < (eventCuts e rho i).length,
      (allCuts e rho)[cutMap e rho i + m]? = (eventCuts e rho i)[m]? :=
    fun m hm => allCuts_getElem?_add e rho i m hi hm
  have hlen := cutMap_succ e rho i
  have hstate := (stateAgreement_all laws hv ev.node i hi.le).symm
  have hy' : rho.ownKey ev.node = y := by rw [hy, Model.Run.ownKey, Equiv.symm_apply_apply]
  cases ev with
  | tick v t =>
    change rho.ownKey v = y at hy'
    subst y
    rw [eventCuts_tick e rho i v t he] at hcut hlen
    by_cases hp : (paramsAtCount p (Fintype.card V) hN hn).IsPublic t
    · rw [ite_eq_left hp] at hcut hlen
      exact ⟨_, _, t, Nat.pair i 0, _, hcut, hstate, h1, by omega,
        fun l hl => hlen ▸ range_of_id e rho hi hl⟩
    · rw [ite_eq_right hp, List.length_nil] at hlen
      omega
  | deliver v o t =>
    change rho.ownKey v = y at hy'
    subst y
    rw [eventCuts_deliver e rho i v o t he] at hcut hlen
    dsimp only at hlen
    obtain ⟨j, st, id, ev, hrec, hst, hj, hk, hu⟩ :=
      delivery_group e rho _ _ _ _ 0 _ hcut hstate
        (fun l _ hl _ => hlen ▸ range_of_id e rho hi hl) (k - cutMap e rho i) (by omega)
    exact ⟨j, st, t, id, ev, hrec, hst, by omega, by omega, hu⟩
  | restart v t =>
    change rho.ownKey v = y at hy'
    subst y
    rw [eventCuts_restart e rho i v t he] at hcut hlen
    exact ⟨_, _, t, Nat.pair i 0, _, hcut, hstate, h1, by omega,
      fun l hl => hlen ▸ range_of_id e rho hi hl⟩

/-- The recorded cuts follow the node's handler law at every actual call. -/
theorem cutLaw {due : e.State hn → Bool} (laws : e.Lawful due) (hv : rho.ExecutionValid)
    (y : Fin (Fintype.card V)) (k : Nat) (c : Cut A) (hc : (simTrace e rho).CallAt y k c) :
    CutStep y ((simTrace e rho).time k) ((simTrace e rho).state y k) c
      ((simTrace e rho).post k) := by
  obtain ⟨j, st, t, id, ev, hrec, hst, h1, h2, _⟩ := records_of_call e rho laws hv hc
  obtain ⟨m, rfl⟩ : ∃ m, k = j + m := ⟨k - j, by omega⟩
  have hm : m < (groupRecs (runProposer rho hn) (digestOf e rho) y st t id ev).length := by
    omega
  have hm' := hm
  rw [length_group e rho] at hm'
  have hr := hrec m hm
  rw [List.getElem?_eq_getElem hm, List.getElem_of_eq (groupRecs_eq ..),
    List.getElem_mapIdx, List.getElem_zip] at hr
  have hl := hc.2
  rw [simTrace_label, hr, Option.map_some, Option.some.injEq] at hl
  subst c
  rw [simTrace_time, simTrace_post, hr, Option.elim_some, Option.elim_some,
    state_in_group e rho _ _ hrec hst m hm'.le, Node.cutPosts_getElem]
  exact Simulation.cutStep_of_cutChain (Compose.exec_is_cut_chain _ _ _ _ _ _) m hm'

/-- Every call is covered by the node handler group that produced it. -/
theorem grouped {due : e.State hn → Bool} (laws : e.Lawful due) (hv : rho.ExecutionValid)
    (y : Fin (Fintype.card V)) (k : Nat) (c : Cut A) (hc : (simTrace e rho).CallAt y k c) :
    ∃ j ev, (simTrace e rho).InGroup (runProposer rho hn) (digestOf e rho) y j k
      ((simTrace e rho).time k) ev := by
  obtain ⟨j, st, t, id, ev, hrec, hst, h1, h2, hu⟩ := records_of_call e rho laws hv hc
  rw [length_group e rho, ← hst] at h2
  have hne : (exec (runProposer rho hn) (digestOf e rho) y st t ev).2 ≠ [] := by
    rw [← hst]
    intro h
    rw [h, List.length_nil] at h2
    omega
  have hg := groupAt_of_recs e rho _ _ hst hne hrec hu
  have ht := (hg.2.1 (k - j) (by omega)).2.1
  rw [Nat.add_sub_cancel' h1] at ht
  rw [ht]
  exact ⟨j, ev, hg, h1, h2⟩

/-- A public engine tick gives one trace group at the prefix cut map.
Kept for a downstream consumer. -/
theorem tick_public_group {due : e.State hn → Bool} (laws : e.Lawful due)
    (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t))
    (hp : (paramsAtCount p (Fintype.card V) hN hn).IsPublic t) :
    (simTrace e rho).GroupAt (runProposer rho hn) (digestOf e rho)
      (rho.ownKey v) (cutMap e rho i) t (.tick (encodeTxs (Model.mempool rho.inbox v t))) ∧
    cutMap e rho (i + 1) = cutMap e rho i +
      (exec (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
        ((simTrace e rho).state (rho.ownKey v) (cutMap e rho i)) t
        (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2.length := by
  have hi := (List.getElem?_eq_some_iff.mp he).1
  have hst := stateAgreement_all laws hv v i hi.le
  have hcuts := eventCuts_tick e rho i v t he
  rw [ite_eq_left hp] at hcuts
  refine ⟨groupAt_of_recs e rho _ _ (id := Nat.pair i 0) hst.symm ?_ ?_ ?_, ?_⟩
  · simp [exec, onTick, runSteps, tickSteps, Node.tickStep]
  · intro k hk
    rw [← hcuts] at hk ⊢
    exact allCuts_getElem?_add e rho i k hi hk
  · intro k hk
    rw [← hcuts, ← cutMap_succ]
    exact range_of_id e rho hi hk
  · rw [cutMap_succ, hcuts, ← hst, length_group]

/-- A node honest and awake at a public time has a tick group there. -/
theorem tick_of_awake {due : e.State hn → Bool} (laws : e.Lawful due)
    (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)} {t : Time}
    (hy : y ∈ honestKeysAt rho t) (ht : 0 ≤ t)
    (hp : (paramsAtCount p (Fintype.card V) hN hn).IsPublic t)
    (hw : (simTrace e rho).awake y t) :
    ∃ j, (simTrace e rho).TickAt (runProposer rho hn) (digestOf e rho) y j t := by
  obtain ⟨hw, _, hth⟩ := (simTrace_awake_iff e rho y t).mp hw
  rw [mem_honestKeysAt_iff, min_eq_left hth] at hy
  obtain ⟨i, he⟩ := List.mem_iff_getElem?.mp (hv.tick_total (rho.key y) t ht hth hy hw)
  have hg := (tick_public_group e rho laws hv he hp).1
  rw [Model.Run.ownKey, Equiv.symm_apply_apply] at hg
  exact ⟨_, _, hg⟩

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace
