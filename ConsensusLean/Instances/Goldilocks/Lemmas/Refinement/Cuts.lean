module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Refinement.Trace

public section

/-! # Goldilocks Refinement: where the cuts of the simulating trace come from

Every node cut of `allCuts` is a cut of one engine event: cut `k` of the trace, below the
length of `allCuts` (which is `cutMap` of the number of events), is the cut `k - cutMap i` of
the event `i` with `cutMap i ≤ k < cutMap (i + 1)` (`allCuts_getElem?`), and conversely
(`allCuts_getElem?_add`). A cut of event `i` is at the event's node and time, under an event id
`Nat.pair i s` (`mem_eventCuts`). The cuts of a group are at the positions `0, 1, …`
(`getElem_groupRecs`); a cut at position `0` starts a group whose handler is of the engine
event's phase (`phase_of_pos_zero`); an `ac_restart` cut is a cut of an engine restart
(`restart_of_mem_eventCuts`). -/

namespace Consensus.Goldilocks.Refinement

open Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload)

/-! ## The phase of a handler's first cut -/

section

variable {P : Params} {A : NodeAC P}

/-- The phase of the event whose handler starts with the cut `c`: an `ac_restart` is `0`, an
`ac_on_tick` is `1`, anything else `2`. -/
private def cutPhase : Cut A → Nat
  | .ac ℓ =>
    match ℓ.call with
    | .restart => 0
    | .tick => 1
    | _ => 2
  | .fg _ => 2

/-- A handler's first cut has the phase of its event. -/
private theorem cutPhase_exec (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n)
    (st : NodeState A) (t : Time) (e : Event A) {c : Cut A} {cs : List (Cut A)}
    (h : (exec dg self st t e).2 = c :: cs) : cutPhase c = e.phase := by
  cases e with
  | tick x =>
    obtain ⟨ℓ, pc, uc, hℓ, hcs, -, -⟩ := Compose.tick_order dg self st t x
    change (onTick dg self st t x).2 = _ at h
    rw [hcs] at h
    obtain ⟨rfl, -⟩ := List.cons.inj h
    simp [cutPhase, hℓ, Event.phase]
  | block B =>
    simp only [exec, onBlock, acCall] at h
    split_ifs at h
    all_goals first | cases h | (split at h <;> (obtain ⟨rfl, -⟩ := List.cons.inj h; rfl))
  | message m =>
    simp only [exec, onMessage, acCall] at h
    obtain ⟨rfl, -⟩ := List.cons.inj h
    rfl
  | attestation a =>
    simp only [exec, onAttestation] at h
    obtain ⟨rfl, -⟩ := List.cons.inj h
    rfl
  | restart =>
    simp only [exec, Node.restart, acCall] at h
    obtain ⟨rfl, -⟩ := List.cons.inj h
    rfl

/-- Only a restart's handler makes an `ac_restart` cut. -/
private theorem restart_of_mem_exec (dg : Digest (List (FG.Att P.n)) A.Payload)
    (self : Fin P.n) (st : NodeState A) (t : Time) (e : Event A) {ℓ : ACLabel A}
    (h : Cut.ac ℓ ∈ (exec dg self st t e).2) (hℓ : ℓ.call = .restart) : e = .restart := by
  cases e with
  | tick x =>
    obtain ⟨ℓ₀, pc, uc, hℓ₀, hcs, hpc, ⟨ℓ₁, hℓ₁, huc⟩⟩ := Compose.tick_order dg self st t x
    change _ ∈ (onTick dg self st t x).2 at h
    rw [hcs] at h
    exfalso
    rcases List.mem_cons.mp h with h | h
    · cases h; simp [hℓ] at hℓ₀
    rcases List.mem_append.mp h with h | h
    · rcases hpc with ⟨-, rfl⟩ | ⟨-, ℓ₂, hℓ₂, hpc⟩
      · simp at h
      rcases hpc with rfl | ⟨B, -, -, rfl | ⟨ℓ₃, hℓ₃, rfl⟩⟩
      · simp only [List.mem_singleton, Cut.ac.injEq] at h; subst h; simp [hℓ] at hℓ₂
      · simp only [List.mem_cons, Cut.ac.injEq, reduceCtorEq, List.not_mem_nil, or_false] at h
        subst h; simp [hℓ] at hℓ₂
      · simp only [List.mem_cons, Cut.ac.injEq, reduceCtorEq, List.not_mem_nil, or_false,
          false_or] at h
        rcases h with rfl | rfl
        · simp [hℓ] at hℓ₂
        · simp [hℓ] at hℓ₃
    · rcases huc with rfl | ⟨C, rfl⟩ | ⟨C, a, rfl⟩ <;>
        simp only [List.mem_cons, Cut.ac.injEq, reduceCtorEq, List.not_mem_nil, or_false] at h <;>
        (subst h; simp [hℓ] at hℓ₁)
  | block B =>
    simp only [exec, onBlock, acCall] at h
    exfalso
    split_ifs at h
    · simp at h
    · split at h
      · simp at h
      · simp only [List.mem_cons, reduceCtorEq, Cut.ac.injEq, List.not_mem_nil, or_false,
          false_or] at h
        subst h; simp at hℓ
  | message m =>
    simp only [exec, onMessage, acCall, List.mem_singleton, Cut.ac.injEq] at h
    subst h; simp at hℓ
  | attestation a => simp [exec, onAttestation] at h
  | restart => rfl

end

/-! ## Groups and deliveries -/

section

variable {sp : SAParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)

/-- One post-state per cut. -/
theorem length_cutPosts (t : Time) (cs : List (Cut (goldilocksNode sp ro)))
    (st : NodeState (goldilocksNode sp ro)) : (cutPosts self t cs st).length = cs.length := by
  induction cs generalizing st with
  | nil => simp only [cutPosts_nil, List.length_nil]
  | cons c cs ih => simp only [cutPosts_cons, List.length_cons, ih]

/-- A group has one cut per handler cut. -/
theorem length_groupRecs (st : NodeState (goldilocksNode sp ro)) (t : Time) (id : Nat)
    (e : Event (goldilocksNode sp ro)) :
    (groupRecs dg self st t id e).length = (exec dg self st t e).2.length := by
  simp [groupRecs_eq, length_cutPosts]

/-- The cut at position `k` of a group: the node, time and event id of the group, position `k`,
the handler's cut `k`. -/
theorem getElem_groupRecs (st : NodeState (goldilocksNode sp ro)) (t : Time) (id : Nat)
    (e : Event (goldilocksNode sp ro)) (k : Nat) (hk : k < (groupRecs dg self st t id e).length) :
    (groupRecs dg self st t id e)[k].node = self ∧ (groupRecs dg self st t id e)[k].time = t ∧
      (groupRecs dg self st t id e)[k].event = id ∧ (groupRecs dg self st t id e)[k].pos = k ∧
      (groupRecs dg self st t id e)[k].label =
        (exec dg self st t e).2[k]'(by rwa [length_groupRecs] at hk) := by
  rw [List.getElem_of_eq (groupRecs_eq dg self st t id e) hk, List.getElem_mapIdx,
    List.getElem_zip]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A cut of a group is at the group's node, time and event id. -/
theorem mem_groupRecs {st : NodeState (goldilocksNode sp ro)} {t : Time} {id : Nat}
    {e : Event (goldilocksNode sp ro)} {r : CutRec sp ro} (hr : r ∈ groupRecs dg self st t id e) :
    r.node = self ∧ r.time = t ∧ r.event = id := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
  obtain ⟨h1, h2, h3, -⟩ := getElem_groupRecs dg self st t id e k hk
  exact ⟨h1, h2, h3⟩

/-- A cut at position `0` of a group is the group's first: its label is the handler's first
cut. -/
private theorem cutPhase_of_mem_groupRecs {st : NodeState (goldilocksNode sp ro)} {t : Time}
    {id : Nat} {e : Event (goldilocksNode sp ro)} {r : CutRec sp ro}
    (hr : r ∈ groupRecs dg self st t id e) (h0 : r.pos = 0) : cutPhase r.label = e.phase := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
  obtain ⟨-, -, -, hpos, hlab⟩ := getElem_groupRecs dg self st t id e k hk
  rw [h0] at hpos
  subst hpos
  have hk' : 0 < (exec dg self st t e).2.length := by rwa [length_groupRecs] at hk
  obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_length_pos hk'
  have hc : (exec dg self st t e).2[0]'hk' = c := by
    rw [List.getElem_of_eq hcs hk']; rfl
  rw [hlab, hc]
  exact cutPhase_exec (P := sp.toParams) (A := goldilocksNode sp ro) dg self st t e hcs

/-- A cut of a delivery's cuts is at the delivery's node and time, under the id of a sub-event
from `sub` on. -/
theorem mem_deliverRecs (hs : List (Header Info × Nat)) (t : Time) (i : Nat)
    {os : List (Wire sp.n)} {st : NodeState (goldilocksNode sp ro)} {sub : Nat}
    {r : CutRec sp ro} (hr : r ∈ deliverRecs dg hs self t i os st sub) :
    r.node = self ∧ r.time = t ∧ ∃ s, sub ≤ s ∧ r.event = Nat.pair i s := by
  induction os generalizing st sub with
  | nil => simp [deliverRecs_nil] at hr
  | cons o os ih =>
    cases he : canonEvent sp ro hs o with
    | none =>
      rw [deliverRecs_cons_none dg hs self t i o os st sub he] at hr
      obtain ⟨h1, h2, s, hs', h3⟩ := ih hr
      exact ⟨h1, h2, s, by omega, h3⟩
    | some e =>
      rw [deliverRecs_cons_some dg hs self t i o os st sub e he] at hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨h1, h2, h3⟩ := mem_groupRecs dg self hr
        exact ⟨h1, h2, sub, le_rfl, h3⟩
      · obtain ⟨h1, h2, s, hs', h3⟩ := ih hr
        exact ⟨h1, h2, s, by omega, h3⟩

private theorem phase_canonEvent {hs : List (Header Info × Nat)} {o : Wire sp.n}
    {e : Event (goldilocksNode sp ro)} (he : canonEvent sp ro hs o = some e) : e.phase = 2 := by
  simp only [canonEvent] at he
  split at he <;> first | (cases he; rfl) | simp at he

private theorem cutPhase_of_mem_deliverRecs (hs : List (Header Info × Nat)) (t : Time) (i : Nat)
    {os : List (Wire sp.n)} {st : NodeState (goldilocksNode sp ro)} {sub : Nat}
    {r : CutRec sp ro} (hr : r ∈ deliverRecs dg hs self t i os st sub) (h0 : r.pos = 0) :
    cutPhase r.label = 2 := by
  induction os generalizing st sub with
  | nil => simp [deliverRecs_nil] at hr
  | cons o os ih =>
    cases he : canonEvent sp ro hs o with
    | none =>
      rw [deliverRecs_cons_none dg hs self t i o os st sub he] at hr
      exact ih hr
    | some e =>
      rw [deliverRecs_cons_some dg hs self t i o os st sub e he] at hr
      rcases List.mem_append.mp hr with hr | hr
      · rw [cutPhase_of_mem_groupRecs dg self hr h0, phase_canonEvent he]
      · exact ih hr

private theorem restart_of_mem_deliverRecs (hs : List (Header Info × Nat)) (t : Time) (i : Nat)
    {os : List (Wire sp.n)} {st : NodeState (goldilocksNode sp ro)} {sub : Nat}
    {r : CutRec sp ro} (hr : r ∈ deliverRecs dg hs self t i os st sub)
    {ℓ : ACLabel (goldilocksNode sp ro)} (hl : r.label = .ac ℓ) (hℓ : ℓ.call = .restart) :
    False := by
  induction os generalizing st sub with
  | nil => simp [deliverRecs_nil] at hr
  | cons o os ih =>
    cases he : canonEvent sp ro hs o with
    | none =>
      rw [deliverRecs_cons_none dg hs self t i o os st sub he] at hr
      exact ih hr
    | some e =>
      rw [deliverRecs_cons_some dg hs self t i o os st sub e he] at hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
        obtain ⟨-, -, -, -, hlab⟩ := getElem_groupRecs dg self st t _ e k hk
        rw [hlab] at hl
        have := restart_of_mem_exec dg self st t e (hl ▸ List.getElem_mem _) hℓ
        subst this
        exact absurd (phase_canonEvent he) (by simp [Event.phase])
      · exact ih hr

end

/-! ## The cuts of the run -/

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (family S)) E) (hn : 1 ≤ Fintype.card V)

private theorem flatMap_range_succ (m : Nat) :
    (List.range (m + 1)).flatMap (eventCuts S rho hn) =
      (List.range m).flatMap (eventCuts S rho hn) ++ eventCuts S rho hn m := by
  simp [List.range_succ, List.flatMap_append]

private theorem length_flatMap_range (m : Nat) :
    ((List.range m).flatMap (eventCuts S rho hn)).length = cutMap S rho hn m := by
  induction m with
  | zero => simp [cutMap_zero]
  | succ m ih => rw [flatMap_range_succ, List.length_append, ih, cutMap_succ]

/-- The number of node cuts is the cut map at the last engine cut. -/
theorem length_allCuts : (allCuts S rho hn).length = cutMap S rho hn rho.events.length := by
  rw [allCuts_eq, length_flatMap_range]

private theorem flatMap_range_getElem? (m k : Nat)
    (hk : k < ((List.range m).flatMap (eventCuts S rho hn)).length) :
    ∃ i < m, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      ((List.range m).flatMap (eventCuts S rho hn))[k]? =
        (eventCuts S rho hn i)[k - cutMap S rho hn i]? := by
  induction m with
  | zero => simp at hk
  | succ m ih =>
    rw [flatMap_range_succ] at hk ⊢
    by_cases hlt : k < ((List.range m).flatMap (eventCuts S rho hn)).length
    · obtain ⟨i, hi, h1, h2, h3⟩ := ih hlt
      exact ⟨i, by omega, h1, h2, by rw [List.getElem?_append_left hlt, h3]⟩
    · rw [List.length_append] at hk
      rw [length_flatMap_range] at hlt hk
      refine ⟨m, by omega, by omega, by rw [cutMap_succ]; omega, ?_⟩
      rw [List.getElem?_append_right (by rw [length_flatMap_range]; omega),
        length_flatMap_range]

private theorem flatMap_range_getElem?_add (m i j : Nat) (hi : i < m)
    (hj : j < (eventCuts S rho hn i).length) :
    ((List.range m).flatMap (eventCuts S rho hn))[cutMap S rho hn i + j]? =
      (eventCuts S rho hn i)[j]? := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [flatMap_range_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have := cutMap_mono S rho hn (Nat.succ_le_of_lt hi)
      rw [cutMap_succ] at this
      rw [List.getElem?_append_left (by rw [length_flatMap_range]; omega), ih hi]
    · rw [List.getElem?_append_right (by rw [length_flatMap_range]; exact Nat.le_add_right _ _),
        length_flatMap_range, Nat.add_sub_cancel_left]

/-- **Every node cut is a cut of one engine event**: cut `k` below the length of `allCuts` is the
cut `k - cutMap i` of the event `i` with `cutMap i ≤ k < cutMap (i + 1)`. -/
theorem allCuts_getElem? (k : Nat) (hk : k < (allCuts S rho hn).length) :
    ∃ i < rho.events.length, cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      (allCuts S rho hn)[k]? = (eventCuts S rho hn i)[k - cutMap S rho hn i]? := by
  rw [allCuts_eq] at hk ⊢
  exact flatMap_range_getElem? S rho hn _ k hk

/-- The cut `j` of the engine event `i` is the node cut `cutMap i + j`. -/
theorem allCuts_getElem?_add (i j : Nat) (hi : i < rho.events.length)
    (hj : j < (eventCuts S rho hn i).length) :
    (allCuts S rho hn)[cutMap S rho hn i + j]? = (eventCuts S rho hn i)[j]? := by
  rw [allCuts_eq]
  exact flatMap_range_getElem?_add S rho hn _ i j hi hj

/-- A node cut that exists is a cut of an engine event `i`, the event at index `i`. -/
theorem exists_event_of_getElem? {k : Nat} {r : CutRec (S.params (pubOf E) hn) (S.ro _)}
    (hr : (allCuts S rho hn)[k]? = some r) :
    ∃ i ev, rho.events[i]? = some ev ∧ cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      (eventCuts S rho hn i)[k - cutMap S rho hn i]? = some r := by
  obtain ⟨i, hi, h1, h2, h3⟩ :=
    allCuts_getElem? S rho hn k (List.getElem?_eq_some_iff.mp hr).1
  exact ⟨i, rho.events[i], List.getElem?_eq_getElem hi, h1, h2, h3 ▸ hr⟩

/-- A cut of engine event `i` is at the event's node (its own key) and time, under an event id
`Nat.pair i s`. -/
theorem mem_eventCuts {i : Nat} {ev : Model.Event V (Model.protoOf (compiled (family S)) E).Object}
    (he : rho.events[i]? = some ev) {r : CutRec (S.params (pubOf E) hn) (S.ro _)}
    (hr : r ∈ eventCuts S rho hn i) :
    r.node = rho.ownKey ev.node ∧ r.time = ev.time ∧ ∃ s, r.event = Nat.pair i s := by
  cases ev with
  | tick v t =>
    by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
    · rw [eventCuts_tick_public S rho hn i v t he hp] at hr
      obtain ⟨h1, h2, h3⟩ := mem_groupRecs _ _ hr
      exact ⟨h1, h2, 0, h3⟩
    · rw [eventCuts_tick_other S rho hn i v t he hp] at hr
      simp at hr
  | deliver v o t =>
    rw [eventCuts_deliver S rho hn i v o t he] at hr
    obtain ⟨h1, h2, s, -, h3⟩ := mem_deliverRecs _ _ _ t i hr
    exact ⟨h1, h2, s, h3⟩
  | restart v t =>
    rw [eventCuts_restart S rho hn i v t he] at hr
    obtain ⟨h1, h2, h3⟩ := mem_groupRecs _ _ hr
    exact ⟨h1, h2, 0, h3⟩

/-- A cut at position `0` of engine event `i` starts a group whose handler is of the engine
event's phase: if its label is the first cut of the handler of `e` (at any state), `e` has the
phase of the engine event. -/
theorem phase_of_pos_zero {i : Nat}
    {ev : Model.Event V (Model.protoOf (compiled (family S)) E).Object}
    (he : rho.events[i]? = some ev) {r : CutRec (S.params (pubOf E) hn) (S.ro _)}
    (hr : r ∈ eventCuts S rho hn i) (h0 : r.pos = 0)
    {dg : Digest (List (FG.Att (Fintype.card V))) (Payload (Fintype.card V))}
    {y : Fin (Fintype.card V)} {st : NodeState (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    {t : Time} {e : Event (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    {cs : List (Cut (goldilocksNode (S.params (pubOf E) hn) (S.ro _)))}
    (hcs : (exec dg y st t e).2 = r.label :: cs) : e.phase = ev.phase := by
  rw [← cutPhase_exec (P := (S.params (pubOf E) hn).toParams)
    (A := goldilocksNode (S.params (pubOf E) hn) (S.ro _)) (c := r.label) (cs := cs)
    dg y st t e hcs]
  cases ev with
  | tick v t' =>
    by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t'
    · rw [eventCuts_tick_public S rho hn i v t' he hp] at hr
      exact cutPhase_of_mem_groupRecs _ _ hr h0
    · rw [eventCuts_tick_other S rho hn i v t' he hp] at hr
      simp at hr
  | deliver v o t' =>
    rw [eventCuts_deliver S rho hn i v o t' he] at hr
    exact cutPhase_of_mem_deliverRecs _ _ _ t' i hr h0
  | restart v t' =>
    rw [eventCuts_restart S rho hn i v t' he] at hr
    exact cutPhase_of_mem_groupRecs _ _ hr h0

/-- An `ac_restart` cut is a cut of an engine restart. -/
theorem restart_of_mem_eventCuts {i : Nat}
    {ev : Model.Event V (Model.protoOf (compiled (family S)) E).Object}
    (he : rho.events[i]? = some ev) {r : CutRec (S.params (pubOf E) hn) (S.ro _)}
    (hr : r ∈ eventCuts S rho hn i) {ℓ : ACLabel (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    (hl : r.label = .ac ℓ) (hℓ : ℓ.call = .restart) : ∃ v t, ev = .restart v t := by
  cases ev with
  | tick v t' =>
    by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t'
    · rw [eventCuts_tick_public S rho hn i v t' he hp] at hr
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hr
      obtain ⟨-, -, -, -, hlab⟩ := getElem_groupRecs _ _ _ t' _ _ k hk
      rw [hlab] at hl
      exact absurd (restart_of_mem_exec _ _ _ _ _ (hl ▸ List.getElem_mem _) hℓ) (by simp)
    · rw [eventCuts_tick_other S rho hn i v t' he hp] at hr
      simp at hr
  | deliver v o t' =>
    rw [eventCuts_deliver S rho hn i v o t' he] at hr
    exact (restart_of_mem_deliverRecs _ _ _ t' i hr hl hℓ).elim
  | restart v t' => exact ⟨v, t', rfl⟩

/-- The cuts of a group-shaped engine event (a tick at a public time, a restart) are at the
positions `0, 1, …`. -/
theorem pos_getElem_eventCuts_of_group {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t) ∨ rho.events[i]? = some (.restart v t)) (m : Nat)
    (hm : m < (eventCuts S rho hn i).length) : (eventCuts S rho hn i)[m].pos = m := by
  rcases he with he | he
  · by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
    · simp only [eventCuts_tick_public S rho hn i v t he hp] at hm ⊢
      exact (getElem_groupRecs _ _ _ _ _ _ m hm).2.2.2.1
    · simp [eventCuts_tick_other S rho hn i v t he hp] at hm
  · simp only [eventCuts_restart S rho hn i v t he] at hm ⊢
    exact (getElem_groupRecs _ _ _ _ _ _ m hm).2.2.2.1

/-- An engine restart has exactly one cut, the restart's `ac_restart`. -/
theorem eventCuts_restart_length {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.restart v t)) : (eventCuts S rho hn i).length = 1 := by
  rw [eventCuts_restart S rho hn i v t he]
  exact (length_groupRecs _ _ _ _ _ _).trans rfl

/-- An engine restart's one cut, at `cutMap i`: at the restart's node and time, an `ac_restart`. -/
theorem restart_getElem? {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.restart v t)) :
    cutMap S rho hn (i + 1) = cutMap S rho hn i + 1 ∧
      ∃ r, (allCuts S rho hn)[cutMap S rho hn i]? = some r ∧ r.node = rho.ownKey v ∧
        r.time = t ∧ ∃ ℓ, r.label = .ac ℓ ∧ ℓ.call = .restart := by
  have hlen := eventCuts_restart_length S rho hn he
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  refine ⟨by rw [cutMap_succ, hlen], (eventCuts S rho hn i)[0], ?_⟩
  have h0 := allCuts_getElem?_add S rho hn i 0 hi (by rw [hlen]; exact Nat.one_pos)
  rw [Nat.add_zero] at h0
  refine ⟨by rw [h0]; exact List.getElem?_eq_getElem _, ?_⟩
  have hm : 0 < (groupRecs (digestOf S rho) (rho.ownKey v) (stateAt S rho hn v i).node t
      (Nat.pair i 0) .restart).length := by
    rw [← eventCuts_restart S rho hn i v t he, hlen]; exact Nat.one_pos
  obtain ⟨h1, h2, -, -, h5⟩ := getElem_groupRecs _ _ _ _ _ _ 0 hm
  simp only [eventCuts_restart S rho hn i v t he]
  refine ⟨h1, h2, _, h5.trans rfl, rfl⟩

/-- **A labelled cut of the trace is a cut of an engine event**: the event `i` at whose cuts
`[cutMap i, cutMap (i + 1))` it lies, with the cut's node (the event node's key), time (the
event's), position and label. -/
theorem simTrace_cut {k : Nat} (hk : (simTrace S rho hn).label k ≠ none) :
    ∃ r i ev, (allCuts S rho hn)[k]? = some r ∧ rho.events[i]? = some ev ∧
      cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) ∧
      (eventCuts S rho hn i)[k - cutMap S rho hn i]? = some r ∧
      (simTrace S rho hn).node k = rho.ownKey ev.node ∧ (simTrace S rho hn).time k = ev.time ∧
      (simTrace S rho hn).pos k = r.pos ∧ (simTrace S rho hn).label k = some r.label := by
  rw [simTrace_label] at hk
  cases hr : (allCuts S rho hn)[k]? with
  | none => simp [hr] at hk
  | some r =>
  obtain ⟨i, ev, he, h1, h2, h3⟩ := exists_event_of_getElem? S rho hn hr
  have hmem : r ∈ eventCuts S rho hn i := List.mem_of_getElem? h3
  obtain ⟨hnode, htime, -⟩ := mem_eventCuts S rho hn he hmem
  refine ⟨r, i, ev, rfl, he, h1, h2, h3, ?_, ?_, ?_, ?_⟩
  · rw [simTrace_node, hr]; exact hnode
  · rw [simTrace_time, hr]; exact htime
  · rw [simTrace_pos, hr]; rfl
  · rw [simTrace_label, hr]; rfl

/-- Past the last node cut the trace is unlabelled, at the horizon. -/
theorem simTrace_of_getElem?_none {k : Nat} (hk : (allCuts S rho hn)[k]? = none) :
    (simTrace S rho hn).label k = none ∧ (simTrace S rho hn).time k = rho.horizon := by
  simp [simTrace_label, simTrace_time, hk]

end Consensus.Goldilocks.Refinement

end
