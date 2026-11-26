module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeStateAgreement
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.NodeDeliveryOrigin
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # The own-admission tail of a tick in the canonical replay

Where a replay cut sits within its engine event (`cut_classify`), and where the cuts with a given
group id lie: a tick's public group, a non-tick event's range, or the tick's own admissions right
after its group. -/

namespace Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

open Blocks Shape Node

variable {V : Type} [Fintype V] {E : Env V}
variable {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
variable {F : ChainShapeFamily O I} {p : Params} {hN : p.n = Fintype.card V}
variable {hn : 1 ≤ Fintype.card V}
variable {A : NodeAC (paramsAtCount p (Fintype.card V) hN hn)}
variable (e : Encoding F E p hN hn A) (rho : Model.Run (compiled F) E)
variable [DecidableEq V]

open Classical in
/-- The public tick group of a tick of `v` at `t` that is engine event `i`. -/
noncomputable def tickGroup (i : Nat) (v : V) (t : Time) : List (CutRec A) :=
  if (paramsAtCount p (Fintype.card V) hN hn).IsPublic t then
    groupRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
      (e.adapter.node (stateAt e rho v i)) t (Nat.pair i 0)
      (.tick (encodeTxs (Model.mempool rho.inbox v t)) (e.adapter.sign (rho.ownKey v) t))
  else []

open Classical in
/-- `tickGroup` unfolded. -/
theorem tickGroup_eq (i : Nat) (v : V) (t : Time) : tickGroup e rho i v t =
    if (paramsAtCount p (Fintype.card V) hN hn).IsPublic t then
      groupRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
        (e.adapter.node (stateAt e rho v i)) t (Nat.pair i 0)
        (.tick (encodeTxs (Model.mempool rho.inbox v t)) (e.adapter.sign (rho.ownKey v) t))
    else [] := by rfl

/-- The own admissions of a tick of `v` that is engine event `i`, right after its tick group. -/
noncomputable def tickTail (v : V) (i : Nat) (t : Time) : List (CutRec A) :=
  admitRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v) t i (admitsAt e rho v i)
    (postTick e rho e.adapter.sign v i t) 1

/-- `tickTail` unfolded. -/
theorem tickTail_eq (v : V) (i : Nat) (t : Time) : tickTail e rho v i t =
    admitRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v) t i (admitsAt e rho v i)
      (postTick e rho e.adapter.sign v i t) 1 := by rfl

/-- A tick's cuts are its public group, then its own admissions. -/
theorem eventCuts_tick_split {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) :
    eventCuts e rho i = tickGroup e rho i v t ++ tickTail e rho v i t := by
  rw [eventCuts_tick e rho i v t he]
  rfl

/-- A cut of a tick's own admissions is a cut of the `.attestation` group of an admitted
attestation, under the id `Nat.pair i s` with `1 ≤ s`. -/
theorem mem_tickTail {v : V} {i : Nat} {t : Time} {r : CutRec A}
    (hr : r ∈ tickTail e rho v i t) :
    ∃ a ∈ admitsAt e rho v i, ∃ (st : NodeState A) (s : Nat), 1 ≤ s ∧
      r ∈ groupRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v) st t (Nat.pair i s)
        (.attestation a) :=
  mem_admitRecs _ _ _ _ _ _ _ _ _ hr

/-- The stuttering ids beyond the replay are not the ids of engine events. -/
theorem event_none {l : Nat} (hr : (allCuts e rho)[l]? = none) {i s : Nat}
    (hi : i < rho.events.length) (hl : (simTrace e rho).event l = Nat.pair i s) : False := by
  rw [simTrace_event, hr, Option.elim_none, Nat.pair_eq_pair] at hl
  omega


/-- Where a replay cut sits within its engine event: a cut of a non-tick event (with that
event's id and node), a cut of a tick's public group, or a cut of the tick's own admissions. -/
theorem cut_classify {l : Nat} {r : CutRec A} (hr : (allCuts e rho)[l]? = some r) :
    ∃ i ev, rho.events[i]? = some ev ∧ cutMap e rho i ≤ l ∧ l < cutMap e rho (i + 1) ∧
      (eventCuts e rho i)[l - cutMap e rho i]? = some r ∧
      (((∀ v t, ev ≠ .tick v t) ∧ ∃ s, r.event = Nat.pair i s ∧ r.node = rho.ownKey ev.node) ∨
       (∃ v t, ev = .tick v t ∧ l - cutMap e rho i < (tickGroup e rho i v t).length ∧
          (tickGroup e rho i v t)[l - cutMap e rho i]? = some r) ∨
       (∃ v t, ev = .tick v t ∧ (tickGroup e rho i v t).length ≤ l - cutMap e rho i ∧
          (tickTail e rho v i t)[l - cutMap e rho i - (tickGroup e rho i v t).length]? =
            some r)) := by
  have hr' := hr
  rw [allCuts_eq] at hr'
  obtain ⟨i, hi, h1, h2, hidx⟩ := cut_event_range e rho _ _ _ hr'
  have he := List.getElem?_eq_getElem hi
  refine ⟨i, rho.events[i], he, h1, h2, hidx, ?_⟩
  have hm := List.mem_of_getElem? hidx
  cases hev : rho.events[i] with
  | tick v t =>
    rw [hev] at he
    right
    rw [eventCuts_tick_split e rho he] at hidx
    by_cases hlt : l - cutMap e rho i < (tickGroup e rho i v t).length
    · rw [List.getElem?_append_left hlt] at hidx
      exact Or.inl ⟨v, t, rfl, hlt, hidx⟩
    · rw [List.getElem?_append_right (by omega)] at hidx
      exact Or.inr ⟨v, t, rfl, by omega, hidx⟩
  | deliver v o t =>
    rw [hev] at he
    have hnode := (eventCut_node_time e rho he hm).2
    left
    refine ⟨fun _ _ h => (by cases h), ?_⟩
    have hm' := hm
    rw [eventCuts_deliver e rho i v o t he] at hm'
    obtain ⟨s, -, hs⟩ := deliverRecs_id _ _ _ _ _ _ _ _ _ _ hm'
    exact ⟨s, hs, hnode⟩
  | restart v t =>
    rw [hev] at he
    have hnode := (eventCut_node_time e rho he hm).2
    left
    refine ⟨fun _ _ h => (by cases h), ?_⟩
    have hm' := hm
    rw [eventCuts_restart e rho i v t he] at hm'
    exact ⟨0, (mem_groupRecs_fields _ _ _ _ _ _ _ hm').2.2.2, hnode⟩

/-- The id of an own-admission cut of event `i`. -/
private theorem tail_id {v : V} {i : Nat} {t : Time} {r : CutRec A}
    (hr : r ∈ tickTail e rho v i t) : ∃ s, 1 ≤ s ∧ r.event = Nat.pair i s := by
  obtain ⟨a, -, st, s, hs, hg⟩ := mem_tickTail e rho hr
  exact ⟨s, hs, (mem_groupRecs_fields _ _ _ _ _ _ _ hg).2.2.2⟩

/-- The id of a tick-group cut of event `i`. -/
private theorem group_id' {v : V} {i : Nat} {t : Time} {r : CutRec A}
    (hr : r ∈ tickGroup e rho i v t) : r.event = Nat.pair i 0 := by
  rw [tickGroup_eq] at hr
  split at hr
  · exact (mem_groupRecs_fields _ _ _ _ _ _ _ hr).2.2.2
  · cases hr

/-- Every cut with the id of a tick's public group lies in that group. -/
theorem range_of_id_tick {i l : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) (hl : (simTrace e rho).event l = Nat.pair i 0) :
    cutMap e rho i ≤ l ∧ l < cutMap e rho i + (tickGroup e rho i v t).length := by
  cases hr : (allCuts e rho)[l]? with
  | none => exact (event_none e rho hr (List.getElem?_eq_some_iff.1 he).1 hl).elim
  | some r =>
    rw [simTrace_event, hr, Option.elim_some] at hl
    obtain ⟨i', ev, he', h1, -, -, hc⟩ := cut_classify e rho hr
    rcases hc with ⟨hnt, s, hs, -⟩ | ⟨v', t', rfl, hm, hg⟩ | ⟨v', t', rfl, -, hs⟩
    · rw [hs, Nat.pair_eq_pair] at hl
      obtain ⟨rfl, -⟩ := hl
      rw [he] at he'
      exact absurd (Option.some.inj he').symm (hnt v t)
    · rw [group_id' e rho (List.mem_of_getElem? hg), Nat.pair_eq_pair] at hl
      obtain ⟨rfl, -⟩ := hl
      rw [he] at he'
      obtain ⟨rfl, rfl⟩ := Model.Event.tick.inj (Option.some.inj he')
      omega
    · obtain ⟨s, hs1, hid⟩ := tail_id e rho (List.mem_of_getElem? hs)
      rw [hid, Nat.pair_eq_pair] at hl
      omega

/-- Every cut with the id of a non-tick event lies in that event's cut range. -/
theorem range_of_id_other {i s l : Nat}
    {ev : Model.Event V (Model.protoOf (compiled F) E).Object}
    (he : rho.events[i]? = some ev) (hnt : ∀ v t, ev ≠ .tick v t)
    (hl : (simTrace e rho).event l = Nat.pair i s) :
    cutMap e rho i ≤ l ∧ l < cutMap e rho (i + 1) := by
  cases hr : (allCuts e rho)[l]? with
  | none => exact (event_none e rho hr (List.getElem?_eq_some_iff.1 he).1 hl).elim
  | some r =>
    rw [simTrace_event, hr, Option.elim_some] at hl
    obtain ⟨i', ev', he', h1, h2, -, hc⟩ := cut_classify e rho hr
    rcases hc with ⟨-, s', hs, -⟩ | ⟨v', t', rfl, -, hg⟩ | ⟨v', t', rfl, -, hs⟩
    · rw [hs, Nat.pair_eq_pair] at hl
      obtain ⟨rfl, -⟩ := hl
      exact ⟨h1, h2⟩
    · rw [group_id' e rho (List.mem_of_getElem? hg), Nat.pair_eq_pair] at hl
      obtain ⟨rfl, -⟩ := hl
      rw [he] at he'
      exact absurd (Option.some.inj he') (hnt v' t')
    · obtain ⟨s', -, hid⟩ := tail_id e rho (List.mem_of_getElem? hs)
      rw [hid, Nat.pair_eq_pair] at hl
      obtain ⟨rfl, -⟩ := hl
      rw [he] at he'
      exact absurd (Option.some.inj he') (hnt v' t')

/-- Every cut with an own-admission id `Nat.pair i s` (`1 ≤ s`) of tick event `i` lies in that
tick's own admissions. -/
theorem range_of_id_admit {i s l : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t)) (hs : 1 ≤ s)
    (hl : (simTrace e rho).event l = Nat.pair i s) :
    cutMap e rho i + (tickGroup e rho i v t).length ≤ l ∧ l < cutMap e rho (i + 1) := by
  cases hr : (allCuts e rho)[l]? with
  | none => exact (event_none e rho hr (List.getElem?_eq_some_iff.1 he).1 hl).elim
  | some r =>
    rw [simTrace_event, hr, Option.elim_some] at hl
    obtain ⟨i', ev', he', h1, h2, -, hc⟩ := cut_classify e rho hr
    rcases hc with ⟨hnt, s', hs', -⟩ | ⟨v', t', rfl, -, hg⟩ | ⟨v', t', rfl, hge, htl⟩
    · rw [hs', Nat.pair_eq_pair] at hl
      obtain ⟨rfl, -⟩ := hl
      rw [he] at he'
      exact absurd (Option.some.inj he').symm (hnt v t)
    · rw [group_id' e rho (List.mem_of_getElem? hg), Nat.pair_eq_pair] at hl
      omega
    · obtain ⟨s', -, hid⟩ := tail_id e rho (List.mem_of_getElem? htl)
      rw [hid, Nat.pair_eq_pair] at hl
      obtain ⟨rfl, -⟩ := hl
      rw [he] at he'
      obtain ⟨rfl, rfl⟩ := Model.Event.tick.inj (Option.some.inj he')
      omega

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace
