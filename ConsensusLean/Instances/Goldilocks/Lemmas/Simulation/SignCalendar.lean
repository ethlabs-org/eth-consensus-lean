module
public import ConsensusLean.Instances.Goldilocks.Results.Spec.CanonicalTrace
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Model
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Cuts

public section

/-! # The canonical trace follows its signing calendar

The canonical trace under a signing calendar `due` (`simTraceWith`) replays each public engine
tick of `y` at `t` as the node's tick with `fgDue = due y t`. Every tick group of the trace,
read with the trace's own proposer and digest, carries exactly that flag
(`simTraceWith_signCalendar`): no other group starts with `ac_on_tick`, and a tick group
contains `ac_to_fg` exactly when it signs. The proof reads only the shape of the replay, not
the engine run's validity. The canonical trace runs the adapter's calendar
(`simTrace_signCalendar`; for Goldilocks, the setup's calendar `S.sign`,
`simTraceAt_signCalendar`). -/

namespace Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

open Blocks Shape Node

section Cuts

variable {Q : Params} {N : NodeAC Q}

/-- A cut that is the AC call `ac_on_tick` or `ac_to_fg`. -/
private def TickOrUpdate (c : Cut N) : Prop :=
  ∃ ℓ : ACLabel N, c = .ac ℓ ∧ (ℓ.call = .tick ∨ ℓ.call = .toFG)

/-- Only a tick makes the AC calls `ac_on_tick` and `ac_to_fg`. -/
private theorem tick_of_tickOrUpdate (pr : Nat → Fin Q.n)
    (dg : Digest (List (FG.Att Q.n)) N.Payload) (y : Fin Q.n) (st : NodeState N) (t : Time)
    (ev : Node.Event N) {c : Cut N}
    (hc : c ∈ (exec pr dg y st t ev).2) (h : TickOrUpdate c) : ∃ x b, ev = .tick x b := by
  obtain ⟨ℓ, rfl, hcall⟩ := h
  cases ev with
  | tick x b => exact ⟨x, b, rfl⟩
  | block B =>
    simp only [exec, onBlock] at hc
    split_ifs at hc
    · cases hc
    · split at hc
      · simp at hc
      · simp only [acCall, List.mem_cons, reduceCtorEq, false_or, List.not_mem_nil, or_false,
          Cut.ac.injEq] at hc
        subst hc
        rcases hcall with h | h <;> cases h
  | message m =>
    simp only [exec, onMessage, acCall, List.mem_singleton, Cut.ac.injEq] at hc
    subst hc
    rcases hcall with h | h <;> cases h
  | attestation a => simp [exec, onAttestation] at hc
  | restart =>
    simp only [exec, Node.restart, acCall, List.mem_singleton, Cut.ac.injEq] at hc
    subst hc
    rcases hcall with h | h <;> cases h

/-- The cuts of a tick start with `ac_on_tick` and contain `ac_to_fg` exactly when it signs. -/
private theorem tick_cuts (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload)
    (y : Fin Q.n) (st : NodeState N) (t : Time) (x : Nat) (b : Bool) :
    (∃ ℓ : ACLabel N, ℓ.call = .tick ∧ ∃ cs, (exec pr dg y st t (.tick x b)).2 = .ac ℓ :: cs) ∧
      ((∃ ℓ : ACLabel N, .ac ℓ ∈ (exec pr dg y st t (.tick x b)).2 ∧ ℓ.call = .toFG) ↔
        b = true) := by
  obtain ⟨ℓ, pc, uc, hℓ, hcs, hpc, huc⟩ := Compose.tick_order pr dg y st t x b
  refine ⟨⟨ℓ, hℓ, _, hcs⟩, ?_⟩
  change (∃ ℓ' : ACLabel N, .ac ℓ' ∈ (onTick pr dg y st t x b).2 ∧ ℓ'.call = .toFG) ↔ _
  rw [hcs]
  have hp : ∀ ℓ' : ACLabel N, Cut.ac ℓ' ∈ pc → ℓ'.call ≠ .toFG := by
    intro ℓ' hm hc
    rcases hpc with ⟨-, rfl⟩ | ⟨-, ℓp, hℓp, hpc⟩
    · cases hm
    · rcases hpc with rfl | ⟨B, -, -, rfl | ⟨ℓb, hℓb, rfl⟩⟩ <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false, Cut.ac.injEq, reduceCtorEq,
          false_or] at hm <;>
        first
        | (subst hm; rw [hℓp] at hc; cases hc)
        | (rcases hm with rfl | rfl
           · rw [hℓp] at hc; cases hc
           · rw [hℓb] at hc; cases hc)
  constructor
  · rintro ⟨ℓ', hm, hc⟩
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at huc
      subst huc
      rcases List.mem_cons.mp hm with h | h
      · cases h; rw [hℓ] at hc; cases hc
      · exact absurd hc (hp ℓ' (by simpa using h))
    · rfl
  · rintro rfl
    obtain ⟨ℓu, hℓu, huc⟩ := huc
    refine ⟨ℓu, List.mem_cons_of_mem _ (List.mem_append_right _ ?_), hℓu⟩
    rcases huc with rfl | ⟨C, rfl⟩ | ⟨C, a, rfl⟩ <;> simp

/-- Each handler cut has one post-state. -/
private theorem cutPosts_length (y : Fin Q.n) (t : Time) (cs : List (Cut N)) (st : NodeState N) :
    (cutPosts y t cs st).length = cs.length := by
  induction cs generalizing st with
  | nil => rw [cutPosts_nil]; rfl
  | cons c cs ih => rw [cutPosts_cons, List.length_cons, ih, List.length_cons]

/-- A cut of a handler group records the group's node, time, id and one of its handler cuts. -/
private theorem mem_groupRecs (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload)
    (y : Fin Q.n) (st : NodeState N) (t : Time) (id : Nat) (ev : Node.Event N)
    {r : CutRec N} (hr : r ∈ groupRecs pr dg y st t id ev) :
    r.node = y ∧ r.time = t ∧ r.event = id ∧ r.label ∈ (exec pr dg y st t ev).2 := by
  rw [groupRecs_eq] at hr
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
  rw [List.getElem_mapIdx, List.getElem_zip]
  exact ⟨rfl, rfl, rfl, List.getElem_mem _⟩

/-- A delivery cut is a handler cut of one of the delivered objects' events. -/
private theorem mem_deliverRecs {I K B : Type} [DecidableEq I] (C : WireCodec N K I B)
    (pr : Nat → Fin Q.n) (dg : Digest (List (FG.Att Q.n)) N.Payload) (hs : List (Header I × Nat))
    (y : Fin Q.n) (t : Time) (i : Nat) (os : List (ShapeObj Q.n K I B)) (st : NodeState N)
    (sub : Nat) {r : CutRec N} (hr : r ∈ deliverRecs C pr dg hs y t i os st sub) :
    ∃ w ev st', canonEvent C hs w = some ev ∧ r.label ∈ (exec pr dg y st' t ev).2 := by
  induction os generalizing st sub with
  | nil => rw [deliverRecs_nil] at hr; cases hr
  | cons w os ih =>
    rw [deliverRecs_cons] at hr
    cases hw : canonEvent C hs w with
    | none => rw [hw] at hr; exact ih _ _ hr
    | some ev =>
      rw [hw] at hr
      rcases List.mem_append.mp hr with hr | hr
      · exact ⟨w, ev, st, hw, (mem_groupRecs _ _ _ _ _ _ _ hr).2.2.2⟩
      · exact ih _ _ hr

/-- The `m`-th cut of a handler group has the group's `m`-th handler cut as its label. -/
private theorem groupRecs_getElem? (pr : Nat → Fin Q.n)
    (dg : Digest (List (FG.Att Q.n)) N.Payload) (y : Fin Q.n) (st : NodeState N) (t : Time)
    (id : Nat) (ev : Node.Event N) (m : Nat) :
    ((groupRecs pr dg y st t id ev)[m]?).map CutRec.label = (exec pr dg y st t ev).2[m]? := by
  rw [groupRecs_eq]
  simp only [List.getElem?_mapIdx, Option.map_map]
  rcases Nat.lt_or_ge m (exec pr dg y st t ev).2.length with hm | hm
  · rw [List.getElem?_eq_getElem (by simp [cutPosts_length, hm]), List.getElem?_eq_getElem hm]
    simp
  · rw [List.getElem?_eq_none hm, List.getElem?_eq_none (by simp [cutPosts_length]; omega)]
    rfl

end Cuts

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
variable {O : OutputSchema} {I : Type} [DecidableEq I] [Countable I]
variable {F : ChainShapeFamily O I} {p : Params} {hN : p.n = Fintype.card V}
variable {hn : 1 ≤ Fintype.card V}
variable {A : NodeAC (paramsAtCount p (Fintype.card V) hN hn)} (e : Encoding F E p hN hn A)
variable (rho : Model.Run (compiled F) E) (due : Fin (Fintype.card V) → Time → Bool)

/-- The replay of the first `n` engine events has `cutMapWith n` cuts. -/
private theorem prefix_length (n : Nat) :
    ((List.range n).flatMap (eventCutsWith e rho due)).length = cutMapWith e rho due n := by
  induction n with
  | zero => rw [cutMapWith_zero]; rfl
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.length_append, ih, cutMapWith_succ]

/-- A replayed cut lies in the cuts of one engine event, at its offset from the event's start. -/
private theorem cut_range {k : Nat} {r : CutRec A} (hr : (allCutsWith e rho due)[k]? = some r) :
    ∃ i < rho.events.length, cutMapWith e rho due i ≤ k ∧
      (eventCutsWith e rho due i)[k - cutMapWith e rho due i]? = some r := by
  rw [allCutsWith_eq] at hr
  generalize rho.events.length = n at hr ⊢
  induction n with
  | zero => simp at hr
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil] at hr
    by_cases hk : k < ((List.range n).flatMap (eventCutsWith e rho due)).length
    · rw [List.getElem?_append_left hk] at hr
      obtain ⟨i, hi, hstart, hm⟩ := ih hr
      exact ⟨i, by omega, hstart, hm⟩
    · rw [List.getElem?_append_right (Nat.le_of_not_gt hk)] at hr
      rw [prefix_length] at hr hk
      exact ⟨n, Nat.lt_succ_self _, by omega, hr⟩

/-- The `m`-th cut of engine event `i` is replayed at `cutMapWith i + m`. -/
private theorem getElem?_add {i m : Nat} (hi : i < rho.events.length)
    (hm : m < (eventCutsWith e rho due i).length) :
    (allCutsWith e rho due)[cutMapWith e rho due i + m]? = (eventCutsWith e rho due i)[m]? := by
  rw [allCutsWith_eq]
  generalize rho.events.length = n at hi ⊢
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · have hmono : cutMapWith e rho due (i + 1) ≤ cutMapWith e rho due n :=
        (monotone_nat_of_le_succ fun j => by
          rw [cutMapWith_succ]; exact Nat.le_add_right _ _)
          (Nat.succ_le_of_lt hi)
      have hsucc := cutMapWith_succ e rho due i
      rw [List.getElem?_append_left (by rw [prefix_length]; omega), ih hi]
    · rw [List.getElem?_append_right (by rw [prefix_length]; omega), prefix_length,
        Nat.add_sub_cancel_left]

/-- A replayed `ac_on_tick` or `ac_to_fg` cut comes from a public engine tick: it is a cut of the
node's tick with the calendar's flag, under the id `⟨i, 0⟩`, the group the event's cuts begin
with. -/
private theorem tick_source {i : Nat} {r : CutRec A} (hr : r ∈ eventCutsWith e rho due i)
    (hc : TickOrUpdate r.label) :
    ∃ v t T, rho.events[i]? = some (.tick v t) ∧
      eventCutsWith e rho due i = groupRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
        (e.adapter.node (stateAt e rho v i)) t (Nat.pair i 0)
        (.tick (encodeTxs (Model.mempool rho.inbox v t)) (due (rho.ownKey v) t)) ++ T ∧
      r ∈ groupRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
        (e.adapter.node (stateAt e rho v i)) t (Nat.pair i 0)
        (.tick (encodeTxs (Model.mempool rho.inbox v t)) (due (rho.ownKey v) t)) := by
  cases he : rho.events[i]? with
  | none => rw [eventCutsWith_none e rho due i he] at hr; cases hr
  | some ev =>
    cases ev with
    | tick v t =>
      have hE := eventCutsWith_tick e rho due i v t he
      rw [hE] at hr
      rcases List.mem_append.mp hr with hr | hr
      · by_cases hp : (paramsAtCount p (Fintype.card V) hN hn).IsPublic t
        · simp only [hp, ↓reduceIte] at hr
          refine ⟨v, t, admitRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v) t i
            (admitsAt e rho v i) (postTick e rho due v i t) 1, rfl, ?_, hr⟩
          rw [hE]
          simp only [hp, ↓reduceIte]
        · simp only [hp, ↓reduceIte] at hr
          exact absurd hr List.not_mem_nil
      · obtain ⟨a, -, st, s, -, hg⟩ := mem_admitRecs _ _ _ _ _ _ _ _ _ hr
        obtain ⟨-, -, -, hl⟩ := mem_groupRecs _ _ _ _ _ _ _ hg
        obtain ⟨x, b, h⟩ := tick_of_tickOrUpdate _ _ _ _ _ _ hl hc
        cases h
    | restart v t =>
      rw [eventCutsWith_restart e rho due i v t he] at hr
      obtain ⟨-, -, -, hl⟩ := mem_groupRecs _ _ _ _ _ _ _ hr
      obtain ⟨_, _, h⟩ := tick_of_tickOrUpdate _ _ _ _ _ _ hl hc
      cases h
    | deliver v o t =>
      rw [eventCutsWith_deliver e rho due i v o t he] at hr
      obtain ⟨w, ev, st', hcanon, hl⟩ := mem_deliverRecs _ _ _ _ _ _ _ _ _ _ hr
      obtain ⟨_, _, rfl⟩ := tick_of_tickOrUpdate _ _ _ _ _ _ hl hc
      unfold canonEvent at hcanon
      split at hcanon <;> cases hcanon

/-- **The canonical trace follows its calendar**: every tick group of the trace under the
signing calendar `due` (with the trace's proposer and digest) is a tick of `y` at `t` with
`fgDue = due y t`, for every honest set. -/
theorem simTraceWith_signCalendar (H : Time → Set (Fin (Fintype.card V))) :
    (simTraceWith e rho due).SignCalendarAt (runProposer rho hn) (digestOf e rho) H due := by
  intro y j t x b _ hg
  obtain ⟨hne, hcuts, hrange⟩ := hg
  obtain ⟨⟨ℓ, hℓ, cs₀, hcs⟩, hiff⟩ := tick_cuts (runProposer rho hn) (digestOf e rho) y
    ((simTraceWith e rho due).state y j) t x b
  -- the first cut of the group is the engine tick `i` of `y` at `t`
  have h0 := hcuts 0 (by rw [hcs]; simp)
  obtain ⟨hy, ht, -, -, hl⟩ := h0
  rw [Nat.add_zero] at hy ht hl
  rw [(simTraceWith_fields e rho due j).2.2.2] at hl
  obtain ⟨r, hr, hrl⟩ := Option.map_eq_some_iff.mp hl
  obtain ⟨i, hi, hji, hri⟩ := cut_range e rho due hr
  have hrm := List.mem_of_getElem? hri
  have hlab : r.label = .ac ℓ := by
    rw [hrl]; simp only [hcs, List.getElem_cons_zero]
  obtain ⟨v, t', T, he, hEC, hrG⟩ := tick_source e rho due hrm ⟨ℓ, hlab, Or.inl hℓ⟩
  obtain ⟨hrn, hrt, hre, -⟩ := mem_groupRecs _ _ _ _ _ _ _ hrG
  rw [(simTraceWith_fields e rho due j).1] at hy
  rw [(simTraceWith_fields e rho due j).2.1] at ht
  rw [hr, Option.elim_some, hrn] at hy
  rw [hr, Option.elim_some, hrt] at ht
  subst hy ht
  have hej : (simTraceWith e rho due).event j = Nat.pair i 0 := by
    rw [(simTraceWith_fields e rho due j).2.2.1, hr, Option.elim_some, hre]
  have hiff' := (tick_cuts (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
    (e.adapter.node (stateAt e rho v i)) t' (encodeTxs (Model.mempool rho.inbox v t'))
    (due (rho.ownKey v) t')).2
  cases hb : b <;> cases hd : due (rho.ownKey v) t'
  · rfl
  · -- the group does not sign, but the engine tick's cuts contain `ac_to_fg`
    obtain ⟨ℓu, hmu, hℓu⟩ := hiff'.mpr hd
    obtain ⟨m, hm, hmeq⟩ := List.getElem_of_mem hmu
    have hmG : m < (groupRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
        (e.adapter.node (stateAt e rho v i)) t' (Nat.pair i 0)
        (.tick (encodeTxs (Model.mempool rho.inbox v t')) (due (rho.ownKey v) t'))).length := by
      rw [groupRecs_eq]; simpa [cutPosts_length] using hm
    have hlen : m < (eventCutsWith e rho due i).length := by
      rw [hEC, List.length_append]; omega
    have hk := getElem?_add e rho due hi hlen
    obtain ⟨r', hr'⟩ : ∃ r', (allCutsWith e rho due)[cutMapWith e rho due i + m]? = some r' :=
      ⟨_, hk.trans (List.getElem?_eq_getElem hlen)⟩
    have hr'm : r' ∈ groupRecs (runProposer rho hn) (digestOf e rho) (rho.ownKey v)
        (e.adapter.node (stateAt e rho v i)) t' (Nat.pair i 0)
        (.tick (encodeTxs (Model.mempool rho.inbox v t')) (due (rho.ownKey v) t')) := by
      rw [hk, hEC, List.getElem?_append_left hmG] at hr'; exact List.mem_of_getElem? hr'
    have hevk : (simTraceWith e rho due).event (cutMapWith e rho due i + m) =
        (simTraceWith e rho due).event j := by
      rw [hej, (simTraceWith_fields e rho due _).2.2.1, hr', Option.elim_some,
        (mem_groupRecs _ _ _ _ _ _ _ hr'm).2.2.1]
    obtain ⟨hlo, hhi⟩ := hrange _ hevk
    obtain ⟨-, -, -, -, hlk⟩ := hcuts (cutMapWith e rho due i + m - j) (by omega)
    rw [Nat.add_sub_cancel' hlo] at hlk
    rw [(simTraceWith_fields e rho due _).2.2.2] at hlk
    have hlab' : ((allCutsWith e rho due)[cutMapWith e rho due i + m]?).map CutRec.label =
        some (.ac ℓu) := by
      rw [hk, hEC, List.getElem?_append_left hmG, groupRecs_getElem?,
        List.getElem?_eq_getElem hm, hmeq]
    rw [hlab', Option.some.injEq] at hlk
    have := hiff.mp ⟨ℓu, hlk ▸ List.getElem_mem _, hℓu⟩
    rw [hb] at this
    cases this
  · -- the group signs, but the engine tick's cuts contain no `ac_to_fg`
    obtain ⟨ℓu, hmu, hℓu⟩ := hiff.mpr hb
    obtain ⟨m, hm, hmeq⟩ := List.getElem_of_mem hmu
    obtain ⟨-, -, hev, -, hlm⟩ := hcuts m hm
    rw [(simTraceWith_fields e rho due _).2.2.2] at hlm
    obtain ⟨r', hr', hr'l⟩ := Option.map_eq_some_iff.mp hlm
    obtain ⟨i', -, -, hri'⟩ := cut_range e rho due hr'
    have hr'm := List.mem_of_getElem? hri'
    have hr'lab : r'.label = .ac ℓu := by rw [hr'l]; exact hmeq
    obtain ⟨v', t'', T', he', -, hr'G⟩ := tick_source e rho due hr'm ⟨ℓu, hr'lab, Or.inr hℓu⟩
    obtain ⟨-, -, hre', hl'⟩ := mem_groupRecs _ _ _ _ _ _ _ hr'G
    have hii : i' = i := by
      have h1 : (simTraceWith e rho due).event (j + m) = Nat.pair i' 0 := by
        rw [(simTraceWith_fields e rho due _).2.2.1, hr', Option.elim_some, hre']
      rw [hev, hej] at h1
      exact (Nat.pair_eq_pair.mp h1).1.symm
    subst hii
    rw [he] at he'
    obtain ⟨rfl, rfl⟩ : v = v' ∧ t' = t'' := by
      cases he'; exact ⟨rfl, rfl⟩
    have := hiff'.mp ⟨ℓu, hr'lab ▸ hl', hℓu⟩
    rw [hd] at this
    cases this
  · rfl

/-- The canonical trace follows the adapter's signing calendar. -/
theorem simTrace_signCalendar (H : Time → Set (Fin (Fintype.card V))) :
    (simTrace e rho).SignCalendarAt (runProposer rho hn) (digestOf e rho) H e.adapter.sign :=
  simTrace_eq_with e rho ▸ simTraceWith_signCalendar e rho _ H

end Consensus.Goldilocks.NodeAsChainShape.CanonicalTrace

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- The Goldilocks canonical trace follows the setup's signing calendar, for every honest set. -/
theorem simTraceAt_signCalendar (H : Time → Set (Fin (Fintype.card V))) :
    (simTraceAt S rho hn).SignCalendarAt (runProposer S rho hn) (digestOf S rho) H
      (S.sign (pubOf E)) := by
  obtain ⟨hpr, hdg⟩ := runProposer_digestOf S rho hn
  rw [simTraceAt_eq, (simTrace_encoding S rho hn).1, hpr, hdg]
  have h := NodeAsChainShape.CanonicalTrace.simTrace_signCalendar (traceEncoding S hn) rho H
  rwa [traceEncoding_adapter_sign] at h

end Consensus.Goldilocks.Simulation
