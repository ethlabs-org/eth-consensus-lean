module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunSimulates
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.WireGroup

public section

/-! # Goldilocks Simulation: the simulating trace is a run

Groups, the cut law and the wire checks complete `simTrace_goldilocksRun`, using the schedule
and credentials of `RunSchedule`, the cut blocks of `RunBlocks` and the engine/trace
correspondence of `RunSimulates`. `Simulation` assembles the full `EngineSimulatesNode`. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)
open SA (SAParams ReplayOrder Vote Payload blockVotes)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : BoundSetup)
  (rho : Model.Run (compiled (goldilocksWith S)) E) (hn : 1 ≤ Fintype.card V)

/-! ## `LocalRun`: groups, the cut law and the wire checks

A labelled cut of an honest node lies in a block of records of one handler call (`groupRecs`)
that starts at the trace's state (`recBlock_of_cut`), and in a group of the trace
(`group_of_cut`): an engine tick at a public time and a restart are one group, a delivery is a
`DeliverSeq` of groups of canonical objects. The cut law at such a cut is the handler's cut chain
(C0.5); a delivered event passes the wire checks because it is `canonEvent` of a delivered object
(the checks `decodeBlock` and `decodeAttObj` make, and the engine's digests), and the first cut of
a handler names its event (the engine-free facts: `deliverSeq_cover`, `cutStep_of_cutChain`,
`Relay`, and `wireOK_of_delivered`, `wireOK_of_group_cut` of `WireGroup`). -/

/-- Across a block of group records starting at the trace's state, the trace's state is the
fold of the handler's first cuts. -/
private theorem state_in_group
    (proposer : Nat → Fin (S.params (pubOf E) hn).n)
    (dg : Digest (List (FG.Att (S.params (pubOf E) hn).n)) (Payload (S.params (pubOf E) hn).n))
    {y : Fin (S.params (pubOf E) hn).n} {j0 : Nat}
    {st : NodeState (goldilocksNode (S.params (pubOf E) hn) (S.ro _))} {t : Time} {id : Nat}
    {e : Event (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    (hcut : ∀ k < (groupRecs proposer dg y st t id e).length,
      (allCuts S rho hn)[j0 + k]? = (groupRecs proposer dg y st t id e)[k]?)
    (h0 : (simTrace S rho hn).state y j0 = st) :
    ∀ k ≤ (exec proposer dg y st t e).2.length,
      (simTrace S rho hn).state y (j0 + k) =
        ((exec proposer dg y st t e).2.take k).foldl (cutPost y t) st := by
  intro k
  induction k with
  | zero => intro _; simpa using h0
  | succ k ih =>
    intro hk
    have hk' : k < (groupRecs proposer dg y st t id e).length := by
      rw [length_groupRecs]; omega
    have hr := hcut k hk'
    rw [List.getElem?_eq_getElem hk'] at hr
    obtain ⟨hnode, -, -, -, -⟩ := getElem_groupRecs proposer dg y st t id e k hk'
    change (simTrace S rho hn).state y (j0 + k).succ = _
    rw [Trace.state.eq_2, ite_eq_left, simTrace_post, hr, Option.elim_some,
      getElem_groupRecs_post, cutPosts_getElem]
    rw [simTrace_node, hr, Option.elim_some, hnode, simTrace_label, hr]
    simp

/-- A cut of a delivery's records lies in the records of one handler call, starting at the
trace's state. -/
private theorem recBlock_of_deliverRecs
    (proposer : Nat → Fin (S.params (pubOf E) hn).n)
    (dg : Digest (List (FG.Att (S.params (pubOf E) hn).n)) (Payload (S.params (pubOf E) hn).n))
    {y : Fin (S.params (pubOf E) hn).n} {t : Time} {i : Nat}
    (hs : List (Header Info × Nat)) (os : List (Wire (S.params (pubOf E) hn).n S.vote)) :
    ∀ (j0 sub : Nat) (st : NodeState (goldilocksNode (S.params (pubOf E) hn) (S.ro _))),
    (∀ k < (deliverRecs proposer dg hs y t i os st sub).length,
      (allCuts S rho hn)[j0 + k]? = (deliverRecs proposer dg hs y t i os st sub)[k]?) →
    (simTrace S rho hn).state y j0 = st →
    ∀ k < (deliverRecs proposer dg hs y t i os st sub).length,
      ∃ j1 st' id e, (∀ m < (groupRecs proposer dg y st' t id e).length,
        (allCuts S rho hn)[j1 + m]? = (groupRecs proposer dg y st' t id e)[m]?) ∧
        (simTrace S rho hn).state y j1 = st' ∧ j1 ≤ j0 + k ∧
        j0 + k < j1 + (groupRecs proposer dg y st' t id e).length := by
  induction os with
  | nil => intro j0 sub st _ _ k hk; simp [deliverRecs_nil] at hk
  | cons o os ih =>
    intro j0 sub st hcut h0 k hk
    cases he : canonEvent (S.params (pubOf E) hn) (S.ro _) hs o with
    | none =>
      rw [deliverRecs_cons_none _ _ _ _ _ _ _ _ _ _ he] at hcut hk
      exact ih j0 (sub + 1) st hcut h0 k hk
    | some e =>
      rw [deliverRecs_cons_some _ _ _ _ _ _ _ _ _ _ e he] at hcut hk
      rw [List.length_append] at hk
      have hcutg : ∀ m < (groupRecs proposer dg y st t (Nat.pair i sub) e).length,
          (allCuts S rho hn)[j0 + m]? = (groupRecs proposer dg y st t (Nat.pair i sub) e)[m]? :=
        fun m hm => by
          rw [hcut m (by rw [List.length_append]; omega), List.getElem?_append_left hm]
      by_cases hkg : k < (groupRecs proposer dg y st t (Nat.pair i sub) e).length
      · exact ⟨j0, st, _, e, hcutg, h0, by omega, by omega⟩
      · obtain ⟨j1, st', id, e', h2, h3, h4, h5⟩ :=
          ih (j0 + (groupRecs proposer dg y st t (Nat.pair i sub) e).length) (sub + 1) _
            (fun m hm => by
              rw [Nat.add_assoc, hcut _ (by rw [List.length_append]; omega),
                List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left])
            (state_of_group S rho hn proposer dg hcutg h0)
            (k - (groupRecs proposer dg y st t (Nat.pair i sub) e).length) (by omega)
        exact ⟨j1, st', id, e', h2, h3, by omega, by omega⟩

omit [DecidableEq V] in
/-- The engine event of a labelled cut of an honest key is an event of an honest node. -/
private theorem honest_of_cut {y : Fin (Fintype.card V)} (hy : y ∈ honestKeys S rho)
    {ev : Model.Event V (Model.protoOf (compiled (goldilocksWith S)) E).Object}
    (h : rho.ownKey ev.node = y) : ev.node ∉ rho.faultyAt 0 := by
  rw [key_of_ownKey S rho h]
  exact (mem_honestKeys_iff S rho y).mp hy

/-- A labelled cut of an honest node lies in the records of one handler call, starting at the
trace's state. -/
private theorem recBlock_of_cut (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)}
    (hy : y ∈ honestKeys S rho) {k : Nat} (hnode : (simTrace S rho hn).node k = y)
    (hl : (simTrace S rho hn).label k ≠ none) :
    ∃ j1 st t id e, (∀ m < (groupRecs (runProposer S rho hn) (digestOf S rho) y st t id e).length,
        (allCuts S rho hn)[j1 + m]? =
          (groupRecs (runProposer S rho hn) (digestOf S rho) y st t id e)[m]?) ∧
      (simTrace S rho hn).state y j1 = st ∧ j1 ≤ k ∧
      k < j1 + (groupRecs (runProposer S rho hn) (digestOf S rho) y st t id e).length := by
  obtain ⟨r, i, ev, -, he, h1, h2, -, hn', -, -, -⟩ := simTrace_cut S rho hn hl
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  have hv' := honest_of_cut S rho hy (hn'.symm.trans hnode)
  have hcut : ∀ m < (eventCuts S rho hn i).length,
      (allCuts S rho hn)[cutMap S rho hn i + m]? = (eventCuts S rho hn i)[m]? :=
    fun m hm => allCuts_getElem?_add S rho hn i m hi hm
  have hlen := cutMap_succ S rho hn i
  have h0 := (simTrace_state S rho hn hf hv ev.node hv' i hi.le).symm
  have hy' := hn'.symm.trans hnode
  cases ev with
  | tick v t =>
    change rho.ownKey v = y at hy'
    subst hy'
    by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
    · rw [eventCuts_tick_public S rho hn i v t he hp] at hcut hlen
      exact ⟨_, _, t, _, _, hcut, h0, h1, by omega⟩
    · rw [eventCuts_tick_other S rho hn i v t he hp, List.length_nil] at hlen
      omega
  | deliver v o t =>
    change rho.ownKey v = y at hy'
    subst hy'
    rw [eventCuts_deliver S rho hn i v o t he] at hcut hlen
    obtain ⟨j1, st', id, e, h3, h4, h5, h6⟩ := recBlock_of_deliverRecs S rho hn _ _ _ _ _ 0 _
      hcut h0 (k - cutMap S rho hn i) (by omega)
    exact ⟨j1, st', t, id, e, h3, h4, by omega, by omega⟩
  | restart v t =>
    change rho.ownKey v = y at hy'
    subst hy'
    rw [eventCuts_restart S rho hn i v t he] at hcut hlen
    exact ⟨_, _, t, _, _, hcut, h0, h1, by omega⟩

/-- A labelled cut of an honest node lies in a group of the trace whose event passes the wire
checks. -/
private theorem group_of_cut (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)}
    (hy : y ∈ honestKeys S rho) {k : Nat} (hnode : (simTrace S rho hn).node k = y)
    (hl : (simTrace S rho hn).label k ≠ none) :
    ∃ j0 t e,
      (simTrace S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho) y j0 t e ∧ j0 ≤ k ∧
      k < j0 + (Node.exec (runProposer S rho hn) (digestOf S rho)
        y ((simTrace S rho hn).state y j0) t e).2.length ∧
      WireOK (digestOf S rho) e := by
  obtain ⟨r, i, ev, -, he, h1, h2, -, hn', -, -, -⟩ := simTrace_cut S rho hn hl
  have hv' := honest_of_cut S rho hy (hn'.symm.trans hnode)
  have hy' := hn'.symm.trans hnode
  cases ev with
  | tick v t =>
    change rho.ownKey v = y at hy'
    subst hy'
    by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
    · obtain ⟨hg, hlen⟩ := simTrace_tick_public_group S rho hn hf hv v hv' i t he hp
      exact ⟨_, t, _, hg, h1, by omega, trivial⟩
    · have := simTrace_tick_other S rho hn hv v hv' i t he hp
      omega
  | deliver v o t =>
    change rho.ownKey v = y at hy'
    subst hy'
    obtain ⟨-, hcov⟩ := deliverSeq_cover (simTrace_deliver S rho hn hf hv v hv' i o t he)
    obtain ⟨j0, e, o', ho, hce, hg, h3, h4⟩ := hcov k h1 h2
    exact ⟨j0, t, e, hg, h3, h4, wireOK_of_delivered S rho hn o ho hce⟩
  | restart v t =>
    change rho.ownKey v = y at hy'
    subst hy'
    obtain ⟨hg, hlen⟩ := simTrace_restart S rho hn hf hv v hv' i t he
    exact ⟨_, t, _, hg, h1, by omega, trivial⟩

/-- Every labelled cut of an honest node lies in the group of a top-level event. -/
theorem simTrace_grouped (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i c, (simTrace S rho hn).CallAt y i c →
      ∃ j e, (simTrace S rho hn).InGroup (runProposer S rho hn)
        (digestOf S rho) y j i ((simTrace S rho hn).time i) e := by
  rintro y hy i c ⟨hnode, hlab⟩
  obtain ⟨j0, t, e, hg, h1, h2, -⟩ := group_of_cut S rho hn hf hv hy hnode (by rw [hlab]; simp)
  have ht : (simTrace S rho hn).time i = t := by
    have := (hg.2.1 (i - j0) (by omega)).2.1
    rwa [Nat.add_sub_cancel' h1] at this
  rw [ht]
  exact ⟨j0, e, hg, h1, h2⟩

/-- Every labelled cut of an honest node obeys the cut law: the handler's cut chain (C0.5). -/
theorem simTrace_cutLaw (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ i c, (simTrace S rho hn).CallAt y i c →
      CutStep y ((simTrace S rho hn).time i) ((simTrace S rho hn).state y i) c
        ((simTrace S rho hn).post i) := by
  rintro y hy i c ⟨hnode, hlab⟩
  obtain ⟨j1, st, t, id, e, hcut, h0, h1, h2⟩ :=
    recBlock_of_cut S rho hn hf hv hy hnode (by rw [hlab]; simp)
  obtain ⟨m, rfl⟩ : ∃ m, i = j1 + m := ⟨i - j1, by omega⟩
  have hm : m < (groupRecs (runProposer S rho hn) (digestOf S rho) y st t id e).length := by omega
  have hm' : m < (exec (runProposer S rho hn) (digestOf S rho) y st t e).2.length := by
    have := length_groupRecs (runProposer S rho hn) (digestOf S rho) y st t id e
    omega
  have hr := hcut m hm
  rw [List.getElem?_eq_getElem hm] at hr
  obtain ⟨-, htime, -, -, hlabel⟩ := getElem_groupRecs _ _ y st t id e m hm
  rw [simTrace_label, hr, Option.map_some, hlabel, Option.some.injEq] at hlab
  subst hlab
  rw [simTrace_time, hr, Option.elim_some, htime, simTrace_post, hr, Option.elim_some,
    getElem_groupRecs_post (runProposer S rho hn) (digestOf S rho) y st t id e m hm]
  have hch :
      CutChain y t st (exec (runProposer S rho hn) (digestOf S rho) y st t e).2
        (exec (runProposer S rho hn) (digestOf S rho) y st t e).1 :=
    Compose.exec_is_cut_chain (P := (S.params (pubOf E) hn).toParams)
      (A := goldilocksNode (S.params (pubOf E) hn) (S.ro _))
      (runProposer S rho hn) (digestOf S rho) y st t e
  have key := cutStep_of_cutChain hch m hm'
  have e1 := cutPosts_getElem y t (exec (runProposer S rho hn) (digestOf S rho) y st t e).2 st m
    (by have := length_cutPosts y t (exec (runProposer S rho hn) (digestOf S rho) y st t e).2 st
        omega)
  rw [state_in_group S rho hn _ _ hcut h0 m hm'.le, e1]
  exact key

/-- A group of an honest node passes the wire checks: its first cut is a cut of an engine event's
group, which starts there, and names the same event (up to a tick's input). -/
theorem simTrace_wire (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid) :
    ∀ y ∈ honestKeys S rho, ∀ j t e,
      (simTrace S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho) y j t e →
      WireOK (digestOf S rho) e := by
  intro y hy j t e hg
  exact wireOK_of_group_cut hg (group_of_cut S rho hn hf hv hy)

/-! ## The trace is a Goldilocks run -/

/-- **The simulating trace is a Goldilocks run** at the engine's digest, for the honest keys.
Stated over the population binding `S : Setup`, its 9124 form. -/
theorem simTrace_goldilocksRun {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)
    (hf : rho.point.ConstantFaults) (hv : rho.ExecutionValid) :
    GoldilocksRun (runProposer ⟨S, stock⟩ rho hn) (digestOf ⟨S, stock⟩ rho)
      (honestKeys ⟨S, stock⟩ rho) (simTrace ⟨S, stock⟩ rho hn) where
  vstart := fun _ => SA.voteStart_initial _
  init := simTrace_init ⟨S, stock⟩ rho hn
  grouped := simTrace_grouped ⟨S, stock⟩ rho hn hf hv
  cutLaw := simTrace_cutLaw ⟨S, stock⟩ rho hn hf hv
  wire := simTrace_wire ⟨S, stock⟩ rho hn hf hv
  proposerCredential := simTrace_proposerCredential ⟨S, stock⟩ rho hn hv
  time_nonneg := simTrace_time_nonneg ⟨S, stock⟩ rho hn hv
  time_mono := simTrace_time_mono ⟨S, stock⟩ rho hn hv
  finite := simTrace_finite ⟨S, stock⟩ rho hn hv
  phase_order := simTrace_phase_order ⟨S, stock⟩ rho hn hv
  tick_public := simTrace_tick_public ⟨S, stock⟩ rho hn hv
  tick_unique := simTrace_tick_unique ⟨S, stock⟩ rho hn hv
  tick_of_awake := simTrace_tick_of_awake ⟨S, stock⟩ rho hn hf hv
  awake_in_horizon := simTrace_awake_in_horizon ⟨S, stock⟩ rho hn
  awake_of_call := simTrace_awake_of_call ⟨S, stock⟩ rho hn hv
  restart_of_sleep := simTrace_restart_of_sleep ⟨S, stock⟩ rho hn hf hv
  restart_at_wake := simTrace_restart_at_wake ⟨S, stock⟩ rho hn hf hv
  sleep_of_restart := simTrace_sleep_of_restart ⟨S, stock⟩ rho hn hv
  block_unforgeable := simTrace_block_unforgeable ⟨S, stock⟩ rho hn hf hv
  att_unforgeable := simTrace_att_unforgeable ⟨S, stock⟩ rho hn hf hv
  msg_unforgeable := simTrace_msg_unforgeable ⟨S, stock⟩ rho hn hf hv
  genesis_root_ok := simTrace_genesis_root_ok ⟨S, stock⟩ rho hn
  carried_vote_unforgeable := simTrace_carried_vote_unforgeable ⟨S, stock⟩ rho hn hf hv

end Consensus.Goldilocks.Simulation

end
