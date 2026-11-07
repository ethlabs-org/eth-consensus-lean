module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Simulation.Events

public section

/-! # Coverage by canonical handler groups

Validity gives state correspondence for every actual event. Group coverage consequently
does not require an honest-set premise: compromise affects credentials, not record expansion.
-/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- Every labelled cut, including one preceding a later compromise, belongs to a handler. -/
theorem simTraceAt_grouped (hv : rho.ExecutionValid) :
    ∀ y i c, (simTraceAt S rho hn).CallAt y i c →
      ∃ j e, (simTraceAt S rho hn).InGroup (runProposer S rho hn)
        (digestOf S rho) y j i ((simTraceAt S rho hn).time i) e := by
  rintro y k c ⟨hnode, hlab⟩
  rw [simTraceAt_eq] at hnode hlab ⊢
  obtain ⟨r, i, ev, -, he, h1, h2, -, hn', -, -, -⟩ :=
    simTrace_cut S rho hn (by rw [hlab]; simp)
  have hy' := hn'.symm.trans hnode
  have hgroup : ∃ j0 t e,
      (simTrace S rho hn).GroupAt (runProposer S rho hn) (digestOf S rho) y j0 t e ∧
      j0 ≤ k ∧ k < j0 + (Node.exec (runProposer S rho hn) (digestOf S rho)
        y ((simTrace S rho hn).state y j0) t e).2.length := by
    cases ev with
    | tick v t =>
      change rho.ownKey v = y at hy'
      subst hy'
      by_cases hp : (S.params (pubOf E) hn).toParams.IsPublic t
      · obtain ⟨hg, hlen⟩ := simTraceAt_tick_public_group S rho hn hv he hp
        rw [simTraceAt_eq] at hg hlen
        exact ⟨_, t, _, hg, h1, by omega⟩
      · have hlen := cutMap_succ S rho hn i
        rw [eventCuts_tick_other S rho hn i v t he hp, List.length_nil] at hlen
        omega
    | deliver v o t =>
      change rho.ownKey v = y at hy'
      subst hy'
      have hseq := simTraceAt_deliver S rho hn hv he
      rw [simTraceAt_eq] at hseq
      obtain ⟨-, hcov⟩ := deliverSeq_cover hseq
      obtain ⟨j0, e, o', ho, hce, hg, h3, h4⟩ := hcov k h1 h2
      exact ⟨j0, t, e, hg, h3, h4⟩
    | restart v t =>
      change rho.ownKey v = y at hy'
      subst hy'
      obtain ⟨hg, hlen⟩ := simTraceAt_restart S rho hn hv he
      rw [simTraceAt_eq] at hg hlen
      exact ⟨_, t, _, hg, h1, by omega⟩
  obtain ⟨j0, t, e, hg, h1, h2⟩ := hgroup
  have ht : (simTrace S rho hn).time k = t := by
    have := (hg.2.1 (k - j0) (by omega)).2.1
    rwa [Nat.add_sub_cancel' h1] at this
  rw [ht]
  exact ⟨j0, e, hg, h1, h2⟩

/-- The state inside a canonical handler is its cut fold. -/
private theorem state_in_group
    {y : Fin (S.params (pubOf E) hn).n} {j0 : Nat}
    {st : NodeState (goldilocksNode (S.params (pubOf E) hn) (S.ro _))} {t : Time} {id : Nat}
    {e : Event (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    (hcut : ∀ k < (groupRecs (runProposer S rho hn) (digestOf S rho) y st t id e).length,
      (allCuts S rho hn)[j0 + k]? =
        (groupRecs (runProposer S rho hn) (digestOf S rho) y st t id e)[k]?)
    (h0 : (simTrace S rho hn).state y j0 = st) :
    ∀ k ≤ (exec (runProposer S rho hn) (digestOf S rho) y st t e).2.length,
      (simTrace S rho hn).state y (j0 + k) =
        ((exec (runProposer S rho hn) (digestOf S rho) y st t e).2.take k).foldl
          (cutPost y t) st := by
  intro k
  induction k with
  | zero => intro _; simpa using h0
  | succ k ih =>
    intro hk
    have hk' : k < (groupRecs (runProposer S rho hn) (digestOf S rho) y st t id e).length := by
      rw [length_groupRecs]; omega
    have hr := hcut k hk'
    rw [List.getElem?_eq_getElem hk'] at hr
    obtain ⟨hnode, -, -, -, -⟩ :=
      getElem_groupRecs (runProposer S rho hn) (digestOf S rho) y st t id e k hk'
    change (simTrace S rho hn).state y (j0 + k).succ = _
    rw [Trace.state.eq_2, ite_eq_left, simTrace_post, hr, Option.elim_some,
      getElem_groupRecs_post, cutPosts_getElem]
    rw [simTrace_node, hr, Option.elim_some, hnode, simTrace_label, hr]
    simp

private theorem recBlock_of_deliverRecs
    {y : Fin (S.params (pubOf E) hn).n} {t : Time} {i : Nat}
    (hs : List (Header Info × Nat)) (os : List (Wire (S.params (pubOf E) hn).n)) :
    ∀ (j0 sub : Nat) (st : NodeState (goldilocksNode (S.params (pubOf E) hn) (S.ro _))),
    (∀ k < (deliverRecs (runProposer S rho hn) (digestOf S rho) hs y t i os st sub).length,
      (allCuts S rho hn)[j0 + k]? =
        (deliverRecs (runProposer S rho hn) (digestOf S rho) hs y t i os st sub)[k]?) →
    (simTrace S rho hn).state y j0 = st →
    ∀ k < (deliverRecs (runProposer S rho hn) (digestOf S rho) hs y t i os st sub).length,
      ∃ j1 st' id e, (∀ m < (groupRecs (runProposer S rho hn) (digestOf S rho)
          y st' t id e).length,
        (allCuts S rho hn)[j1 + m]? =
          (groupRecs (runProposer S rho hn) (digestOf S rho) y st' t id e)[m]?) ∧
        (simTrace S rho hn).state y j1 = st' ∧ j1 ≤ j0 + k ∧
        j0 + k < j1 + (groupRecs (runProposer S rho hn) (digestOf S rho) y st' t id e).length := by
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
      have hcutg : ∀ m < (groupRecs (runProposer S rho hn) (digestOf S rho)
          y st t (Nat.pair i sub) e).length,
          (allCuts S rho hn)[j0 + m]? = (groupRecs (runProposer S rho hn) (digestOf S rho)
            y st t (Nat.pair i sub) e)[m]? := fun m hm => by
          rw [hcut m (by rw [List.length_append]; omega), List.getElem?_append_left hm]
      by_cases hkg : k < (groupRecs (runProposer S rho hn) (digestOf S rho)
          y st t (Nat.pair i sub) e).length
      · exact ⟨j0, st, _, e, hcutg, h0, by omega, by omega⟩
      · obtain ⟨j1, st', id, e', h2, h3, h4, h5⟩ :=
          ih (j0 + (groupRecs (runProposer S rho hn) (digestOf S rho)
            y st t (Nat.pair i sub) e).length) (sub + 1) _
            (fun m hm => by
              rw [Nat.add_assoc, hcut _ (by rw [List.length_append]; omega),
                List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left])
            (state_of_group S rho hn _ _ hcutg h0)
            (k - (groupRecs (runProposer S rho hn) (digestOf S rho)
              y st t (Nat.pair i sub) e).length) (by omega)
        exact ⟨j1, st', id, e', h2, h3, by omega, by omega⟩

private theorem recBlock_of_cut (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} {k : Nat} (hnode : (simTrace S rho hn).node k = y)
    (hl : (simTrace S rho hn).label k ≠ none) :
    ∃ j1 st t id e, (∀ m < (groupRecs (runProposer S rho hn) (digestOf S rho) y st t id e).length,
        (allCuts S rho hn)[j1 + m]? =
          (groupRecs (runProposer S rho hn) (digestOf S rho) y st t id e)[m]?) ∧
      (simTrace S rho hn).state y j1 = st ∧ j1 ≤ k ∧
      k < j1 + (groupRecs (runProposer S rho hn) (digestOf S rho) y st t id e).length := by
  obtain ⟨r, i, ev, -, he, h1, h2, -, hn', -, -, -⟩ := simTrace_cut S rho hn hl
  have hi : i < rho.events.length := (List.getElem?_eq_some_iff.mp he).1
  have hcut : ∀ m < (eventCuts S rho hn i).length,
      (allCuts S rho hn)[cutMap S rho hn i + m]? = (eventCuts S rho hn i)[m]? :=
    fun m hm => allCuts_getElem?_add S rho hn i m hi hm
  have hlen := cutMap_succ S rho hn i
  have h0 := (simTraceAt_state_all S rho hn hv ev.node i hi.le).symm
  rw [simTraceAt_eq] at h0
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
    obtain ⟨j1, st', id, e, h3, h4, h5, h6⟩ := recBlock_of_deliverRecs S rho hn _ _ _ 0 _
      hcut h0 (k - cutMap S rho hn i) (by omega)
    exact ⟨j1, st', t, id, e, h3, h4, by omega, by omega⟩
  | restart v t =>
    change rho.ownKey v = y at hy'
    subst hy'
    rw [eventCuts_restart S rho hn i v t he] at hcut hlen
    exact ⟨_, _, t, _, _, hcut, h0, h1, by omega⟩

/-- The canonical record expansion obeys the handler cut law at every actual call. -/
theorem simTraceAt_cutLaw (hv : rho.ExecutionValid) :
    ∀ y i c, (simTraceAt S rho hn).CallAt y i c →
      CutStep y ((simTraceAt S rho hn).time i) ((simTraceAt S rho hn).state y i) c
        ((simTraceAt S rho hn).post i) := by
  rw [simTraceAt_eq]
  rintro y i c ⟨hnode, hlab⟩
  obtain ⟨j1, st, t, id, e, hcut, h0, h1, h2⟩ :=
    recBlock_of_cut S rho hn hv hnode (by rw [hlab]; simp)
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
  have hch := Compose.exec_is_cut_chain (P := (S.params (pubOf E) hn).toParams)
    (A := goldilocksNode (S.params (pubOf E) hn) (S.ro _))
    (runProposer S rho hn) (digestOf S rho) y st t e
  have key := cutStep_of_cutChain hch m hm'
  have e1 := cutPosts_getElem y t (exec (runProposer S rho hn) (digestOf S rho) y st t e).2 st m
    (by have := length_cutPosts y t (exec (runProposer S rho hn) (digestOf S rho) y st t e).2 st
        omega)
  rw [state_in_group S rho hn hcut h0 m hm'.le, e1]
  exact key

end Consensus.Goldilocks.Simulation
