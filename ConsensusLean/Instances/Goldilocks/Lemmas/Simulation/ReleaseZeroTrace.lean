module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.ReleaseZero
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.SignBridge
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.TraceDefs

public section

/-! # Goldilocks Simulation: the own admission of a stock tick

At the stock schedule (`release ≡ true`) the own admissions of a tick are exactly the attestation
its signing cut creates, when that attestation is new to the pool (`admitsAt_tick_of_signing`),
and nothing when the tick does not sign (`admitsAt_tick_of_no_signing`). In the canonical trace
each own admission is its own `.attestation` group right after the tick group of the same
engine event, so at `R = 0` the tick group's signing cut of `a` is followed by the one-cut group
of `a`, whose state is `on_attestation(a)` of the tick group's.

Every step is proved. -/

namespace Consensus.Goldilocks.Simulation

open AsChainShape Blocks Shape Node
open Model (pubOf)

/-- A signing cut of the node's tick: the signing calendar is on at the tick, and the FG update
on the node state the AC tick and the proposal leave signs `a` for the source `ac_to_fg`
returns. -/
theorem attest_of_mem_exec_tick {P : Params} {A : NodeAC P} (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (self : Fin P.n) (st : NodeState A) (t : Time)
    (x : Nat) (b : Bool) {C : A.Blk} {a : FG.Att P.n}
    (h : Cut.fg (.attest C (some a)) ∈ (exec proposer dg self st t (.tick x b)).2) :
    b = true ∧
      let n := (tickStep proposer dg self (tickStep proposer dg self st t x .acTick).1
        t x .proposal).1
      (acToFG n t).2.2 = some C ∧
        ∃ Λ', (acToFG n t).1.fg.attest (acToFG n t).1.record self C = some (a, Λ') := by
  -- the AC tick and the proposal emit no signing cut
  have hno : Cut.fg (.attest C (some a)) ∉
      (exec proposer dg self st t (.tick x false)).2 := by
    intro h'
    simp only [exec, onTick, runSteps, tickSteps, Bool.false_eq_true, ↓reduceIte,
      List.foldl_cons, List.foldl_nil, List.nil_append] at h'
    rcases List.mem_append.mp h' with h' | h'
    · simp [tickStep, acCall] at h'
    · simp only [tickStep] at h'
      split at h'
      · simp only [acProposal] at h'
        split at h'
        · simp at h'
        · simp only [proposeBlock, Node.onBlock, List.mem_cons] at h'
          split at h'
          · simp at h'
          · split at h' <;> simp [acCall] at h'
      · simp at h'
  cases b with
  | false => exact absurd h hno
  | true =>
    refine ⟨rfl, ?_⟩
    change _ ∈ (exec proposer dg self st t (.tick x false)).2 ++
      (tickStep proposer dg self (tickStep proposer dg self
        (tickStep proposer dg self st t x .acTick).1 t x .proposal).1 t x .fgUpdate).2 at h
    rcases List.mem_append.mp h with h | h
    · exact absurd h hno
    generalize (tickStep proposer dg self (tickStep proposer dg self st t x .acTick).1
      t x .proposal).1 = n at h ⊢
    simp only [tickStep] at h
    split at h
    · simp [acToFG] at h
    · rename_i C' hC'
      simp only [Node.attest] at h
      split at h
      · simp [acToFG] at h
      · rename_i a' Λ' ha'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h
        · simp [acToFG] at h
        · simp only [Cut.fg.injEq, FGLabel.attest.injEq, Option.some.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hC', Λ', ha'⟩

variable {V : Type} [Fintype V] {E : Env V} [DecidableEq V] (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- The engine node before a tick's first trailing poll is the one after the proposal duty. -/
private theorem beforeTrailing_atProposal (v : V) (i : Nat) (t : Time) :
    beforeTrailing S rho v i t = (rho.runDuties v (atProposal S rho v (rho.stateBefore i v) t)
      ((skeleton (pubOf E) S.vote).proposeAt t)).1 := by
  rw [beforeTrailing_eq, atProposal_eq]

/-- **At the stock schedule a tick that signs `a` admits exactly `a`, when it is new to the
pool.** -/
theorem admitsAt_tick_of_signing (hR : S.release (pubOf E) = fun _ _ => true)
    (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t) {C} {a : FG.Att (Fintype.card V)}
    (hc : Cut.fg (.attest C (some a)) ∈ (exec (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (stateAt S rho hn v i).node t (.tick (encodeTxs (Model.mempool rho.inbox v t))
        (S.sign (pubOf E) (rho.ownKey v) t))).2) :
    admitsAt S rho hn v i = [a].filter (fun b => b ∉ (stateAt S rho hn v i).node.fg.atts) := by
  rw [admitsAt_tick_of_release_eq S rho hn hR hv he]
  obtain ⟨hb, hC, Λ', ha⟩ := attest_of_mem_exec_tick _ _ _ _ _ _ _ hc
  obtain ⟨hself, hnow, hfg, hnode⟩ := updateNode_of_tick_public S rho hn hv v i t he hp
  rw [beforeTrailing_atProposal, hfg, hb]
  simp only [↓reduceIte, fgSigned_eq, hnode, hnow, hself, hC, ha, Option.bind_some,
    Option.map_some, Option.toList_some]

/-- At the stock schedule a public tick without a signing cut admits nothing. -/
theorem admitsAt_tick_of_no_signing (hR : S.release (pubOf E) = fun _ _ => true)
    (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t)
    (hc : ∀ C (a : FG.Att (Fintype.card V)), Cut.fg (.attest C (some a)) ∉
      (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v) (stateAt S rho hn v i).node t
        (.tick (encodeTxs (Model.mempool rho.inbox v t)) (S.sign (pubOf E) (rho.ownKey v) t))).2) :
    admitsAt S rho hn v i = [] := by
  rw [admitsAt_tick_of_release_eq S rho hn hR hv he]
  obtain ⟨hself, hnow, hfg, hnode⟩ := updateNode_of_tick_public S rho hn hv v i t he hp
  rw [beforeTrailing_atProposal, hfg]
  cases hsg : S.sign (pubOf E) (rho.ownKey v) t
  · simp
  · simp only [↓reduceIte]
    cases hf : fgSigned (shapeOf S hn (rho.runDuties v (atProposal S rho v (rho.stateBefore i v) t)
        ((skeleton (pubOf E) S.vote).proposeAt t)).1) with
    | none => simp
    | some a =>
      exfalso
      rw [fgSigned_eq, hnode, hnow, hself] at hf
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hf
      obtain ⟨C, hC, ⟨a', Λ'⟩, ha, rfl⟩ := hf
      have hcut := attest_mem_exec_tick _ _ _ _ _ _ hC ha
      rw [← hsg] at hcut
      exact hc C a' hcut

/-- **The own admission of a stock tick in the trace.** At the stock
schedule, the cuts of a public tick of `v` whose group signs a new `a` are the tick group,
followed by the one-cut `.attestation a` group (event id `Nat.pair i 1`) from the tick group's end
state; that group's state is `on_attestation(a)` of it. -/
theorem pool_release_zero_relation_tick (hR : S.release (pubOf E) = fun _ _ => true)
    (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t) {C} {a : FG.Att (Fintype.card V)}
    (hc : Cut.fg (.attest C (some a)) ∈ (exec (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (stateAt S rho hn v i).node t (.tick (encodeTxs (Model.mempool rho.inbox v t))
        (S.sign (pubOf E) (rho.ownKey v) t))).2)
    (hnew : a ∉ (stateAt S rho hn v i).node.fg.atts) :
    eventCuts S rho hn i =
      groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t (Nat.pair i 0)
        (.tick (encodeTxs (Model.mempool rho.inbox v t)) (S.sign (pubOf E) (rho.ownKey v) t)) ++
      groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v) (stateAt S rho hn v i).node t
          (.tick (encodeTxs (Model.mempool rho.inbox v t))
            (S.sign (pubOf E) (rho.ownKey v) t))).1
        t (Nat.pair i 1) (.attestation a) := by
  rw [eventCuts_tick_public S rho hn i v t he hp, tickTail_eq,
    admitsAt_tick_of_signing S rho hn hR hv he hp hc, postTick_eq, ite_eq_left hp]
  simp only [List.filter_cons, hnew, not_false_eq_true, decide_true, ↓reduceIte,
    List.filter_nil]
  rw [admitRecs_cons, admitRecs_nil, List.append_nil]

/-- At the stock schedule a public tick whose group signs nothing new has only its tick group. -/
theorem pool_release_zero_relation_tick_none (hR : S.release (pubOf E) = fun _ _ => true)
    (hv : rho.ExecutionValid) {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (pubOf E) hn).toParams.IsPublic t)
    (hc : ∀ C (a : FG.Att (Fintype.card V)), Cut.fg (.attest C (some a)) ∈
      (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v) (stateAt S rho hn v i).node t
        (.tick (encodeTxs (Model.mempool rho.inbox v t)) (S.sign (pubOf E) (rho.ownKey v) t))).2 →
      a ∈ (stateAt S rho hn v i).node.fg.atts) :
    eventCuts S rho hn i =
      groupRecs (runProposer S rho hn) (digestOf S rho) (rho.ownKey v)
        (stateAt S rho hn v i).node t (Nat.pair i 0)
        (.tick (encodeTxs (Model.mempool rho.inbox v t)) (S.sign (pubOf E) (rho.ownKey v) t)) := by
  rw [eventCuts_tick_public S rho hn i v t he hp, tickTail_eq]
  by_cases hs : ∃ C, ∃ a : FG.Att (Fintype.card V), Cut.fg (.attest C (some a)) ∈
      (exec (runProposer S rho hn) (digestOf S rho) (rho.ownKey v) (stateAt S rho hn v i).node t
        (.tick (encodeTxs (Model.mempool rho.inbox v t)) (S.sign (pubOf E) (rho.ownKey v) t))).2
  · obtain ⟨C, a, hca⟩ := hs
    rw [admitsAt_tick_of_signing S rho hn hR hv he hp hca]
    simp only [List.filter_cons, hc C a hca, not_true_eq_false, decide_false,
      Bool.false_eq_true, ↓reduceIte, List.filter_nil]
    rw [admitRecs_nil, List.append_nil]
  · simp only [not_exists] at hs
    rw [admitsAt_tick_of_no_signing S rho hn hR hv he hp hs, admitRecs_nil, List.append_nil]

end Consensus.Goldilocks.Simulation
