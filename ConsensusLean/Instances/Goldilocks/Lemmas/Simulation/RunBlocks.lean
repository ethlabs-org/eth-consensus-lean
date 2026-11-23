module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.RunSchedule
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.PayloadSource
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.AttUnforgeable
import ConsensusLean.Lemmas.Model.Constant

public section

/-! # Goldilocks Simulation: payload credentials and blocks of cuts

Carried votes and attestations come from earlier signing cuts. The trace's states and groups
across blocks of cuts support the engine/trace correspondence proved in `RunSimulates`. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)
open AC (ACParams ReplayOrder Vote Payload declaredHeadVotes)

variable {binding : VoteBinding}

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-! ## `GoldilocksRun` -/

omit [DecidableEq V] in
/-- The genesis block's root is the digest of its content: `dgOf` at `none` is the genesis
root. -/
theorem simTrace_genesis_root_ok :
    ((S.params (pubOf E) hn).toParams.genesisBlock
      (goldilocksNode (S.params (pubOf E) hn) (S.ro _)).genesisPayload).RootOk
        (digestOf S rho) := by
  have hd : NodeAsChainShape.CanonicalTrace.digestOf (traceEncoding S hn) rho = digestOf S rho := by
    apply traceEncoding_induction S hn (fun e _ =>
      NodeAsChainShape.CanonicalTrace.digestOf e rho = digestOf S rho)
    intro _ h
    exact (h rho).trans (digestOf_eq S rho).symm
  rw [← hd]
  exact NodeAsChainShape.CanonicalTrace.genesis_root_ok (traceEncoding S hn) rho

/-! ## Blocks of cuts

The trace's state across a block of cuts: unchanged across other nodes' cuts, the handler's
state across a group, `deliverState` across a delivery's groups; and a block with the engine's
ids is a `GroupAt` / `DeliverSeq` of the trace. -/

section

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  (proposer : Nat → Fin sp.n)
  (dg : Digest (List (FG.Att sp.n)) (Payload sp.n)) (self : Fin sp.n)

/-- A tick makes a cut (the AC's tick). -/
theorem exec_tick_ne_nil (st : NodeState (goldilocksNode sp ro)) (t : Time) (x : Nat) :
    (exec proposer dg self st t (.tick x)).2 ≠ [] := by
  simp [Node.exec, onTick, runSteps, tickSteps, Node.tickStep]

/-- A restart makes a cut (`ac_restart`). -/
theorem exec_restart_ne_nil (st : NodeState (goldilocksNode sp ro)) (t : Time) :
    (exec proposer dg self st t .restart).2 ≠ [] := by
  simp [Node.exec, Node.restart]

end

/-- The trace's state across a group block at `j0`: the handler's state, by the cut law's
successors. -/
theorem state_of_group
    (proposer : Nat → Fin (S.params (pubOf E) hn).n)
    (dg : Digest (List (FG.Att (S.params (pubOf E) hn).n)) (Payload (S.params (pubOf E) hn).n))
    {y : Fin (S.params (pubOf E) hn).n} {j0 : Nat}
    {st : NodeState (goldilocksNode (S.params (pubOf E) hn) (S.ro _))} {t : Time} {id : Nat}
    {e : Event (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    (hcut : ∀ k < (groupRecs proposer dg y st t id e).length,
      (allCuts S rho hn)[j0 + k]? = (groupRecs proposer dg y st t id e)[k]?)
    (h0 : (simTrace S rho hn).state y j0 = st) :
    (simTrace S rho hn).state y (j0 + (groupRecs proposer dg y st t id e).length) =
      (exec proposer dg y st t e).1 := by
  have heq : ∀ k < (NodeAsChainShape.CanonicalTrace.groupRecs proposer dg y st t id e).length,
      (NodeAsChainShape.CanonicalTrace.allCuts (traceEncoding S hn) rho)[j0 + k]? =
        (NodeAsChainShape.CanonicalTrace.groupRecs proposer dg y st t id e)[k]? := by
    intro k hk
    apply (allCuts_groupRecs_getElem?_iff S rho hn proposer dg y st t id e (j0 + k) k).mp
    apply hcut k
    rw [NodeAsChainShape.CanonicalTrace.groupRecs_eq, List.length_mapIdx,
      List.length_zip, length_cutPosts, min_self] at hk
    rwa [length_groupRecs]
  rw [(simTrace_encoding S rho hn).1] at h0 ⊢
  rw [length_groupRecs, NodeAsChainShape.CanonicalTrace.state_in_group _ _ _ _ heq h0 _ le_rfl,
    List.take_length, foldl_cutPost_exec]

/-- The event id of an existing cut is its record's. -/
private theorem event_of_getElem? {k : Nat} {r : CutRec (S.params (pubOf E) hn) (S.ro _)}
    (hr : (allCuts S rho hn)[k]? = some r) : (simTrace S rho hn).event k = r.event := by
  rw [simTrace_event, hr]; rfl

/-- A cut with an event id of engine event `i` lies in the range of event `i`. -/
theorem range_of_event {i : Nat} (hi : i < rho.events.length) {k s : Nat}
    (h : (simTrace S rho hn).event k = Nat.pair i s) :
    cutMap S rho hn i ≤ k ∧ k < cutMap S rho hn (i + 1) := by
  cases hr : (allCuts S rho hn)[k]? with
  | none =>
    rw [simTrace_event, hr, Option.elim_none, Nat.pair_eq_pair] at h
    omega
  | some r =>
    rw [event_of_getElem? S rho hn hr] at h
    obtain ⟨i', ev, he, h1, h2, h3⟩ := exists_event_of_getElem? S rho hn hr
    obtain ⟨-, -, s', hs'⟩ := mem_eventCuts S rho hn he (List.mem_of_getElem? h3)
    rw [hs', Nat.pair_eq_pair] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨h1, h2⟩

/-- A block of group cuts at `j0` whose event id is unique to the block is a group of the
trace; its length is the handler's cut count on the trace's state. -/
theorem groupAt_of_group
    (proposer : Nat → Fin (S.params (pubOf E) hn).n)
    (dg : Digest (List (FG.Att (S.params (pubOf E) hn).n)) (Payload (S.params (pubOf E) hn).n))
    {y : Fin (S.params (pubOf E) hn).n} {j0 : Nat}
    {st : NodeState (goldilocksNode (S.params (pubOf E) hn) (S.ro _))} {t : Time} {id : Nat}
    {e : Event (goldilocksNode (S.params (pubOf E) hn) (S.ro _))}
    (hcut : ∀ k < (groupRecs proposer dg y st t id e).length,
      (allCuts S rho hn)[j0 + k]? = (groupRecs proposer dg y st t id e)[k]?)
    (h0 : (simTrace S rho hn).state y j0 = st) (hne : (exec proposer dg y st t e).2 ≠ [])
    (huniq : ∀ k, (simTrace S rho hn).event k = id →
      j0 ≤ k ∧ k < j0 + (groupRecs proposer dg y st t id e).length) :
    (simTrace S rho hn).GroupAt proposer dg y j0 t e ∧
      (groupRecs proposer dg y st t id e).length =
        (exec proposer dg y ((simTrace S rho hn).state y j0) t e).2.length := by
  have hlen : (NodeAsChainShape.CanonicalTrace.groupRecs proposer dg y st t id e).length =
      (groupRecs proposer dg y st t id e).length := by
    rw [NodeAsChainShape.CanonicalTrace.groupRecs_eq, List.length_mapIdx,
      List.length_zip, length_cutPosts, min_self, length_groupRecs]
  have htrace := (simTrace_encoding S rho hn).1
  refine ⟨?_, by rw [h0, length_groupRecs]⟩
  rw [htrace] at h0 huniq ⊢
  apply NodeAsChainShape.CanonicalTrace.groupAt_of_recs (traceEncoding S hn) rho proposer dg
    (id := id) h0 hne
  · intro k hk
    rw [hlen] at hk
    exact (allCuts_groupRecs_getElem?_iff S rho hn proposer dg y st t id e (j0 + k) k).mp
      (hcut k hk)
  · intro k hk
    rw [hlen]
    exact huniq k hk

/-- A delivery block at `j0` whose sub-event ids from `sub` on are unique to the block is a
`DeliverSeq` of the trace. -/
theorem deliverSeq_of_recs
    (proposer : Nat → Fin (S.params (pubOf E) hn).n)
    (dg : Digest (List (FG.Att (S.params (pubOf E) hn).n)) (Payload (S.params (pubOf E) hn).n))
    {y : Fin (S.params (pubOf E) hn).n} {t : Time} {i : Nat}
    (io : VoteAuth (S.params (pubOf E) hn).n S.vote)
    (hs : List (Header Info × Nat)) (os : List (Wire (S.params (pubOf E) hn).n S.vote)) :
    ∀ (j0 sub : Nat) (st : NodeState (goldilocksNode (S.params (pubOf E) hn) (S.ro _))),
    (∀ k < (deliverRecs io proposer dg hs y t i os st sub).length,
      (allCuts S rho hn)[j0 + k]? = (deliverRecs io proposer dg hs y t i os st sub)[k]?) →
    (simTrace S rho hn).state y j0 = st →
    (∀ k s, (simTrace S rho hn).event k = Nat.pair i s → sub ≤ s →
      j0 ≤ k ∧ k < j0 + (deliverRecs io proposer dg hs y t i os st sub).length) →
    DeliverSeq proposer (simTrace S rho hn) dg io hs y t os j0
      (j0 + (deliverRecs io proposer dg hs y t i os st sub).length) := by
  induction os with
  | nil =>
    intro j0 sub st _ _ _
    rw [deliverRecs_nil, List.length_nil, Nat.add_zero]
    exact .nil j0
  | cons o os ih =>
    intro j0 sub st hcut h0 huniq
    cases he : canonEvent (S.params (pubOf E) hn) (S.ro _) io hs o with
    | none =>
      rw [deliverRecs_cons_none io _ _ _ _ _ _ _ _ _ _ he] at hcut huniq ⊢
      exact .drop he (ih j0 (sub + 1) st hcut h0 fun k s hk hs => huniq k s hk (by omega))
    | some e =>
      rw [deliverRecs_cons_some io _ _ _ _ _ _ _ _ _ _ e he] at hcut huniq ⊢
      rcases eq_or_ne (exec proposer dg y st t e).2 [] with hnil | hnil
      · have hg : groupRecs proposer dg y st t (Nat.pair i sub) e = [] :=
          List.length_eq_zero_iff.mp (by rw [length_groupRecs, hnil, List.length_nil])
        have hst : (exec proposer dg y st t e).1 = st := by
          have := foldl_cutPost_exec proposer dg y st t e
          rwa [hnil, List.foldl_nil, eq_comm] at this
        rw [hg, List.nil_append, hst] at hcut huniq ⊢
        exact .noCut e he (by rw [h0]; exact hnil)
          (ih j0 (sub + 1) st hcut h0 fun k s hk hs => huniq k s hk (by omega))
      · have hlen := length_groupRecs proposer dg y st t (Nat.pair i sub) e
        have hcutg : ∀ k < (groupRecs proposer dg y st t (Nat.pair i sub) e).length,
            (allCuts S rho hn)[j0 + k]? = (groupRecs proposer dg y st t (Nat.pair i sub) e)[k]? :=
          fun k hk => by
            rw [hcut k (by rw [List.length_append]; omega), List.getElem?_append_left hk]
        -- a cut with an id of the rest is past the group; one with the group's id is in it
        have hrest : ∀ k, (groupRecs proposer dg y st t (Nat.pair i sub) e).length ≤ k →
            k < (groupRecs proposer dg y st t (Nat.pair i sub) e).length +
              (deliverRecs io proposer dg hs y t i os
                (exec proposer dg y st t e).1 (sub + 1)).length →
            ∃ s, sub + 1 ≤ s ∧ (simTrace S rho hn).event (j0 + k) = Nat.pair i s := by
          intro k hk1 hk2
          have hr := hcut k (by rw [List.length_append]; omega)
          have hlt : k - (groupRecs proposer dg y st t (Nat.pair i sub) e).length <
              (deliverRecs io proposer dg hs y t i os
                (exec proposer dg y st t e).1 (sub + 1)).length := by omega
          rw [List.getElem?_append_right hk1, List.getElem?_eq_getElem hlt] at hr
          obtain ⟨-, -, s, hs1, hs2⟩ :=
            mem_deliverRecs proposer dg y io hs t i (List.getElem_mem hlt)
          exact ⟨s, hs1, by rw [event_of_getElem? S rho hn hr, hs2]⟩
        have hgrp : ∀ k < (groupRecs proposer dg y st t (Nat.pair i sub) e).length,
            (simTrace S rho hn).event (j0 + k) = Nat.pair i sub := by
          intro k hk
          have hr := hcutg k hk
          rw [List.getElem?_eq_getElem hk] at hr
          rw [event_of_getElem? S rho hn hr]
          exact (getElem_groupRecs proposer dg y st t (Nat.pair i sub) e k hk).2.2.1
        obtain ⟨hG, hGlen⟩ := groupAt_of_group S rho hn proposer dg hcutg h0 hnil fun k hk => by
          obtain ⟨h1, h2⟩ := huniq k sub hk le_rfl
          rw [List.length_append] at h2
          refine ⟨h1, ?_⟩
          by_contra h3
          obtain ⟨s, hs1, hs2⟩ := hrest (k - j0) (by omega) (by omega)
          rw [Nat.add_sub_cancel' h1, hk, Nat.pair_eq_pair] at hs2
          omega
        refine .event e he hG ?_
        rw [← hGlen, List.length_append, ← Nat.add_assoc]
        refine ih (j0 + (groupRecs proposer dg y st t (Nat.pair i sub) e).length) (sub + 1) _
          (fun k hk => ?_) (state_of_group S rho hn proposer dg hcutg h0) (fun k s hk hs => ?_)
        · rw [Nat.add_assoc, hcut _ (by rw [List.length_append]; omega),
            List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
        · obtain ⟨h1, h2⟩ := huniq k s hk (by omega)
          rw [List.length_append, ← Nat.add_assoc] at h2
          refine ⟨?_, h2⟩
          by_contra h3
          have := hgrp (k - j0) (by omega)
          rw [Nat.add_sub_cancel' h1, hk, Nat.pair_eq_pair] at this
          omega

end Consensus.Goldilocks.Simulation

end
