module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.SignBridge
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Provenance

public section

/-! # Goldilocks Simulation: an engine signing is a cut of the node's tick

An engine signing (`EngineSignsAt`) is the FG update of the first trailing poll of a public tick
of the node, which runs on the node state the tick's proposal step leaves: it is the signing cut
`fg_attest(C) = a` of the node's `on_tick` at that tick
(`engineSignsAt_tick_cut`). A delivery never signs (its poll has no FG update due), and nor does
any other poll of a tick. -/

namespace Consensus.Goldilocks.Simulation
open AsChainShape

open Blocks Shape Node
open Consensus.Model (pubOf)

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

omit [DecidableEq V] in
/-- After a selected poll the FG update is not due. -/
private theorem dutyStep_poll_fgDue (v : V) (hsel : rho.ownKey v ∈ rho.sel .poll)
    (nd : Model.Node (Model.protoOf (compiled (goldilocks S)) E)) (k : Nat) :
    (shapeOf S hn (rho.dutyStep v nd (.poll k)).1).fgDue = false := by
  rw [dutyStep_poll S rho hn v nd k hsel, pollBatch_fgDue]

/-- **An engine signing is a signing cut of the node's public tick.** The FG update that signs
`a` at a duty of event `j` is that of the first trailing poll of a tick of `v` at a public time
`t`, run on the node state the tick's proposal step leaves; so `fg_attest(C) = a` is a cut of the
node's `on_tick` at `t` from the node state before the event. -/
theorem engineSignsAt_tick_cut (hv : rho.ExecutionValid) {v : V} {j q : Nat}
    {a : FG.Att (Fintype.card V)} (hs : EngineSignsAt S rho hn v j q a) :
    ∃ t, rho.events[j]? = some (.tick v t) ∧ (S.params (pubOf E) hn).toParams.IsPublic t ∧
      ∃ C, Cut.fg (.attest C (some a)) ∈ (exec (runProposer S rho hn) (digestOf S rho)
        (rho.ownKey v) (stateAt S rho hn v j).node t
        (.tick (encodeTxs (Model.mempool rho.inbox v t))
          (S.sign (pubOf E) (rho.ownKey v) t))).2 := by
  have hsel := poll_selected S rho hv v
  obtain ⟨nd, hc, k, hd, -, hdue, C, Λ', hC, ha⟩ := (engineSignsAt_iff S rho hn v j q a).1 hs
  have hf0 := fgDue_eq_false S rho hn v j
  rw [stateAt_eq] at hf0
  cases hc with
  | deliver he hp =>
    rename_i t o
    exfalso
    rcases hd with ⟨t', he', -⟩ | ⟨t', o', he', hq⟩
    · cases Option.some.inj (he'.symm.trans he)
    cases Option.some.inj (he'.symm.trans he)
    have ht0 := (hv.in_horizon _ (List.mem_of_getElem? he)).1
    have hlen : ((Model.protoOf (compiled (goldilocks S)) E).deliverDuties t).length = 1 := by
      rw [deliverDuties_eq S t ht0]; rfl
    have hq0 : q = 0 := by
      have := (List.getElem?_eq_some_iff.mp hq).1
      omega
    subst hq0
    rw [List.take_zero, rho.runDuties_nil] at hdue
    have h2 := (process_fgDue _ o (Model.digests rho.hash o)).trans hf0
    exact Bool.false_ne_true (h2.symm.trans hdue)
  | tick he hw hp =>
    rename_i t
    rcases hd with ⟨t', he', -, hq⟩ | ⟨t', o', he', -⟩
    swap
    · cases Option.some.inj (he'.symm.trans he)
    cases Option.some.inj (he'.symm.trans he)
    refine ⟨t, he, ?_⟩
    have ht0 := (hv.in_horizon _ (List.mem_of_getElem? he)).1
    -- the cut is the first trailing poll: `nd` is the node the proposal step leaves
    have hU : (rho.runDuties v ⟨(Model.protoOf (compiled (goldilocks S)) E).clock
        (rho.stateBefore j v).st t (Model.mempool rho.inbox v t), (rho.stateBefore j v).seen⟩
        (((Model.protoOf (compiled (goldilocks S)) E).duties t).take q)).1 =
        (rho.runDuties v (atProposal S rho v (rho.stateBefore j v) t)
          ((skeleton (pubOf E) S.vote).proposeAt t)).1 := by
      have hds := duties_eq (E := E) S t ht0
      have hp1 : ∀ (N : Model.Node (Model.protoOf (compiled (goldilocks S)) E))
          (ds : List (Model.protoOf (compiled (goldilocks S)) E).Duty),
          ((rho.runDuties v N (ds ++ [.poll t.toNat])).1.st.1 hn).fgDue = false := by
        intro N ds
        rw [runDuties_fst_append]
        exact dutyStep_poll_fgDue S rho hn v hsel _ _
      rcases Skeleton.proposeAt_cases (skeleton (pubOf E) S.vote) t with ⟨hnil, -⟩ |
        ⟨s, hs0, hone, -⟩
      · have hD : (Model.protoOf (compiled (goldilocks S)) E).duties t =
            ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat, .poll t.toNat, .poll t.toNat] :
              List (Model.protoOf (compiled (goldilocks S)) E).Duty) := by
          rw [hds]; simp only [dutiesInit, hnil]; rfl
        rw [hD] at hq hdue
        rw [hD, hnil, atProposal_eq]
        have hlt : q < 5 := (List.getElem?_eq_some_iff.mp hq).1
        interval_cases q
        · exact absurd (hf0.symm.trans hdue) Bool.false_ne_true
        · exact absurd ((hp1 _ []).symm.trans hdue) Bool.false_ne_true
        · cases hq
        · rfl
        · exact absurd ((hp1 _ [.poll t.toNat, .poll t.toNat, .pollPropose t.toNat]).symm.trans
            hdue) Bool.false_ne_true
      · have hD : (Model.protoOf (compiled (goldilocks S)) E).duties t =
            ([.poll t.toNat, .poll t.toNat, .pollPropose t.toNat, .propose s hs0, .poll t.toNat,
              .poll t.toNat] : List (Model.protoOf (compiled (goldilocks S)) E).Duty) := by
          rw [hds]; simp only [dutiesInit, hone]; rfl
        rw [hD] at hq hdue
        rw [hD, hone, atProposal_eq]
        have hlt : q < 6 := (List.getElem?_eq_some_iff.mp hq).1
        interval_cases q
        · exact absurd (hf0.symm.trans hdue) Bool.false_ne_true
        · exact absurd ((hp1 _ []).symm.trans hdue) Bool.false_ne_true
        · cases hq
        · cases hq
        · rfl
        · exact absurd ((hp1 _ [.poll t.toNat, .poll t.toNat, .pollPropose t.toNat,
            .propose s hs0]).symm.trans hdue) Bool.false_ne_true
    rw [hU] at hdue hC ha
    -- the tick is public: otherwise the FG update is not due after the proposal step
    have hpub : (S.params (pubOf E) hn).toParams.IsPublic t := by
      by_contra hnp
      have hA : (shapeOf S hn (atProposal S rho v (rho.stateBefore j v) t)).fgDue = false := by
        rw [atProposal_shape S rho hn v _ t hsel, nodeTick_eq (sign := _),
          ite_eq_right (by rw [pollBatch_now, pollBatch_now]; exact hnp), pollBatch_fgDue]
      have hB : (shapeOf S hn (rho.runDuties v (atProposal S rho v (rho.stateBefore j v) t)
          ((skeleton (pubOf E) S.vote).proposeAt t)).1).fgDue = false := by
        rcases Skeleton.proposeAt_cases (skeleton (pubOf E) S.vote) t with ⟨hnil, -⟩ |
          ⟨s, hs0, hone, -⟩
        · rw [hnil]; exact hA
        · rw [hone]
          exact dutyStep_propose_pres S rho hn (fun st => st.fgDue = false)
            (fun st o hs h => (recordOwn_fgDue st o hs).trans h)
            (fun st s h => (propose_fgDue st s).trans h) v _ s hs0 hA
      exact Bool.false_ne_true (hB.symm.trans hdue)
    refine ⟨hpub, ?_⟩
    obtain ⟨hself, hnow, hfg, hnode⟩ := updateNode_of_tick_public S rho hn hv v j t he hpub
    have hsign : S.sign (pubOf E) (rho.ownKey v) t = true := hfg.symm.trans hdue
    rw [hsign]
    rw [hnode, hnow] at hC
    rw [hnode, hnow, hself] at ha
    exact ⟨C, attest_mem_exec_tick _ _ _ _ _ _ hC ha⟩

end Consensus.Goldilocks.Simulation

end
