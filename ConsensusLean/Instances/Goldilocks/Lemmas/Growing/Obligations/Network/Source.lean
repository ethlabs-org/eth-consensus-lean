module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Obligations.Network.Transport
import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo
import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Groups
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.GoldilocksAC
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Network transport under growing faults: a source processes its own vote

* `own_proposal_payload_pooled_run`: in any Goldilocks run, the votes of an honest node's own
  proposal payload were pooled before its AC block cut (the node-local core of the static
  `own_proposal_payload_pooled`, which it gives on the prefix through the proposal);
* `sendOrAdmit_process_same_time_at`: a node honest at a cut at which it sends or freshly admits a
  vote processes it at that same time.

The node-local steps run on the prefix through the cut's time, where the node is honest throughout
(`Growing.GoldilocksRun.upTo`). -/

namespace Consensus.Goldilocks.Obligations.Growing
open AsChainShape Simulation
open Shape Blocks

section Node

variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- Votes in an actual own-proposal payload were already pooled before its AC block cut. -/
theorem own_proposal_payload_pooled_run (hr : GoldilocksRun proposer dg H tr)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {t : Time} {x : Nat}
    (hg : tr.GroupAt proposer dg y j t (.tick x))
    {d : DutyHead sp.n (List (FG.Att sp.n)) (SA.Payload sp.n)} {p : SA.Payload sp.n}
    (hd : (Node.acProposal
      (Node.tickStep proposer dg y (tr.state y j) t x .acTick).1 t).2.2 = some (d, p))
    (hprop : ∃ ℓp, tr.CallAt y (j + 1) (.ac ℓp) ∧ ℓp.call = .proposal)
    (hfg : ∃ B, tr.CallAt y (j + 2) (.fg (.block B true)))
    {m : SA.Vote sp.n} (hm : m ∈ p.1) :
    m ∈ (tr.state y (j + 3)).ac.pool m.slot := by
  have htick := hg.2.1 0 (by simp [Node.exec, Node.onTick, Node.runSteps, Node.tickSteps,
    Node.tickStep, Node.acCall])
  have hct : tr.CallAt y j (Node.acCall y (tr.state y j) t .tick).2 := by
    exact ⟨by simpa using htick.1, by
      simpa [Node.exec, Node.onTick, Node.runSteps, Node.tickSteps, Node.tickStep,
        Node.acCall] using htick.2.2.2.2⟩
  have hstate : (tr.state y (j + 1)).ac =
      (Node.tickStep proposer dg y (tr.state y j) t x .acTick).1.ac := by
    rw [tr.state_succ_of_call hct]
    have hl := hr.cutLaw y hy j _ hct
    have ht : tr.time j = t := by simpa using htick.2.1
    rw [ht] at hl
    exact (congrArg Prod.fst hl.2.1).symm
  have hp : ∃ σ, m ∈ (tr.state y (j + 1)).ac.pool σ := by
    rw [hstate]
    change (SA.acProposal sp _ _ t).2 = some (d, p) at hd
    unfold SA.acProposal at hd
    split_ifs at hd
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj hd)
    simp only [SA.voteViewList, List.mem_filter] at hm
    unfold SA.SAState.poolAt at hm
    split_ifs at hm
    · simp at hm
    · exact ⟨_, hm.1⟩
  obtain ⟨σ, hm⟩ := hp
  have hslot := (Compose.state_pool_cap hr hy (j + 1) σ).1 m
    (by simpa only [Compose.projAC_state hr.toLocalRun hy] using hm)
  obtain ⟨ℓp, hcp, hpc⟩ := hprop
  obtain ⟨B, hcb⟩ := hfg
  have hp := (hr.cutLaw y hy (j + 1) _ hcp).2.1
  rw [hpc] at hp
  have hpools : (tr.state y (j + 2)).ac.pool = (tr.state y (j + 1)).ac.pool := by
    have he := congrArg Prod.fst hp
    dsimp only [Prod.fst] at he
    rw [show j + 2 = (j + 1) + 1 by omega, tr.state_succ_of_call hcp, ← he]
    change (SA.acProposal _ _ _ _).1.pool = _
    unfold SA.acProposal
    split_ifs <;> rfl
  rw [show j + 3 = (j + 2) + 1 by omega, tr.state_succ_of_call hcb,
    (hr.cutLaw y hy (j + 2) _ hcb).2.2.1, hpools, hslot]
  exact hm

end Node

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
  (S : Setup) (rho : Model.Run (compiled (goldilocks S)) E)

/-- A node honest at a cut at which it sends or freshly admits a vote processes it at that same
time. Recursive delivery processing may occur later in the event, never at a later time. -/
theorem sendOrAdmit_process_same_time_at (hn : 1 ≤ Fintype.card V) (hv : rho.ExecutionValid)
    {y : Fin (Fintype.card V)} {i : Nat}
    (hy : y ∈ honestKeysAt S rho ((simTraceAt S rho hn).time i))
    {m : SA.Vote (Fintype.card V)} (hsource : (simTraceAt S rho hn).SendOrAdmitAt y i m) :
    ∃ k, (simTraceAt S rho hn).projAC.ProcessAt y k m ∧
      (simTraceAt S rho hn).time k = (simTraceAt S rho hn).time i := by
  have hrun := simTraceAt_goldilocksRun S rho hn hv
  have hsim := simTraceAt_simulates S rho hn hv
  rw [simTraceAt_eq] at hrun hsim hy hsource ⊢
  have hmono := hrun.time_mono
  have hr := hrun.upTo (hrun.time_nonneg i)
  set d := (simTrace S rho hn).time i with hdd
  have hsource' : ((simTrace S rho hn).upTo d).SendOrAdmitAt y i m :=
    (RunTrace.upTo_sendOrAdmitAt hmono).mpr ⟨le_rfl, hsource⟩
  have hproj : ((simTrace S rho hn).upTo d).projAC.SendOrAdmit y i m := by
    obtain ⟨ℓ, hc, hs⟩ := hsource'
    refine ⟨ℓ, Compose.projAC_callAt.mpr hc, ?_⟩
    rw [Compose.projAC_state hr.toLocalRun hy]
    exact hs
  rcases Compose.sendOrAdmit_forward_source hr hy hproj with hem | ⟨hc, hf, _⟩
  · obtain ⟨ℓ, hc, he⟩ := hem
    have hc' := ((Trace.upTo_callAt _).mp hc).2
    exact ⟨i, ⟨ℓ, Compose.projAC_callAt.mpr hc', Or.inr he⟩, rfl⟩
  rcases hc with ⟨ℓ, hc, hm⟩ | ⟨ℓ, B, hc, hb, hm⟩
  · have hc' := ((Trace.upTo_callAt _).mp hc).2
    exact ⟨i, ⟨ℓ, Compose.projAC_callAt.mpr hc', Or.inl hm⟩, rfl⟩
  have hct : (simTrace S rho hn).CallAt y i (.ac ℓ) := ((Trace.upTo_callAt _).mp hc).2
  have hl : (simTrace S rho hn).label i ≠ none := by
    rw [hct.2]; simp
  obtain ⟨r, n, ev, _, he, hlo, hhi, hidx, hnode, ht, _, hlabel⟩ :=
    simTrace_cut S rho hn hl
  have hrlabel : r.label = .ac ℓ := Option.some.inj (hlabel.symm.trans hct.2)
  have hkey : rho.ownKey ev.node = y := hnode.symm.trans hct.1
  cases ev with
  | deliver v o t =>
    obtain ⟨k, _, _, hp, hkt⟩ := delivery_block_payload_processAt S rho hn he
      (List.mem_of_getElem? hidx) hrlabel hb hm
    exact ⟨k, hkey ▸ hp, hkt.trans ht.symm⟩
  | restart v t =>
    have hm := List.mem_of_getElem? hidx
    rw [eventCuts_restart S rho hn n v t he] at hm
    obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hm
    have hq' := hq
    rw [length_groupRecs] at hq'
    have hq0 : q = 0 := by
      simpa only [Node.exec, Node.restart, List.length_singleton, Nat.lt_one_iff] using hq'
    subst q
    have hrlabel' := (getElem_groupRecs _ _ _ _ _ _ _ 0 hq).2.2.2.2
    rw [hrlabel'] at hrlabel
    have hcall := congrArg (fun c => match c with | .ac l => l.call | _ => .restart) hrlabel
    simp only [Node.exec, Node.restart, Node.acCall] at hcall
    rw [← hcall] at hb
    cases hb
  | tick v t =>
    change rho.ownKey v = y at hkey
    have hpublic : (S.params (Model.pubOf E) hn).toParams.IsPublic t := by
      by_contra h
      rw [eventCuts_tick_other S rho hn n v t he h] at hidx
      simp at hidx
    obtain ⟨hengine, hlen⟩ := hsim.tick_public v n t he hpublic
    rw [hkey] at hengine hlen
    have htd : t ≤ d := ht.symm.le
    have hcn : (simTrace S rho hn).time (cutMap S rho hn n) ≤ d :=
      (hengine.2.1 0 (List.length_pos_of_ne_nil hengine.1)).2.1 ▸ htd
    have hengine' := (RunTrace.upTo_groupAt hmono (d := d)).mpr ⟨htd, hengine⟩
    rw [← RunTrace.upTo_state_of_le hmono hcn] at hlen
    obtain ⟨i', hi, hacc, htime⟩ := Compose.acBlock_prev hr.toLocalRun hy hc hb
    rcases Compose.blockCall_cases hr.toLocalRun hy hacc with hg |
        ⟨j, x, hij, hg, hproposes, dd, p, hd, hB, _, htick, hproposal, hfg⟩
    · have hib : i' < cutMap S rho hn n +
          (Node.exec (runProposer S rho hn) (digestOf S rho) y
            (((simTrace S rho hn).upTo d).state y (cutMap S rho hn n)) t
            (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2.length := by omega
      have hstart : i' = cutMap S rho hn n := by
        by_cases hle : cutMap S rho hn n ≤ i'
        · exact Compose.group_start hengine' hg hle hib
        · obtain ⟨l, heq, _⟩ := Compose.before_tick hr.toLocalRun hy ⟨_, hengine'⟩ hacc
            (by omega) (by
              exact htime.trans ht)
          cases heq
      subst i'
      have hf := Compose.group_phase hengine' hg
      cases hf
    · have hcp : ∃ ℓp, ((simTrace S rho hn).upTo d).CallAt y (j + 1) (.ac ℓp) ∧
          ℓp.call = .proposal := by
        have hd' := hd
        simp only [Node.tickStep, Node.acCall] at hd'
        have hlen : 1 < (Node.exec (runProposer S rho hn) (digestOf S rho) y
            (((simTrace S rho hn).upTo d).state y j) (((simTrace S rho hn).upTo d).time i')
            (.tick x)).2.length := by
          simp only [Node.exec, Node.onTick, Node.runSteps, Node.tickSteps, List.foldl_cons,
            List.foldl_nil, Node.tickStep, Node.acCall, hproposes, ↓reduceIte, hd']
          simp
        obtain ⟨hnode, _, _, _, hl⟩ := hg.2.1 1 hlen
        simp only [Node.exec, Node.onTick, Node.runSteps, Node.tickSteps, List.foldl_cons,
          List.foldl_nil, Node.tickStep, Node.acCall, hproposes, ↓reduceIte, hd'] at hl
        simp only [List.nil_append,
          List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero] at hl
        exact ⟨_, ⟨hnode, hl⟩, rfl⟩
      have him : i = j + 3 := by omega
      apply False.elim
      apply hf
      rw [him]
      apply own_proposal_payload_pooled_run hr hy hg hd hcp
        ⟨B, by simpa only [hij] using hacc⟩
      simpa only [hB, Node.mkBlock, SA.blockVotes] using hm

end Consensus.Goldilocks.Obligations.Growing

end
