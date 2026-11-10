module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Simulation.Core
import ConsensusLean.Instances.Goldilocks.Lemmas.Obligations.OwnProposalPool
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Groups

public section

/-! # A node processes what it releases at the release time: the event-local steps

The attestations a node signs and the votes it sends or freshly admits are processed by the node
at the time of their release. The steps below read the simulating trace's events and the node's
own cuts only, not the fault model; each fault model supplies the tick group of the node and its
run, and the release or source facts of its own.

* `tick_attest_processAt`: an attestation signed in a public tick's group is processed by the
  node at the tick;
* `acBlock_cut_cases`: an AC block cut carrying a vote is in a delivery, which processes the vote
  at the cut's time, or in a public tick of the cut's node;
* `acBlock_vote_pooled_in_tick`: in any Goldilocks run, an AC block cut inside a tick group of
  its node has the block's votes already pooled (the block is the node's own proposal). -/

namespace Consensus.Goldilocks.Obligations
open AsChainShape Simulation
open Shape Blocks

section Events

variable {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (S : Setup)
  (rho : Model.Run (compiled (goldilocks S)) E) (hn : 1 ≤ Fintype.card V)

/-- **An attestation signed in a public tick is processed at the tick.** The tick event `i` of
`v` at a public time `t` whose group has the signing cut `fg_attest(C)` of `a` has a cut of
`rho.ownKey v` processing `a` at time `t`. -/
theorem tick_attest_processAt {i : Nat} {v : V} {t : Time}
    (he : rho.events[i]? = some (.tick v t))
    (hp : (S.params (Model.pubOf E) hn).toParams.IsPublic t)
    {a : FG.Att (Fintype.card V)} {C : Blk (S.params (Model.pubOf E) hn)}
    (hc : Cut.fg (.attest C (some a)) ∈ (Node.exec (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (stateAt S rho hn v i).node t
      (.tick (encodeTxs (Model.mempool rho.inbox v t)))).2) :
    ∃ k, (simTrace S rho hn).ProcessAttAt (rho.ownKey v) k a ∧
      (simTrace S rho hn).time k = t := by
  obtain ⟨m, hm, hcm⟩ := List.getElem_of_mem hc
  have hnxt := Compose.exec_attest_next
    (A := goldilocksNode (S.params (Model.pubOf E) hn) (S.ro _))
    (runProposer S rho hn) (digestOf S rho)
    (rho.ownKey v) (stateAt S rho hn v i).node t
    (.tick (encodeTxs (Model.mempool rho.inbox v t)))
    (k := m) (C := C) (a := a) (List.getElem?_eq_some_iff.mpr ⟨hm, hcm⟩)
  have hlen := (List.getElem?_eq_some_iff.mp hnxt).1
  have hEC := eventCuts_tick_public S rho hn i v t he hp
  have hm' : m + 1 < (eventCuts S rho hn i).length := by
    rw [hEC, length_groupRecs]
    exact hlen
  have hk := allCuts_getElem?_add S rho hn i (m + 1)
    (List.getElem?_eq_some_iff.mp he).1 hm'
  rw [hEC] at hk
  have hlen' : m + 1 < (groupRecs (runProposer S rho hn) (digestOf S rho)
      (rho.ownKey v) (stateAt S rho hn v i).node t (Nat.pair i 0)
      (.tick (encodeTxs (Model.mempool rho.inbox v t)))).length := by
    rw [length_groupRecs]; exact hlen
  rw [List.getElem?_eq_getElem hlen'] at hk
  obtain ⟨hnode, htime, _, _, hlab⟩ := getElem_groupRecs _ _ _ _ _ _ _ (m + 1) hlen'
  have hl := (List.getElem?_eq_some_iff.mp hnxt).2
  refine ⟨cutMap S rho hn i + (m + 1), Or.inl ⟨?_, ?_⟩, ?_⟩
  · simpa only [simTrace_node, hk, Option.elim_some] using hnode
  · simp only [simTrace_label, hk, Option.map_some, hlab, hl]
  · simpa only [simTrace_time, hk, Option.elim_some] using htime

/-- **The event of an AC block cut carrying a vote.** An AC cut `i` of `y` calling the block `B`
with `m ∈ blockVotes B` is in a delivery, which processes `m` at `y` at the cut's time, or in a
public tick event `n` of the node `v` of `y`, with `i ∈ [cutMap n, cutMap (n + 1))` at the tick's
time. A restart has no such cut. -/
theorem acBlock_cut_cases {y : Fin (Fintype.card V)} {i : Nat}
    {ℓ : ACLabel (goldilocksNode (S.params (Model.pubOf E) hn) (S.ro _))}
    {B : Blk (S.params (Model.pubOf E) hn)} {m : SA.Vote (Fintype.card V)}
    (hc : (simTrace S rho hn).CallAt y i (.ac ℓ)) (hb : ℓ.call = .block B)
    (hm : m ∈ SA.blockVotes B) :
    (∃ k, (simTrace S rho hn).projAC.ProcessAt y k m ∧
        (simTrace S rho hn).time k = (simTrace S rho hn).time i) ∨
      ∃ n v t, rho.events[n]? = some (.tick v t) ∧
        (S.params (Model.pubOf E) hn).toParams.IsPublic t ∧ rho.ownKey v = y ∧
        cutMap S rho hn n ≤ i ∧ i < cutMap S rho hn (n + 1) ∧ (simTrace S rho hn).time i = t := by
  have hl : (simTrace S rho hn).label i ≠ none := by rw [hc.2]; simp
  obtain ⟨r, n, ev, _, he, hlo, hhi, hidx, hnode, ht, _, hlabel⟩ :=
    simTrace_cut S rho hn hl
  have hrlabel : r.label = .ac ℓ := Option.some.inj (hlabel.symm.trans hc.2)
  have hkey : rho.ownKey ev.node = y := hnode.symm.trans hc.1
  cases ev with
  | deliver v o t =>
    obtain ⟨k, _, _, hp, hkt⟩ := delivery_block_payload_processAt S rho hn he
      (List.mem_of_getElem? hidx) hrlabel hb hm
    exact Or.inl ⟨k, hkey ▸ hp, hkt.trans ht.symm⟩
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
    have hpublic : (S.params (Model.pubOf E) hn).toParams.IsPublic t := by
      by_contra h
      rw [eventCuts_tick_other S rho hn n v t he h] at hidx
      simp at hidx
    exact Or.inr ⟨n, v, t, he, hpublic, hkey, hlo, hhi, ht⟩

end Events

variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- **An AC block cut inside a tick group has its votes pooled.** In a Goldilocks run, an honest
`y`'s AC cut `i` calling the block `B`, inside `y`'s tick group at cut `c` and time `t`, has every
`m ∈ blockVotes B` in `y`'s pool before the cut: the block is not a delivered one (the tick group
starts with the tick), so it is `y`'s own proposal (`own_proposal_payload_pooled_run`). -/
theorem acBlock_vote_pooled_in_tick (hr : GoldilocksRun proposer dg H tr) {y : Fin sp.n}
    (hy : y ∈ H) {c i : Nat} {t : Time} {x : Nat} (hg : tr.GroupAt proposer dg y c t (.tick x))
    (hlo : c ≤ i) (hhi : i < c + (Node.exec proposer dg y (tr.state y c) t (.tick x)).2.length)
    (ht : tr.time i = t) {ℓ : ACLabel (goldilocksNode sp ro)} {B : Blk sp}
    {m : SA.Vote sp.n} (hc : tr.CallAt y i (.ac ℓ)) (hb : ℓ.call = .block B)
    (hm : m ∈ SA.blockVotes B) :
    m ∈ (tr.state y i).ac.pool m.slot := by
  obtain ⟨i', hi, hacc, htime⟩ := Compose.acBlock_prev hr.toLocalRun hy hc hb
  rcases Compose.blockCall_cases hr.toLocalRun hy hacc with hg' |
      ⟨j, x', hij, hg', hproposes, d, p, hd, hB, _, -, -, -⟩
  · exfalso
    have hib : i' < c + (Node.exec proposer dg y (tr.state y c) t (.tick x)).2.length := by
      omega
    have hstart : i' = c := by
      by_cases hle : c ≤ i'
      · exact Compose.group_start hg hg' hle hib
      · obtain ⟨l, heq, _⟩ := Compose.before_tick hr.toLocalRun hy ⟨_, hg⟩ hacc
          (by omega) (htime.trans ht)
        cases heq
    subst i'
    have hf := Compose.group_phase hg hg'
    cases hf
  · have hcp : ∃ ℓp, tr.CallAt y (j + 1) (.ac ℓp) ∧ ℓp.call = .proposal := by
      have hd' := hd
      simp only [Node.tickStep, Node.acCall] at hd'
      have hlen :
          1 < (Node.exec proposer dg y (tr.state y j) (tr.time i') (.tick x')).2.length := by
        simp only [Node.exec, Node.onTick, Node.runSteps, Node.tickSteps, List.foldl_cons,
          List.foldl_nil, Node.tickStep, Node.acCall, hproposes, ↓reduceIte, hd']
        simp
      obtain ⟨hnode, _, _, _, hl⟩ := hg'.2.1 1 hlen
      simp only [Node.exec, Node.onTick, Node.runSteps, Node.tickSteps, List.foldl_cons,
        List.foldl_nil, Node.tickStep, Node.acCall, hproposes, ↓reduceIte, hd'] at hl
      simp only [List.nil_append,
        List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero] at hl
      exact ⟨_, ⟨hnode, hl⟩, rfl⟩
    have him : i = j + 3 := by omega
    rw [him]
    apply Growing.own_proposal_payload_pooled_run hr hy hg' hd hcp
      ⟨B, by simpa only [hij] using hacc⟩
    simpa only [hB, Node.mkBlock, SA.blockVotes] using hm

end Consensus.Goldilocks.Obligations

end
