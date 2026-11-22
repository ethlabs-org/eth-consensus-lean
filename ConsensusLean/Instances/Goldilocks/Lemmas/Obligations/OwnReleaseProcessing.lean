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
theorem acBlock_cut_cases (hv : rho.ExecutionValid) {y : Fin (Fintype.card V)} {i : Nat}
    {ℓ : ACLabel (goldilocksNode (S.params (Model.pubOf E) hn) (S.ro _))}
    {B : Blk (S.params (Model.pubOf E) hn)} {m : SA.Vote (Fintype.card V)}
    (hc : (simTrace S rho hn).CallAt y i (.ac ℓ)) (hb : ℓ.call = .block B)
    (hm : m ∈ SA.blockVotes B) :
    (∃ k, (simTrace S rho hn).projAC.ProcessAt y k m ∧
        (simTrace S rho hn).time k = (simTrace S rho hn).time i) ∨
      ∃ n v t, rho.events[n]? = some (.tick v t) ∧
        (S.params (Model.pubOf E) hn).toParams.IsPublic t ∧ rho.ownKey v = y ∧
        cutMap S rho hn n ≤ i ∧ i < cutMap S rho hn (n + 1) ∧ (simTrace S rho hn).time i = t := by
  rw [(simTrace_encoding S rho hn).1] at hc ⊢
  rw [(simTrace_encoding S rho hn).2]
  apply NodeAsChainShape.CanonicalTrace.acBlock_cut_cases (traceEncoding S hn) rho
    (traceEncoding_opLaws S hn) hv hc hb
  apply traceEncoding_induction S hn (fun e _ =>
    ∀ o : (Model.protoOf (compiled (goldilocks S)) E).Object,
      ∃ w ∈ e.codec.carried B.fgPayload B.acPayload,
        NodeAsChainShape.canonEvent e.codec (Model.digests rho.hash o) w = some (.message m))
  intro _ _ o
  exact ⟨voteObj (binding := S.vote) m,
    List.mem_append_right _ (List.mem_map.mpr ⟨m, List.mem_append_left _ hm, rfl⟩),
    canonEvent_voteObj (sp := S.params (Model.pubOf E) hn) (ro := S.ro _)
      (Model.digests rho.hash o) m⟩

end Events

variable {sp : SA.SAParams} {ro : SA.ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (SA.Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- **An AC block cut inside a tick group has its votes pooled.** In a Goldilocks run, an honest
`y`'s AC cut `i` calling the block `B`, inside `y`'s tick group at cut `c` and time `t`, has every
`m ∈ blockVotes B` in `y`'s pool before the cut: the block is not a delivered one (the tick group
starts with the tick), so it is `y`'s own proposal (`own_proposal_payload_pooled_run`). -/
theorem acBlock_vote_pooled_in_tick {ini} (hr : GoldilocksRun proposer dg H tr ini)
    {y : Fin sp.n}
    (hy : y ∈ H) {c i : Nat} {t : Time} {x : Nat} (hg : tr.GroupAt proposer dg y c t (.tick x))
    (hlo : c ≤ i) (hhi : i < c + (Node.exec proposer dg y (tr.state y c) t (.tick x)).2.length)
    (ht : tr.time i = t) {ℓ : ACLabel (goldilocksNode sp ro)} {B : Blk sp}
    {m : SA.Vote sp.n} (hc : tr.CallAt y i (.ac ℓ)) (hb : ℓ.call = .block B)
    (hm : m ∈ SA.blockVotes B) :
    m ∈ (tr.state y i).ac.pool m.slot := by
  obtain ⟨σ, hmem⟩ := Compose.acBlock_vote_pooled_in_tick hr.toLocalRun
    (pooled := fun a m => ∃ σ, m ∈ a.pool σ) (carries := fun p m => m ∈ p.1)
    (fun _ _ _ _ _ hd hm => Growing.proposal_pool (ro := ro) hd hm)
    (Growing.proposal_preserves_pool (ro := ro) y) hy hg hlo hhi ht hc hb hm
  have hslot := (Compose.state_pool_cap hr hy i σ).1 m
    (by simpa only [Compose.projAC_state hr.toLocalRun hy] using hmem)
  rwa [hslot]

end Consensus.Goldilocks.Obligations

end
