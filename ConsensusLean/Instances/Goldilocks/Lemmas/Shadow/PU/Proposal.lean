module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Reachable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Coherence
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Reach
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Run

public section

/-! # Shadow P-U: proposal and attestation interfaces

The proposal and attestation source proofs use the stock handler-cut arguments.
This module stays downstream of Run and Coherence; neither supplier module imports it.
-/

namespace Consensus.Goldilocks.Coherence

open AC (ACParams ReplayOrder Payload)

section Proposals

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}
  {proposer : Nat → Fin sp.n} {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)}
  {H : Set (Fin sp.n)} {tr : GoldilocksTrace sp ro}

/-- An honest proposal is accepted at its cut, from arbitrary run starts. -/
theorem accept_of_proposesAt {ini : Fin sp.n → (goldilocksNode sp ro).State}
    (hrun : GoldilocksRun proposer dg H tr ini) (hnc : Compose.NoCollRun dg tr)
    {p : Fin sp.n} (hp : p ∈ H) {k : Nat} {W : AC.Blk sp.n (List (FG.Att sp.n))}
    (hW : tr.ProposesAt p k W) :
    tr.AcceptAt p k W ∧ W ∈ (tr.state p (k + 1)).fg.tree ∧ tr.post k = tr.state p (k + 1) := by
  have h := hrun.toLocalRun
  obtain ⟨⟨⟨acc, hc⟩, hpos⟩, -, -⟩ := hW
  rcases blockCall_cases h hp hc with hg |
    ⟨j, x, fgDue, rfl, hg, hpr, d, p', hdp, rfl, -, -, -, -⟩
  · rw [RunTrace.groupAt_iff] at hg
    exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  have hreq := Compose.requirements_from sp ro (hrun.vstart p)
  obtain ⟨hacc, -⟩ := Healing.own_block_accepted h hreq hrun.genesis_root_ok hnc hp hg hpr hdp
  have he := hc.2.symm.trans hacc.2
  simp only [Option.some.injEq, Cut.fg.injEq, FGLabel.block.injEq] at he
  obtain rfl := he.2
  exact ⟨hc, accept_mem_from h hp hc, (tr.state_succ_of_call hc).symm⟩

/-- Extraction of the AC proposal run from the proposal cut. -/
theorem honestProposalRun_of_proposesAt {ini} (hrun : GoldilocksRun proposer dg H tr ini)
    (hnc : Compose.NoCollRun dg tr)
    {p : Fin sp.n} {kP s : Nat} {P : AC.Blk sp.n (List (FG.Att sp.n))}
    (hp : p ∈ H) (hpp : p = proposer s) (hP : tr.ProposesAt p kP P)
    (hPs : P.slot = s) : Healing.HonestProposalRun tr H proposer s P := by
  have h := hrun.toLocalRun
  subst p
  obtain ⟨⟨⟨acc, hc⟩, hpos⟩, -, htk⟩ := hP
  refine ⟨hp, ?_⟩
  rcases blockCall_cases h hp hc with hg |
    ⟨j, x, fgDue, rfl, hg, hpr, d, pay, hdp, hB, -, -, -, -⟩
  · rw [RunTrace.groupAt_iff] at hg
    exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  have hreq := Compose.requirements_from sp ro (hrun.vstart (proposer s))
  obtain ⟨hc1, ht1, hst1⟩ := tick_proposal_call h hp hg hpr
  obtain ⟨hacc, ht2⟩ := Healing.own_block_accepted h hreq hrun.genesis_root_ok hnc hp hg hpr hdp
  obtain ⟨hacc3, ht3, -⟩ := Healing.ac_block_after h hp hacc
  simp only [Node.acProposal_eq] at hc1
  simp only [Node.acProposal_eq, Node.tickStep_eq, Node.acCall_eq] at hacc3
  have hts : tr.time (j + 2) = sp.ts s := by
    rw [htk, sp.slotTime_eq, hPs]; rfl
  subst hB
  refine ⟨j + 1, ⟨.proposal, Node.frame
    (Node.tickStep proposer dg _ (tr.state _ j) (tr.time (j + 2)) x .acTick).1, []⟩,
    d, pay, Compose.projAC_callAt.2 hc1, rfl, ?_, ht1.trans hts, rfl, hPs, rfl,
    rfl, j + 3, by omega, hacc3, ht3.trans (ht2.trans hts)⟩
  have ht1' : tr.projAC.time (j + 1) = tr.time (j + 2) := ht1
  rw [Compose.projAC_state' h hp, hst1, ht1']
  simpa only [Node.acProposal_eq] using hdp

end Proposals

section Attestations

open Node

variable {P : Params} {A : NodeAC P} {proposer : Nat → Fin P.n}
  {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

private theorem proposal_no_attest {y : Fin P.n} (st : NodeState A) (t : Time) (x : Nat)
    (C : A.Blk) (s : Option (FG.Att P.n)) :
    Cut.fg (.attest C s) ∉ (tickStep proposer dg y st t x .proposal).2 := by
  simp only [tickStep_eq]
  split_ifs
  · split
    · simp [acProposal_eq]
    · simp only [proposeBlock_eq, onBlock_eq]
      split_ifs
      · simp [acProposal_eq]
      · split <;> simp [acProposal_eq, acCall_eq]
  · simp

private theorem tick_cuts (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) :
    (exec proposer dg y st t (.tick x true)).2 = (tickStep proposer dg y st t x .acTick).2 ++
      (tickStep proposer dg y (tickStep proposer dg y st t x .acTick).1 t x .proposal).2 ++
      (tickStep proposer dg y
        (tickStep proposer dg y (tickStep proposer dg y st t x .acTick).1 t x .proposal).1
        t x .fgUpdate).2 := by
  simp [exec_eq, onTick_eq, runSteps_eq, tickSteps]

private theorem signed_only_in_ticks (dg : Digest (List (FG.Att P.n)) A.Payload)
    (self : Fin P.n) (st : NodeState A) (t : Time) (e : Event A) (C : A.Blk) (a : FG.Att P.n)
    (h : Cut.fg (.attest C (some a)) ∈ (exec proposer dg self st t e).2) :
    ∃ x, e = .tick x true := by
  cases e with
  | tick x fgDue =>
    cases fgDue
    · exfalso
      simp only [exec_eq, onTick_eq, runSteps_eq, tickSteps, Bool.false_eq_true,
        ↓reduceIte, List.foldl_cons, List.foldl_nil, List.nil_append, List.mem_append] at h
      rcases h with h | h
      · simp [tickStep_eq, acCall_eq] at h
      · exact proposal_no_attest _ t x C _ h
    · exact ⟨x, rfl⟩
  | block B =>
    simp only [exec_eq, onBlock_eq, acCall_eq] at h
    split_ifs at h
    · simp at h
    · split at h <;> simp at h
  | message m => simp [exec_eq, onMessage_eq, acCall_eq] at h
  | attestation a' => simp [exec_eq, onAttestation] at h
  | restart => simp [exec_eq, restart_eq, acCall_eq] at h

private theorem update_attest (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (x : Nat) {m : Nat} {C : A.Blk} {a : FG.Att P.n}
    (hm : (tickStep proposer dg y st t x .fgUpdate).2[m]? = some (.fg (.attest C (some a)))) :
    m = 1 ∧ (tickStep proposer dg y st t x .fgUpdate).2[0]? =
      some (.ac ⟨.toFG, frame st, []⟩) ∧ (A.toFG st.ac (frame st) t).2 = some C := by
  simp only [tickStep_eq, acToFG_eq] at hm ⊢
  split at hm
  · rcases m with _ | m <;>
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
        Option.some.injEq, reduceCtorEq] at hm
  rename_i C' hC'
  simp only [attest] at hm
  split at hm
  · rcases m with _ | _ | m <;>
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ,
        List.getElem?_nil, Option.some.injEq, Cut.fg.injEq, FGLabel.attest.injEq,
        reduceCtorEq, and_false] at hm
  rcases m with _ | _ | m <;>
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
      Option.some.injEq, Cut.fg.injEq, FGLabel.attest.injEq, reduceCtorEq] at hm
  obtain ⟨rfl, -⟩ := hm
  exact ⟨rfl, rfl, hC'⟩

private theorem attest_prev (dg : Digest (List (FG.Att P.n)) A.Payload) (y : Fin P.n)
    (st : NodeState A) (t : Time) (e : Event A) {k : Nat} {C : A.Blk} {a : FG.Att P.n}
    (hk : (exec proposer dg y st t e).2[k]? = some (.fg (.attest C (some a)))) :
    ∃ k', k = k' + 1 ∧ ∃ st₁, CutChain y t st ((exec proposer dg y st t e).2.take k') st₁ ∧
      (exec proposer dg y st t e).2[k']? = some (.ac ⟨.toFG, frame st₁, []⟩) ∧
      (A.toFG st₁.ac (frame st₁) t).2 = some C := by
  obtain ⟨x, rfl⟩ := signed_only_in_ticks dg y st t e C a (List.mem_of_getElem? hk)
  rw [tick_cuts] at hk ⊢
  set l₁ := (tickStep proposer dg y st t x .acTick).2 with hl₁
  set r₂ := tickStep proposer dg y (tickStep proposer dg y st t x .acTick).1 t x .proposal
  have hch : CutChain y t st (l₁ ++ r₂.2) r₂.1 :=
    Compose.chain_append' y (Compose.tickStep_chain' proposer dg y st t x _)
      (Compose.tickStep_chain' proposer dg y _ t x _)
  have hn : (l₁ ++ r₂.2).length ≤ k := by
    by_contra hlt
    rw [List.getElem?_append_left (by omega)] at hk
    rcases List.mem_append.1 (List.mem_of_getElem? hk) with hm | hm
    · simp [hl₁, tickStep_eq, acCall_eq] at hm
    · exact proposal_no_attest _ t x C _ hm
  rw [List.getElem?_append_right hn] at hk
  obtain ⟨hm, h0, hC⟩ := update_attest dg y r₂.1 t x hk
  refine ⟨(l₁ ++ r₂.2).length, by omega, r₂.1, by rw [List.take_left' rfl]; exact hch, ?_, hC⟩
  rw [List.getElem?_append_right le_rfl, Nat.sub_self]
  exact h0

/-- An attestation is sourced by the immediately preceding AC toFG call. -/
theorem attest_source (h : Node.LocalRun proposer dg H sg tr ini) {y : Fin P.n} (hy : y ∈ H)
    {j : Nat} {C : A.Blk} {a : FG.Att P.n} (hc : tr.CallAt y j (.fg (.attest C (some a)))) :
    ∃ j', j = j' + 1 ∧ ∃ ℓ : ACLabel A, tr.CallAt y j' (.ac ℓ) ∧ ℓ.call = .toFG ∧
      tr.time j' = tr.time j ∧ (A.toFG (tr.state y j').ac ℓ.frame (tr.time j')).2 = some C ∧
      (tr.state y j).fg = (tr.state y j').fg := by
  obtain ⟨j₀, e, k, hg, rfl, hk⟩ := call_in_group h hy hc
  obtain ⟨k', rfl, st₁, hch, hk', hC⟩ := attest_prev dg y _ _ e hk
  have hlen := (List.getElem?_eq_some_iff.1 hk').1
  have hst : tr.state y (j₀ + k') = st₁ := by
    have hg' := (RunTrace.groupAt_iff _ _ _ _ _ _ _).1 hg
    have := Compose.cutChain_run' h hy hch j₀ rfl fun m hm => by
      rw [List.length_take] at hm
      obtain ⟨hn, ht, -, -, hl⟩ := hg'.2.1 m (by omega)
      exact ⟨hn, ht, by rw [hl, List.getElem_take]⟩
    rwa [List.length_take, min_eq_left hlen.le] at this
  obtain ⟨hc', ht⟩ := Compose.group_cut hg hk'
  refine ⟨j₀ + k', by omega, _, hc', rfl, ht, by rw [hst, ht]; exact hC, ?_⟩
  rw [show j₀ + (k' + 1) = j₀ + k' + 1 by omega, tr.state_succ_of_call hc']
  exact ((cutStep_ac _ _ _ _ _).1 (h.cutLaw y hy _ _ hc')).2.2.1

end Attestations

end Consensus.Goldilocks.Coherence
