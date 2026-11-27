module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.FGProjection
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Handlers
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Trace
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Reachable
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Coherence
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Reach
import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Handlers

public section

/-! # Shadow P-U: the FG projection of a shadow run

`Compose.fg_tick_order'` and `Compose.fg_projection_from'` (moved from `Shadow/PU/Trace`, which
`Shadow/PU/Coherence` imports): copies of stock `Compose/Run/FGProjection` (`own_accept`,
`fg_projection_from`) and of the tick-order handler facts of `Compose/Run/Handlers`
(`attestCall_tick`, `before_tick`, `fg_before_attest`, `exec_attest`, `tick_before_attest`,
`update_attest_pos`) and `Compose/Reach` (`proposal_no_attest`) over the shadow `exec'`.
Uses `group_step'` (Shadow/PU/Handlers) and the shadow C0.3 `honest_block_accepted_from'`
(Shadow/PU/Reach). -/

namespace Consensus.Goldilocks.Compose

open Node

variable {P : Params} {A : NodeAC P}
variable {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

/-! ### Handler facts (copies of the stock private ones over `exec'`) -/

private theorem tick_cuts (y : Fin P.n) (st : NodeState A) (t : Time) (x : Nat) :
    (exec proposer dg y st t (.tick x true)).2 = (tickStep proposer dg y st t x .acTick).2 ++
      (tickStep proposer dg y (tickStep proposer dg y st t x .acTick).1 t x .proposal).2 ++
      (tickStep proposer dg y
        (tickStep proposer dg y (tickStep proposer dg y st t x .acTick).1 t x .proposal).1
        t x .fgUpdate).2 := by
  simp [exec_eq, onTick_eq, runSteps_eq, tickSteps]

private theorem tick_cuts_false (y : Fin P.n) (st : NodeState A) (t : Time) (x : Nat) :
    (exec proposer dg y st t (.tick x false)).2 = (tickStep proposer dg y st t x .acTick).2 ++
      (tickStep proposer dg y (tickStep proposer dg y st t x .acTick).1 t x .proposal).2 := by
  simp [exec_eq, onTick_eq, runSteps_eq, tickSteps]

/-- An `fg_attest` cut is in a tick (a copy of `exec_attest`). -/
theorem exec_attest (y : Fin P.n) (st : NodeState A) (t : Time) (e : Event A)
    {C : A.Blk} {s : Option (FG.Att P.n)}
    (h : Cut.fg (.attest C s) ∈ (exec proposer dg y st t e).2) : ∃ x, e = .tick x true := by
  cases e with
  | tick x fgDue =>
    cases fgDue
    · exfalso
      rw [tick_cuts_false] at h
      rcases List.mem_append.1 h with h | h
      · simp [tickStep_eq, acCall_eq] at h
      · exact proposal_no_attest proposer dg y _ t x C s h
    · exact ⟨x, rfl⟩
  | block B =>
    simp only [exec_eq, Node.onBlock_eq, acCall_eq] at h
    split_ifs at h
    · simp at h
    · split at h <;> simp at h
  | message m => simp [exec_eq, onMessage_eq, acCall_eq] at h
  | attestation a' => simp [exec_eq, onAttestation] at h
  | restart => simp [exec_eq, restart_eq, acCall_eq] at h

/-- The FG update's `fg_attest` cut is its second (a copy of `update_attest_pos`). -/
private theorem update_attest_pos (y : Fin P.n) (st : NodeState A) (t : Time) (x : Nat)
    {m : Nat} {C : A.Blk} {s : Option (FG.Att P.n)}
    (hm : (tickStep proposer dg y st t x .fgUpdate).2[m]? = some (.fg (.attest C s))) :
    m = 1 := by
  simp only [tickStep_eq, acToFG_eq] at hm
  split at hm
  · rcases m with _ | m <;> simp at hm
  simp only [attest] at hm
  split at hm
  · rcases m with _ | _ | m <;> simp at hm ⊢
  · rcases m with _ | _ | _ | m <;> simp at hm ⊢

/-- In a tick, the FG cuts before an `fg_attest` cut are the own proposal's (a copy of
`tick_before_attest`). -/
private theorem tick_before_attest (y : Fin P.n) (st : NodeState A) (t : Time) (x : Nat)
    {m m₂ : Nat} {ℓ : FGLabel P A.Payload} {C : A.Blk} {s : Option (FG.Att P.n)}
    (hm : (exec proposer dg y st t (.tick x true)).2[m]? = some (.fg ℓ))
    (hm₂ : (exec proposer dg y st t (.tick x true)).2[m₂]? = some (.fg (.attest C s)))
    (hlt : m < m₂) :
    ∃ B acc, ℓ = .block B acc ∧ B.proposer = y ∧ P.slotTime B.slot = t := by
  rw [tick_cuts] at hm hm₂
  set l := (tickStep proposer dg y st t x .acTick).2 ++
    (tickStep proposer dg y (tickStep proposer dg y st t x .acTick).1 t x .proposal).2
  have hl : l.length ≤ m₂ := by
    by_contra hlt'
    rw [List.getElem?_append_left (by omega)] at hm₂
    rcases List.mem_append.1 (List.mem_of_getElem? hm₂) with h | h
    · simp [tickStep_eq, acCall_eq] at h
    · exact proposal_no_attest proposer dg y _ t x C s h
  rw [List.getElem?_append_right hl] at hm₂
  have h₂ := update_attest_pos y _ t x hm₂
  rcases lt_trichotomy m l.length with hml | hml | hml
  · rw [List.getElem?_append_left hml] at hm
    rcases m with _ | m
    · simp [l, tickStep_eq, acCall_eq] at hm
    rw [List.getElem?_append_right (by simp [tickStep_eq]), show (m + 1 -
      (tickStep proposer dg y st t x .acTick).2.length) = m by simp [tickStep_eq]] at hm
    simp only [tickStep_eq] at hm
    split_ifs at hm with hp
    · split at hm
      · rcases m with _ | m <;>
          simp only [acProposal_eq, List.getElem?_cons_zero, List.getElem?_cons_succ,
            List.getElem?_nil, Option.some.injEq, reduceCtorEq] at hm
      rename_i d p _
      rcases m with _ | m
      · simp only [acProposal_eq, List.getElem?_cons_zero, Option.some.injEq,
          reduceCtorEq] at hm
      simp only [List.getElem?_cons_succ, proposeBlock_eq, Node.onBlock_eq] at hm
      split_ifs at hm
      · simp at hm
      split at hm <;> rcases m with _ | _ | m <;>
        simp only [acCall_eq, List.getElem?_cons_zero, List.getElem?_cons_succ,
          List.getElem?_nil, Option.some.injEq, Cut.fg.injEq, reduceCtorEq] at hm
      all_goals
        subst hm
        exact ⟨_, _, rfl, rfl, hp.2.1.symm⟩
    · simp at hm
  · subst hml
    rw [List.getElem?_append_right le_rfl, Nat.sub_self] at hm
    simp only [tickStep_eq] at hm
    split at hm <;> simp [acToFG_eq] at hm
  · omega

/-! ### In the run -/

/-- **An honest node accepts its own block in the tick that makes it**, after the tick's two
AC cuts, at the FG state before the tick, and its attestations are the proposal attestations of
that state (a copy of `own_accept`). -/
private theorem own_accept (hq : ∀ y ∈ H, ({ A with initial := ini y } : NodeAC P).Requirements)
    (hg₀ : (P.genesisBlock A.genesisPayload).RootOk dg)
    (h : Node.LocalRun proposer dg H sg tr ini) (hnc : NoCollRun dg tr)
    {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {B : A.Blk} (hc : tr.CallAt y i (.fg (.block B true))) (hp : B.proposer = y) :
    ∃ j, i = j + 2 ∧ tr.TickAt proposer dg y j (tr.time i) ∧
      (∀ k, j ≤ k → k < i → ∃ ℓ : ACLabel A, tr.CallAt y k (.ac ℓ)) ∧
      (tr.state y i).fg = (tr.state y j).fg ∧
      ∃ H₀, B.fgPayload = (tr.state y j).fg.proposalAttestations H₀ := by
  obtain ⟨j', hj'i, hcall, hpos⟩ := h.block_unforgeable y hy i B ⟨true, hc⟩ (hp ▸ hy)
  rw [hp] at hcall
  obtain ⟨acc, hcall⟩ := hcall
  rcases Coherence.blockCall_cases h hy hcall with
    hg | ⟨j, x, f, rfl, hg, hpr, d, p, hdp, hB, hacc, ⟨ℓ₀, c₀⟩, ⟨ℓ₁, c₁⟩, hfg⟩
  · have hg := (RunTrace.groupAt_iff _ _ _ _ _ _ _).1 hg
    exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  -- C0.3: the own block is accepted at its tick
  obtain ⟨cfg, hreach, hst, hstep⟩ := group_step h hy hg
  have hC03 := honest_block_accepted_from' proposer dg y (hq y hy) hg₀ cfg _ (tr.time (j + 2)) x f
    hreach hstep hpr d p (by rw [hst]; exact hdp)
  simp only [hst] at hC03
  have hfg₀ : (acProposal (tickStep proposer dg y (tr.state y j) (tr.time (j + 2)) x .acTick).1
      (tr.time (j + 2))).1.fg = (tr.state y j).fg := by
    simp only [acProposal_eq, tickStep_eq, acCall_eq]
  rw [hfg₀] at hC03
  have key : NoCollOn dg (insert B (tr.state y j).fg.tree) →
      (tr.state y j).fg.blocks B.root = none ∧ ∃ fg', (tr.state y j).fg.onBlock B = some fg' := by
    rw [hB]
    exact hC03.2.2.2.2.2.2
  obtain ⟨-, fg', hon⟩ := key <| hnc.mono <| Set.insert_subset_iff.2
    ⟨Or.inr ⟨y, j + 2, acc, hcall⟩, Coherence.tree_subset_run h hy j⟩
  obtain rfl : acc = true := hacc.2 ⟨fg', hon⟩
  have hfgB : B ∈ (tr.state y (j + 2 + 1)).fg.tree := by
    have hb := ((cutStep_block_true _ _ _ _ _).1 (h.cutLaw y hy _ _ hcall)).2.1
    rw [Store.onBlock_eq_onBlockWith] at hb
    rw [tr.state_succ_of_call hcall,
      (Store.tree_grows_with Store.finalitySpec_updateFinality).1 B _ hb]
    exact Set.mem_insert _ _
  -- so the acceptance at `i` is that one
  obtain rfl : j + 2 = i := by
    by_contra hne
    have hnew := (Coherence.accept_facts h hy hc).2.2.1
    have := Coherence.tree_mono' h hy (show j + 2 + 1 ≤ i by omega) hfgB
    change (tr.state y i).fg.blocks B.root = some B at this
    rw [hnew] at this
    cases this
  refine ⟨j, rfl, (RunTrace.tickAt_iff _ _ _ _ _ _).2 ⟨x, f, hg⟩, fun k hk hki => ?_, hfg,
    d.head, by rw [hB]; rfl⟩
  rcases (show k = j ∨ k = j + 1 by omega) with rfl | rfl
  exacts [⟨_, c₀⟩, ⟨_, c₁⟩]

/-- The tick order through the FG calls for a shadow run: the FG laws `attest_public`,
`own_first`, `attest_order` and `own_payload` of the projection (copies of `attestCall_tick`,
`own_accept`, `before_tick` and `fg_before_attest` over the shadow groups). -/
theorem fg_tick_order (hq : ∀ y ∈ H, ({ A with initial := ini y } : NodeAC P).Requirements)
    (hg₀ : (P.genesisBlock A.genesisPayload).RootOk dg)
    (h : Node.LocalRun proposer dg H sg tr ini) (hnc : NoCollRun dg tr) :
    (∀ y ∈ H, ∀ i src signed, tr.projFG.CallAt y i (.attest src signed) →
      P.IsPublic (tr.projFG.time i)) ∧
    (∀ y ∈ H, ∀ i B, tr.projFG.CallAt y i (.block B true) → B.proposer = y →
      P.slotTime B.slot = tr.projFG.time i → ∀ k < i, ∀ ℓ, tr.projFG.CallAt y k ℓ →
        tr.projFG.time k < tr.projFG.time i) ∧
    (∀ y ∈ H, ∀ j src signed, tr.projFG.CallAt y j (.attest src signed) →
      ∀ i ℓ, i < j → tr.projFG.CallAt y i ℓ → tr.projFG.time i = tr.projFG.time j →
        ∃ B acc, ℓ = .block B acc ∧ B.proposer = y ∧ P.slotTime B.slot = tr.projFG.time j) ∧
    (∀ y ∈ H, ∀ i B, tr.projFG.CallAt y i (.block B true) → B.proposer = y →
      P.slotTime B.slot = tr.projFG.time i → ∀ a ∈ B.fgPayload,
        a ∈ (tr.projFG.store y i).atts) := by
  refine ⟨fun y hy i src signed hc => ?_, fun y hy i B hc hp _ k hk ℓ hck => ?_,
    fun y hy j src signed hc i ℓ hij hci ht =>
      fg_before_attest h hy (projFG_callAt.1 hc) (projFG_callAt.1 hci) hij ht,
    fun y hy i B hc hp _ a ha => ?_⟩
  · obtain ⟨j, -, hg⟩ := attestCall_tick h hy (projFG_callAt.1 hc)
    exact h.tick_public y hy j _ hg
  · -- the own acceptance is after the tick's AC cuts and the restarts of its time
    have hc := projFG_callAt.1 hc
    have hck := projFG_callAt.1 hck
    obtain ⟨j, rfl, hg, hac, -⟩ := own_accept hq hg₀ h hnc hy hc hp
    refine lt_of_le_of_ne (h.time_mono hk.le) fun ht => ?_
    by_cases hkj : k < j
    · obtain ⟨ℓ', he, -⟩ := before_tick h hy hg hck hkj ht
      cases he
    · obtain ⟨ℓ', hℓ'⟩ := hac k (by omega) hk
      cases Option.some.inj (hck.2.symm.trans hℓ'.2)
  · have hc := projFG_callAt.1 hc
    obtain ⟨j, rfl, -, -, hfg, H₀, hpay⟩ := own_accept hq hg₀ h hnc hy hc hp
    rw [FGTrace.store, projFG_state h hy, hfg]
    rw [hpay] at ha
    exact (List.mem_filter.1 ha).1

end Consensus.Goldilocks.Compose

end
