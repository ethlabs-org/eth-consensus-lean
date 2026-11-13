module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Trees
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run

public section

/-! # Goldilocks runs: the FG projection is an FG trace with the contract (C0.5 (c))

Each honest FG call executes the FG by the cut law, on the FG part and the record of the run's
state; every honest tree is inside the honest blocks (coherent under `NoColl`). The tick order
through the FG calls: an `fg_attest` is in a tick, after only the tick's AC cuts and its own
proposal's cuts; an honest node's acceptance of its own block is the one in the tick that made
it (by unforgeability it made the block in a tick at or before; there C0.3 accepts it, so a
later acceptance would find its root held), after the tick's two AC cuts and the restarts of
that time; and the own block's attestations are `proposal_attestations`, from the pool. -/

namespace Consensus.Goldilocks.Compose

open Node

variable {P : Params} {A : NodeAC P} {dg : Digest (List (FG.Att P.n)) A.Payload}
  {proposer : Nat → Fin P.n} {H : Set (Fin P.n)} {sg : A.Msg → Fin P.n} {tr : RunTrace A}

/-- **An honest node accepts its own block in the tick that makes it**, after the tick's two
AC cuts, at the FG state before the tick, and its attestations are the proposal attestations of
that state. -/
theorem own_accept (hq : A.Requirements) (hg₀ : (P.genesisBlock A.genesisPayload).RootOk dg)
    (h : Node.LocalRun proposer dg H sg tr) (hnc : NoCollRun dg tr)
    {y : Fin P.n} (hy : y ∈ H) {i : Nat}
    {B : A.Blk} (hc : tr.CallAt y i (.fg (.block B true))) (hp : B.proposer = y) :
    ∃ j, i = j + 2 ∧ tr.TickAt proposer dg y j (tr.time i) ∧
      (∀ k, j ≤ k → k < i → ∃ ℓ : ACLabel A, tr.CallAt y k (.ac ℓ)) ∧
      (tr.state y i).fg = (tr.state y j).fg ∧
      ∃ H₀, B.fgPayload = (tr.state y j).fg.proposalAttestations H₀ := by
  obtain ⟨j', hj'i, hcall, hpos⟩ := h.block_unforgeable y hy i B ⟨true, hc⟩ (hp ▸ hy)
  rw [hp] at hcall
  obtain ⟨acc, hcall⟩ := hcall
  rcases blockCall_cases h hy hcall with hg | ⟨j, x, rfl, hg, hpr, d, p, hdp, hB, hacc, ⟨ℓ₀, c₀⟩,
    ⟨ℓ₁, c₁⟩, hfg⟩
  · exact absurd (by simpa using (hg.2.1 0 (List.length_pos_iff.2 hg.1)).2.2.2.1) hpos
  -- C0.3: the own block is accepted at its tick
  obtain ⟨cfg, hreach, hst, hstep⟩ := group_step h hy hg
  have hC03 := honest_block_accepted proposer dg y hq hg₀ cfg _ (tr.time (j + 2)) x
    hreach hstep hpr d p
    (by rw [hst]; exact hdp)
  simp only [hst] at hC03
  have key : NoCollOn dg (insert B (tr.state y j).fg.tree) →
      (tr.state y j).fg.blocks B.root = none ∧ ∃ fg', (tr.state y j).fg.onBlock B = some fg' := by
    rw [hB]
    exact hC03.2.2.2.2.2.2
  obtain ⟨-, fg', hon⟩ := key <| hnc.mono <| Set.insert_subset_iff.2
    ⟨Or.inr ⟨y, j + 2, acc, hcall⟩, tree_subset_run h hy j⟩
  obtain rfl : acc = true := hacc.2 ⟨fg', hon⟩
  have hfgB : B ∈ (tr.state y (j + 2 + 1)).fg.tree := by
    rw [tr.state_succ_of_call hcall,
      (Store.tree_grows P _ _ _ (fg_reachable h hy _)).1 B _ (h.cutLaw y hy _ _ hcall).2.1]
    exact Set.mem_insert _ _
  -- so the acceptance at `i` is that one
  obtain rfl : j + 2 = i := by
    by_contra hne
    have hnew := (accept_facts h hy hc).2.2.1
    have := tree_mono h hy (show j + 2 + 1 ≤ i by omega) hfgB
    change (tr.state y i).fg.blocks B.root = some B at this
    rw [hnew] at this
    cases this
  refine ⟨j, rfl, ⟨x, hg⟩, fun k hk hki => ?_, hfg, d.head, by rw [hB]; rfl⟩
  rcases (show k = j ∨ k = j + 1 by omega) with rfl | rfl
  exacts [⟨_, c₀⟩, ⟨_, c₁⟩]

/-- **The FG projection executes the FG** at the honest nodes (no `NoColl`): the initial state
and every FG call's step. -/
theorem fg_exec (h : Node.LocalRun proposer dg H sg tr) :
    Store.FGExec A.genesisPayload H tr.projFG := by
  refine ⟨fun y hy => by simp [RunTrace.projFG, h.init y hy, Node.initWith], fun i ℓ hl hH => ?_⟩
  have hH : tr.node i ∈ H := hH
  have hc : tr.CallAt (tr.node i) i (.fg ℓ) := projFG_callAt.1 ⟨rfl, hl⟩
  have hlaw := h.cutLaw _ hH i _ hc
  change FGLabel.Step (tr.node i) (tr.projFG.state (tr.node i) i) ℓ
    ((tr.post i).fg, (tr.post i).record)
  rw [projFG_state h hH]
  cases ℓ with
  | block B acc =>
    cases acc with
    | true => exact Or.inl ⟨rfl, hlaw.2.1, hlaw.2.2.2⟩
    | false => exact Or.inr ⟨rfl, hlaw.1, by rw [hlaw.2]⟩
  | attestation a => exact Prod.ext hlaw.1 hlaw.2.2
  | attest C s =>
    cases s with
    | none =>
      refine ⟨by rw [hlaw.2], ?_⟩
      simp only [hlaw.1]
      exact ⟨trivial, by rw [hlaw.2]⟩
    | some a =>
      exact ⟨hlaw.2.1, by simp [hlaw.1]⟩

/-- **C0.5 (c), the FG projection.** -/
theorem fg_projection : FGProjection := by
  intro P A dg H sg tr proposer hq hg₀ h hnc
  refine
    { coherent := honest_blocks_coherent h hnc
      init := (fg_exec h).init
      exec := (fg_exec h).exec
      tree_subset := fun y hy i X hX => ⟨y, hy, i, by
        rw [FGTrace.store, projFG_state h hy] at hX
        exact hX⟩
      time_nonneg := h.time_nonneg
      time_mono := h.time_mono
      attest_public := fun y hy i src signed hc => by
        obtain ⟨j, -, hg⟩ := attestCall_tick h hy (projFG_callAt.1 hc)
        exact h.tick_public y hy j _ hg
      own_first := fun y hy i B hc hp _ k hk ℓ hck => ?_
      attest_order := fun y hy j src signed hc i ℓ hij hci ht =>
        let ⟨B, acc, hℓ, hBp, hBs⟩ :=
          fg_before_attest h hy (projFG_callAt.1 hc) (projFG_callAt.1 hci) hij ht
        ⟨B, acc, hℓ, hBp, hBs⟩
      own_payload := fun y hy i B hc hp _ a ha => ?_
      unforgeable := fun y hy i a ⟨ℓ, hc, ha⟩ hv => ?_ }
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
  · have hc := projFG_callAt.1 hc
    have hpr : tr.AttCallAt y i a ∨ ∃ B, tr.BlockCallAt y i B ∧ a ∈ B.fgPayload := by
      cases ℓ with
      | block B acc =>
        cases acc with
        | true => exact Or.inr ⟨B, ⟨true, hc⟩, ha⟩
        | false => cases ha
      | attestation a' =>
        rw [FGLabel.processed, List.mem_singleton] at ha
        subst ha
        exact Or.inl hc
      | attest C s => cases ha
    obtain ⟨j, hj, src, hs⟩ := h.att_unforgeable y hy i a hpr hv
    exact ⟨j, hj, src, projFG_callAt.2 hs⟩

end Consensus.Goldilocks.Compose

end
