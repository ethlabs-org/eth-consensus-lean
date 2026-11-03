module
public import ConsensusLeanTest.GoldilocksFastUpdateWitness
public import ConsensusLean.Instances.Goldilocks.Proofs.ACSteps.Main
@[expose] public section

/-! # Witness for the premises of the Goldilocks ACSteps statement A1.1 `ProposerVotersAgree`

Kind (a), joint satisfiability (CONTRIBUTING "Statements"): the hypotheses of A1.1
`ProposerVotersAgree` (`Statements/AC/Steps.lean`) hold together on the AC projection of the
one-validator tick run of `GoldilocksWitness` (`n = 1`, `Δ = 1`, `t_s = 4s`, `k = c = 2`, a tick
at every time, no restart), so the proved milestone is not vacuous. At the tick of
`t_{k+1} = 4(k + 1)` the validator, proposer of slot `k + 1`, calls `ac_proposal` at cut
`8 · t_{k+1} + 1` (`proposal_label`), which returns the payload `([cv k], [cv k])` of its own
block `blk (k + 1)` (`proposal_payload`, from `onTick_block_made`), and votes in
`ac_on_block (blk (k + 1))` at cut `8 · t_{k+1} + 3`.

* `frames_agree_slot_one`: at `s = 1` the proposal's frame (the chain `blk 0, blk 1`) and the
  voter's frame (the chain `blk 0, blk 1, blk 2`) hold the same blocks of slot at most `1`:
  both have `Φ.F = blk 0`, since `jexp 1 = jexp 2 = 0`.
* `proposerVotersAgree_premises_slot_one` bundles every hypothesis at `s = 1` (proposal cut
  `65`, time `8 = t_2`; vote cut `67`); `proposerVotersAgree_premises_satisfiable` states, at
  `sp1`, `FGP := List (FG.Att sp1.n)`, `ro1`, that there are values of all the statement's
  universally bound variables satisfying `ACRun` and every hypothesis (copied from the
  statement), with a block of slot at most `s` in the proposal's frame;
  `proposerVotersAgree_on_witness` applies the proved milestone (`acStepsAt`).

Limitations: `n = 1` and `f = 0`, and the run is one chain, so the opponents are trivially equal:
both are empty (`opponents_chain_empty` for the proposal's view, `opponents_vote_empty` for the
voter's merged view, through the milestone). The witness is at `s = 1` only: for larger `s` the
voter's `ac_on_block` follows the acceptance of `blk (s + 1)`, which can move `Φ.F` (the store
pins it only below `jexp`), and the frames' agreement on slots `≤ s` is not established here. -/

namespace Consensus.Goldilocks.Witness.One

open SA Node ChainFrame

/-! ## The proposal of slot `k + 1` -/

/-- The cut `8 · t_{k+1} + 1` is the `ac_proposal` of the tick of `t_{k+1}`. -/
theorem proposal_label (k : Nat) : (tickRun N1 dg1).label (8 * (4 * (k + 1)) + 1) =
    some (.ac ⟨.proposal, Node.frame (tickState N1 dg1 (4 * (k + 1))), []⟩) := by
  obtain ⟨fg', e, -, -, he, -, -⟩ := tickCuts_A k
  rw [tickRun_label, show (8 * (4 * (k + 1)) + 1) / 8 = 4 * (k + 1) by omega,
    show (8 * (4 * (k + 1)) + 1) % 8 = 1 by omega, he]
  rfl

theorem proposal_time (k : Nat) :
    (tickRun N1 dg1).projAC.time (8 * (4 * (k + 1)) + 1) = sp1.ts ((k + 1 : Nat) : Int) := by
  rw [time_eq, ts_nat, show (8 * (4 * (k + 1)) + 1) / 8 = 4 * (k + 1) by omega]
  push_cast
  ring

/-- `ac_proposal` at the tick of `t_{k+1}` returns the payload `([cv k], [cv k])`: the own
block `blk (k + 1)` is made from its result. -/
theorem proposal_payload (k : Nat) : ∃ d, (SA.acProposal sp1
    ((tickRun N1 dg1).projAC.state v0 (8 * (4 * (k + 1)) + 1))
    (Node.frame (tickState N1 dg1 (4 * (k + 1))))
    ((tickRun N1 dg1).projAC.time (8 * (4 * (k + 1)) + 1))).2 = some (d, ([cv k], [cv k])) := by
  obtain ⟨fg', e, -, -, he, -, -⟩ := tickCuts_A k
  have hc : Cut.fg (.block (blk (k + 1)) true) ∈ (Node.onTick (fun _ => v0) dg1 v0
      (tickState N1 dg1 (4 * (k + 1))) ((4 * (k + 1) : Nat) : Int) 0).2 := by
    rw [← tickCuts_eq, he]
    simp
  obtain ⟨d, p, hr, hB⟩ := onTick_block_made N1 dg1 v0 _ _ 0 hc (Or.inl ⟨true, rfl⟩)
  have hp : p = ([cv k], [cv k]) := by
    rw [← blk_acPayload k, hB]
    rfl
  subst hp
  refine ⟨d, ?_⟩
  rw [projAC_state', state_eq, time_eq, show (8 * (4 * (k + 1)) + 1) / 8 = 4 * (k + 1) by omega,
    show (8 * (4 * (k + 1)) + 1) % 8 = 1 by omega, tickMid_one]
  exact hr

/-- (a) **`ProposalAt` on the tick run**: the proposer `v0` of slot `k + 1` proposes at cut
`8 · t_{k+1} + 1` with the payload `([cv k], [cv k])`. -/
theorem proposalAt_tickRun (k : Nat) :
    ProposalAt (tickRun N1 dg1).projAC v0 (8 * (4 * (k + 1)) + 1)
      ⟨.proposal, Node.frame (tickState N1 dg1 (4 * (k + 1))), []⟩ ([cv k], [cv k]) :=
  ⟨Compose.projAC_callAt.2 ⟨rfl, proposal_label k⟩, rfl, proposal_payload k⟩

/-! ## The frames at slot `1` -/

/-- (a) **The proposal's frame and the voter's frame agree on slots `≤ 1`**: both trees are
chains from `blk 0`, up to `blk 1` and `blk 2`. -/
theorem frames_agree_slot_one {fg' : Store sp1.toParams N1.Payload} (hfg : FGGood fg' (1 + 1)) :
    {X | X ∈ (Node.frame (tickState N1 dg1 (4 * (1 + 1)))).tree ∧ X.slot ≤ 1} =
      {X | X ∈ fg'.toFrame.tree ∧ X.slot ≤ 1} := by
  obtain ⟨f, hf⟩ := good_frame (good_tick (4 * (1 + 1)))
  rw [tip_A] at hf
  obtain ⟨f', hf'⟩ := fgGood_frame hfg
  obtain rfl : f = 0 := Nat.le_zero.1 hf.fj
  obtain rfl : f' = 0 := Nat.le_zero.1 hf'.fj
  ext X
  simp only [Set.mem_ofPred_eq]
  rw [hf.tree, hf'.tree]
  constructor
  · rintro ⟨⟨m, -, -, rfl⟩, hs⟩
    rw [blk_slot] at hs
    exact ⟨⟨m, Nat.zero_le _, by omega, rfl⟩, by rw [blk_slot]; exact hs⟩
  · rintro ⟨⟨m, -, -, rfl⟩, hs⟩
    rw [blk_slot] at hs
    exact ⟨⟨m, Nat.zero_le _, hs, rfl⟩, by rw [blk_slot]; exact hs⟩

/-- (a) **The premises of A1.1 (`ProposerVotersAgree`) at `s = 1`**: the proposal of slot `2`
at cut `65` (time `t_2 = 8`, payload `([cv 1], [cv 1])`), the slot-`2` vote at cut `67` in
`ac_on_block (blk 2)`, `blk 2` in the voter's frame with that payload, `Sync[t_1, t_2]`, and the
two frames agreeing on slots `≤ 1`. -/
theorem proposerVotersAgree_premises_slot_one :
    ∃ (fg' : Store sp1.toParams N1.Payload) (e : N1.Em),
      ProposalAt (tickRun N1 dg1).projAC v0 (8 * (4 * (1 + 1)) + 1)
        ⟨.proposal, Node.frame (tickState N1 dg1 (4 * (1 + 1))), []⟩ ([cv 1], [cv 1]) ∧
      (tickRun N1 dg1).projAC.time (8 * (4 * (1 + 1)) + 1) = sp1.ts ((1 + 1 : Nat) : Int) ∧
      CastAt (tickRun N1 dg1).projAC v0 (8 * (4 * (1 + 1)) + 3)
        ⟨.block (blk (1 + 1)), fg'.toFrame, [e]⟩ e ∧ e.msg.slot = 1 + 1 ∧
      (∃ P ∈ fg'.toFrame.tree, P.slot = 1 + 1 ∧ P.acPayload = ([cv 1], [cv 1])) ∧
      SyncAC N1 Set.univ ((tickRun N1 dg1).HonestBlocks Set.univ) (sp1.ts 1)
        (sp1.ts ((1 + 1 : Nat) : Int)) (tickRun N1 dg1).projAC ∧
      {X | X ∈ (Node.frame (tickState N1 dg1 (4 * (1 + 1)))).tree ∧ X.slot ≤ 1} =
        {X | X ∈ fg'.toFrame.tree ∧ X.slot ≤ 1} := by
  obtain ⟨fg', e, hl, hfg', hm, -⟩ := vote_label 1
  obtain ⟨f', hf'⟩ := fgGood_frame hfg'
  have hf1 : f' ≤ 1 := le_trans hf'.fj (jexp_succ_le 1)
  refine ⟨fg', e, proposalAt_tickRun 1, proposal_time 1,
    ⟨Compose.projAC_callAt.2 ⟨rfl, hl⟩, List.mem_singleton_self _⟩, by rw [hm]; rfl,
    ⟨blk (1 + 1), hf'.mem (by omega) le_rfl, blk_slot _, blk_acPayload 1⟩,
    Compose.sync_projection _ _ _ _ _ _ _ _ _ _ tickRun_goldilocksRun.toLocalRun
      (tickRun_syncOn _ _ id fun _ => le_rfl), frames_agree_slot_one hfg'⟩

/-- (a) **A1.1, `ProposerVotersAgree`: the premises are satisfiable.** Every hypothesis of the
statement holds of the AC projection of the tick run at `s = 1`, with `p = y = v0` the proposer
of slot `2`, and the proposal's frame holds a block of slot at most `s` (`blk 0`), so the
conclusion is not vacuous. -/
theorem proposerVotersAgree_premises_satisfiable :
    ∃ (H : Set (Fin sp1.n)) (U : Set (Blk sp1.n (List (FG.Att sp1.n))))
      (tr : SATrace sp1 (List (FG.Att sp1.n)) ro1) (proposer : Nat → Fin sp1.n) (s : Nat)
      (p y : Fin sp1.n) (i j : Nat)
      (ℓp ℓy : ACLabel (goldilocksSA sp1 (List (FG.Att sp1.n)) ro1))
      (pay : Payload sp1.n) (e : Em sp1 (List (FG.Att sp1.n))),
    ACRun proposer tr H U ∧
    p ∈ H ∧ y ∈ H ∧ p = proposer (s + 1) ∧
    ProposalAt tr p i ℓp pay ∧ tr.time i = sp1.ts (s + 1 : Nat) ∧
    CastAt tr y j ℓy e ∧ e.msg.slot = s + 1 ∧
    (∃ P ∈ ℓy.frame.tree, P.slot = s + 1 ∧ P.acPayload = pay) ∧
    SyncAC (goldilocksSA sp1 (List (FG.Att sp1.n)) ro1) H U (sp1.ts s) (sp1.ts (s + 1 : Nat))
      tr ∧
    {X | X ∈ ℓp.frame.tree ∧ X.slot ≤ s} = {X | X ∈ ℓy.frame.tree ∧ X.slot ≤ s} ∧
    ∃ B ∈ ℓp.frame.tree, B.slot ≤ s := by
  obtain ⟨fg', e, hp, ht, hc, hs, hP, hsy, heq⟩ := proposerVotersAgree_premises_slot_one
  obtain ⟨f, hf⟩ := good_frame (good_tick (4 * (1 + 1)))
  rw [tip_A] at hf
  obtain rfl : f = 0 := Nat.le_zero.1 hf.fj
  exact ⟨Set.univ, _, _, fun _ => v0, 1, v0, v0, _, _, _, _, _, e, acRun, Set.mem_univ _,
    Set.mem_univ _, rfl, hp, ht, hc, hs, hP, hsy, heq, blk 0, hf.mem le_rfl (Nat.zero_le _),
    by rw [blk_slot]; exact Nat.zero_le _⟩

/-! ## The milestone on the witness -/

/-- (a) A1.1 on the run at `s = 1`: the proposal's view and the voter's merged view give the
same opponents (against the slot-`1` votes) to every block of slot at most `1` of the
proposal's frame. -/
theorem proposerVotersAgree_on_witness :
    ∃ (fg' : Store sp1.toParams N1.Payload) (e : N1.Em),
      CastAt (tickRun N1 dg1).projAC v0 (8 * (4 * (1 + 1)) + 3)
        ⟨.block (blk (1 + 1)), fg'.toFrame, [e]⟩ e ∧
      ∀ B ∈ (Node.frame (tickState N1 dg1 (4 * (1 + 1)))).tree, B.slot ≤ 1 →
        opponents sp1 (Node.frame (tickState N1 dg1 (4 * (1 + 1))))
            (View.ofLists ([cv 1], [cv 1])) ((1 : Nat) : Int) B =
          opponents sp1 fg'.toFrame (mergedVoteView sp1 e.readPoint fg'.toFrame (1 + 1))
            ((1 : Nat) : Int) B := by
  obtain ⟨fg', e, hp, ht, hc, hs, hP, hsy, heq⟩ := proposerVotersAgree_premises_slot_one
  refine ⟨fg', e, hc, fun B hB hBs => ?_⟩
  exact (acStepsAt sp1).proposerVotersAgree (List (FG.Att sp1.n)) ro1 Set.univ
    ((tickRun N1 dg1).HonestBlocks Set.univ) (tickRun N1 dg1).projAC (fun _ => v0) acRun 1 v0 v0
    (8 * (4 * (1 + 1)) + 1) (8 * (4 * (1 + 1)) + 3)
    ⟨.proposal, Node.frame (tickState N1 dg1 (4 * (1 + 1))), []⟩
    ⟨.block (blk (1 + 1)), fg'.toFrame, [e]⟩ ([cv 1], [cv 1]) e (Set.mem_univ _) (Set.mem_univ _)
    rfl hp ht hc hs hP hsy heq B hB hBs

/-- On a chain frame, the view of copies of one vote gives no block an opponent: nobody
equivocates, and every two blocks of the frame are compatible. -/
theorem opponents_chain_empty {Φ : N1.Frm} {f j τ : Nat} (hΦ : ChainFrame Φ f j τ)
    (w : Vote sp1.n) (σ : Int) {B : N1.Blk} (hB : B ∈ Φ.tree) :
    opponents sp1 Φ (View.ofLists ([w], [w])) σ B = ∅ := by
  ext i
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro (⟨x, hx, z, hz, hne, -, -⟩ | ⟨x, -, -, -, H, hH, -, hnc⟩)
  · exact hne ((List.mem_singleton.1 hx).trans (List.mem_singleton.1 hz).symm)
  · exact hnc (compatible_chain hΦ hH hB)

/-- (a) **The opponents of A1.1's conclusion on the run are empty on both sides**: the
proposal's view gives none (`opponents_chain_empty`), so neither does the voter's merged view. -/
theorem opponents_vote_empty :
    ∃ (fg' : Store sp1.toParams N1.Payload) (e : N1.Em),
      CastAt (tickRun N1 dg1).projAC v0 (8 * (4 * (1 + 1)) + 3)
        ⟨.block (blk (1 + 1)), fg'.toFrame, [e]⟩ e ∧
      ∀ B ∈ (Node.frame (tickState N1 dg1 (4 * (1 + 1)))).tree, B.slot ≤ 1 →
        opponents sp1 fg'.toFrame (mergedVoteView sp1 e.readPoint fg'.toFrame (1 + 1))
          ((1 : Nat) : Int) B = ∅ := by
  obtain ⟨fg', e, hc, h⟩ := proposerVotersAgree_on_witness
  obtain ⟨f, hf⟩ := good_frame (good_tick (4 * (1 + 1)))
  exact ⟨fg', e, hc, fun B hB hBs => (h B hB hBs).symm.trans (opponents_chain_empty hf _ _ hB)⟩

end Consensus.Goldilocks.Witness.One

end
