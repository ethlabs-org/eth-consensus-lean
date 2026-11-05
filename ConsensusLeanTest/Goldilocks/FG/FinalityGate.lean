module
public import ConsensusLeanTest.Goldilocks.FG.Faulty
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Finality
@[expose] public section

/-! # Witness for `FinalityBeforeGate` (G0.8) and its quorum boundary

At `n = 4` (`gp4`, `q = 3`), chain A's prefix of two blocks (`chainA`, signed by validators
`0, 1, 2`) has chain state `σP`: height `3`, entered by block `2`, its previous height `2`
justified by `J = 1` (a block, not genesis), `(2, 1)` pending and not finalized. Chain A's third
block `B` is accepted on `σP`, and `σPre` is the state that `stateTransition` hands to
`heightEvents` (the attestations counted, the latest block set), before the finality step.
Labelled by kind (CONTRIBUTING "Statements"):

* (a) `finality_gate_premises`: the five premises of `FinalityBeforeGate` hold together at
  `σPre`, with `J` not genesis and a target quorum. `finality_gate_witness` is
  `finality_before_gate`'s conclusion there: the finality step finalizes `(h_j, J) = (2, 1)` and
  the same block justifies; `finalizePrune_σPre` computes the same values directly.
* (c) `control_premises`: block `B'` differs from `B` only in validator `2`'s finality pair,
  which it leaves empty, so `q − 1 = 2` validators sign the finality pair `(2, 1)`. `B'` is
  accepted on `σP`, and its pre-finalize state `σPre'` keeps every other premise and the target
  quorum (`σPre'_eq`), but `(2, 1)` is not finalized and the block does not justify
  (`control_not_finalized`): the finality quorum premise cannot be dropped. -/

namespace Consensus.Goldilocks.FinalityGateWitness

open FG FaultyWitness

/-! ## The parent state and the accepted block -/

/-- The chain state of chain A's prefix of two blocks. -/
def σP : ChainState 4 := (gp4.chainState (chainA.take 2)).get (by decide +kernel)

/-- Chain A's prefix of two blocks is accepted, with chain state `σP`. -/
theorem chainState_parent : gp4.chainState (chainA.take 2) = some σP :=
  (Option.some_get _).symm

/-- The parent state `σP`: height `3` entered by block `2` (slot `2`), its previous height `2`
justified by block `1` (not genesis), genesis finalized at height `1`, `(2, 1)` pending with no
finality bit, no target or progress bit. -/
theorem σP_eq :
    σP.h = 3 ∧ σP.Th = 2 ∧ σP.hj = 2 ∧ σP.J = 1 ∧
      (σP.L, σP.s, σP.ThSlot, σP.F, σP.hF) = (2, 2, 2, 0, 1) ∧ σP.pending = [(2, 1)] ∧
      σP.fin 2 = ∅ ∧ σP.target = ∅ ∧ σP.prog = ∅ ∧ σP.previousHeightJustified ∧
      σP.J ≠ gp4.genesis := by
  decide +kernel

/-- Chain A's third block: block `3` at slot `3`, the target votes of `0, 1, 2` for the entry
`(3, 2)` of `σP`, each with the finality pair `(2, 1)`. -/
def B : FGBlock 4 := ⟨3, 3, 0, tvs [0, 1, 2] 3 2 (some (2, 1))⟩

/-- `B` is chain A's third block. -/
theorem chainA_eq : chainA = chainA.take 2 ++ [B] := rfl

/-- The state that `stateTransition σP B` hands to `heightEvents`: `B`'s attestations counted,
the latest block set, before the finality step. -/
def σPre : ChainState 4 :=
  { B.atts.foldl ChainState.processAtt { σP with s := B.slot } with L := B.root }

/-- `B` is accepted on `σP`, and the accepted state is `heightEvents σPre`. -/
theorem stateTransition_B : gp4.stateTransition σP B = some (gp4.heightEvents σPre) := by
  rw [FGParams.stateTransition, ite_eq_left (by decide +kernel)]
  rfl

/-- Chain A is accepted, and its chain state is the accepted state of `B` on `σP`. -/
theorem chainState_chainA : gp4.chainState chainA = some (gp4.heightEvents σPre) := by
  rw [chainA_eq, FGParams.chainState, List.foldl_append, ← FGParams.chainState,
    chainState_parent]
  exact stateTransition_B

/-- The pre-finalize state `σPre`: `σP` with slot `3`, latest block `3`, and the finality bits
of `0, 1, 2` for height `2`; the target and progress bits of `0, 1, 2`. -/
theorem σPre_eq :
    σPre.h = 3 ∧ σPre.Th = 2 ∧ σPre.hj = 2 ∧ σPre.J = 1 ∧
      (σPre.L, σPre.s, σPre.ThSlot, σPre.F, σPre.hF) = (3, 3, 2, 0, 1) ∧
      σPre.pending = [(2, 1)] ∧ σPre.fin 2 = {0, 1, 2} ∧ σPre.target = {0, 1, 2} ∧
      σPre.prog = {0, 1, 2} := by
  decide +kernel

/-! ## The witness -/

/-- (a) The premises of `FinalityBeforeGate` hold together at `σPre`: previous height justified,
`(h_j, J) = (2, 1)` pending, the pending pairs increasing and none above `h_j`, a finality quorum
for `h_j`; and `J` is not genesis, and there is a target quorum. -/
theorem finality_gate_premises :
    σPre.previousHeightJustified ∧ (σPre.hj, σPre.J) ∈ σPre.pending ∧
      σPre.pending.Pairwise (fun p r => p.1 < r.1) ∧ (∀ p ∈ σPre.pending, p.1 ≤ σPre.hj) ∧
      gp4.q ≤ (σPre.fin σPre.hj).card ∧ σPre.J ≠ gp4.genesis ∧ gp4.q ≤ σPre.target.card := by
  decide +kernel

/-- `finality_before_gate` at `σPre`: the finality step finalizes `J = 1` at `h_j = 2`, and the
same block justifies. -/
theorem finality_gate_witness :
    (gp4.finalizePrune σPre).hF = 2 ∧ (gp4.finalizePrune σPre).F = 1 ∧
      gp4.justifies (gp4.finalizePrune σPre) := by
  obtain ⟨hb, hm, hpw, hle, hq, -, ht⟩ := finality_gate_premises
  obtain ⟨hF, hJ, hjust⟩ := finality_before_gate gp4 σPre hb hm hpw hle hq
  obtain ⟨-, -, hhj, hJ', -⟩ := σPre_eq
  exact ⟨hF.trans hhj, hJ.trans hJ', hjust ht⟩

/-- The finality step at `σPre`, computed: `(2, 1)` finalized and pruned, the block justifies;
the accepted state enters height `4` by block `3`, justifying block `2` at height `3`. -/
theorem finalizePrune_σPre :
    (gp4.finalizePrune σPre).hF = 2 ∧ (gp4.finalizePrune σPre).F = 1 ∧
      (gp4.finalizePrune σPre).pending = [] ∧ gp4.justifies (gp4.finalizePrune σPre) ∧
      ((gp4.heightEvents σPre).h, (gp4.heightEvents σPre).Th, (gp4.heightEvents σPre).hj,
        (gp4.heightEvents σPre).J, (gp4.heightEvents σPre).hF, (gp4.heightEvents σPre).F) =
        (4, 3, 3, 2, 2, 1) := by
  decide +kernel

/-! ## The control: one finality signer short of the quorum -/

/-- Block `B` with validator `2`'s finality pair left empty: the target votes of `0, 1, 2` for
`(3, 2)`, only `0` and `1` with the finality pair `(2, 1)`. -/
def B' : FGBlock 4 := ⟨3, 3, 0, tvs [0, 1] 3 2 (some (2, 1)) ++ [tv 2 3 2 none]⟩

/-- `B'` has `B`'s root, slot and proposer, and the same attestations except for validator `2`'s
finality pair. -/
theorem B'_eq :
    (B'.root, B'.slot, B'.proposer) = (B.root, B.slot, B.proposer) ∧
      B'.atts.map (fun a => (a.val, a.h, a.T, a.timeout)) =
        B.atts.map (fun a => (a.val, a.h, a.T, a.timeout)) ∧
      B'.atts.map Att.fin = [some (2, 1), some (2, 1), none] ∧
      B.atts.map Att.fin = [some (2, 1), some (2, 1), some (2, 1)] := by
  decide +kernel

/-- The state that `stateTransition σP B'` hands to `heightEvents`. -/
def σPre' : ChainState 4 :=
  { B'.atts.foldl ChainState.processAtt { σP with s := B'.slot } with L := B'.root }

/-- `B'` is accepted on `σP`, and the accepted state is `heightEvents σPre'`. -/
theorem stateTransition_B' : gp4.stateTransition σP B' = some (gp4.heightEvents σPre') := by
  rw [FGParams.stateTransition, ite_eq_left (by decide +kernel)]
  rfl

/-- `σPre'` agrees with `σPre` except for the finality bits of height `2`: only `0` and `1`. -/
theorem σPre'_eq :
    (σPre'.h, σPre'.Th, σPre'.hj, σPre'.J) = (σPre.h, σPre.Th, σPre.hj, σPre.J) ∧
      (σPre'.L, σPre'.s, σPre'.ThSlot, σPre'.F, σPre'.hF) =
        (σPre.L, σPre.s, σPre.ThSlot, σPre.F, σPre.hF) ∧
      σPre'.pending = σPre.pending ∧ σPre'.target = σPre.target ∧ σPre'.prog = σPre.prog ∧
      σPre'.fin 2 = {0, 1} := by
  decide +kernel

/-- (c) At `σPre'` every premise of `FinalityBeforeGate` but the finality quorum holds, with
`J` not genesis and a target quorum; the finality bits for `h_j` are `q − 1 = 2`. -/
theorem control_premises :
    σPre'.previousHeightJustified ∧ (σPre'.hj, σPre'.J) ∈ σPre'.pending ∧
      σPre'.pending.Pairwise (fun p r => p.1 < r.1) ∧ (∀ p ∈ σPre'.pending, p.1 ≤ σPre'.hj) ∧
      σPre'.J ≠ gp4.genesis ∧ gp4.q ≤ σPre'.target.card ∧
      (σPre'.fin σPre'.hj).card = gp4.q - 1 ∧ (σPre'.fin σPre'.hj).card < gp4.q := by
  decide +kernel

/-- (c) Without the finality quorum the conclusion of `FinalityBeforeGate` fails at `σPre'`:
the finality step keeps `F = 0` at `h_F = 1 < h_j`, `(2, 1)` stays pending, and the block does not
justify; the accepted state stays at height `3`. -/
theorem control_not_finalized :
    (gp4.finalizePrune σPre').hF = 1 ∧ (gp4.finalizePrune σPre').F = 0 ∧
      (gp4.finalizePrune σPre').hF < σPre'.hj ∧ (gp4.finalizePrune σPre').F ≠ σPre'.J ∧
      (σPre'.hj, σPre'.J) ∈ (gp4.finalizePrune σPre').pending ∧
      ¬ gp4.justifies (gp4.finalizePrune σPre') ∧
      ((gp4.heightEvents σPre').h, (gp4.heightEvents σPre').hj,
        (gp4.heightEvents σPre').hF) = (3, 2, 1) := by
  decide +kernel

end Consensus.Goldilocks.FinalityGateWitness

end
