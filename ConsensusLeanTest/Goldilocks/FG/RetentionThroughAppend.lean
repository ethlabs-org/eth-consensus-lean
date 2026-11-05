module
public import ConsensusLeanTest.Goldilocks.FG.Statements
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Invariants
@[expose] public section

/-! # Witness for `RetentionThroughAppend` (G0.9 (b)): the newest pending pair, not an older one

On `Goldilocks/FG/Statements`'s timeout/append chain `chainW` (one validator, roots equal slots),
the prefix of four blocks has chain state `σW`: blocks `1` and `4` justified heights `1` and `3`,
the heights `2` and `4` timed out, and the pending window holds `[(1, 0), (3, 3)]` (full,
`K_W = 2`), with only genesis finalized. `chainW`'s fifth block `B7` is accepted on `σW`: it
justifies height `5`, so its entry `(5, 6)` is appended and the window keeps `[(3, 3), (5, 6)]`.
Labelled by kind (CONTRIBUTING "Statements"):

* (a) `newest_retention_premises`: the four premises of `RetentionThroughAppend` hold for the
  parent's newest pair `P = (3, 3)`, and `newest_retained` is `retention_through_append`'s
  conclusion: `P` stays pending.
* (c) `older_pair_dropped`: the parent's older pair `Q = (1, 0)` (height `1`, justified by
  genesis) satisfies every other premise fact (pending in the parent, above the finalized height
  after the block), but it is not the newest (`getLast? ≠ some Q`), and the same transition drops
  it. So the newest-pair premise cannot be weakened to "pending": the window of two pairs evicts an
  unfinalized older pair. -/

namespace Consensus.Goldilocks.FG.RetentionWitness

open FG.Test

/-- The chain state of `chainW`'s prefix of four blocks. -/
def σW : ChainState 1 := (gp1.chainState (chainW.take 4)).get (by decide +kernel)

/-- `chainW`'s prefix of four blocks is accepted, with chain state `σW`. -/
theorem chainState_parent : gp1.chainState (chainW.take 4) = some σW :=
  (Option.some_get _).symm

/-- `chainW`'s fifth block: block `7` at slot `7`, the target vote for the entry `(5, 6)`. -/
def B7 : FGBlock 1 := ⟨7, 7, 0, [tv 5 6 none]⟩

/-- `B7` is `chainW`'s fifth block. -/
theorem chainW_eq : chainW = chainW.take 4 ++ [B7] := rfl

/-- The chain state of the whole `chainW`. -/
def σW' : ChainState 1 := (gp1.stateTransition σW B7).get (by decide +kernel)

/-- `B7` is accepted on `σW`, with state `σW'`. -/
theorem stateTransition_B7 : gp1.stateTransition σW B7 = some σW' :=
  (Option.some_get _).symm

/-- `chainW` is accepted, and its chain state is the accepted state of `B7` on `σW`. -/
theorem chainState_chainW : gp1.chainState chainW = some σW' := by
  have h : gp1.chainState chainW =
      (gp1.chainState (chainW.take 4)).bind (fun σ => gp1.stateTransition σ B7) := by
    conv_lhs => rw [chainW_eq]
    simp only [FGParams.chainState]
    exact List.foldl_append ..
  rw [h, chainState_parent]
  exact stateTransition_B7

/-- The window before and after `B7`: `[(1, 0), (3, 3)]` becomes `[(3, 3), (5, 6)]`, with only
genesis finalized on both sides; `B7` justifies height `5` (entry `(5, 6)`), the height becomes
`6` (entry `(6, 7)`). -/
theorem window_before_after :
    σW.pending = [(1, 0), (3, 3)] ∧ σW.hF = 0 ∧ σW.F = 0 ∧
      (σW.h, σW.Th, σW.hj, σW.J) = (5, 6, 3, 3) ∧
      σW'.pending = [(3, 3), (5, 6)] ∧ σW'.hF = 0 ∧ σW'.F = 0 ∧
      (σW'.h, σW'.Th, σW'.hj, σW'.J) = (6, 7, 5, 6) := by
  decide +kernel

/-! ## The newest pair -/

/-- The parent's newest pending pair. -/
def P : Nat × Nat := (3, 3)

/-- (a) The premises of `RetentionThroughAppend` hold together for `chainW.take 4`, `σW`, `σW'`,
`B7` and the newest pair `P = (3, 3)`. -/
theorem newest_retention_premises :
    gp1.chainState (chainW.take 4) = some σW ∧ gp1.stateTransition σW B7 = some σW' ∧
      σW.pending.getLast? = some P ∧ σW'.hF < P.1 :=
  ⟨chainState_parent, stateTransition_B7, by decide +kernel, by decide +kernel⟩

/-- `retention_through_append`'s conclusion on the witness: the newest pair stays pending through
the append. -/
theorem newest_retained : P ∈ σW'.pending := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := newest_retention_premises
  exact FG.retention_through_append gp1 _ σW σW' B7 P h₁ h₂ h₃ h₄

/-! ## The older pair -/

/-- The parent's older pending pair. -/
def Q : Nat × Nat := (1, 0)

/-- (c) The older pair `Q = (1, 0)` is pending in the parent and stays above the finalized height
after `B7`, on the same accepted transition as the witness; but it is not the parent's newest
pair, and `B7` drops it from the window. -/
theorem older_pair_dropped :
    gp1.chainState (chainW.take 4) = some σW ∧ gp1.stateTransition σW B7 = some σW' ∧
      Q ∈ σW.pending ∧ σW'.hF < Q.1 ∧ σW.pending.getLast? ≠ some Q ∧ Q ∉ σW'.pending :=
  ⟨chainState_parent, stateTransition_B7, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel⟩

end Consensus.Goldilocks.FG.RetentionWitness

end
