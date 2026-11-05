module
public import ConsensusLeanTest.Goldilocks.FG.Statements
import ConsensusLean.Instances.Goldilocks.Lemmas.FGChain.Invariants
@[expose] public section

/-! # Witness and rejection for `FG.Retention` (G0.9 (a))

On `Goldilocks/FG/Statements`'s one-validator chain `chainA` (`gp1`: `n = q = 1`, `δ_t = 2`, genesis
root `0`). Its first block `1` justifies genesis at height `1`: the chain state `σ₁` has `h = 2`,
`h_j = 1`, `J = 0`, `h_F = 0` and the pending window `[(1, 0)]`, so height `2` has its previous
height justified. Labelled by kind (CONTRIBUTING "Statements"):

* (a) `retention_premises`: the empty block `2` (no attestations) is accepted on `σ₁` with state
  `σ₂`: every premise of `Retention` holds (the height stays `2`, `h_F = 0 < 1 = h_j`), and
  `retention_applies` is `FG.retention`'s conclusion there: `(1, 0)` stays pending
  (`σ₂.pending = [(1, 0)]`, `retention_conclusion`).
* (r) `retention_needs_height_stays`: `chainA`'s second block `2` (the target for height `2` with
  the finality pair `(1, 0)`) is accepted on `σ₁`; every other premise holds (`σ₁`'s previous
  height is justified, `h_F = 1 < 2 = h_j` after it), but the height rises to `3`, and `(1, 0)`,
  finalized by this block, leaves the window: the conclusion fails.
* (control) `retention_of_height_stays`: the premise `σ.previousHeightJustified` is not needed:
  `ChainInvariants` (the newest pending pair is `(h_j, J)` when `h_F < h_j`) and `HeightStep`
  (`J`, `h_j` are kept while the height stays) give the conclusion without it, so no rejection
  of that premise exists. -/

namespace Consensus.Goldilocks.FG.RetentionWitnessA

open FG.Test

/-- The chain state after `chainA`'s first block. -/
def σ₁ : ChainState 1 := (gp1.chainState (chainA.take 1)).get (by decide +kernel)

theorem chainState_σ₁ : gp1.chainState (chainA.take 1) = some σ₁ := (Option.some_get _).symm

/-- An empty block `2` of slot `2` on `σ₁`. -/
def B₀ : FGBlock 1 := ⟨2, 2, 0, []⟩

/-- The state after `B₀`. -/
def σ₂ : ChainState 1 := (gp1.stateTransition σ₁ B₀).get (by decide +kernel)

theorem stateTransition_B₀ : gp1.stateTransition σ₁ B₀ = some σ₂ := (Option.some_get _).symm

/-- `chainA`'s second block: the target for height `2`, finalizing `(1, 0)`. -/
def B₂ : FGBlock 1 := ⟨2, 2, 0, [tv 2 1 (some (1, 0))]⟩

/-- The state after `B₂`. -/
def σ₃ : ChainState 1 := (gp1.stateTransition σ₁ B₂).get (by decide +kernel)

theorem stateTransition_B₂ : gp1.stateTransition σ₁ B₂ = some σ₃ := (Option.some_get _).symm

/-- The states read off: `σ₁` at height `2` with `(1, 0)` justified and pending; `σ₂` keeps all
of it; `σ₃` is at height `3`, has finalized `(1, 0)` and holds only `(2, 1)`. -/
theorem states :
    σ₁.h = 2 ∧ σ₁.hj = 1 ∧ σ₁.J = 0 ∧ σ₁.hF = 0 ∧ σ₁.pending = [(1, 0)] ∧
      σ₂.h = 2 ∧ σ₂.hj = 1 ∧ σ₂.J = 0 ∧ σ₂.hF = 0 ∧ σ₂.pending = [(1, 0)] ∧
      σ₃.h = 3 ∧ σ₃.hj = 2 ∧ σ₃.J = 1 ∧ σ₃.hF = 1 ∧ σ₃.pending = [(2, 1)] := by
  decide +kernel

/-- (a) The premises of `Retention` hold together for `chainA.take 1`, `σ₁`, `B₀`, `σ₂`. -/
theorem retention_premises :
    gp1.chainState (chainA.take 1) = some σ₁ ∧ gp1.stateTransition σ₁ B₀ = some σ₂ ∧
      σ₁.previousHeightJustified ∧ σ₂.h = σ₁.h ∧ σ₂.hF < σ₂.hj :=
  ⟨chainState_σ₁, stateTransition_B₀, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- `FG.retention` applied to the witness: the predecessor `(h_j, J) = (1, 0)` stays pending. -/
theorem retention_applies : (σ₁.hj, σ₁.J) ∈ σ₂.pending := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := retention_premises
  exact FG.retention gp1 _ σ₁ σ₂ B₀ h₁ h₂ h₃ h₄ h₅

/-- The conclusion read directly: `(1, 0) ∈ σ₂.pending`. -/
theorem retention_conclusion : ((1 : Nat), (0 : Nat)) ∈ σ₂.pending := by decide +kernel

/-- (r) **The height premise is needed.** On `σ₁` and `B₂`, every premise but `σ₃.h = σ₁.h`
holds, and `(σ₁.h_j, σ₁.J) = (1, 0)` is not pending after `B₂`. -/
theorem retention_needs_height_stays :
    gp1.chainState (chainA.take 1) = some σ₁ ∧ gp1.stateTransition σ₁ B₂ = some σ₃ ∧
      σ₁.previousHeightJustified ∧ σ₃.h ≠ σ₁.h ∧ σ₃.hF < σ₃.hj ∧
      (σ₁.hj, σ₁.J) ∉ σ₃.pending :=
  ⟨chainState_σ₁, stateTransition_B₂, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel⟩

/-- (control) **`Retention` without `σ.previousHeightJustified`**, for every `gp`: while the
height stays and the justification is unfinalized after the block, the predecessor is pending. -/
theorem retention_of_height_stays (gp : FGParams) (c : List (FGBlock gp.n))
    (σ σ' : ChainState gp.n) (B : FGBlock gp.n) (hc : gp.chainState c = some σ)
    (h : gp.stateTransition σ B = some σ') (hh : σ'.h = σ.h) (hlt : σ'.hF < σ'.hj) :
    (σ.hj, σ.J) ∈ σ'.pending := by
  have hc' : gp.chainState (c ++ [B]) = some σ' := by
    rw [FG.FGParams.chainState_append, hc]; exact h
  have hlast := (FG.chain_invariants gp _ _ hc').2.2.2.2.2.2.2.2.1 hlt
  obtain ⟨-, -, -, hkeep, -⟩ := FG.height_step gp c σ σ' B hc h
  obtain ⟨-, hJ, hj⟩ := hkeep hh
  rw [← hJ, ← hj]
  exact List.mem_of_getLast? hlast

end Consensus.Goldilocks.FG.RetentionWitnessA

end
