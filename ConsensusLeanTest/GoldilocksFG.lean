module
public import ConsensusLean
@[expose] public section

/-! # Witnesses for the Goldilocks FG statements (milestone M₁)

On the pure FG of `Instances/Goldilocks/Spec/FG`, labelled by kind (CONTRIBUTING "Statements"):

* (b) `oneValidator_finalizes`: with one validator, a chain of three blocks justifies
  genesis, then block `1` (a bound height whose predecessor genesis finalizes in the
  same block, before the gate), then finalizes block `1`.
* (a) `conflicting_finalizations`: two chains that finalize conflicting blocks exist (the
  hypotheses of `AccountableSafety`), and the one validator's height-2 targets on them are
  slashable (E2).
* (b) `bound_entry_after_justification`: after the second block the height is bound
  (`HeightStep`'s bound case is reachable).
* (b) `gate_keeps_target_quorum`: a bound height whose predecessor is not finalized keeps a
  target quorum without justifying (the hypothesis of `GatedConsumption` is reachable).
* (limit, G0.9 (c)) `window_drops_unfinalized`: bound timeout, unbound append, bound timeout,
  unbound append drops the first pending pair while nothing is finalized
  (`[P] → [P,Q] → [Q,R]`). -/

namespace Consensus.Goldilocks.FG.Test

/-- One validator, `δt = 2`, genesis root `0`. -/
def gp1 : FGParams := ⟨1, le_rfl, 2, 0⟩

/-- A target vote of validator `0` at height `h` for root `T`, with finality pair `f`. -/
def tv (h T : Nat) (f : Option (Nat × Nat)) : Att 1 := ⟨0, h, T, false, f⟩

/-- Blocks `1, 2, 3` on one branch: each carries the target for the current entry,
with the predecessor as finality pair from height `2` on. -/
def chainA : List (FGBlock 1) :=
  [⟨1, 1, 0, [tv 1 0 none]⟩, ⟨2, 2, 0, [tv 2 1 (some (1, 0))]⟩,
   ⟨3, 3, 0, [tv 3 2 (some (2, 1))]⟩]

/-- A conflicting branch: blocks `11, 12, 13` from genesis, finalizing block `11`. -/
def chainB : List (FGBlock 1) :=
  [⟨11, 1, 0, [tv 1 0 none]⟩, ⟨12, 2, 0, [tv 2 11 (some (1, 0))]⟩,
   ⟨13, 3, 0, [tv 3 12 (some (2, 11))]⟩]

theorem oneValidator_finalizes :
    (gp1.chainState chainA).map (fun σ => (σ.F, σ.hF, σ.J, σ.hj, σ.h)) =
      some (1, 2, 2, 3, 4) := by decide +kernel

theorem bound_entry_after_justification :
    (gp1.chainState (chainA.take 2)).map (fun σ => decide σ.bound) = some true := by decide +kernel

theorem conflicting_finalizations :
    (gp1.chainState chainA).map (fun σ => σ.F) = some 1 ∧
      (gp1.chainState chainB).map (fun σ => σ.F) = some 11 ∧
      1 ∉ gp1.roots chainB ∧ 11 ∉ gp1.roots chainA ∧
      slashable (tv 2 1 (some (1, 0))) (tv 2 11 (some (1, 0))) := by decide +kernel

/-- A timeout of validator `0` at height `h` for root `T`. -/
def tmo (h T : Nat) : Att 1 := ⟨0, h, T, true, none⟩

theorem gate_keeps_target_quorum :
    (gp1.chainState ([⟨1, 1, 0, [tv 1 0 none]⟩, ⟨2, 2, 0, [tv 2 1 none]⟩] : List (FGBlock 1))).map
      (fun σ => (σ.h, σ.target.card, decide σ.bound, σ.hF, σ.hj)) = some (2, 1, true, 0, 1) := by
  decide +kernel

/-- Roots equal slots: justify `1`, time out at `2`, justify `3`, time out at `4`, justify `5`. -/
def chainW : List (FGBlock 1) :=
  [⟨1, 1, 0, [tv 1 0 none]⟩, ⟨3, 3, 0, [tmo 2 1]⟩, ⟨4, 4, 0, [tv 3 3 none]⟩,
   ⟨6, 6, 0, [tmo 4 4]⟩, ⟨7, 7, 0, [tv 5 6 none]⟩]

theorem window_drops_unfinalized :
    (gp1.chainState chainW).map (fun σ => (σ.pending, σ.hF)) = some ([(3, 3), (5, 6)], 0) := by
  decide +kernel

end Consensus.Goldilocks.FG.Test

end
