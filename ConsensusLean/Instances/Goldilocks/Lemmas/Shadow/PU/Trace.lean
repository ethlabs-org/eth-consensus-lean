module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Model
public import ConsensusLean.Instances.Goldilocks.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Growing
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Handlers
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.FG.Store.Trace
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Node.Handlers
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Model
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.Handlers
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.View
public import ConsensusLean.Instances.Goldilocks.Spec.Node.Handlers
public import ConsensusLean.Instances.Goldilocks.Spec.Node.State
public import ConsensusLean.Instances.Goldilocks.Lemmas.Shadow.PU.Node
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Run.Growing.Goldilocks
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Compose.GenericRun
public import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Run
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Run.Components
public import ConsensusLean.Instances.Goldilocks.Lemmas.Growing.Run.UpTo

public section

/-! # Shadow P-U: the trace laws of a shadow run

The shadow node runs the stock node with the shadow FG store (`Store.onBlock'`, `Node.frame'`).
This file copies the stock trace laws that read the node's execution, over `goldilocksNode'`:

* the FG execution law `FGLabel.Step'` and the FG trace contract `FGLocalRun'` (static) and
  `Growing.FGLocalRun'`, copies of `FGLabel.Step`, `FGLocalRun` and `Growing.FGLocalRun` with
  `Store.onBlock'` in place of `Store.onBlock`;
* the component state `Compose.projFG_state'` (`Compose.projAC_state'` is in
  `Shadow/PU/Node`, the proved honest-tree coherence in `Shadow/PU/Coherence`), the FG
  execution `Compose.fg_exec'` (the FG projection `Compose.fg_projection_from'` is in
  `Shadow/PU/FGProjection`);
* (the AC projection `Compose.goldilocks_ac_projection_from'` is in `Shadow/PU/ACProjection`);
* the run laws under growing faults, `Growing.LocalRun'` and `Growing.GoldilocksRun'`, copies of
  `Growing.LocalRun` and `Growing.GoldilocksRun` with the shadow cut law and groups;
* the prefix transport `Growing.GoldilocksRun'.upTo`.

**Reused, not copied.** `goldilocksNode'` is the stock AC (`goldilocksAC`), so the AC trace contract
`ACLocalRun`, `SyncAC`, `AC.ACRun` and the projection `projAC` are the stock ones: they are generic
in the AC interface, and the shadow changes only the FG store and the frame. The AC projections here
conclude the stock `AC.ACRun`. The run carrier `RunTrace' = RunTrace` is shared, so the pure trace
predicates (`SyncRunAt`, `GSTRunAt`, `HealthyRunAt`, `CatchRun`, `NoCollRun`, `projAC_callAt`,
`projFG_callAt`, `HonestBlocks`, `Trace.upTo`, `projFG`) are reused as they are; only the lemmas
that read the run laws are copied. -/

namespace Consensus.Goldilocks

variable {P : Params} {ACP : Type}

/-- The shadow FG execution law of an FG call of validator `v` (stock `FGLabel.Step` with
`Store.onBlock'`). -/
theorem FGLabel.step_block (v : Fin P.n) (s s' : FGState P ACP) (B : NodeBlock P ACP)
    (accepted : Bool) :
    FGLabel.Step v s (.block B accepted) s' ↔
      (accepted = true ∧ s.1.onBlock B = some s'.1 ∧ s'.2 = s.2) ∨
      (accepted = false ∧ s.1.onBlock B = none ∧ s' = s) := by rfl

theorem FGLabel.step_attestation (v : Fin P.n) (s s' : FGState P ACP) (a : FG.Att P.n) :
    FGLabel.Step v s (.attestation a) s' ↔ s' = (s.1.onAttestation a, s.2) := by rfl

theorem FGLabel.step_attest (v : Fin P.n) (s s' : FGState P ACP) (src : NodeBlock P ACP)
    (signed : Option (FG.Att P.n)) :
    FGLabel.Step v s (.attest src signed) s' ↔
      s'.1 = s.1 ∧
      match s.1.attest s.2 v src with
      | some (a, Λ') => signed = some a ∧ s'.2 = Λ'
      | none => signed = none ∧ s'.2 = s.2 := by rfl

namespace Growing

end Growing

end Consensus.Goldilocks

namespace Consensus.Goldilocks.Growing

open AC (ACParams ReplayOrder Vote Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))}

end Consensus.Goldilocks.Growing

namespace Consensus.Goldilocks.Compose

open Node

variable {P : Params} {A : NodeAC P}
variable {proposer : Nat → Fin P.n} {dg : Digest (List (FG.Att P.n)) A.Payload} {H : Set (Fin P.n)}
  {sg : A.Msg → Fin P.n} {tr : RunTrace A} {ini : Fin P.n → A.State}

end Consensus.Goldilocks.Compose

namespace Consensus.Goldilocks.RunTrace

variable {P : Params} {A : NodeAC P} (tr : RunTrace A) {d : Time}

end Consensus.Goldilocks.RunTrace

namespace Consensus.Goldilocks.Growing

open AC (ACParams ReplayOrder Payload)

variable {sp : ACParams} {ro : ReplayOrder sp (List (FG.Att sp.n))} {proposer : Nat → Fin sp.n}
  {dg : Digest (List (FG.Att sp.n)) (Payload sp.n)} {H : Time → Set (Fin sp.n)}
  {tr : GoldilocksTrace sp ro}

end Consensus.Goldilocks.Growing

end
