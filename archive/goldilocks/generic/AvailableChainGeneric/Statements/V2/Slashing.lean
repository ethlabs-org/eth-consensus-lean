module
public import AvailableChainGeneric.Statements.V2.Interface

@[expose] public section

namespace AvailableChain.Gen.V2

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

/-- DC `DecoupledConsensusStatements/Generic/Interface.lean:58` puts `slashes`
in the base interface. Here it is an additive extension: the Gen interface is
frozen at G-F0a, and the SA and GridCO protocols have no evidence carrier.
The validator type `V` is the validator type of the run.
DC: Interface.lean:58; same: Frozen base; no SA/GridCO evidence; GLY r3.19 S132. -/
structure SlashingInterface {V : Type} {In : Type} (P : ProtocolSpec In)
    extends FinalityInterface P where
  /-- Two reads of the run, at any nodes and any times, hold evidence
  attributable to `v`. The nodes that hold the evidence need not be honest. -/
  slashes : Run V P → V → Prop

variable {V : Type} {In : Type} {P : ProtocolSpec In}

/-- The conclusion of DC `Generic/Claims.lean:63`, in the same quantifier
order. This proposition states the conclusion only; it supplies no claim
or unforgeability premise.
DC: Claims.lean:63; same: Same conclusion; claim premise separate; GLY r3.19 S133. -/
def HonestNeverSlashed (I : SlashingInterface (V := V) P) (rho : Run V P) : Prop :=
  ∀ v ∈ rho.honest, ¬ I.slashes rho v

theorem HonestNeverSlashed_def (I : SlashingInterface (V := V) P) (rho : Run V P) :
    HonestNeverSlashed I rho = (∀ v ∈ rho.honest, ¬ I.slashes rho v) := by
  rw [HonestNeverSlashed]

end AvailableChain.Gen.V2
