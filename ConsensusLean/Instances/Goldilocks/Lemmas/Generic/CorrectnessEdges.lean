module
public import ConsensusLean.Spec.Shape.Obligations
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ClaimTransports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.ChainRepresentationEdges
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.EngineEdges
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.CorrectLocal

public section

/-! # Open correctness assembly edges

All edges are admission-free proposition definitions. Nothing here is supplied as evidence to a
definition, instance, type witness or compiled endpoint. The capstone `meetsObligations_of_local`
is proved from the claim reductions in `ClaimReductionEdges` (`meetsObligations_of_local_proof`);
its local supplier record remains to be supplied per instance.
-/

namespace Consensus.Goldilocks.Generic

open Shape Blocks

/-- The independent suppliers consumed by the claim reductions, each named once.
The read-point records are separate local obligations, not fields of `ACCorrectLocal`.
Outage policy and stored-read context are data parameters, never hidden Prop fields.
This record supplies neither a compiled protocol run nor any endpoint claim. -/
structure LocalClaimSuppliers {P : Params} {A : NodeAC P} {O : OutputSchema} {Info : Type}
    [DecidableEq Info] [Countable Info] {F : ChainShapeFamily O Info}
    {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat}
    (M : RunMap rho payload) (C : ACCorrectLocal A M.signer) (K : Contract ProgressReq)
    (D : OutagePolicy M) (R : StoredReadContext M) (events : SleepyLayer1.Data A) : Prop where
  regime : RegimeTransport M K C
  /-- Output validity on valid executions, without a readiness or regime premise. -/
  outputValidity : OutputValidityEdge M
  reads : ReadRepresentation M
  honestReads : HonestReadTransport M
  chains : ChainRepresentation A M.chain M.header
  honestChains : HonestChainReads M
  coherent : ¬ rho.HashCollision → Coherent (M.trace.HonestBlocksAt M.honest)
  engineRead : EngineReadPoint M
  localRead : LocalReadPoint C
  sleepyProposal : SleepyLayer1.ProposalCoverage M C events
  eventSafety : SleepyLayer1.EventSafety M C events
  outputProvenance : SleepyLayer1.OutputProvenance C events
  extension : SleepyLayer1.Extension M C events
  sourceProvenance : SleepyLayer1.SourceProvenance C events
  populationQuorum : PopulationQuorumSupply M K
  sleepyWindows : SleepyWindowSupply M K C
  healthyRead : HealthyReadPoint C
  outageRead : OutageReadPoint C
  deadlines : ClaimDeadlineFit M K C
  progress : ProposalProgressTransport M
  proposalWitness : ProposalWitnessRefinement M K C
  deadlinePremises : DeadlinePremisesSupply M K
  finalWindow : FinalWindowSupply M K C.catchUp C.hold
  finalReads : FinalReadTransport M C
  accountability : ActualReadAccountability M C.run
  outage : OutageTransport M D K
  recovery : OutageRecoveryBinding M K C
  outageService : OutageServiceSupply M K C
  resilience : ResilienceTipTransport M
  preparation : PreparationPremisesSupply M K
  highCanonical : HighCanonicalSupply M K C
  resetBudget : ResetHealBudgetSupply M K C
  storedRead : StoredReadTransport M R
  healedAncestry : HealedReadAncestry M K R

/-- Every claim is vacuous without validators: reads have a validator argument, and
proposal liveness requires an existing ready reader. No regime or excuse is used. -/
theorem shapeClaimsAt_of_isEmpty {O : OutputSchema} {Info : Type}
    [DecidableEq Info] [Countable Info] (F : ChainShapeFamily O Info)
    (K : Contract ProgressReq) (V : Type) [Fintype V] [DecidableEq V]
    (h : IsEmpty V) : ShapeClaimsAt F K V where
  outputValid := fun _ _ _ _ _ v => (h.false v).elim
  nested := fun _ _ _ _ _ _ _ _ _ v => (h.false v).elim
  finalMonotone := fun _ _ _ _ v => (h.false v).elim
  finalAccountable := fun _ _ _ _ _ => Or.inl (fun u => (h.false u).elim)
  healthyLive := fun _ _ _ _ _ _ _ _ =>
    Or.inl (fun _ _ _ hr => (h.false hr.choose).elim)
  sleepySafe := fun _ _ _ _ _ _ _ =>
    Or.inl ⟨fun u => (h.false u).elim, fun v => (h.false v).elim⟩
  sleepyLive := fun _ _ _ _ _ _ _ _ =>
    Or.inl (fun _ _ _ hr => (h.false hr.choose).elim)
  healedSafe := fun _ _ _ _ _ _ _ _ _ =>
    Or.inl ⟨fun u => (h.false u).elim, fun v => (h.false v).elim⟩
  persists := fun _ _ _ _ _ _ _ _ => Or.inl (fun v => (h.false v).elim)

/-- Assembly from local correctness and its engine suppliers, proved by
`meetsObligations_of_local_proof` (`Lemmas/Generic/ClaimReductionEdges`).
The proof uses OutputValidAlways (with OutputValidityEdge), NestedChainsAlways,
FinalChainsAlways and the six regime/accountability reductions in ClaimReductionEdges,
then holds_of_forall_public and holdsAlways_of_forall_public. Those reductions are the
proof route, not premises. Requirements and genesis roots come from the binding's
run_transport and the AC run laws. No ShapeClaims or compiled-run premise is admitted.
The four non-claim obligations, HealthyBetaFit and CommitteeHalfFit remain independent inputs.
Local AC parameters require a positive population. Empty validator types need no binding:
their reader/proposer claims are vacuous; the conclusion still covers every finite type. -/
def meetsObligations_of_local {O : OutputSchema} {Info : Type}
    [DecidableEq Info] [Countable Info] (F : ChainShapeFamily O Info)
    (K : Contract ProgressReq) : Prop :=
  ∀ (P : {pub : Model.Public // 1 ≤ pub.n} → Params) (A : ∀ pub, NodeAC (P pub))
    (sg : ∀ pub, (A pub).Msg → Fin (P pub).n)
    (C : ∀ pub, ACCorrectLocal (A pub) (sg pub))
    (events : ∀ pub, SleepyLayer1.Data (A pub))
    (B : ∀ (V : Type) [Fintype V] [DecidableEq V] pub,
      EngineBinding (F := F) (V := V) pub.val (C pub).payload (sg pub) (C pub).run)
    (D : ∀ (V : Type) [Fintype V] [DecidableEq V] pub E hE rho hv,
      OutagePolicy ((B V pub).map E hE rho hv))
    (R : ∀ (V : Type) [Fintype V] [DecidableEq V] pub E hE rho hv,
      StoredReadContext ((B V pub).map E hE rho hv)),
    (∀ (V : Type) [Fintype V] [DecidableEq V] pub E hE rho hv,
      LocalClaimSuppliers ((B V pub).map E hE rho hv)
        ((B V pub).signer_eq E hE rho hv ▸ C pub) K
        (D V pub E hE rho hv) (R V pub E hE rho hv) (events pub)) →
    K.params.Admissible → O.Serves → ProgressFits K F → ProgressTolerant O K →
    HealthyBetaFit K → CommitteeHalfFit K → ShapeObligations F K


/-- The capstone contract, read through its suppliers and fits. -/
theorem meetsObligations_of_local_iff {O : OutputSchema} {Info : Type}
    [DecidableEq Info] [Countable Info] (F : ChainShapeFamily O Info)
    (K : Contract ProgressReq) :
    meetsObligations_of_local F K ↔
    ∀ (P : {pub : Model.Public // 1 ≤ pub.n} → Params) (A : ∀ pub, NodeAC (P pub))
      (sg : ∀ pub, (A pub).Msg → Fin (P pub).n)
      (C : ∀ pub, ACCorrectLocal (A pub) (sg pub))
      (events : ∀ pub, SleepyLayer1.Data (A pub))
      (B : ∀ (V : Type) [Fintype V] [DecidableEq V] pub,
        EngineBinding (F := F) (V := V) pub.val (C pub).payload (sg pub) (C pub).run)
      (D : ∀ (V : Type) [Fintype V] [DecidableEq V] pub E hE rho hv,
        OutagePolicy ((B V pub).map E hE rho hv))
      (R : ∀ (V : Type) [Fintype V] [DecidableEq V] pub E hE rho hv,
        StoredReadContext ((B V pub).map E hE rho hv)),
      (∀ (V : Type) [Fintype V] [DecidableEq V] pub E hE rho hv,
        LocalClaimSuppliers ((B V pub).map E hE rho hv)
          ((B V pub).signer_eq E hE rho hv ▸ C pub) K
          (D V pub E hE rho hv) (R V pub E hE rho hv) (events pub)) →
      K.params.Admissible → O.Serves → ProgressFits K F → ProgressTolerant O K →
      HealthyBetaFit K → CommitteeHalfFit K → ShapeObligations F K :=
  by exact Iff.rfl

/-- A property of local suppliers over every signer survives transporting a supplier along a
signer equality. In particular, every field whose type does not mention the signer is unchanged:
take `Q s C' := C'.f = C.f`. -/
theorem ACCorrectLocal.cast_signer {P : Params} {A : NodeAC P} {sg sg' : A.Msg → Fin P.n}
    (h : sg = sg') (C : ACCorrectLocal A sg) (Q : ∀ s, ACCorrectLocal A s → Prop)
    (hC : Q sg C) : Q sg' (h ▸ C) := by
  subst h
  exact hC

end Consensus.Goldilocks.Generic

end
