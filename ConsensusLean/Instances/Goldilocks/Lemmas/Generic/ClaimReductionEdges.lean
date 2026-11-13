module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ClaimTransports
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.Correctness
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.EngineEdges
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.ChainRepresentationEdges

public section

/-! # Conditional claim reduction rows

UNPROVED intended theorem types only. No evidence, instance, admission or correctness
claim is supplied. All suppliers below refer to the binding's same map. Healed safety
uses a separate stored-clock context and explicit transport, never an inference from
compatibility to temporal ancestry. The realization of that context remains OPEN.
-/

set_option autoImplicit false
namespace Consensus.Goldilocks.Generic
open Shape Blocks

variable {P : Params} {A : NodeAC P} {O : OutputSchema} {Info : Type}
  [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {payload : A.Blk → Set Nat}

/-- UNPROVED exact output-validity wrapper. OutputValidityEdge, not held_view alone,
is the reduction input. The original unconditional HoldsAlways is retained. -/
def OutputValidAlways (B : EngineBinding (A := A) (F := F) (V := V) payload) : Prop :=
  (∀ E rho (hv : rho.ExecutionValid),
    OutputValidityEdge (B.map E rho hv) ∧ ReadRepresentation (B.map E rho hv) ∧
      HonestReadTransport (B.map E rho hv)) →
    (Sys F V).HoldsAlways fun r => ∀ c g, O.output c = some g → OutputValid r.2 g

/-- UNPROVED bounded explicit-read sleepy safety reduction. Coherent union and
root suppliers remain explicit; none enters an unconditional claim. Source:
Concrete/Fields.meetsObligations_sleepySafe_growing. -/
def SleepySafetyReduction (B : EngineBinding (A := A) (F := F) (V := V) payload)
    (K : Contract ProgressReq)
    (C : ∀ E rho (hv : rho.ExecutionValid), ACCorrectLocal A (B.map E rho hv).signer) : Prop :=
  (∀ E rho (hv : rho.ExecutionValid),
    let M := B.map E rho hv
    let L := C E rho hv
    GrowingRunTransport M ∧ RegimeTransport M K L.look ∧ EngineReadPoint M ∧
      LocalReadPoint L ∧ SleepyReadPoint L ∧ ClaimDeadlineFit M K L ∧
      ReadRepresentation M ∧ HonestReadTransport M ∧
      (¬ rho.HashCollision → Coherent (M.trace.HonestBlocksAt M.honest))) →
    ∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
      (Sys F V).Holds ((Sys F V).Sleepy K) fun r =>
        (chainTrace r.2).ReadySafe ((Sys F V).cDur K r) g 0

/-- UNPROVED sleepy proposal reduction, keeping the original progress interval,
reader-conditional deadline and hash-collision branch. The strengthened witness
supplier is OPEN; it does not follow from the old proposal budget. -/
def SleepyLivenessReduction (B : EngineBinding (A := A) (F := F) (V := V) payload)
    (K : Contract ProgressReq)
    (C : ∀ E rho (hv : rho.ExecutionValid), ACCorrectLocal A (B.map E rho hv).signer) : Prop :=
  (∀ E rho (hv : rho.ExecutionValid),
    let M := B.map E rho hv
    let L := C E rho hv
    GrowingRunTransport M ∧ RegimeTransport M K L.look ∧
      ProposalProgressTransport M K L.healing L.catchUp L.hold L.margin ∧
      SleepyProposalBudgetSupply M K L.catchUp L.hold L.margin ∧
      ProposalWitnessRefinement M K L ∧ ClaimDeadlineFit M K L ∧
      EndReadTransport M K L ∧ SleepyReadPoint L ∧ LocalReadPoint L ∧
      ReadRepresentation M ∧ HonestReadTransport M ∧
      (¬ rho.HashCollision → Coherent (M.trace.HonestBlocksAt M.honest))) →
    ∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
      ∀ idx : K.Idx, (Sys F V).Holds
        (fun r => (Sys F V).Sleepy K r ∧ (Sys F V).prog (shapeProgress F V) K cap idx 0
          ((Sys F V).pt r).horizon r)
        fun r => ProposalLiveReady r.2 ((Sys F V).cDur K r) g 0 (K.params.latency cap idx)

/-- UNPROVED all-capability healthy liveness reduction. Actual final deadline premises,
processing and actual-read cache transport remain separate OPEN suppliers. FinalWindowSupply
jointly selects the same window, its delivery-spacing guard at E.ΔFG and pointwise heights.
No constant FrameWindow production or progress-form exclusion is assumed. -/
def HealthyLivenessReduction (B : EngineBinding (A := A) (F := F) (V := V) payload)
    (K : Contract ProgressReq)
    (C : ∀ E rho (hv : rho.ExecutionValid), ACCorrectLocal A (B.map E rho hv).signer) : Prop :=
  (∀ E rho (hv : rho.ExecutionValid),
    let M := B.map E rho hv
    let L := C E rho hv
    A.Requirements ∧ GrowingRunTransport M ∧ RegimeTransport M K L.look ∧
      ProposalProgressTransport M K L.healing L.catchUp L.hold L.margin ∧
      ProposalBudgetSupply M K L.catchUp L.hold L.margin ∧
      ProposalWitnessRefinement M K L ∧ ClaimDeadlineFit M K L ∧
      DeadlinePremisesSupply M K ∧ FinalWindowSupply M K L.healing L.catchUp L.hold ∧
      FinalCarrierSupply M L.catchUp L.hold ∧ FinalCacheSupply M L.healing L.catchUp L.hold ∧
      FinalProposerTransport M K L ∧ FinalReadTransport M L ∧
      EndReadTransport M K L ∧ HealthyReadPoint L ∧ LocalReadPoint L ∧
      ReadRepresentation M ∧ HonestReadTransport M ∧
      (¬ rho.HashCollision → Coherent (M.trace.HonestBlocksAt M.honest))) →
    ∀ cap g, O.output cap = some g → ∀ (idx : K.Idx) (gst : Time), (Sys F V).Holds
      (fun r => (Sys F V).Healthy K gst r ∧ (Sys F V).prog (shapeProgress F V) K cap idx
        ((Sys F V).ready K gst r) ((Sys F V).pt r).horizon r)
      fun r => ProposalLiveReady r.2 ((Sys F V).cDur K r) g ((Sys F V).heal K cap idx gst r)
        (K.params.latency cap idx)

/-- UNPROVED actual-read accountability reduction. The population supplier retains
both readers' own observation times and the attestation evidence; the map and honest
view contracts bind the same evidence to the engine conviction rule. -/
def FinalAccountabilityReduction
    (B : EngineBinding (A := A) (F := F) (V := V) payload) (K : Contract ProgressReq)
    (C : ∀ E rho (hv : rho.ExecutionValid), ACCorrectLocal A (B.map E rho hv).signer) : Prop :=
  (∀ E rho (hv : rho.ExecutionValid),
    let M := B.map E rho hv
    A.Requirements ∧ (P.genesisBlock A.genesisPayload).RootOk M.digest ∧
      GrowingRunTransport M ∧ EngineReadPoint M ∧ ActualReadAccountability M ∧
      ClaimDeadlineFit M K (C E rho hv) ∧ ReadRepresentation M ∧ HonestReadTransport M ∧
      HonestChainReads M ∧
      (¬ rho.HashCollision → Coherent (M.trace.HonestBlocksAt M.honest))) →
    ∀ g, O.output .final = some g → (Sys F V).Holds (fun _ => True)
      fun r => (chainTrace r.2).AccountablySafe r.2.ViewIdx r.2.Slashable K.params.α g 0

/-- UNPROVED outage reduction with the original source/destination, recovery time
and collision alternative. The same local supplier's fixed recovery policy is explicitly
matched to the advertised duration. The independent pre-outage service reserve remains
an unresolved supplier, never a strengthening of ServiceTransport.sync. -/
def PersistenceReduction (B : EngineBinding (A := A) (F := F) (V := V) payload)
    (K : Contract ProgressReq)
    (C : ∀ E rho (hv : rho.ExecutionValid), ACCorrectLocal A (B.map E rho hv).signer)
    (D : ∀ E rho (hv : rho.ExecutionValid), OutagePolicy (B.map E rho hv)) : Prop :=
  (∀ E rho (hv : rho.ExecutionValid),
    let M := B.map E rho hv
    let L := C E rho hv
    GrowingRunTransport M ∧ OutageTransport M (D E rho hv) K L.catchUp L.look ∧
      OutageRecoveryBinding M K L ∧ OutageServiceSupply M K ∧
      ResilienceTipTransport M ∧ OutageReadPoint L ∧
      EndReadTransport M K L ∧ LocalReadPoint L ∧
      ReadRepresentation M ∧ HonestReadTransport M ∧
      (¬ rho.HashCollision → Coherent (M.trace.HonestBlocksAt M.honest))) →
    ∀ g, O.output .stable = some g → ∀ T b₀ b₁,
      (Sys F V).Holds ((Sys F V).Outage (shapeProgress F V).toExternal K T b₀ b₁) fun r =>
        (chainTrace r.2).ProtectedReadyFrom ((Sys F V).cDur K r) g
          (resilienceTarget O g) T ((Sys F V).recoveryAt K b₁ r)

/-- UNPROVED healed-safety reduction. Reset, canonicality and the selected drain
budget are independent inputs to healing. Same-reader ancestry uses its own actual
stored-read context and transport; representation still supplies the chain-prefix step. -/
def HealedSafetyReduction (B : EngineBinding (A := A) (F := F) (V := V) payload)
    (K : Contract ProgressReq)
    (C : ∀ E rho (hv : rho.ExecutionValid), ACCorrectLocal A (B.map E rho hv).signer)
    (R : ∀ E rho (hv : rho.ExecutionValid), StoredReadContext (B.map E rho hv)) : Prop :=
  (∀ E rho (hv : rho.ExecutionValid),
    let M := B.map E rho hv
    let L := C E rho hv
    GrowingRunTransport M ∧ RegimeTransport M K L.look ∧ EngineReadPoint M ∧
      ClaimDeadlineFit M K L ∧ PreparationPremisesSupply M K ∧
      ResetProgressSupply M K L.healing ∧ ActualResetSupply M K L ∧
      HighCanonicalSupply M K L ∧ ResetHealBudgetSupply M K L ∧
      HealthyReadPoint L ∧ LocalReadPoint L ∧
      StoredReadTransport M (R E rho hv) ∧ HealedReadAncestry M K (R E rho hv) ∧
      ReadRepresentation M ∧ HonestReadTransport M ∧
      (¬ rho.HashCollision → Coherent (M.trace.HonestBlocksAt M.honest))) →
    ∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
      ∀ (idx : K.Idx) (gst : Time), (Sys F V).Holds
        (fun r => (Sys F V).Healthy K gst r ∧ (Sys F V).prog (shapeProgress F V) K cap idx
          ((Sys F V).ready K gst r) ((Sys F V).heal K cap idx gst r) r)
        fun r => (chainTrace r.2).ReadySafe ((Sys F V).cDur K r) g
          ((Sys F V).heal K cap idx gst r)

/-- UNPROVED mechanical bundling only, not a reduction from local correctness.
Each premise is an individual endpoint field, not evidence supplied by this file.
No whole ShapeClaims premise is used; the four non-claim obligations remain downstream. -/
def GenericClaimsBundling (K : Contract ProgressReq) : Prop :=
  (∀ (V : Type) [Fintype V] [DecidableEq V],
    ((Sys F V).HoldsAlways fun r => ∀ c g, O.output c = some g → OutputValid r.2 g) ∧
    (∀ c₁ c₂ g₁ g₂, c₁.rank < c₂.rank → O.output c₁ = some g₁ →
      O.output c₂ = some g₂ →
      (Sys F V).HoldsAlways fun r => (chainTrace r.2).Nested g₁ g₂) ∧
    (∀ g, O.output .final = some g →
      (Sys F V).HoldsAlways fun r => (chainTrace r.2).Monotone g 0) ∧
    (∀ g, O.output .final = some g → (Sys F V).Holds (fun _ => True)
      fun r => (chainTrace r.2).AccountablySafe r.2.ViewIdx r.2.Slashable K.params.α g 0) ∧
    (∀ cap g, O.output cap = some g → ∀ (idx : K.Idx) (gst : Time), (Sys F V).Holds
      (fun r => (Sys F V).Healthy K gst r ∧ (Sys F V).prog (shapeProgress F V) K cap idx
        ((Sys F V).ready K gst r) ((Sys F V).pt r).horizon r)
      fun r => ProposalLiveReady r.2 ((Sys F V).cDur K r) g
        ((Sys F V).heal K cap idx gst r) (K.params.latency cap idx)) ∧
    (∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
      (Sys F V).Holds ((Sys F V).Sleepy K) fun r =>
        (chainTrace r.2).ReadySafe ((Sys F V).cDur K r) g 0) ∧
    (∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
      ∀ idx : K.Idx, (Sys F V).Holds
        (fun r => (Sys F V).Sleepy K r ∧ (Sys F V).prog (shapeProgress F V) K cap idx 0
          ((Sys F V).pt r).horizon r)
        fun r => ProposalLiveReady r.2 ((Sys F V).cDur K r) g 0 (K.params.latency cap idx)) ∧
    (∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
      ∀ (idx : K.Idx) (gst : Time), (Sys F V).Holds
        (fun r => (Sys F V).Healthy K gst r ∧ (Sys F V).prog (shapeProgress F V) K cap idx
          ((Sys F V).ready K gst r) ((Sys F V).heal K cap idx gst r) r)
        fun r => (chainTrace r.2).ReadySafe ((Sys F V).cDur K r) g
          ((Sys F V).heal K cap idx gst r)) ∧
    (∀ g, O.output .stable = some g → ∀ T b₀ b₁,
      (Sys F V).Holds ((Sys F V).Outage (shapeProgress F V).toExternal K T b₀ b₁) fun r =>
        (chainTrace r.2).ProtectedReadyFrom ((Sys F V).cDur K r) g
          (resilienceTarget O g) T ((Sys F V).recoveryAt K b₁ r))) →
    GenericClaims F K

end Consensus.Goldilocks.Generic

end
