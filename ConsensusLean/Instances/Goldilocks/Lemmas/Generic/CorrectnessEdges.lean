module
public import ConsensusLean.Spec.Shape.Obligations
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ClaimTransports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.ChainRepresentationEdges
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.CorrectLocal
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.FG
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.SyncUntil

public section

/-! # Open correctness assembly edges

All edges are admission-free proposition definitions, not proofs. Nothing here is supplied as
evidence to a definition, instance, type witness or compiled endpoint. Reductions remain open rows
until the concrete morphism and missing local interfaces have been specified.
-/

namespace Consensus.Goldilocks.Generic

open Shape Blocks

/-- Intended window extraction edge. FrameWindow retains its constant-frame meaning;
the four anchors and their height steps are explicit data, not a second window record.
The designated proposals are a progress premise, not an output guarantee. -/
def final_window_extract_at {P : Params} (A : NodeAC P) (sg : A.Msg → Fin P.n)
    (C : ACCorrectLocal A sg) : Prop :=
  ∀ (cm : Time → Finset (Fin P.n)) (βK : ℚ) (tr : RunTrace A)
    (H : Time → Set (Fin P.n)) (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (g ΔF deadline : Time)
    (start gap floor : Nat) (kindJ : Prop) (J : A.Blk)
    (block : Fin 4 → A.Blk) (cut : Fin 4 → Nat),
    βK ≤ 1 / 2 →
    C.run.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF deadline →
    FrameWindow tr H (P.slotTime start) deadline floor kindJ J →
    HealedFrom tr H proposer start deadline → 2 ≤ gap → 3 * gap ≤ P.δt →
    StrictMono cut →
    (∀ a, (block a).slot = start + a.val * gap ∧
      tr.ProposesAt (block a).proposer (cut a) (block a) ∧
      ReadyCut tr H C.catchUp (block a).proposer (cut a) ∧
      (block a).proposer ∈ H (tr.time (cut a) + C.hold)) →
    tr.time (cut 3) + P.Δ ≤ deadline →
    (∀ a, tr.AcceptAt (block a).proposer (cut a) (block a)) ∧
      (∀ a b, a ≤ b → Anc (tr.HonestBlocksAt H) (block a) (block b)) ∧
      ∀ a : Fin 3, ∃ z i j, z ∈ H (tr.time i) ∧ z ∈ H (tr.time j) ∧
        block a.castSucc ∈ (tr.state z i).fg.tree ∧ block a.succ ∈ (tr.state z j).fg.tree ∧
        ((tr.state z i).fg.σ (block a.castSucc).root).h + 1 ≤
          ((tr.state z j).fg.σ (block a.succ).root).h

/-- Intended cache-coverage edge from an explicit four-anchor chain and three height steps.
Population safety and actual processing of the carrier remain explicit inputs. -/
def final_cache_coverage_at {P : Params} (A : NodeAC P) (sg : A.Msg → Fin P.n)
    (C : ACCorrectLocal A sg) : Prop :=
  ∀ (cm : Time → Finset (Fin P.n)) (βK : ℚ) (tr : RunTrace A)
    (H : Time → Set (Fin P.n)) (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload) (g ΔF deadline : Time)
    (start gap floor : Nat) (kindJ : Prop) (J : A.Blk)
    (block : Fin 4 → A.Blk) (cut : Fin 4 → Nat),
    βK ≤ 1 / 2 →
    C.run.Run cm proposer dg H tr → Premises tr H cm βK proposer dg sg g ΔF deadline →
    FrameWindow tr H (P.slotTime start) deadline floor kindJ J →
    HealedFrom tr H proposer start deadline → 2 ≤ gap → 3 * gap ≤ P.δt →
    StrictMono cut →
    (∀ a, (block a).slot = start + a.val * gap ∧
      tr.ProposesAt (block a).proposer (cut a) (block a) ∧
      tr.AcceptAt (block a).proposer (cut a) (block a) ∧
      ReadyCut tr H C.catchUp (block a).proposer (cut a)) →
    (∀ a b, a ≤ b → Anc (tr.HonestBlocksAt H) (block a) (block b)) →
    (∀ a : Fin 3, ∃ z i j, z ∈ H (tr.time i) ∧ z ∈ H (tr.time j) ∧
      block a.castSucc ∈ (tr.state z i).fg.tree ∧ block a.succ ∈ (tr.state z j).fg.tree ∧
      ((tr.state z i).fg.σ (block a.castSucc).root).h + 1 ≤
        ((tr.state z j).fg.σ (block a.succ).root).h) →
    tr.time (cut 3) + P.Δ ≤ deadline →
    ∀ y j, deadline ≤ tr.time j → ReadyCut tr H C.catchUp y j →
      (H (tr.time j))ᶜ.ncard < 2 * P.q - P.n →
      (∃ k < j, tr.BlockCallAt y k (block 3)) →
      Anc (tr.HonestBlocksAt H) (block 0) (tr.finalizedAt y j)

/-- Prefix-reader bridge on generic runs: freeze honesty at the observation, retain the
prefix run and recover the original state at every cut no later than the observation. -/
def prefix_reader_edge {P : Params} (A : NodeAC P) (sg : A.Msg → Fin P.n)
    (runs : ACRun A sg) : Prop :=
  ∀ (cm : Time → Finset (Fin P.n)) (proposer : Nat → Fin P.n)
    (dg : Digest (List (FG.Att P.n)) A.Payload)
    (H : Time → Set (Fin P.n)) (tr : RunTrace A),
    runs.Run cm proposer dg H tr →
    ∀ d, 0 ≤ d → Node.LocalRun proposer dg (H d) sg (tr.upTo d) (runs.start cm) ∧
      ∀ y i, (∀ k < i, tr.time k ≤ d) → (tr.upTo d).state y i = tr.state y i

/-- Collision freedom transports to a prefix; this is not supplied evidence. -/
def noColl_transport_edge {P : Params} (A : NodeAC P) : Prop :=
  ∀ (dg : Digest (List (FG.Att P.n)) A.Payload) (tr : RunTrace A) (d : Time),
    Compose.NoCollRun dg tr → Compose.NoCollRun dg (tr.upTo d)

/-- Deadline service of the generic AC projection supplies actual processing witnesses.
This is the run-level deadline bridge, not an assertion of an unspecified engine morphism. -/
def syncUntil_service_edge {P : Params} (A : NodeAC P) : Prop :=
  ∀ (tr : RunTrace A) (H : Time → Set (Fin P.n)) (b d : Time),
    SyncUntilAC A (H d) (tr.HonestBlocksAt H) b tr.projAC →
    ∀ x, x ∈ H d → ∀ i m, tr.projAC.SendOrAdmit x i m →
      ∀ y, y ∈ H d → ∀ j ℓ, tr.projAC.CallAt y j ℓ →
        tr.projAC.deadline y j (tr.projAC.time i) ≤ tr.projAC.time j →
        tr.projAC.deadline y j (tr.projAC.time i) ≤ b + 1 →
        ∃ k ≤ j, tr.projAC.time i ≤ tr.projAC.time k ∧ tr.projAC.ProcessAt y k m ∧
          tr.projAC.time k < tr.projAC.deadline y k (tr.projAC.time i) ∧
          ∀ r, k < r → r ≤ j → ¬ tr.projAC.RestartAt y r

/-- The independent suppliers consumed by the claim reductions, each named once.
The read-point records are separate local obligations, not fields of `ACCorrectLocal`.
Outage policy and stored-read context are data parameters, never hidden Prop fields.
This record supplies neither a compiled protocol run nor any endpoint claim. -/
structure LocalClaimSuppliers {P : Params} {A : NodeAC P} {O : OutputSchema} {Info : Type}
    [DecidableEq Info] [Countable Info] {F : ChainShapeFamily O Info}
    {V : Type} [Fintype V] [DecidableEq V] {E : Env V}
    {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat}
    (M : RunMap rho payload) (C : ACCorrectLocal A M.signer) (K : Contract ProgressReq)
    (D : OutagePolicy M) (R : StoredReadContext M) : Prop where
  regime : RegimeTransport M K C.look
  reads : ReadRepresentation M
  honestReads : HonestReadTransport M
  chains : ChainRepresentation A M.chain M.header
  honestChains : HonestChainReads M
  coherent : ¬ rho.HashCollision → Coherent (M.trace.HonestBlocksAt M.honest)
  engineRead : EngineReadPoint M
  localRead : LocalReadPoint C
  sleepyRead : SleepyReadPoint C
  healthyRead : HealthyReadPoint C
  outageRead : OutageReadPoint C
  deadlines : ClaimDeadlineFit M K C
  endReads : EndReadTransport M K C
  progress : ProposalProgressTransport M K C.healing
  proposalWitness : ProposalWitnessRefinement M K C
  deadlinePremises : DeadlinePremisesSupply M K
  finalWindow : FinalWindowSupply M K C.run C.catchUp C.hold
  finalReads : FinalReadTransport M K C
  accountability : ActualReadAccountability M C.run
  outage : OutageTransport M D K
  recovery : OutageRecoveryBinding M K C
  outageService : OutageServiceSupply M K C
  resilience : ResilienceTipTransport M
  preparation : PreparationPremisesSupply M K
  resetProgress : ResetProgressSupply M K C.healing
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

/-- UNPROVED assembly from local correctness and its engine suppliers.
The intended proof uses OutputValidAlways (with OutputValidityEdge), NestedChainsAlways,
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
    (B : ∀ (V : Type) [Fintype V] [DecidableEq V] pub,
      EngineBinding (F := F) (V := V) pub.val (C pub).payload (sg pub) (C pub).run)
    (D : ∀ (V : Type) [Fintype V] [DecidableEq V] pub E hE rho hv,
      OutagePolicy ((B V pub).map E hE rho hv))
    (R : ∀ (V : Type) [Fintype V] [DecidableEq V] pub E hE rho hv,
      StoredReadContext ((B V pub).map E hE rho hv)),
    (∀ (V : Type) [Fintype V] [DecidableEq V] pub E hE rho hv,
      LocalClaimSuppliers ((B V pub).map E hE rho hv)
        ((B V pub).signer_eq E hE rho hv ▸ C pub) K
        (D V pub E hE rho hv) (R V pub E hE rho hv)) →
    K.params.Admissible → O.Serves → ProgressFits K F → ProgressTolerant O K →
    HealthyBetaFit K → CommitteeHalfFit K → ShapeObligations F K

end Consensus.Goldilocks.Generic

end
