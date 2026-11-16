module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ClaimTransports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.EngineEdges
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.ChainRepresentationEdges
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.CorrectnessEdges
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.OutageSupply
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.HealingLeaves
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.SleepyFG
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.SleepyGlue
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.SleepyTransport
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.Invariant
import ConsensusLean.Instances.Goldilocks.Lemmas.FGStore.SeedCandidacy
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Lemmas.Model.Laws

public section

/-! # Conditional claim reduction rows

Conditional theorem contracts, all proved: output validity and final accountability (section
"Output-validity and accountability proofs"), persistence (section "Persistence proof"), healed
safety (section "Healed safety proof"), healthy liveness (section "Healthy liveness proof"), and
sleepy safety and liveness (section `SleepyReductions`). No supplier instance or unconditional
correctness claim is supplied. All suppliers below refer to the binding's same map. Every regime
reduction reads outputs through the one stored-read context and its transport: engine-cut reads
at the stored read, claim-time reads at `endCut t`. Healed safety's same-reader ancestry is never
inferred from compatibility.
-/

set_option autoImplicit false
namespace Consensus.Goldilocks.Generic
open Shape Blocks

variable {P : Params} {A : NodeAC P} {O : OutputSchema} {Info : Type}
  [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {payload : A.Blk → Set Nat}
  {sg : A.Msg → Fin P.n} {runs : ACRun A sg}
  {pub : Model.Public}

section StoredReads

variable {E : Env V} {rho : Model.Run (compiled F) E}

/-- The engine cut at the end of `t ≥ 0` is at a time `≤ t`. -/
theorem cutTime_endCut_le (rho : Model.Run (compiled F) E) {t : Time} (ht : 0 ≤ t) :
    rho.cutTime ((chainTrace rho).endCut t) ≤ t :=
  Nat.findGreatest_spec (P := fun i => rho.cutTime i ≤ t) (Nat.zero_le _)
    (by simpa [Model.Run.cutTime] using ht)

/-- A confirmed-tip output of a node honest at its engine cut is the chain of its stored read tip
in its store at the stored read's cut. -/
theorem stored_output_eq {M : RunMap rho payload} {R : StoredReadContext M}
    (hR : StoredReadTransport M R) (hv : rho.ExecutionValid) {g : O.Id}
    (hg : ∀ st t, M.tip g st t = A.confirmed st.ac (Node.frame st) t) {v : V} {i : Nat}
    (hi : i ≤ rho.events.length) (hh : rho.point.HonestAt v (rho.cutTime i)) :
    (chainTrace rho).read g v i =
      (M.chain (M.trace.state (M.validator.symm v) (R.cut v i)) (R.tip v i)).map M.header := by
  change (F (Model.pubOf E)).out g (rho.stateBefore i v).st.1 = _
  rw [M.output_eq g v i hi, M.state_eq v i hi hh, hg, hR.source_state hv v i hi,
    hR.current_tip hv v i hi hh]
  rfl

/-- A confirmed-tip output read at the end of a time `t` at which its reader is ready is the chain
of the confirmed read at `t` in its store at the mapped cut of `endCut t`. -/
theorem end_read_output_eq {M : RunMap rho payload} {R : StoredReadContext M}
    (hR : StoredReadTransport M R) (hv : rho.ExecutionValid) {g : O.Id}
    (hg : ∀ st t, M.tip g st t = A.confirmed st.ac (Node.frame st) t) {c : Time} (hc : 0 ≤ c)
    {v : V} {t : Time} (ht : 0 ≤ t) (hth : t ≤ rho.horizon) (hr : rho.point.Ready c v t) :
    (chainTrace rho).readAt g v t =
      (M.chain (M.trace.state (M.validator.symm v) (M.cut ((chainTrace rho).endCut t)))
        (confirmedRead M.trace (M.validator.symm v) (M.cut ((chainTrace rho).endCut t))
          t)).map M.header := by
  have hi : (chainTrace rho).endCut t ≤ rho.events.length := Nat.findGreatest_le _
  have hh : rho.point.HonestAt v (rho.cutTime ((chainTrace rho).endCut t)) := fun h =>
    hr.1 (rho.faultyAt_mono (cutTime_endCut_le rho ht) h)
  change (chainTrace rho).read g v ((chainTrace rho).endCut t) = _
  rw [stored_output_eq hR hv hg hi hh, hR.source_tip, (hR.end_read hv c hc v t ht hth hr).1]
  unfold confirmedRead
  rw [hR.source_state hv v _ hi]

end StoredReads

/-- Exact output-validity wrapper. OutputValidityEdge, not held_view alone,
is the reduction input. HoldsAlways remains excuse-free at the fixed public parameters.
Proved by `outputValidAlways`. -/
def OutputValidAlways (B : EngineBinding (F := F) (V := V) pub payload sg runs) : Prop :=
  (∀ E hE rho (hv : rho.ExecutionValid),
    OutputValidityEdge (B.map E hE rho hv) ∧ ReadRepresentation (B.map E hE rho hv) ∧
      HonestReadTransport (B.map E hE rho hv)) →
    (Sys F V).HoldsAlways fun r => Model.pubOf r.1 = pub →
      ∀ c g, O.output c = some g → OutputValid r.2 g

/-- Bounded explicit-read sleepy safety reduction, proved by `sleepy_safety_reduction`.
Coherent union and
root suppliers remain explicit; none enters an unconditional claim. Source:
Concrete/Fields.meetsObligations_sleepySafe_growing. -/
def SleepySafetyReduction (C : ACCorrectLocal A sg)
    (B : EngineBinding (F := F) (V := V) pub payload sg C.run) (K : Contract ProgressReq)
    (D : SleepyLayer1.Data A)
    (R : ∀ E hE rho (hv : rho.ExecutionValid), StoredReadContext (B.map E hE rho hv)) : Prop :=
  (∀ E hE rho (hv : rho.ExecutionValid),
    let M := B.map E hE rho hv
    let L : ACCorrectLocal A M.signer := B.signer_eq E hE rho hv ▸ C
    RegimeTransport M K L ∧ EngineReadPoint M ∧ StoredReadTransport M (R E hE rho hv) ∧
      LocalReadPoint L ∧ SleepyLayer1.EventSafety M L D ∧ SleepyLayer1.OutputProvenance L D ∧
      SleepyLayer1.Extension M L D ∧ SleepyLayer1.SourceProvenance L D ∧
      PopulationQuorumSupply M K ∧ SleepyWindowSupply M K L ∧ ClaimDeadlineFit M K L ∧
      ReadRepresentation M ∧ HonestReadTransport M ∧
      (¬ rho.HashCollision → Coherent (M.trace.HonestBlocksAt M.honest))) →
    ∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
      (Sys F V).Holds (fun r => Model.pubOf r.1 = pub ∧
        (Sys F V).Sleepy (shapeProgress F V).toExternal K r) fun r =>
        (chainTrace r.2).ReadySafe ((Sys F V).cDur K r) g 0

/-- Sleepy proposal reduction, proved by `sleepy_liveness_reduction`, keeping the original
progress interval,
reader-conditional deadline and hash-collision branch. The strengthened witness
supplier selects advertised readiness jointly with the proposal. -/
def SleepyLivenessReduction (C : ACCorrectLocal A sg)
    (B : EngineBinding (F := F) (V := V) pub payload sg C.run) (K : Contract ProgressReq)
    (D : SleepyLayer1.Data A)
    (R : ∀ E hE rho (hv : rho.ExecutionValid), StoredReadContext (B.map E hE rho hv)) : Prop :=
  (∀ E hE rho (hv : rho.ExecutionValid),
    let M := B.map E hE rho hv
    let L : ACCorrectLocal A M.signer := B.signer_eq E hE rho hv ▸ C
    RegimeTransport M K L ∧
      ProposalProgressTransport M ∧
      ProposalWitnessRefinement M K L ∧ ClaimDeadlineFit M K L ∧
      StoredReadTransport M (R E hE rho hv) ∧ SleepyLayer1.ProposalCoverage M L D ∧
      LocalReadPoint L ∧
      SleepyLayer1.EventSafety M L D ∧ SleepyLayer1.OutputProvenance L D ∧
      SleepyLayer1.Extension M L D ∧ SleepyLayer1.SourceProvenance L D ∧
      PopulationQuorumSupply M K ∧ SleepyWindowSupply M K L ∧
      ReadRepresentation M ∧ HonestReadTransport M ∧
      (¬ rho.HashCollision → Coherent (M.trace.HonestBlocksAt M.honest))) →
    ∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
      ∀ idx : K.Idx, (Sys F V).Holds
        (fun r => Model.pubOf r.1 = pub ∧ (Sys F V).Sleepy (shapeProgress F V).toExternal K r ∧
          (Sys F V).prog (shapeProgress F V) K cap idx 0
          ((Sys F V).pt r).horizon r)
        fun r => ProposalLiveReady r.2 ((Sys F V).cDur K r) g 0 (K.params.latency cap idx)

/-- All-capability healthy liveness reduction. Actual final deadline premises,
processing and actual-read cache transport are separate supplier contracts. FinalWindowSupply
jointly selects advertised anchor readiness, delivery spacing and pointwise heights.
No constant FrameWindow production or progress-form exclusion is assumed. The nonfinal
inclusion reads at L7 (`HealthyReadPoint.proposal`), whose premises and selected reset come from
the healthy preparation (`PreparationPremisesSupply`) and reset budget (`ResetHealBudgetSupply`)
suppliers. Proved by `healthyLivenessReduction`. -/
def HealthyLivenessReduction (C : ACCorrectLocal A sg)
    (B : EngineBinding (F := F) (V := V) pub payload sg C.run) (K : Contract ProgressReq)
    (R : ∀ E hE rho (hv : rho.ExecutionValid), StoredReadContext (B.map E hE rho hv)) : Prop :=
  K.params.Admissible → HealthyBetaFit K → CommitteeHalfFit K →
  (∀ E hE rho (hv : rho.ExecutionValid),
    let M := B.map E hE rho hv
    let L : ACCorrectLocal A M.signer := B.signer_eq E hE rho hv ▸ C
    RegimeTransport M K L ∧
      ProposalProgressTransport M ∧
      ProposalWitnessRefinement M K L ∧ ClaimDeadlineFit M K L ∧
      DeadlinePremisesSupply M K ∧ FinalWindowSupply M K L.run L.catchUp L.hold ∧
      FinalReadTransport M K L ∧ PreparationPremisesSupply M K ∧ ResetHealBudgetSupply M K L ∧
      StoredReadTransport M (R E hE rho hv) ∧ HealthyReadPoint L ∧ LocalReadPoint L ∧
      ReadRepresentation M ∧ HonestReadTransport M ∧
      (¬ rho.HashCollision → Coherent (M.trace.HonestBlocksAt M.honest))) →
    ∀ cap g, O.output cap = some g → ∀ (idx : K.Idx) (gst : Time), (Sys F V).Holds
      (fun r => Model.pubOf r.1 = pub ∧ (Sys F V).Healthy (shapeProgress F V).toExternal K gst r ∧
        (Sys F V).prog (shapeProgress F V) K cap idx
        ((Sys F V).ready K gst r) ((Sys F V).pt r).horizon r)
      fun r => ProposalLiveReady r.2 ((Sys F V).cDur K r) g ((Sys F V).heal K cap idx gst r)
        (K.params.latency cap idx)

/-- Actual-read accountability reduction. The population supplier retains
both readers' own observation times and the attestation evidence; the map and honest
view contracts bind the same evidence to the engine conviction rule.
Proved by `finalAccountabilityReduction`. -/
def FinalAccountabilityReduction (C : ACCorrectLocal A sg)
    (B : EngineBinding (F := F) (V := V) pub payload sg C.run) (K : Contract ProgressReq) : Prop :=
  (∀ E hE rho (hv : rho.ExecutionValid),
    let M := B.map E hE rho hv
    let L : ACCorrectLocal A M.signer := B.signer_eq E hE rho hv ▸ C
    EngineReadPoint M ∧ ActualReadAccountability M L.run ∧
      ClaimDeadlineFit M K L ∧ ReadRepresentation M ∧ HonestReadTransport M ∧
      HonestChainReads M ∧
      (¬ rho.HashCollision → Coherent (M.trace.HonestBlocksAt M.honest))) →
    ∀ g, O.output .final = some g → (Sys F V).Holds (fun r => Model.pubOf r.1 = pub ∧ True)
      fun r => (chainTrace r.2).AccountablySafe r.2.ViewIdx r.2.Slashable K.params.α g 0

/-- Outage reduction with the original source/destination, recovery time
and collision alternative. The fixed local policy matches the contract by equality;
recipient-deadline service permits AC-owned retained evidence. OC-K and the instance
transports remain obligations, not consequences of these numerical fits.
Proved by `persistenceReduction`. -/
def PersistenceReduction (C : ACCorrectLocal A sg)
    (B : EngineBinding (F := F) (V := V) pub payload sg C.run) (K : Contract ProgressReq)
    (D : ∀ E hE rho (hv : rho.ExecutionValid), OutagePolicy (B.map E hE rho hv))
    (R : ∀ E hE rho (hv : rho.ExecutionValid), StoredReadContext (B.map E hE rho hv)) : Prop :=
  (∀ E hE rho (hv : rho.ExecutionValid),
    let M := B.map E hE rho hv
    let L : ACCorrectLocal A M.signer := B.signer_eq E hE rho hv ▸ C
    OutageTransport M (D E hE rho hv) K ∧
      OutageRecoveryBinding M K L ∧ OutageServiceSupply M K L ∧
      ResilienceTipTransport M ∧ OutageReadPoint L ∧
      StoredReadTransport M (R E hE rho hv) ∧ LocalReadPoint L ∧
      ReadRepresentation M ∧ HonestReadTransport M ∧
      (¬ rho.HashCollision → Coherent (M.trace.HonestBlocksAt M.honest))) →
    ∀ g, O.output .stable = some g → ∀ T b₀ b₁,
      (Sys F V).Holds (fun r => Model.pubOf r.1 = pub ∧
        (Sys F V).Outage (shapeProgress F V).toExternal K T b₀ b₁ r) fun r =>
        (chainTrace r.2).ProtectedReadyFrom ((Sys F V).cDur K r) g
          (resilienceTarget O g) T ((Sys F V).recoveryAt K b₁ r)

/-- Healed-safety reduction. Reset, canonicality and the selected drain
budget are independent inputs to healing. Same-reader ancestry uses its own actual
stored-read context and transport; representation still supplies the chain-prefix step.
Proved by `healedSafetyReduction`. -/
def HealedSafetyReduction (C : ACCorrectLocal A sg)
    (B : EngineBinding (F := F) (V := V) pub payload sg C.run) (K : Contract ProgressReq)
    (R : ∀ E hE rho (hv : rho.ExecutionValid), StoredReadContext (B.map E hE rho hv)) : Prop :=
  K.params.Admissible → HealthyBetaFit K → CommitteeHalfFit K →
  (∀ E hE rho (hv : rho.ExecutionValid),
    let M := B.map E hE rho hv
    let L : ACCorrectLocal A M.signer := B.signer_eq E hE rho hv ▸ C
    RegimeTransport M K L ∧ EngineReadPoint M ∧
      ClaimDeadlineFit M K L ∧ PreparationPremisesSupply M K ∧
      HighCanonicalSupply M K L ∧ ResetHealBudgetSupply M K L ∧
      HealthyReadPoint L ∧ LocalReadPoint L ∧
      StoredReadTransport M (R E hE rho hv) ∧ HealedReadAncestry M K (R E hE rho hv) ∧
      ReadRepresentation M ∧ HonestReadTransport M ∧
      (¬ rho.HashCollision → Coherent (M.trace.HonestBlocksAt M.honest))) →
    ∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
      ∀ (idx : K.Idx) (gst : Time), (Sys F V).Holds
        (fun r => Model.pubOf r.1 = pub ∧ (Sys F V).Healthy (shapeProgress F V).toExternal K gst r ∧
          (Sys F V).prog (shapeProgress F V) K cap idx
          ((Sys F V).ready K gst r) ((Sys F V).heal K cap idx gst r) r)
        fun r => (chainTrace r.2).ReadySafe ((Sys F V).cDur K r) g
          ((Sys F V).heal K cap idx gst r)

section OutputAccountabilityProofs

/-- Output validity at fixed public parameters: the binding's map of each valid run supplies
`OutputValidityEdge` together with its representation premises. -/
theorem outputValidAlways (B : EngineBinding (F := F) (V := V) pub payload sg runs) :
    OutputValidAlways B := by
  intro h r hv hpub _ g _
  obtain ⟨E, rho⟩ := r
  obtain ⟨hov, hrep, hhr⟩ := h E hpub rho hv
  exact (outputValidityEdge_iff _).1 hov hrep hhr hv g

/-- A local record transported along signer equality has the same runs. -/
private theorem cast_local_run {sg' : A.Msg → Fin P.n} (h : sg = sg') (C : ACCorrectLocal A sg) :
    (h ▸ C).run.Run = C.run.Run := by
  subst h
  rfl

/-- Accountable safety of the final output at fixed public parameters. A hash collision is the
claim's excuse. Otherwise two final reads at honest engine cuts are the chains of the readers'
finalized caches (`HonestChainReads`). Compatible caches give a chain prefix
(`ReadRepresentation.ancestor_prefix` in the coherent honest universe). Incompatible caches give
`2q − n` validators with slashable attestation pairs on the two finality chains
(`ActualReadAccountability`), which the readers' views hold (`chain_att_view`), and
`α·n ≤ 2q − n` (`ClaimDeadlineFit.accountable`). -/
theorem finalAccountabilityReduction (C : ACCorrectLocal A sg)
    (B : EngineBinding (F := F) (V := V) pub payload sg C.run) (K : Contract ProgressReq) :
    FinalAccountabilityReduction C B K := by
  intro h g hg r hv hpub
  obtain ⟨E, rho⟩ := r
  obtain ⟨hpub, -⟩ := hpub
  by_cases hc : rho.HashCollision
  · exact Or.inr hc
  refine Or.inl ?_
  obtain ⟨heng, hacc, hfit, hrep, hhr, hcr, hcoh⟩ := h E hpub rho hv
  set M := B.map E hpub rho hv
  have hT := B.run_transport E hpub rho hv
  have hrun : (B.signer_eq E hpub rho hv ▸ C).run.Run M.committee M.proposer M.digest M.honest
      M.trace := by
    rw [cast_local_run]
    have := hT.run hv
    rwa [ACRun.cast_run] at this
  have hcoh := hcoh hc
  have hread : ∀ v i, i ≤ rho.events.length → rho.point.HonestAt v (rho.cutTime i) →
      (chainTrace rho).read g v i =
        (M.chain (mappedReadState M v i) (mappedReadState M v i).fg.F).map M.header := by
    intro v i hi hh
    rw [hcr.output_read v i hi hh g, hcr.finalized_tip g hg]
  have hsub : ∀ v i, i ≤ rho.events.length → rho.point.HonestAt v (rho.cutTime i) →
      (mappedReadState M v i).fg.tree ⊆ M.trace.HonestBlocksAt M.honest := by
    intro v i hi hh X hX
    obtain ⟨hy, hle, ht0, -⟩ := heng.honest hv v i hi hh
    exact ⟨_, _, _, ht0, hle.1, hy, hX⟩
  intro u v i j hi hj hu hv'
  rw [hread u i hi.1 hu, hread v j hj.1 hv']
  by_cases hcomp : Compatible (M.trace.HonestBlocksAt M.honest)
      (M.trace.finalizedAt (M.validator.symm u) (M.cut i))
      (M.trace.finalizedAt (M.validator.symm v) (M.cut j))
  · left
    rcases hcomp with hanc | hanc
    · exact Or.inl (hrep.ancestor_prefix u v i j hi.1 hj.1 hu hv' (hhr.reachable hv u i hi.1 hu)
        (hhr.reachable hv v j hj.1 hv') (hhr.roots hv u i hi.1 hu) (hhr.roots hv v j hj.1 hv')
        hcoh (hsub u i hi.1 hu) (hsub v j hj.1 hv') _ _ (hcr.finalized_held hv u i hi.1 hu)
        (hcr.finalized_held hv v j hj.1 hv') hanc)
    · exact Or.inr (hrep.ancestor_prefix v u j i hj.1 hi.1 hv' hu (hhr.reachable hv v j hj.1 hv')
        (hhr.reachable hv u i hi.1 hu) (hhr.roots hv v j hj.1 hv') (hhr.roots hv u i hi.1 hu)
        hcoh (hsub v j hj.1 hv') (hsub u i hi.1 hu) _ _ (hcr.finalized_held hv v j hj.1 hv')
        (hcr.finalized_held hv u i hi.1 hu) hanc)
  · right
    obtain ⟨X, -, Y, -, W, hW, hWatt⟩ := hacc hrun (hT.no_collision hv hc) _ _ _ _ _ _
      (heng.honest hv u i hi.1 hu) (heng.honest hv v j hj.1 hv') hcomp
    have hview : ∀ a ∈ BlockFinality.ChainAtts M.trace (M.validator.symm u) (M.cut i) X ∪
        BlockFinality.ChainAtts M.trace (M.validator.symm v) (M.cut j) Y,
        M.attObject a ∈ rho.ViewIdx u i ∪ rho.ViewIdx v j := by
      intro a ha
      rcases ha with ha | ha
      · exact Or.inl (hhr.chain_att_view hv u i hi.1 hu X a ha)
      · exact Or.inr (hhr.chain_att_view hv v j hj.1 hv' Y a ha)
    have hconv : W.map M.validator.toEmbedding ⊆
        Consensus.convicted rho.Slashable (rho.ViewIdx u i ∪ rho.ViewIdx v j) := by
      intro x hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.1 hx
      obtain ⟨a, ha, b, hb, haw, hab⟩ := hWatt w hw
      classical
      simp only [Consensus.convicted, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨M.attObject a, hview a ha, M.attObject b, hview b hb, ?_, ?_, M.att_conflict a b hab⟩
      · rw [M.att_signer, haw]; rfl
      · rw [M.att_signer, ← hab.1, haw]; rfl
    have hcard := Finset.card_le_card hconv
    rw [Finset.card_map] at hcard
    have hV : Fintype.card V = P.n := by
      simpa using (Fintype.card_congr M.validator).symm
    have hacc' := hfit.accountable
    rw [hV]
    calc (P.n : ℚ) * K.params.α = K.params.α * P.n := mul_comm _ _
      _ ≤ ((2 * P.q - P.n : Nat) : ℚ) := hacc'
      _ ≤ W.card := by exact_mod_cast hW
      _ ≤ _ := by exact_mod_cast hcard

end OutputAccountabilityProofs

section PersistenceProof

/-- Persistence of the stable output at fixed public parameters. A hash collision is the claim's
excuse. Otherwise both reads are confirmed reads at the readers' end cuts
(`end_read_output_eq`, with `confirmed_tip` and `ResilienceTipTransport`). The outage
policy's protection (`OutageReadPoint.protection`) relates them in the honest universe from the
recovery point on: the outage times and service come from `Outage` (`OutageServiceSupply`), its
participation at the local catch-up from `OutageTransport.participation_local`, the policy
durations from `OutageRecoveryBinding`, and both ready read points from
`StoredReadTransport.end_read` at the local catch-up `C.catchUp ≤ cDur`. Their honest ancestry
gives a chain prefix (`ReadRepresentation.ancestor_prefix`), with both tips held
(`LocalReadPoint.held`). -/
theorem persistenceReduction (C : ACCorrectLocal A sg)
    (B : EngineBinding (F := F) (V := V) pub payload sg C.run) (K : Contract ProgressReq)
    (D : ∀ E hE rho (hv : rho.ExecutionValid), OutagePolicy (B.map E hE rho hv))
    (R : ∀ E hE rho (hv : rho.ExecutionValid), StoredReadContext (B.map E hE rho hv)) :
    PersistenceReduction C B K D R := by
  intro h g hg T b₀ b₁ r hv hpre
  obtain ⟨E, rho⟩ := r
  obtain ⟨hpub, hout⟩ := hpre
  by_cases hc : rho.HashCollision
  · exact Or.inr hc
  refine Or.inl ?_
  obtain ⟨hOT, hOR, hOS, hRT, hOP, hSR, hLR, hrep, hhr, hcoh⟩ := h E hpub rho hv
  set M := B.map E hpub rho hv
  have hT := B.run_transport E hpub rho hv
  have hrun : (B.signer_eq E hpub rho hv ▸ C).run.Run M.committee M.proposer M.digest M.honest
      M.trace := by
    rw [cast_local_run]
    have := hT.run hv
    rwa [ACRun.cast_run] at this
  have hcoh := hcoh hc
  obtain ⟨hsvc, hgst⟩ := hOS hv hc T b₀ b₁ hout
  obtain ⟨hpop, hcom⟩ := hOT.participation_local hOR hv hout
  obtain ⟨htimes, -⟩ := hout
  change 0 ≤ T ∧ T + (K.params.lag : Time) * E.ΔAC ≤ b₀ ∧ b₀ ≤ b₁ ∧
    b₁ ≤ b₀ + (K.params.budget : Time) * E.ΔAC at htimes
  obtain ⟨hT0, hlag, hb01, hbud⟩ := htimes
  have hΔ : 0 < E.ΔAC := by rw [← M.delta_eq]; exact P.hΔ
  have hcDur : 0 ≤ (Sys F V).cDur K ⟨E, rho⟩ := by
    change 0 ≤ (K.params.catchUp : Time) * E.ΔAC
    positivity
  have hcu : (B.signer_eq E hpub rho hv ▸ C).catchUp ≤ (Sys F V).cDur K ⟨E, rho⟩ := by
    linarith [hOR.catchUp]
  have hlag0 : (0 : Time) ≤ (K.params.lag : Time) * E.ΔAC := by positivity
  have hrec0 : (0 : Time) ≤ (K.params.recovery : Time) * E.ΔAC := by positivity
  have hmono : ∀ {y i t}, ReadyReadPoint M.trace M.honest rho.horizon
      ((Sys F V).cDur K ⟨E, rho⟩) y i t →
      ReadyReadPoint M.trace M.honest rho.horizon (B.signer_eq E hpub rho hv ▸ C).catchUp y i t :=
    fun hr => ⟨hr.1, fun u hu hut => hr.2 u ((max_le_max le_rfl (by linarith)).trans hu) hut⟩
  intro v hvT t ht₀ ht w hwt
  change b₁ + (K.params.recovery : Time) * E.ΔAC ≤ t at ht₀
  have hTt : T ≤ t := by linarith
  have hTh : T ≤ rho.horizon := hTt.trans ht
  have ht0 : 0 ≤ t := hT0.trans hTt
  obtain ⟨-, -, hpv, hbv⟩ := hSR.end_read hv _ hcDur v T hT0 hTh hvT
  obtain ⟨-, -, hpw, hbw⟩ := hSR.end_read hv _ hcDur w t ht0 ht hwt
  rw [end_read_output_eq hSR hv (hrep.confirmed_tip g hg) hcDur hT0 hTh hvT,
    end_read_output_eq hSR hv (hRT g hg) hcDur ht0 ht hwt]
  have hanc := hOP.protection _ _ _ _ _ (D E hpub rho hv).point E.ΔFG T b₀ b₁
    ((Sys F V).recoveryAt K b₁ ⟨E, rho⟩) hrun (hT.no_collision hv hc) (D E hpub rho hv).binding
    hT0 (by rw [hOR.lag]; exact hlag) hb01 (by rw [hOR.budget]; exact hbud)
    (by change b₁ ≤ b₁ + (K.params.recovery : Time) * E.ΔAC; linarith)
    (by rw [hOR.duration]; exact le_rfl) hsvc hgst hpop hcom
    _ _ _ _ _ (by rw [(D E hpub rho hv).horizon]; exact hmono hpv) hbv ht₀
    (by rw [(D E hpub rho hv).horizon]; exact hmono hpw) hbw
  have hi : (chainTrace rho).endCut T ≤ rho.events.length := Nat.findGreatest_le _
  have hj : (chainTrace rho).endCut t ≤ rho.events.length := Nat.findGreatest_le _
  have hhv : rho.point.HonestAt v (rho.cutTime ((chainTrace rho).endCut T)) := fun hf =>
    hvT.1 (rho.faultyAt_mono (cutTime_endCut_le rho hT0) hf)
  have hhw : rho.point.HonestAt w (rho.cutTime ((chainTrace rho).endCut t)) := fun hf =>
    hwt.1 (rho.faultyAt_mono (cutTime_endCut_le rho ht0) hf)
  have hsub : ∀ {y i u}, HonestReadPoint M.trace M.honest rho.horizon y i u →
      (M.trace.state y i).fg.tree ⊆ M.trace.HonestBlocksAt M.honest :=
    fun hr X hX => ⟨_, _, _, hr.2.2.1, hr.2.1.1, hr.1, hX⟩
  exact hrep.ancestor_prefix v w _ _ hi hj hhv hhw (hhr.reachable hv v _ hi hhv)
    (hhr.reachable hv w _ hj hhw) (hhr.roots hv v _ hi hhv) (hhr.roots hv w _ hj hhw) hcoh
    (hsub hpv.1) (hsub hpw.1) _ _ (hLR.held _ _ _ _ _ hrun _ _ _ _ hpv.1)
    (hLR.held _ _ _ _ _ hrun _ _ _ _ hpw.1) hanc

end PersistenceProof

section HealedSafetyProof

/-- Healed safety of a nonfinal output at fixed public parameters. A hash collision is the
claim's excuse, and without validators past the horizon no cut is from the heal point. Every
read at an engine cut is the chain of the reader's stored read tip (`stored_output_eq`), held in
its store (`LocalReadPoint.held` at the stored read point of `StoredReadTransport.ready_point`).
- Monotonicity: the same reader's tips are ancestors (`HealedReadAncestry`).
- Agreement: the selected reset and its opening (`ResetHealBudgetSupply`) with the premises
  (`PreparationPremisesSupply`), canonicality (`HighCanonicalSupply`) and the healing bound
  (`ACHealing.heal_after_reset`) give compatible tips at the opening's margin
  (`HealthyReadPoint.healed`): the stored reads are at `R.now ≥ cutTime − 1 ≥ heal − 1`.
Honest ancestry of two held tips is a chain prefix (`ReadRepresentation.ancestor_prefix`). -/
theorem healedSafetyReduction (C : ACCorrectLocal A sg)
    (B : EngineBinding (F := F) (V := V) pub payload sg C.run) (K : Contract ProgressReq)
    (R : ∀ E hE rho (hv : rho.ExecutionValid), StoredReadContext (B.map E hE rho hv)) :
    HealedSafetyReduction C B K R := by
  intro _ hβ hcf h cap g hcap hg idx gst r hv hpre
  obtain ⟨E, rho⟩ := r
  obtain ⟨hpub, hH, hprog⟩ := hpre
  by_cases hc : rho.HashCollision
  · exact Or.inr hc
  refine Or.inl ?_
  obtain ⟨-, heng, hfit, hprep, hhc, hbud, hHR, hLR, hSR, hanc, hrep, hhr, hcoh⟩ :=
    h E hpub rho hv
  set M := B.map E hpub rho hv
  set L : ACCorrectLocal A M.signer := B.signer_eq E hpub rho hv ▸ C
  have hT := B.run_transport E hpub rho hv
  have hrun : L.run.Run M.committee M.proposer M.digest M.honest M.trace := by
    rw [cast_local_run]
    have := hT.run hv
    rwa [ACRun.cast_run] at this
  have hcoh := hcoh hc
  set heal := (Sys F V).heal K cap idx gst ⟨E, rho⟩
  have hlaws := (Model.sysOf_laws O (compiled F) V).trace ⟨E, rho⟩ hv
  by_cases hb : heal ≤ rho.horizon
  swap
  · have hnone : ∀ k, ¬ (chainTrace rho).InCuts heal k := fun k hk =>
      hb (hk.2.trans (hlaws.cutTime_le_horizon k hk.1))
    exact ⟨fun _ _ i _ hi => (hnone i hi).elim, fun _ i _ hi => (hnone i hi).elim⟩
  have hΔ : 0 < E.ΔAC := by rw [← M.delta_eq]; exact P.hΔ
  have hheal0 : 0 ≤ heal := by
    change 0 ≤ max gst 0 + (K.params.heal cap idx : Time) * E.ΔAC
    have := le_max_right gst 0
    positivity
  set c := (Sys F V).cDur K ⟨E, rho⟩
  have hcu0 := L.durations.2.1
  have hcu := hfit.catchUp
  have hc0 : 0 ≤ c - 1 := by linarith
  have hgtip : ∀ st t, M.tip g st t = A.confirmed st.ac (Node.frame st) t := by
    rcases hcap with rfl | rfl
    · exact M.available_tip g hg
    · exact hrep.confirmed_tip g hg
  -- the stored read of a reader ready at an engine cut, and its tip held at the mapped cut
  have hread : ∀ v i, (chainTrace rho).InCuts heal i → rho.point.Ready c v (rho.cutTime i) →
      ReadyReadPoint M.trace M.honest rho.horizon (c - 1) (M.validator.symm v)
        ((R E hpub rho hv).cut v i) ((R E hpub rho hv).now v i) ∧
      ReadBoundary M.trace (M.validator.symm v) ((R E hpub rho hv).cut v i) ∧
      rho.cutTime i - 1 ≤ (R E hpub rho hv).now v i ∧
      (chainTrace rho).read g v i =
        (M.chain (M.trace.state (M.validator.symm v) (M.cut i)) ((R E hpub rho hv).tip v i)).map
          M.header ∧
      (R E hpub rho hv).tip v i ∈ (M.trace.state (M.validator.symm v) (M.cut i)).fg.tree := by
    intro v i hi hr
    obtain ⟨hp, hbd, hnow⟩ := hSR.ready_point hv (c - 1) hc0 v i hi.1 (by rwa [sub_add_cancel])
    have hheld := hLR.held _ _ _ _ _ hrun _ _ _ _ hp.1
    rw [← hSR.source_tip, hSR.source_state hv v i hi.1] at hheld
    refine ⟨hp, hbd, hnow, ?_, hheld⟩
    rw [stored_output_eq hSR hv hgtip hi.1 hr.1, hSR.source_state hv v i hi.1]
  have hsub : ∀ v i, i ≤ rho.events.length → rho.point.HonestAt v (rho.cutTime i) →
      (M.trace.state (M.validator.symm v) (M.cut i)).fg.tree ⊆ M.trace.HonestBlocksAt M.honest := by
    intro v i hi hh X hX
    obtain ⟨hy, hle, ht0, -⟩ := heng.honest hv v i hi hh
    exact ⟨_, _, _, ht0, hle.1, hy, hX⟩
  have hpre : ∀ u v i j, (chainTrace rho).InCuts heal i → (chainTrace rho).InCuts heal j →
      rho.point.HonestAt u (rho.cutTime i) → rho.point.HonestAt v (rho.cutTime j) →
      ∀ {X Y}, X ∈ (M.trace.state (M.validator.symm u) (M.cut i)).fg.tree →
      Y ∈ (M.trace.state (M.validator.symm v) (M.cut j)).fg.tree →
      Anc (M.trace.HonestBlocksAt M.honest) X Y →
      List.IsPrefix ((M.chain (M.trace.state (M.validator.symm u) (M.cut i)) X).map M.header)
        ((M.chain (M.trace.state (M.validator.symm v) (M.cut j)) Y).map M.header) :=
    fun u v i j hi hj hu hv' _ _ hX hY hXY =>
      hrep.ancestor_prefix u v i j hi.1 hj.1 hu hv' (hhr.reachable hv u i hi.1 hu)
        (hhr.reachable hv v j hj.1 hv') (hhr.roots hv u i hi.1 hu) (hhr.roots hv v j hj.1 hv')
        hcoh (hsub u i hi.1 hu) (hsub v j hj.1 hv') _ _ hX hY hXY
  refine ⟨fun u v i j hi hj hu hv' => ?_, fun v i j hi hij hj hvi hvj => ?_⟩
  · obtain ⟨hpu, hbu, hnu, hru, hmu⟩ := hread u i hi hu
    obtain ⟨hpv, hbv, hnv, hrv, hmv⟩ := hread v j hj hv'
    rw [hru, hrv]
    have hP := hprep hβ hv hc cap idx gst hcap hH hprog hb
    obtain ⟨a, ha, hab, -, -, s₁, z, k, X, hs₁, hgs₁, h6, hms₁, hX⟩ :=
      hbud hv hc cap idx gst hcap hH hprog hb
    have hcan := hhc hcf hv hc gst a hH hrun hP ha hab
    have hheal := L.healing.heal_after_reset hcf hrun hP ha hab hcan
    have hheal₁ : HealedFrom M.trace M.honest M.proposer s₁ rho.horizon :=
      fun s s' z z' k k' X X' hs => hheal s s' z z' k k' X X' (hs₁.trans hs)
    have hmono : ∀ {y i t}, ReadyReadPoint M.trace M.honest rho.horizon (c - 1) y i t →
        ReadyReadPoint M.trace M.honest rho.horizon L.catchUp y i t :=
      fun hr => ⟨hr.1, fun w hw hwt => hr.2 w ((max_le_max le_rfl (by linarith)).trans hw) hwt⟩
    have hg0 : max gst 0 ≤ P.slotTime s₁ := by
      change SA.gbar gst + 4 * P.Δ ≤ P.slotTime s₁ at hgs₁
      have := P.hΔ
      unfold SA.gbar at hgs₁
      linarith
    have hcomp := ((hHR.healed _ _ _ _ _ _ _ _ _ _ _ hcf hrun hP ha hab hs₁ hheal₁ hg0).1
      ⟨z, k, X, hX⟩ h6 hgs₁ _ _ _ _ _ _
      (by have := hi.2; change heal ≤ rho.cutTime i at this; linarith)
      (by have := hj.2; change heal ≤ rho.cutTime j at this; linarith)
      (hmono hpu) (hmono hpv) hbu hbv)
    rw [← hSR.source_tip, ← hSR.source_tip] at hcomp
    rcases hcomp with hXY | hXY
    · exact Or.inl (hpre u v i j hi hj hu.1 hv'.1 hmu hmv hXY)
    · exact Or.inr (hpre v u j i hj hi hv'.1 hu.1 hmv hmu hXY)
  · obtain ⟨-, -, -, hri, hmi⟩ := hread v i hi hvi
    obtain ⟨-, -, -, hrj, hmj⟩ := hread v j hj hvj
    rw [hri, hrj]
    exact hpre v v i j hi hj hvi.1 hvj.1 hmi hmj
      (hanc hv hc cap idx gst hcap hH hprog hheal0 hb v i j hi hij hj hvi hvj
        (hSR.now_bound hv v j hj.1 hvj.1))

end HealedSafetyProof

section HealthyLivenessProof

/-- Healthy liveness at fixed public parameters. A hash collision is the claim's excuse. For a
query `t` from the heal point with a ready reader at the deadline `D = t + latency·ΔAC`, the
proposal witness is released after `t` by a proposer ready then, as an honest engine proposal
(`ProposalProgressTransport.proposal`). Every reader ready at `D` reads, at the end cut of `D`
(`StoredReadTransport.end_read`), a chain whose tip has the proposal as an honest ancestor:
- nonfinal outputs: `ProposalWitnessRefinement.healthy` selects the proposal, and
  `HealthyReadPoint.proposal` (L7) includes it in the confirmed read, with the premises
  (`PreparationPremisesSupply`) and the reset and its opening (`ResetHealBudgetSupply`) on
  `[ready, heal]`;
- the final output: `FinalWindowSupply` selects the four-anchor window, and
  `FinalReadTransport` includes its first anchor in the finalized read, with the deadline
  premises (`DeadlinePremisesSupply`).
The ancestor is held in the reader's store (`mem_of_honest_anc_at_from`), so its header is in
the read (`ReadRepresentation.tip_in_chain` and `ancestor_prefix`). -/
theorem healthyLivenessReduction (C : ACCorrectLocal A sg)
    (B : EngineBinding (F := F) (V := V) pub payload sg C.run) (K : Contract ProgressReq)
    (R : ∀ E hE rho (hv : rho.ExecutionValid), StoredReadContext (B.map E hE rho hv)) :
    HealthyLivenessReduction C B K R := by
  intro _ hβ hcf h cap g hg idx gst r hv hpre
  obtain ⟨E, rho⟩ := r
  obtain ⟨hpub, hH, hprog⟩ := hpre
  by_cases hc : rho.HashCollision
  · exact Or.inr hc
  refine Or.inl ?_
  obtain ⟨-, hpp, hpw, hfit, hdp, hfw, hfr, hprep, hbud, hSR, hHR, hLR, hrep, hhr, hcoh⟩ :=
    h E hpub rho hv
  set M := B.map E hpub rho hv
  set L : ACCorrectLocal A M.signer := B.signer_eq E hpub rho hv ▸ C
  have hT := B.run_transport E hpub rho hv
  have hrun : L.run.Run M.committee M.proposer M.digest M.honest M.trace := by
    rw [cast_local_run]
    have := hT.run hv
    rwa [ACRun.cast_run] at this
  have hnc := hT.no_collision hv hc
  have hcoh := hcoh hc
  have hloc := L.run.run_local hrun
  set heal := (Sys F V).heal K cap idx gst ⟨E, rho⟩
  set c := (Sys F V).cDur K ⟨E, rho⟩
  have hΔ : 0 < E.ΔAC := by rw [← M.delta_eq]; exact P.hΔ
  have hcu0 := L.durations.2.1
  have hm0 := L.durations.2.2.1
  have hcu := hfit.catchUp
  have hc0 : 0 ≤ c := by linarith
  have hheal0 : 0 ≤ heal := by
    change 0 ≤ max gst 0 + (K.params.heal cap idx : Time) * E.ΔAC
    have := le_max_right gst 0
    positivity
  have hmono : ∀ {y i u}, ReadyReadPoint M.trace M.honest rho.horizon c y i u →
      ReadyReadPoint M.trace M.honest rho.horizon L.catchUp y i u :=
    fun hr => ⟨hr.1, fun w hw hwt => hr.2 w ((max_le_max le_rfl (by linarith)).trans hw) hwt⟩
  -- an honest ancestor of a held read tip is in the read
  have hincl : ∀ {w : V} {D : Time} {X Y : A.Blk}, 0 ≤ D → D ≤ rho.horizon →
      rho.point.Ready c w D →
      Y ∈ (M.trace.state (M.validator.symm w) (M.cut ((chainTrace rho).endCut D))).fg.tree →
      Anc (M.trace.HonestBlocksAt M.honest) X Y → X.root ≠ P.genesisRoot →
      M.header X ∈ (M.chain (M.trace.state (M.validator.symm w)
        (M.cut ((chainTrace rho).endCut D))) Y).map M.header := by
    intro w D X Y hD0 hDh hwr hY hXY hX
    obtain ⟨-, -, hp, -⟩ := hSR.end_read hv c hc0 w D hD0 hDh hwr
    have hi : (chainTrace rho).endCut D ≤ rho.events.length := Nat.findGreatest_le _
    have hh : rho.point.HonestAt w (rho.cutTime ((chainTrace rho).endCut D)) := fun hf =>
      hwr.1 (rho.faultyAt_mono (cutTime_endCut_le rho hD0) hf)
    have hXt := mem_of_honest_anc_at_from hloc hnc hp.1.2.2.1 hp.1.2.1.1 hp.1.1 hXY hY
    have hsub : (M.trace.state (M.validator.symm w) (M.cut ((chainTrace rho).endCut D))).fg.tree
        ⊆ M.trace.HonestBlocksAt M.honest :=
      fun Z hZ => ⟨_, _, _, hp.1.2.2.1, hp.1.2.1.1, hp.1.1, hZ⟩
    exact (hrep.ancestor_prefix w w _ _ hi hi hh hh (hhr.reachable hv w _ hi hh)
      (hhr.reachable hv w _ hi hh) (hhr.roots hv w _ hi hh) (hhr.roots hv w _ hi hh) hcoh
      hsub hsub _ _ hXt hY hXY).subset (hrep.tip_in_chain _ _ hXt hX)
  intro t ht htD hex
  set D := t + (K.params.latency cap idx : Time) * E.ΔAC
  have ht0 : 0 ≤ t := hheal0.trans ht
  have hD0 : 0 ≤ D := by positivity
  have htD' : t ≤ D := le_add_of_nonneg_right (by positivity)
  by_cases hfin : cap = .final
  · subst hfin
    obtain ⟨W, hroot, hready0, hhp3, -, hhealed, -, hacc, hanc, hheights⟩ :=
      hfw hv hc idx gst t hH hprog ht htD hex
    have hP := hdp hv hc idx gst t hH hprog ht htD hex
    have hy0 := (W.ready 0).1
    refine ⟨M.trace.time (W.cut 0), M.keyIndex (W.block 0).proposer, M.header (W.block 0),
      W.fresh, by rw [M.key_eq]; exact hready0,
      hpp.proposal _ _ (W.proposals 0) hy0, fun w hwr => ?_⟩
    obtain ⟨-, hlt, hp, hbd⟩ := hSR.end_read hv c hc0 w D hD0 htD hwr
    have hi : (chainTrace rho).endCut D ≤ rho.events.length := Nat.findGreatest_le _
    have hh : rho.point.HonestAt w (rho.cutTime ((chainTrace rho).endCut D)) := fun hf =>
      hwr.1 (rho.faultyAt_mono (cutTime_endCut_le rho hD0) hf)
    have hwr' : rho.point.Ready c (M.validator (M.validator.symm w)) D := by
      rw [Equiv.apply_symm_apply]; exact hwr
    have hpr := hfr.processed hv hc idx gst t D W hH hprog ht rfl htD hhp3 _ _ hwr'
      (hmono hp) hbd hlt
    have hF := hfr.cache _ gst t D W hcf hrun hP hhealed hacc hanc hheights _ _ D le_rfl
      (hmono hp) hbd (hfit.final_faults D hD0 htD (hP.faults D hD0 le_rfl)) hpr
    have hFt : (M.trace.state (M.validator.symm w)
        (M.cut ((chainTrace rho).endCut D))).fg.F ∈ (M.trace.state (M.validator.symm w)
        (M.cut ((chainTrace rho).endCut D))).fg.tree :=
      (Store.cache_invariants _ _ _ _ (hhr.reachable hv w _ hi hh)).1
    change M.header (W.block 0) ∈ (chainTrace rho).read g w ((chainTrace rho).endCut D)
    change M.header (W.block 0) ∈
      (F (Model.pubOf E)).out g (rho.stateBefore ((chainTrace rho).endCut D) w).st.1
    rw [M.output_eq g w _ hi, M.state_eq w _ hi hh, hrep.finalized_tip g hg]
    exact hincl hD0 htD hwr hFt hF hroot
  have hcap : cap = .available ∨ cap = .stable := by
    cases cap
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hfin
  have hheal : heal ≤ rho.horizon := ht.trans (htD'.trans htD)
  have hprog' := (shapeProgress F V).mono le_rfl hheal hprog
  have hP := hprep hβ hv hc _ idx gst hcap hH hprog' hheal
  obtain ⟨a, ha, hab, -, hdrain, s₁, -, -, -, -, hgs₁, -, hms₁, -⟩ :=
    hbud hv hc _ idx gst hcap hH hprog' hheal
  obtain ⟨X, k, htk, hXr, hkm, hroot, hk0, hkh, hkr⟩ :=
    hpw.healthy hv hc _ idx gst t hcap hH hprog ht htD hex
  have hgtip : ∀ st u, M.tip g st u = A.confirmed st.ac (Node.frame st) u := by
    rcases hcap with rfl | rfl
    · exact M.available_tip g hg
    · exact hrep.confirmed_tip g hg
  have hslot : M.trace.time k = P.slotTime X.slot := hXr.1.2.2
  have hdX : P.slotOf a + L.healing.drain ≤ X.slot := by
    by_contra hlt
    have := P.slotTime_strictMono.monotone (not_le.1 hlt).le
    linarith
  refine ⟨M.trace.time k, M.keyIndex X.proposer, M.header X, htk,
    by rw [M.key_eq]; exact hkr, hpp.proposal _ _ hXr.1 hXr.2.1.1, fun w hwr => ?_⟩
  obtain ⟨-, hlt, hp, hbd⟩ := hSR.end_read hv c hc0 w D hD0 htD hwr
  have hanc := hHR.proposal _ _ _ _ _ _ _ _ _ _ heal hcf hrun hP ha hab
    (hfit.healthy_start _ idx gst hcap) X k _ _ D hXr hdX
    (by change SA.gbar gst + 4 * P.Δ ≤ P.slotTime s₁ at hgs₁; linarith) hk0
    (by linarith [hkh, L.durations.2.2.2.2]) hkh (by linarith)
    (by linarith [hfit.latency_le_margin]) (hmono hp) hbd hlt
  have hCt := hLR.held _ _ _ _ _ hrun _ _ _ _ hp.1
  rw [end_read_output_eq hSR hv hgtip hc0 hD0 htD hwr]
  exact hincl hD0 htD hwr hCt hanc hroot

end HealthyLivenessProof

section SleepyReductions

variable {E : Env V} {rho : Model.Run (compiled F) E}

private theorem local_cast_run {sg' : A.Msg → Fin P.n} (h : sg = sg')
    (C : ACCorrectLocal A sg) : (h ▸ C).run.Run = (h ▸ C.run).Run := by
  cases h
  rfl

private theorem sleepy_windows {M : RunMap rho payload} {K : Contract ProgressReq}
    {C : ACCorrectLocal A M.signer} (hw : SleepyWindowSupply M K C)
    (hf : ClaimDeadlineFit M K C) (hv : rho.ExecutionValid)
    (hs : (Sys F V).Sleepy (shapeProgress F V).toExternal K ⟨E, rho⟩) :
    ∃ p, RunPointBinding M.trace M.honest p ∧
      SleepyLayer1.CommitteeWindow C p M.committee rho.horizon ∧
      SleepyLayer1.PopulationWindow C p rho.horizon := by
  obtain ⟨p, hp, hb, hθ, h0, h1, hl, hcl, hw⟩ := hw
  obtain ⟨hpop, hK⟩ := hw hv hs
  have hc : C.catchUp ≤ (Sys F V).cDur K ⟨E, rho⟩ :=
    (le_add_of_nonneg_right zero_le_one).trans hf.catchUp
  exact ⟨p, hp,
    SleepyLayer1.committee_transport M C p rho.horizon _ _ hb.ge hc rfl h0 h1 hK,
    SleepyLayer1.population_transport M C p rho.horizon _ _ hb.ge hc rfl h0 h1 hpop⟩

private theorem sleepy_frames {M : RunMap rho payload} {K : Contract ProgressReq}
    {C : ACCorrectLocal A M.signer} {D : SleepyLayer1.Data A}
    (hsource : SleepyLayer1.SourceProvenance C D)
    (hq : PopulationQuorumSupply M K) (hv : rho.ExecutionValid)
    (hs : (Sys F V).Sleepy (shapeProgress F V).toExternal K ⟨E, rho⟩)
    (hrun : C.run.Run M.committee M.proposer M.digest M.honest M.trace)
    (hnc : Compose.NoCollRun M.digest M.trace) :
    SleepyLayer1.AnchoredFrames D M.trace M.honest rho.horizon := by
  exact SleepyLayer1.frames_from_sources C D
    (SleepyLayer1.cache_provenance C D) (SleepyLayer1.row_provenance C D)
    (SleepyLayer1.conditional_viability C D) hsource _ _ _ _ _ _ hrun hnc
    (fun _ _ t hr => hq hv hs t hr.2.2.1 hr.2.2.2)

/-- Bounded explicit-read sleepy safety, preserving the original collision excuse. -/
theorem sleepy_safety_reduction (C : ACCorrectLocal A sg)
    (B : EngineBinding (F := F) (V := V) pub payload sg C.run) (K : Contract ProgressReq)
    (D : SleepyLayer1.Data A)
    (R : ∀ E hE rho (hv : rho.ExecutionValid), StoredReadContext (B.map E hE rho hv)) :
    SleepySafetyReduction C B K D R := by
  intro supply cap g hcap hg r hv ⟨hpub, hs⟩
  by_cases hcollision : r.2.HashCollision
  · exact Or.inr hcollision
  left
  let M := B.map r.1 hpub r.2 hv
  let L : ACCorrectLocal A M.signer := B.signer_eq r.1 hpub r.2 hv ▸ C
  obtain ⟨hreg, _, hstored, hlocal, hevents, houtputs, hext, hsource,
    hquorum, hwindow, hfit, hrep, hread, hcoh⟩ := supply r.1 hpub r.2 hv
  have hrun : L.run.Run M.committee M.proposer M.digest M.honest M.trace := by
    rw [local_cast_run]
    exact (B.run_transport r.1 hpub r.2 hv).run hv
  have hnc := (B.run_transport r.1 hpub r.2 hv).no_collision hv hcollision
  obtain ⟨p, hp, hK, hpop⟩ := sleepy_windows hwindow hfit hv hs
  have hframes := sleepy_frames hsource hquorum hv hs hrun hnc
  have hsafe := SleepyLayer1.ready_read_safety M L D
    (SleepyLayer1.read_agreement M L D) hevents houtputs hext
    r.1.ΔFG r.2.horizon p le_rfl hrun hnc hp (hreg.sleepy hv hcollision hs)
    hK hpop hframes
  have htip : ∀ st t, M.tip g st t = A.confirmed st.ac (Node.frame st) t := by
    rcases hcap with rfl | rfl
    · exact M.available_tip g hg
    · exact hrep.confirmed_tip g hg
  have ready {v i} (hi : i ≤ r.2.events.length)
      (hr : r.2.point.Ready ((Sys F V).cDur K r) v (r.2.cutTime i)) :
      ReadyReadPoint M.trace M.honest r.2.horizon L.catchUp
        (M.validator.symm v) ((R r.1 hpub r.2 hv).cut v i)
        ((R r.1 hpub r.2 hv).now v i) ∧
      ReadBoundary M.trace (M.validator.symm v) ((R r.1 hpub r.2 hv).cut v i) ∧
      r.2.cutTime i - 1 ≤ (R r.1 hpub r.2 hv).now v i := by
    apply hstored.ready_point hv L.catchUp L.durations.2.1 v i hi
    refine ⟨hr.1, fun u hu hut => hr.2 u ?_ hut⟩
    apply le_trans (max_le_max_left 0 ?_) hu
    have hc := hfit.catchUp
    change L.catchUp + 1 ≤ (Sys F V).cDur K r at hc
    linarith
  have chainPrefix {u v i j} (hi : i ≤ r.2.events.length) (hj : j ≤ r.2.events.length)
      (hu : r.2.point.Ready ((Sys F V).cDur K r) u (r.2.cutTime i))
      (hv' : r.2.point.Ready ((Sys F V).cDur K r) v (r.2.cutTime j))
      (ha : Anc (M.trace.HonestBlocksAt M.honest)
        ((R r.1 hpub r.2 hv).tip u i) ((R r.1 hpub r.2 hv).tip v j)) :
      (chainTrace r.2).read g u i <+: (chainTrace r.2).read g v j := by
    obtain ⟨hui, hub, _⟩ := ready hi hu
    obtain ⟨hvj, hvb, _⟩ := ready hj hv'
    have heldU := hlocal.held _ _ _ _ _ hrun _ _ _ _ hui.1
    have heldV := hlocal.held _ _ _ _ _ hrun _ _ _ _ hvj.1
    rw [← hstored.source_tip] at heldU heldV
    rw [hstored.source_state hv u i hi] at heldU
    rw [hstored.source_state hv v j hj] at heldV
    rw [stored_output_eq hstored hv htip hi hu.1,
      stored_output_eq hstored hv htip hj hv'.1,
      hstored.source_state hv u i hi, hstored.source_state hv v j hj]
    exact hrep.ancestor_prefix u v i j hi hj hu.1 hv'.1
      (hread.reachable hv u i hi hu.1) (hread.reachable hv v j hj hv'.1)
      (hread.roots hv u i hi hu.1) (hread.roots hv v j hj hv'.1) (hcoh hcollision)
      (fun X hX => ⟨_, _, _, hui.1.2.2.1, hui.1.2.1.1, hui.1.1,
        (hstored.source_state hv u i hi).symm ▸ hX⟩)
      (fun X hX => ⟨_, _, _, hvj.1.2.2.1, hvj.1.2.1.1, hvj.1.1,
        (hstored.source_state hv v j hj).symm ▸ hX⟩)
      _ _ heldU heldV ha
  constructor
  · intro u v i j hi hj hu hv'
    obtain ⟨hui, hub, _⟩ := ready hi.1 hu
    obtain ⟨hvj, hvb, _⟩ := ready hj.1 hv'
    have ha := hsafe.1 _ _ _ _ _ _ hui hvj hub hvb
    rw [← hstored.source_tip, ← hstored.source_tip] at ha
    exact ha.elim (fun h => Or.inl (chainPrefix hi.1 hj.1 hu hv' h))
      (fun h => Or.inr (chainPrefix hj.1 hi.1 hv' hu h))
  · intro v i j hi hij hj hvi hvj
    obtain ⟨hri, hbi, _⟩ := ready hi.1 hvi
    obtain ⟨hrj, hbj, _⟩ := ready hj.1 hvj
    have ha := hsafe.2 _ _ _ _ _ hri hrj hbi hbj
      (hstored.cut_mono v hij) (hstored.now_mono hv v hij)
    rw [← hstored.source_tip, ← hstored.source_tip] at ha
    exact chainPrefix hi.1 hj.1 hvi hvj ha

private theorem ancestor_held {st : Store P A.Payload} {U : Set A.Blk}
    (hr : st.Reachable A.genesisPayload) (hU : Coherent U) (hsub : st.tree ⊆ U)
    {X Y : A.Blk} (ha : Anc U X Y) (hy : Y ∈ st.tree) : X ∈ st.tree := by
  by_cases he : X = Y
  · exact he ▸ hy
  · exact (Anc.mem (Store.anc_of_anc_universe hr hU hsub ha hy) he).1

/-- Reader-conditional proposal liveness from the jointly admissible witness. -/
theorem sleepy_liveness_reduction (C : ACCorrectLocal A sg)
    (B : EngineBinding (F := F) (V := V) pub payload sg C.run) (K : Contract ProgressReq)
    (D : SleepyLayer1.Data A)
    (R : ∀ E hE rho (hv : rho.ExecutionValid), StoredReadContext (B.map E hE rho hv)) :
    SleepyLivenessReduction C B K D R := by
  intro supply cap g hcap hg idx r hv ⟨hpub, hs, hprog⟩
  by_cases hcollision : r.2.HashCollision
  · exact Or.inr hcollision
  left
  let M := B.map r.1 hpub r.2 hv
  let L : ACCorrectLocal A M.signer := B.signer_eq r.1 hpub r.2 hv ▸ C
  obtain ⟨hreg, hprogress, hwitness, hfit, hstored, hcoverage, hlocal,
    _, _, _, hsource, hquorum, hwindow, hrep, hread, hcoh⟩ := supply r.1 hpub r.2 hv
  have hrun : L.run.Run M.committee M.proposer M.digest M.honest M.trace := by
    rw [local_cast_run]
    exact (B.run_transport r.1 hpub r.2 hv).run hv
  have hnc := (B.run_transport r.1 hpub r.2 hv).no_collision hv hcollision
  obtain ⟨p, hp, hK, hpop⟩ := sleepy_windows hwindow hfit hv hs
  have hframes := sleepy_frames hsource hquorum hv hs hrun hnc
  have htip : ∀ st t, M.tip g st t = A.confirmed st.ac (Node.frame st) t := by
    rcases hcap with rfl | rfl
    · exact M.available_tip g hg
    · exact hrep.confirmed_tip g hg
  intro t ht hb hr
  obtain ⟨X, k, htk, hP, hmargin, hnonroot, hk, hhold, hready⟩ :=
    hwitness.sleepy hv hcollision cap idx t hcap hs hprog ht hb hr
  refine ⟨M.trace.time k, M.keyIndex X.proposer, M.header X, htk, ?_,
    hprogress.proposal X k hP.1 hP.2.1.1, ?_⟩
  · rw [M.key_eq]
    exact hready
  · intro v hvready
    let d := t + (K.params.latency cap idx : Time) * r.1.ΔAC
    have hd : 0 ≤ d := ht.trans (le_add_of_nonneg_right
      (mul_nonneg (Nat.cast_nonneg _) (by have := r.1.ΔAC_pos; linarith)))
    have hvlocal : r.2.point.Ready L.catchUp v d := by
      refine ⟨hvready.1, fun u hu hut => hvready.2 u ?_ hut⟩
      apply le_trans (max_le_max_left 0 ?_) hu
      have hc := hfit.catchUp
      change L.catchUp + 1 ≤ (Sys F V).cDur K r at hc
      linarith
    obtain ⟨_, hstrict, hreader, hboundary⟩ :=
      hstored.end_read hv L.catchUp L.durations.2.1 v d hd hb hvlocal
    have hkb : M.trace.time k ≤ r.2.horizon :=
      (le_add_of_nonneg_right L.durations.2.2.2.2).trans hhold
    have hanc := hcoverage r.1.ΔFG r.2.horizon p le_rfl hrun hnc hp
      (hreg.sleepy hv hcollision hs) hK hpop hframes X k _ _ d
      hP hk hhold hkb hmargin hreader hboundary hstrict
    have hheld := hlocal.held _ _ _ _ _ hrun _ _ _ _ hreader.1
    have hsub : (M.trace.state (M.validator.symm v)
        (M.cut ((chainTrace r.2).endCut d))).fg.tree ⊆ M.trace.HonestBlocksAt M.honest :=
      fun Y hY => ⟨_, _, _, hreader.1.2.2.1, hreader.1.2.1.1, hreader.1.1, hY⟩
    have hi : (chainTrace r.2).endCut d ≤ r.2.events.length := Nat.findGreatest_le _
    have hhonest : r.2.point.HonestAt v (r.2.cutTime ((chainTrace r.2).endCut d)) :=
      fun hf => hvready.1 (r.2.faultyAt_mono (cutTime_endCut_le r.2 hd) hf)
    rw [end_read_output_eq hstored hv htip L.durations.2.1 hd hb hvlocal]
    have hX := ancestor_held (hread.reachable hv v _ hi hhonest)
      (hcoh hcollision) hsub hanc hheld
    have hchain := (hrep.ancestor_prefix v v _ _ hi hi hhonest hhonest
      (hread.reachable hv v _ hi hhonest) (hread.reachable hv v _ hi hhonest)
      (hread.roots hv v _ hi hhonest) (hread.roots hv v _ hi hhonest)
      (hcoh hcollision) hsub hsub X _
      hX hheld hanc)
    exact hchain.subset (hrep.tip_in_chain _ X hX hnonroot)

end SleepyReductions

section Capstone

/-- **The capstone assembly** (`meetsObligations_of_local`). Every claim at a positive population
reduces, at the run's public parameters, to the reduction proved above at the binding's map of
each valid run, whose suppliers are fields of `LocalClaimSuppliers`
(`holds_of_forall_public`, `holdsAlways_of_forall_public`). Without validators every claim is
vacuous (`shapeClaimsAt_of_isEmpty`). The four non-claim obligations are the inputs themselves. -/
theorem meetsObligations_of_local_proof {O : OutputSchema} {Info : Type} [DecidableEq Info]
    [Countable Info]
    (F : ChainShapeFamily O Info) (K : Contract ProgressReq) :
    meetsObligations_of_local F K := by
  rw [meetsObligations_of_local_iff]
  intro P A sg C events B D R hL hadm hserv hfit htol hβ hcf
  refine ⟨fun V _ _ => ?_, hadm, hserv, hfit, htol⟩
  have hE := shapeClaimsAt_of_isEmpty F K V
  refine
    { outputValid := holdsAlways_of_forall_public (fun pub hn =>
        outputValidAlways (B V ⟨pub, hn⟩) fun E hE rho hv =>
          let L := hL V ⟨pub, hn⟩ E hE rho hv
          ⟨L.outputValidity, L.reads, L.honestReads⟩) fun h => (hE h).outputValid
      nested := fun c₁ c₂ g₁ g₂ hc h₁ h₂ => holdsAlways_of_forall_public (fun pub hn =>
        (nestedChainsAlways_iff _).1 (nestedChainsAlways (B V ⟨pub, hn⟩)) (fun E hE rho hv =>
          let L := hL V ⟨pub, hn⟩ E hE rho hv
          ⟨L.chains, L.honestChains⟩) c₁ c₂ g₁ g₂ hc h₁ h₂)
        fun h => (hE h).nested c₁ c₂ g₁ g₂ hc h₁ h₂
      finalMonotone := fun g hg => holdsAlways_of_forall_public (fun pub hn =>
        (finalChainsAlways_iff _).1 (finalChainsAlways (B V ⟨pub, hn⟩)) (fun E hE rho hv =>
          let L := hL V ⟨pub, hn⟩ E hE rho hv
          ⟨L.chains, L.honestChains⟩) g hg) fun h => (hE h).finalMonotone g hg
      finalAccountable := fun g hg => holds_of_forall_public (fun pub hn =>
        finalAccountabilityReduction (C ⟨pub, hn⟩) (B V ⟨pub, hn⟩) K (fun E hE rho hv =>
          let L := hL V ⟨pub, hn⟩ E hE rho hv
          ⟨L.engineRead, L.accountability, L.deadlines, L.reads, L.honestReads,
            L.honestChains, L.coherent⟩) g hg) fun h => (hE h).finalAccountable g hg
      healthyLive := fun cap g hg idx gst => holds_of_forall_public (fun pub hn =>
        healthyLivenessReduction (C ⟨pub, hn⟩) (B V ⟨pub, hn⟩) K (R V ⟨pub, hn⟩) hadm hβ hcf
          (fun E hE rho hv =>
          let L := hL V ⟨pub, hn⟩ E hE rho hv
          ⟨L.regime, L.progress, L.proposalWitness, L.deadlines, L.deadlinePremises,
            L.finalWindow, L.finalReads, L.preparation, L.resetBudget,
            L.storedRead, L.healthyRead, L.localRead, L.reads,
            L.honestReads, L.coherent⟩) cap g hg idx gst)
        fun h => (hE h).healthyLive cap g hg idx gst
      sleepySafe := fun cap g hcap hg => holds_of_forall_public (fun pub hn =>
        sleepy_safety_reduction (C ⟨pub, hn⟩) (B V ⟨pub, hn⟩) K (events ⟨pub, hn⟩) (R V ⟨pub, hn⟩)
          (fun E hE rho hv =>
          let L := hL V ⟨pub, hn⟩ E hE rho hv
          ⟨L.regime, L.engineRead, L.storedRead, L.localRead, L.eventSafety,
            L.outputProvenance, L.extension, L.sourceProvenance, L.populationQuorum,
            L.sleepyWindows, L.deadlines, L.reads, L.honestReads, L.coherent⟩) cap g hcap hg)
        fun h => (hE h).sleepySafe cap g hcap hg
      sleepyLive := fun cap g hcap hg idx => holds_of_forall_public (fun pub hn =>
        sleepy_liveness_reduction (C ⟨pub, hn⟩) (B V ⟨pub, hn⟩) K (events ⟨pub, hn⟩) (R V ⟨pub, hn⟩)
          (fun E hE rho hv =>
          let L := hL V ⟨pub, hn⟩ E hE rho hv
          ⟨L.regime, L.progress, L.proposalWitness, L.deadlines, L.storedRead,
            L.sleepyProposal, L.localRead, L.eventSafety, L.outputProvenance, L.extension,
            L.sourceProvenance, L.populationQuorum, L.sleepyWindows, L.reads, L.honestReads,
            L.coherent⟩) cap g hcap hg idx)
        fun h => (hE h).sleepyLive cap g hcap hg idx
      healedSafe := fun cap g hcap hg idx gst => holds_of_forall_public (fun pub hn =>
        healedSafetyReduction (C ⟨pub, hn⟩) (B V ⟨pub, hn⟩) K (R V ⟨pub, hn⟩) hadm hβ hcf
          (fun E hE rho hv =>
          let L := hL V ⟨pub, hn⟩ E hE rho hv
          ⟨L.regime, L.engineRead, L.deadlines, L.preparation,
            L.highCanonical, L.resetBudget, L.healthyRead, L.localRead, L.storedRead,
            L.healedAncestry, L.reads, L.honestReads, L.coherent⟩) cap g hcap hg idx gst)
        fun h => (hE h).healedSafe cap g hcap hg idx gst
      persists := fun g hg T b₀ b₁ => holds_of_forall_public (fun pub hn =>
        persistenceReduction (C ⟨pub, hn⟩) (B V ⟨pub, hn⟩) K (D V ⟨pub, hn⟩) (R V ⟨pub, hn⟩)
          (fun E hE rho hv =>
          let L := hL V ⟨pub, hn⟩ E hE rho hv
          ⟨L.outage, L.recovery, L.outageService, L.resilience, L.outageRead, L.storedRead,
            L.localRead, L.reads, L.honestReads, L.coherent⟩) g hg T b₀ b₁)
        fun h => (hE h).persists g hg T b₀ b₁ }


end Capstone

end Consensus.Goldilocks.Generic

end
