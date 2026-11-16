module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ClaimTransports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.EngineEdges
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.ChainRepresentationEdges
import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.OutageSupply
import ConsensusLean.Lemmas.Tactic.Linarith
import ConsensusLean.Lemmas.Model.Laws

public section

/-! # Conditional claim reduction rows

Intended theorem types; output validity, final accountability (section "Output-validity and
accountability proofs"), persistence (section "Persistence proof") and healed safety (section
"Healed safety proof") are proved, the other regime reductions remain UNPROVED. No
evidence, instance, admission or correctness claim is supplied. All suppliers below refer to
the binding's same map. Every regime reduction reads outputs through the one stored-read
context and its transport: engine-cut reads at the stored read, claim-time reads at `endCut t`.
Healed safety's same-reader ancestry is never inferred from compatibility.
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

/-- UNPROVED bounded explicit-read sleepy safety reduction. Coherent union and
root suppliers remain explicit; none enters an unconditional claim. Source:
Concrete/Fields.meetsObligations_sleepySafe_growing. -/
def SleepySafetyReduction (C : ACCorrectLocal A sg)
    (B : EngineBinding (F := F) (V := V) pub payload sg C.run) (K : Contract ProgressReq)
    (D : SleepyLayer1.Data A)
    (R : ∀ E hE rho (hv : rho.ExecutionValid), StoredReadContext (B.map E hE rho hv)) : Prop :=
  (∀ E hE rho (hv : rho.ExecutionValid),
    let M := B.map E hE rho hv
    let L : ACCorrectLocal A M.signer := B.signer_eq E hE rho hv ▸ C
    RegimeTransport M K L.look ∧ EngineReadPoint M ∧ StoredReadTransport M (R E hE rho hv) ∧
      LocalReadPoint L ∧ SleepyLayer1.EventSafety M L D ∧ SleepyLayer1.OutputProvenance L D ∧
      SleepyLayer1.Extension M L D ∧ SleepyLayer1.SourceProvenance L D ∧
      PopulationQuorumSupply M K ∧ SleepyWindowSupply M K L ∧ ClaimDeadlineFit M K L ∧
      ReadRepresentation M ∧ HonestReadTransport M ∧
      (¬ rho.HashCollision → Coherent (M.trace.HonestBlocksAt M.honest))) →
    ∀ cap g, (cap = .available ∨ cap = .stable) → O.output cap = some g →
      (Sys F V).Holds (fun r => Model.pubOf r.1 = pub ∧
        (Sys F V).Sleepy (shapeProgress F V).toExternal K r) fun r =>
        (chainTrace r.2).ReadySafe ((Sys F V).cDur K r) g 0

/-- UNPROVED sleepy proposal reduction, keeping the original progress interval,
reader-conditional deadline and hash-collision branch. The strengthened witness
supplier selects advertised readiness jointly with the proposal. -/
def SleepyLivenessReduction (C : ACCorrectLocal A sg)
    (B : EngineBinding (F := F) (V := V) pub payload sg C.run) (K : Contract ProgressReq)
    (D : SleepyLayer1.Data A)
    (R : ∀ E hE rho (hv : rho.ExecutionValid), StoredReadContext (B.map E hE rho hv)) : Prop :=
  (∀ E hE rho (hv : rho.ExecutionValid),
    let M := B.map E hE rho hv
    let L : ACCorrectLocal A M.signer := B.signer_eq E hE rho hv ▸ C
    RegimeTransport M K L.look ∧
      ProposalProgressTransport M K L.healing ∧
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

/-- UNPROVED all-capability healthy liveness reduction. Actual final deadline premises,
processing and actual-read cache transport are separate supplier contracts. FinalWindowSupply
jointly selects advertised anchor readiness, delivery spacing and pointwise heights.
No constant FrameWindow production or progress-form exclusion is assumed. The nonfinal
inclusion reads at L7 (`HealthyReadPoint.proposal`), whose premises and selected reset come from
the healthy preparation (`PreparationPremisesSupply`) and reset budget (`ResetHealBudgetSupply`)
suppliers. -/
def HealthyLivenessReduction (C : ACCorrectLocal A sg)
    (B : EngineBinding (F := F) (V := V) pub payload sg C.run) (K : Contract ProgressReq)
    (R : ∀ E hE rho (hv : rho.ExecutionValid), StoredReadContext (B.map E hE rho hv)) : Prop :=
  K.params.Admissible → HealthyBetaFit K → CommitteeHalfFit K →
  (∀ E hE rho (hv : rho.ExecutionValid),
    let M := B.map E hE rho hv
    let L : ACCorrectLocal A M.signer := B.signer_eq E hE rho hv ▸ C
    RegimeTransport M K L.look ∧
      ProposalProgressTransport M K L.healing ∧
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
    RegimeTransport M K L.look ∧ EngineReadPoint M ∧
      ClaimDeadlineFit M K L ∧ PreparationPremisesSupply M K ∧
      ResetProgressSupply M K L.healing ∧
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
  obtain ⟨-, heng, hfit, hprep, -, hhc, hbud, hHR, hLR, hSR, hanc, hrep, hhr, hcoh⟩ :=
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

end Consensus.Goldilocks.Generic

end
