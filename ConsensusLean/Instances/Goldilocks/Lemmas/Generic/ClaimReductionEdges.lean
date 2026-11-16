module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ClaimTransports
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.EngineEdges
public import ConsensusLean.Instances.Goldilocks.Lemmas.Generic.ChainRepresentationEdges

public section

/-! # Conditional claim reduction rows

Intended theorem types; output validity and final accountability are proved (section
"Output-validity and accountability proofs"), the regime reductions remain UNPROVED. No
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
No constant FrameWindow production or progress-form exclusion is assumed. -/
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
      FinalReadTransport M K L ∧
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

/-- UNPROVED outage reduction with the original source/destination, recovery time
and collision alternative. The fixed local policy matches the contract by equality;
recipient-deadline service permits AC-owned retained evidence. OC-K and the instance
transports remain obligations, not consequences of these numerical fits. -/
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

/-- UNPROVED healed-safety reduction. Reset, canonicality and the selected drain
budget are independent inputs to healing. Same-reader ancestry uses its own actual
stored-read context and transport; representation still supplies the chain-prefix step. -/
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

end Consensus.Goldilocks.Generic

end
