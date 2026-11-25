module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ClaimTransports

public section

/-! # The local supplier's `fgHold` binder changes no reader at `fgHold = 0`

The readers of `ACCorrectLocal` in `Statements/Generic` (ReadPoint, EngineTransport, SleepyLayer1,
ClaimTransports, CorrectLocal) take the supplier at any release hold `fgHold`. For each, the
reader's form over a supplier without a hold is copied verbatim as `<Name>Old`, and
`<name>_iff_old` shows that the generalized reader at `fgHold = 0` is that form. -/

namespace Consensus.Goldilocks.Generic

variable {P : Params}

/-- `ACServiceBefore` over a supplier without a release hold. -/
structure ACServiceBeforeOld {A : NodeAC P} {sg : A.Msg → Fin P.n}
    (C : ACCorrectLocal A sg) (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (ΔF b : Time) : Prop where
  deltaF : 0 < ΔF
  message : ∀ x i m, x ∈ H (tr.time i) → tr.SendOrAdmitAt x i m → 0 ≤ tr.time i →
    ∀ y j ℓ, y ∈ H (tr.time j) → tr.CallAt y j (.ac ℓ) →
      tr.deadline y j (tr.time i) P.Δ ≤ b →
      tr.deadline y j (tr.time i) P.Δ ≤ tr.time j → C.served tr y j (tr.time i) m
  relay : ∀ x i B, x ∈ H (tr.time i) → tr.AcceptAt x i B → 0 ≤ tr.time i →
    ∀ y j, y ∈ H (tr.time j) → tr.IsCall y j → tr.deadline y j (tr.time i) P.Δ ≤ b →
      tr.deadline y j (tr.time i) P.Δ ≤ tr.time j →
      Anc (tr.HonestBlocksAt H) (tr.state y j).fg.F B → tr.BlockAcceptedBy y j (tr.time i) B

/-- At `fgHold = 0`, `ACServiceBefore` is its form without a release hold. -/
theorem acServiceBefore_iff_old
    {A : NodeAC P} {sg : A.Msg → Fin P.n} (C : ACCorrectLocal A sg) (tr : RunTrace A)
    (H : Time → Set (Fin P.n)) (ΔF b : Time) :
    ACServiceBefore (fgHold := 0) C tr H ΔF b ↔ ACServiceBeforeOld C tr H ΔF b :=
  ⟨fun h => by cases h; constructor <;> assumption,
    fun h => by cases h; constructor <;> assumption⟩

/-- `SleepyServicePrefix` over a supplier without a release hold. -/
def SleepyServicePrefixOld {A : NodeAC P} {sg : A.Msg → Fin P.n} (C : ACCorrectLocal A sg)
    (tr : RunTrace A) (H : Time → Set (Fin P.n)) (ΔF look b : Time) : Prop :=
  0 ≤ b ∧ ACServiceBefore C tr H ΔF b ∧
    ∀ s : Nat, ∀ d ∈ ({0, P.Δ, 2 * P.Δ} : Set Time), P.slotTime s + d ≤ b →
      tr.FaultBoundAt H (P.slotTime s + d) (min (P.slotTime s + d + look) b)

/-- At `fgHold = 0`, `SleepyServicePrefix` is its form without a release hold. -/
theorem sleepyServicePrefix_iff_old
    {A : NodeAC P} {sg : A.Msg → Fin P.n} (C : ACCorrectLocal A sg) (tr : RunTrace A)
    (H : Time → Set (Fin P.n)) (ΔF look b : Time) :
    SleepyServicePrefix (fgHold := 0) C tr H ΔF look b ↔ SleepyServicePrefixOld C tr H ΔF look b :=
  Iff.rfl

end Consensus.Goldilocks.Generic

namespace Consensus.Goldilocks.Generic

open AC (gbar)

open Healing.Growing (IsReset)

variable {P : Params} {A : NodeAC P}

/-- `LocalReadPoint` over a supplier without a release hold. -/
structure LocalReadPointOld {sg : A.Msg → Fin P.n} (C : ACCorrectLocal A sg) : Prop where
  tips : ∀ cm proposer dg H (tr : RunTrace A),
    C.run.Run cm proposer dg H tr → ∀ b y i t,
    HonestReadPoint tr H b y i t →
      confirmedRead tr y i t ∈ (Node.frame (tr.state y i)).tree ∧
      (Node.frame (tr.state y i)).Anc (tr.finalizedAt y i) (confirmedRead tr y i t) ∧
      (Node.frame (tr.state y i)).Anc (confirmedRead tr y i t) (headRead tr y i t)
  held : ∀ cm proposer dg H (tr : RunTrace A),
    C.run.Run cm proposer dg H tr → ∀ b y i t,
    HonestReadPoint tr H b y i t → confirmedRead tr y i t ∈ (tr.state y i).fg.tree

/-- At `fgHold = 0`, `LocalReadPoint` is its form without a release hold. -/
theorem localReadPoint_iff_old
    {sg : A.Msg → Fin P.n} (C : ACCorrectLocal A sg) :
    LocalReadPoint (fgHold := 0) C ↔ LocalReadPointOld C :=
  ⟨fun h => by cases h; constructor <;> assumption,
    fun h => by cases h; constructor <;> assumption⟩

/-- `OutageReadPoint` over a supplier without a release hold. -/
structure OutageReadPointOld {sg : A.Msg → Fin P.n} (C : ACCorrectLocal A sg) : Prop where
  protection : ∀ cm proposer dg H (tr : RunTrace A) (p : EnvPoint (Fin P.n))
    ΔF T b₀ b₁ recoveryTime,
    C.run.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    RunPointBinding tr H p → 0 ≤ T → T + C.outageLag ≤ b₀ →
    b₀ ≤ b₁ → b₁ ≤ b₀ + C.outageBudget → b₁ ≤ recoveryTime →
    b₁ + C.recovery ≤ recoveryTime →
    ACServiceBefore C tr H ΔF b₀ → PostStopService tr H b₁ →
    p.EtaSleepyOn C.θ C.outageEta (max C.catchUp (C.outageEta - 1)) C.look 0 p.horizon →
    (∀ δ, 0 ≤ δ → δ ≤ C.outageEta →
      p.CommitteeSleepyOn (fun t => cm (max 0 (t - δ))) C.θ C.outageEta
        (max C.catchUp (C.outageEta - 1)) C.committeeLook 0 p.horizon) → ∀ x i y j t,
    ReadyReadPoint tr H p.horizon C.catchUp x i T → ReadBoundary tr x i → T < tr.time i →
    recoveryTime ≤ t → ReadyReadPoint tr H p.horizon C.catchUp y j t →
    ReadBoundary tr y j → t < tr.time j →
      Anc (tr.HonestBlocksAt H) (confirmedRead tr x i T) (confirmedRead tr y j t)

/-- At `fgHold = 0`, `OutageReadPoint` is its form without a release hold. -/
theorem outageReadPoint_iff_old
    {sg : A.Msg → Fin P.n} (C : ACCorrectLocal A sg) :
    OutageReadPoint (fgHold := 0) C ↔ OutageReadPointOld C :=
  ⟨fun ⟨h⟩ => ⟨h⟩, fun ⟨h⟩ => ⟨h⟩⟩

section Engine

open Shape Blocks

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V} {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat}

end Engine

end Consensus.Goldilocks.Generic

namespace Consensus.Goldilocks.Generic

open Shape Blocks Generic

variable {P : Params} {A : NodeAC P} {O : OutputSchema} {Info : Type}
  [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V}

variable {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat}

/-- `RegimeTransport` over a supplier without a release hold. -/
structure RegimeTransportOld (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) (hold : Time := 0) : Prop where
  sleepy : rho.ExecutionValid → ¬ rho.HashCollision →
    (Sys F V).Sleepy (shapeProgress F V).toExternal K ⟨E, rho⟩ →
    SleepyServicePrefix C M.trace M.honest E.ΔFG C.look rho.horizon
  healthy : rho.ExecutionValid → ¬ rho.HashCollision → ∀ g,
    (Sys F V).Healthy (shapeProgress F V).toExternal K g ⟨E, rho⟩ →
    Service M.trace M.honest g (E.ΔFG + hold) rho.horizon hold ∧
    (∀ y t, max g 0 ≤ t → t ≤ rho.horizon → y ∈ M.honest t → M.trace.awake y t) ∧
    (∀ d, 0 ≤ d → d ≤ rho.horizon → ((M.honest d)ᶜ.ncard : ℚ) < K.params.β * P.n) ∧
    (∀ t d, max g 0 ≤ t → t ≤ rho.horizon → 0 ≤ d → d ≤ rho.horizon →
      (M.committee t).Nonempty →
      (((↑(M.committee t) : Set (Fin P.n)) ∩ (M.honest d)ᶜ).ncard : ℚ) <
        K.params.βK * (M.committee t).card)
  ready : ∀ c v i, i ≤ rho.events.length → rho.point.Ready c v (rho.cutTime i) →
    ReadyRead M c (M.validator.symm v) (M.cut i) (rho.cutTime i)

/-- At `fgHold = 0`, `RegimeTransport` is its form without a release hold. -/
theorem regimeTransport_iff_old
    (M : RunMap rho payload) (K : Contract ProgressReq) (C : ACCorrectLocal A M.signer)
    (hold : Time := 0) :
    RegimeTransport (fgHold := 0) M K C hold ↔ RegimeTransportOld M K C hold :=
  ⟨fun h => by cases h; constructor <;> assumption,
    fun h => by cases h; constructor <;> assumption⟩

end Consensus.Goldilocks.Generic

namespace Consensus.Goldilocks.Generic.SleepyLayer1

variable {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n}

open Shape Blocks

variable {O : OutputSchema} {Info : Type} [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V} {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat}

/-- `CommitteeWindow` over a supplier without a release hold. -/
def CommitteeWindowOld (C : ACCorrectLocal A sg) (p : EnvPoint (Fin P.n))
    (cm : Time → Finset (Fin P.n)) (b : Time) : Prop :=
  ∀ t d, 0 ≤ t → t ≤ d → d ≤ min b (p.lookAhead C.committeeLook t) →
    (cm t).Nonempty →
    let q := p.retain d
    C.θ * (((q.readyAt C.catchUp t ∩ cm t).card +
      (q.faultyAt t ∩ cm t).card : Nat) : ℚ) <
      ((q.readyAt C.catchUp t ∩ cm t).card : ℚ)

/-- At `fgHold = 0`, `CommitteeWindow` is its form without a release hold. -/
theorem committeeWindow_iff_old
    (C : ACCorrectLocal A sg) (p : EnvPoint (Fin P.n)) (cm : Time → Finset (Fin P.n)) (b : Time) :
    CommitteeWindow (fgHold := 0) C p cm b ↔ CommitteeWindowOld C p cm b :=
  Iff.rfl

/-- `PopulationWindow` over a supplier without a release hold. -/
def PopulationWindowOld (C : ACCorrectLocal A sg) (p : EnvPoint (Fin P.n))
    (b : Time) : Prop :=
  ∀ t d, 0 ≤ t → t ≤ d → d ≤ min b (p.lookAhead C.look t) →
    (p.retain d).ReadyAbove C.θ C.catchUp t

/-- At `fgHold = 0`, `PopulationWindow` is its form without a release hold. -/
theorem populationWindow_iff_old
    (C : ACCorrectLocal A sg) (p : EnvPoint (Fin P.n)) (b : Time) :
    PopulationWindow (fgHold := 0) C p b ↔ PopulationWindowOld C p b :=
  Iff.rfl

/-- `EventSafety` over a supplier without a release hold. -/
def EventSafetyOld (M : RunMap rho payload) (C : ACCorrectLocal A M.signer) (D : Data A) : Prop :=
  ∀ ΔF b p, b ≤ rho.horizon →
    C.run.Run M.committee M.proposer M.digest M.honest M.trace →
    Compose.NoCollRun M.digest M.trace → RunPointBinding M.trace M.honest p →
    SleepyServicePrefix C M.trace M.honest ΔF C.look b →
    CommitteeWindow C p M.committee b → PopulationWindow C p b →
    AnchoredFrames D M.trace M.honest b →
    ∀ B B', EventWithin D M.trace M.honest b b B → EventWithin D M.trace M.honest b b B' →
      Compatible (M.trace.HonestBlocksAt M.honest) B B'

/-- At `fgHold = 0`, `EventSafety` is its form without a release hold. -/
theorem eventSafety_iff_old
    (M : RunMap rho payload) (C : ACCorrectLocal A M.signer) (D : Data A) :
    EventSafety (fgHold := 0) M C D ↔ EventSafetyOld M C D :=
  Iff.rfl

/-- `OutputProvenance` over a supplier without a release hold. -/
def OutputProvenanceOld (C : ACCorrectLocal A sg) (D : Data A) : Prop :=
  ∀ cm proposer dg H tr b,
    C.run.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    ∀ y i t, HonestReadPoint tr H b y i t → ReadBoundary tr y i →
      confirmedRead tr y i t ∈ (tr.state y i).fg.tree ∧
      (Anchored D tr H b t (confirmedRead tr y i t) ∨
        Anc (tr.HonestBlocksAt H) (confirmedRead tr y i t) (tr.state y i).fg.F)

/-- At `fgHold = 0`, `OutputProvenance` is its form without a release hold. -/
theorem outputProvenance_iff_old
    (C : ACCorrectLocal A sg) (D : Data A) :
    OutputProvenance (fgHold := 0) C D ↔ OutputProvenanceOld C D :=
  Iff.rfl

/-- `Extension` over a supplier without a release hold. -/
def ExtensionOld (M : RunMap rho payload) (C : ACCorrectLocal A M.signer) (D : Data A) : Prop :=
  ∀ ΔF b p, b ≤ rho.horizon →
    C.run.Run M.committee M.proposer M.digest M.honest M.trace →
    Compose.NoCollRun M.digest M.trace → RunPointBinding M.trace M.honest p →
    SleepyServicePrefix C M.trace M.honest ΔF C.look b →
    CommitteeWindow C p M.committee b → PopulationWindow C p b →
    AnchoredFrames D M.trace M.honest b →
    ∀ y i j t u, ReadyReadPoint M.trace M.honest b C.catchUp y i t →
    ReadyReadPoint M.trace M.honest b C.catchUp y j u →
    ReadBoundary M.trace y i → ReadBoundary M.trace y j →
    i ≤ j → t ≤ u →
      Anc (M.trace.HonestBlocksAt M.honest)
        (confirmedRead M.trace y i t) (confirmedRead M.trace y j u)

/-- At `fgHold = 0`, `Extension` is its form without a release hold. -/
theorem extension_iff_old
    (M : RunMap rho payload) (C : ACCorrectLocal A M.signer) (D : Data A) :
    Extension (fgHold := 0) M C D ↔ ExtensionOld M C D :=
  Iff.rfl

/-- `ProposalCoverage` over a supplier without a release hold. -/
def ProposalCoverageOld (M : RunMap rho payload) (C : ACCorrectLocal A M.signer)
    (D : Data A) : Prop :=
  ∀ ΔF b p, b ≤ rho.horizon →
    C.run.Run M.committee M.proposer M.digest M.honest M.trace →
    Compose.NoCollRun M.digest M.trace → RunPointBinding M.trace M.honest p →
    SleepyServicePrefix C M.trace M.honest ΔF C.look b →
    CommitteeWindow C p M.committee b → PopulationWindow C p b →
    AnchoredFrames D M.trace M.honest b →
    ∀ B k y j t, ReadyProposal M.trace M.honest C.catchUp C.hold B k → 0 ≤ M.trace.time k →
    M.trace.time k + C.hold ≤ b → M.trace.time k ≤ b → M.trace.time k + C.margin ≤ t →
    ReadyReadPoint M.trace M.honest b C.catchUp y j t →
    ReadBoundary M.trace y j → t < M.trace.time j →
      Anc (M.trace.HonestBlocksAt M.honest) B (confirmedRead M.trace y j t)

/-- At `fgHold = 0`, `ProposalCoverage` is its form without a release hold. -/
theorem proposalCoverage_iff_old
    (M : RunMap rho payload) (C : ACCorrectLocal A M.signer) (D : Data A) :
    ProposalCoverage (fgHold := 0) M C D ↔ ProposalCoverageOld M C D :=
  Iff.rfl

/-- `SourceProvenance` over a supplier without a release hold. -/
def SourceProvenanceOld (C : ACCorrectLocal A sg) (D : Data A) : Prop :=
  ∀ cm proposer dg H tr b,
    C.run.Run cm proposer dg H tr → Compose.NoCollRun dg tr → ∀ y i B,
    y ∈ H (tr.time i) → tr.time i ≤ b → ReportAt tr y i B →
    B.root = P.genesisRoot ∨ ∃ k s B', k ≤ i ∧ y ∈ H (tr.time k) ∧
      tr.time k ≤ b ∧ D.ConfirmedEvent tr y k s B' ∧ Anc (tr.HonestBlocksAt H) B B'

/-- At `fgHold = 0`, `SourceProvenance` is its form without a release hold. -/
theorem sourceProvenance_iff_old
    (C : ACCorrectLocal A sg) (D : Data A) :
    SourceProvenance (fgHold := 0) C D ↔ SourceProvenanceOld C D :=
  Iff.rfl

/-- `CacheProvenance` over a supplier without a release hold. -/
def CacheProvenanceOld (C : ACCorrectLocal A sg) (D : Data A) : Prop :=
  ∀ cm proposer dg H tr b,
    C.run.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    ∀ y i t, HonestReadPoint tr H b y i t →
      2 * (H t)ᶜ.ncard < P.n → SourcedRows D tr H b t →
      Anchored D tr H b t (tr.state y i).fg.F ∧
      Anchored D tr H b t (tr.state y i).fg.J

/-- At `fgHold = 0`, `CacheProvenance` is its form without a release hold. -/
theorem cacheProvenance_iff_old
    (C : ACCorrectLocal A sg) (D : Data A) :
    CacheProvenance (fgHold := 0) C D ↔ CacheProvenanceOld C D :=
  Iff.rfl

/-- `RowProvenance` over a supplier without a release hold. -/
def RowProvenanceOld (C : ACCorrectLocal A sg) (D : Data A) : Prop :=
  SourceProvenance C D →
  ∀ cm proposer dg H tr b,
    C.run.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    ∀ x k a, x ∈ H (tr.time k) → tr.SignAt x k a → tr.time k ≤ b →
      ∃ j src E, j < k ∧ tr.time j = tr.time k ∧ ReportAt tr x j src ∧
        tr.CallAt x k (.fg (.attest src (some a))) ∧
        E ∈ (tr.state x k).fg.tree ∧ E.root = a.T ∧
        E.root = ((tr.state x k).fg.σ src.root).Th ∧
        Anc (tr.HonestBlocksAt H) E src ∧ Anchored D tr H b (tr.time k) E

/-- At `fgHold = 0`, `RowProvenance` is its form without a release hold. -/
theorem rowProvenance_iff_old
    (C : ACCorrectLocal A sg) (D : Data A) :
    RowProvenance (fgHold := 0) C D ↔ RowProvenanceOld C D :=
  Iff.rfl

/-- `ConditionalViability` over a supplier without a release hold. -/
def ConditionalViabilityOld (C : ACCorrectLocal A sg) (D : Data A) : Prop :=
  ∀ cm proposer dg H tr b,
    C.run.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    ∀ y i t, HonestReadPoint tr H b y i t →
      2 * (H t)ᶜ.ncard < P.n → SourcedRows D tr H b t → ViableAt D tr H b y i t

/-- At `fgHold = 0`, `ConditionalViability` is its form without a release hold. -/
theorem conditionalViability_iff_old
    (C : ACCorrectLocal A sg) (D : Data A) :
    ConditionalViability (fgHold := 0) C D ↔ ConditionalViabilityOld C D :=
  Iff.rfl

/-- `FramesFromSources` over a supplier without a release hold. -/
def FramesFromSourcesOld (C : ACCorrectLocal A sg) (D : Data A) : Prop :=
  CacheProvenance C D → RowProvenance C D → ConditionalViability C D →
  SourceProvenance C D →
  ∀ cm proposer dg H tr b,
    C.run.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    (∀ y i t, HonestReadPoint tr H b y i t → 2 * (H t)ᶜ.ncard < P.n) →
    AnchoredFrames D tr H b

/-- At `fgHold = 0`, `FramesFromSources` is its form without a release hold. -/
theorem framesFromSources_iff_old
    (C : ACCorrectLocal A sg) (D : Data A) :
    FramesFromSources (fgHold := 0) C D ↔ FramesFromSourcesOld C D :=
  Iff.rfl

/-- `ReadAgreement` over a supplier without a release hold. -/
def ReadAgreementOld (M : RunMap rho payload) (C : ACCorrectLocal A M.signer)
    (D : Data A) : Prop :=
  EventSafety M C D → OutputProvenance C D →
  ∀ ΔF b p, b ≤ rho.horizon →
    C.run.Run M.committee M.proposer M.digest M.honest M.trace →
    Compose.NoCollRun M.digest M.trace → RunPointBinding M.trace M.honest p →
    SleepyServicePrefix C M.trace M.honest ΔF C.look b →
    CommitteeWindow C p M.committee b → PopulationWindow C p b →
    AnchoredFrames D M.trace M.honest b →
    ∀ y z i j t u, ReadyReadPoint M.trace M.honest b C.catchUp y i t →
      ReadyReadPoint M.trace M.honest b C.catchUp z j u →
      ReadBoundary M.trace y i → ReadBoundary M.trace z j →
      Compatible (M.trace.HonestBlocksAt M.honest)
        (confirmedRead M.trace y i t) (confirmedRead M.trace z j u)

/-- At `fgHold = 0`, `ReadAgreement` is its form without a release hold. -/
theorem readAgreement_iff_old
    (M : RunMap rho payload) (C : ACCorrectLocal A M.signer) (D : Data A) :
    ReadAgreement (fgHold := 0) M C D ↔ ReadAgreementOld M C D :=
  Iff.rfl

/-- `CommitteeTransport` over a supplier without a release hold. -/
def CommitteeTransportOld (M : RunMap rho payload) (C : ACCorrectLocal A M.signer) : Prop :=
  ∀ (p : EnvPoint (Fin P.n)) b c W,
    b ≤ p.horizon → C.catchUp ≤ c → C.committeeLook = W →
    0 ≤ C.θ → C.θ ≤ 1 →
    p.CommitteeSleepyOn M.committee C.θ 0 c W 0 b → CommitteeWindow C p M.committee b

/-- At `fgHold = 0`, `CommitteeTransport` is its form without a release hold. -/
theorem committeeTransport_iff_old
    (M : RunMap rho payload) (C : ACCorrectLocal A M.signer) :
    CommitteeTransport (fgHold := 0) M C ↔ CommitteeTransportOld M C :=
  Iff.rfl

/-- `PopulationTransport` over a supplier without a release hold. -/
def PopulationTransportOld (M : RunMap rho payload) (C : ACCorrectLocal A M.signer) : Prop :=
  ∀ (p : EnvPoint (Fin P.n)) b c W,
    b ≤ p.horizon → C.catchUp ≤ c → C.look = W →
    0 ≤ C.θ → C.θ ≤ 1 →
    p.SleepyOn C.θ c W 0 b → PopulationWindow C p b

/-- At `fgHold = 0`, `PopulationTransport` is its form without a release hold. -/
theorem populationTransport_iff_old
    (M : RunMap rho payload) (C : ACCorrectLocal A M.signer) :
    PopulationTransport (fgHold := 0) M C ↔ PopulationTransportOld M C :=
  Iff.rfl

/-- `ReadyReadSafety` over a supplier without a release hold. -/
def ReadyReadSafetyOld (M : RunMap rho payload) (C : ACCorrectLocal A M.signer)
    (D : Data A) : Prop :=
  ReadAgreement M C D → EventSafety M C D → OutputProvenance C D → Extension M C D →
  ∀ ΔF b p, b ≤ rho.horizon →
    C.run.Run M.committee M.proposer M.digest M.honest M.trace →
    Compose.NoCollRun M.digest M.trace → RunPointBinding M.trace M.honest p →
    SleepyServicePrefix C M.trace M.honest ΔF C.look b →
    CommitteeWindow C p M.committee b → PopulationWindow C p b →
    AnchoredFrames D M.trace M.honest b →
    (∀ y z i j t u, ReadyReadPoint M.trace M.honest b C.catchUp y i t →
      ReadyReadPoint M.trace M.honest b C.catchUp z j u →
      ReadBoundary M.trace y i → ReadBoundary M.trace z j →
      Compatible (M.trace.HonestBlocksAt M.honest)
        (confirmedRead M.trace y i t) (confirmedRead M.trace z j u)) ∧
    (∀ y i j t u, ReadyReadPoint M.trace M.honest b C.catchUp y i t →
      ReadyReadPoint M.trace M.honest b C.catchUp y j u →
      ReadBoundary M.trace y i → ReadBoundary M.trace y j →
      i ≤ j → t ≤ u →
      Anc (M.trace.HonestBlocksAt M.honest)
        (confirmedRead M.trace y i t) (confirmedRead M.trace y j u))

/-- At `fgHold = 0`, `ReadyReadSafety` is its form without a release hold. -/
theorem readyReadSafety_iff_old
    (M : RunMap rho payload) (C : ACCorrectLocal A M.signer) (D : Data A) :
    ReadyReadSafety (fgHold := 0) M C D ↔ ReadyReadSafetyOld M C D :=
  Iff.rfl

end Consensus.Goldilocks.Generic.SleepyLayer1

namespace Consensus.Goldilocks.Generic

open Shape Blocks

variable {P : Params} {A : NodeAC P} {O : OutputSchema} {Info : Type}
  [DecidableEq Info] [Countable Info]
  {F : ChainShapeFamily O Info} {V : Type} [Fintype V] [DecidableEq V]
  {E : Env V} {rho : Model.Run (compiled F) E} {payload : A.Blk → Set Nat}

/-- `SleepyWindowSupply` over a supplier without a release hold. -/
def SleepyWindowSupplyOld (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) : Prop :=
  ∃ p : EnvPoint (Fin P.n), RunPointBinding M.trace M.honest p ∧
    p.horizon = rho.horizon ∧ C.θ = K.params.θ ∧ 0 ≤ C.θ ∧ C.θ ≤ 1 ∧
    C.look = (Sys F V).aheadDur K ⟨E, rho⟩ ∧
    C.committeeLook = (Sys F V).committeeAheadDur K ⟨E, rho⟩ ∧
    (rho.ExecutionValid →
      (Sys F V).Sleepy (shapeProgress F V).toExternal K ⟨E, rho⟩ →
      p.SleepyOn C.θ ((Sys F V).cDur K ⟨E, rho⟩) C.look 0 rho.horizon ∧
      p.CommitteeSleepyOn M.committee C.θ 0 ((Sys F V).cDur K ⟨E, rho⟩)
        C.committeeLook 0 rho.horizon)

/-- At `fgHold = 0`, `SleepyWindowSupply` is its form without a release hold. -/
theorem sleepyWindowSupply_iff_old
    (M : RunMap rho payload) (K : Contract ProgressReq) (C : ACCorrectLocal A M.signer) :
    SleepyWindowSupply (fgHold := 0) M K C ↔ SleepyWindowSupplyOld M K C :=
  Iff.rfl

/-- `ClaimDeadlineFit` over a supplier without a release hold. -/
structure ClaimDeadlineFitOld (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) : Prop where
  /-- One unit of readiness slack permits the local read at the stored clock. -/
  catchUp : C.catchUp + 1 ≤ (Sys F V).cDur K ⟨E, rho⟩
  latency_le_margin : C.latency ≤ C.margin
  healthy_start : ∀ cap idx gst, (cap = .available ∨ cap = .stable) →
    max gst 0 + C.margin ≤ (Sys F V).heal K cap idx gst ⟨E, rho⟩
  accountable : K.params.α * (P.n : ℚ) ≤ (2 * P.q - P.n : Nat)
  final_faults : ∀ t, 0 ≤ t → t ≤ rho.horizon →
    3 * (M.honest t)ᶜ.ncard ≤ P.n - 1 →
    (M.honest t)ᶜ.ncard < 2 * P.q - P.n

/-- At `fgHold = 0`, `ClaimDeadlineFit` is its form without a release hold. -/
theorem claimDeadlineFit_iff_old
    (M : RunMap rho payload) (K : Contract ProgressReq) (C : ACCorrectLocal A M.signer) :
    ClaimDeadlineFit (fgHold := 0) M K C ↔ ClaimDeadlineFitOld M K C :=
  ⟨fun h => by cases h; constructor <;> assumption,
    fun h => by cases h; constructor <;> assumption⟩

/-- `AdmissibleProposal` over a supplier without a release hold. -/
def AdmissibleProposalOld (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) (B : A.Blk) (k : Nat) : Prop :=
  B.root ≠ P.genesisRoot ∧
    0 ≤ M.trace.time k ∧ M.trace.time k + C.hold ≤ rho.horizon ∧
    rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩)
      (M.validator B.proposer) (M.trace.time k)

/-- At `fgHold = 0`, `AdmissibleProposal` is its form without a release hold. -/
theorem admissibleProposal_iff_old
    (M : RunMap rho payload) (K : Contract ProgressReq) (C : ACCorrectLocal A M.signer) (B : A.Blk)
    (k : Nat) :
    AdmissibleProposal (fgHold := 0) M K C B k ↔ AdmissibleProposalOld M K C B k :=
  Iff.rfl

/-- `ProposalWitnessRefinement` over a supplier without a release hold. -/
structure ProposalWitnessRefinementOld (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) : Prop where
  sleepy : rho.ExecutionValid → ¬ rho.HashCollision → ∀ cap idx t,
    (cap = .available ∨ cap = .stable) →
    (Sys F V).Sleepy (shapeProgress F V).toExternal K ⟨E, rho⟩ →
    (Sys F V).prog (shapeProgress F V) K cap idx 0 rho.horizon ⟨E, rho⟩ →
    0 ≤ t → t + (K.params.latency cap idx : Time) * E.ΔAC ≤ rho.horizon →
    (∃ v, rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩) v
      (t + (K.params.latency cap idx : Time) * E.ΔAC)) →
    ∃ B k, t < M.trace.time k ∧ ReadyProposal M.trace M.honest C.catchUp C.hold B k ∧
      M.trace.time k + C.margin ≤ t + (K.params.latency cap idx : Time) * E.ΔAC ∧
      AdmissibleProposal M K C B k
  healthy : rho.ExecutionValid → ¬ rho.HashCollision → ∀ cap idx gst t,
    (cap = .available ∨ cap = .stable) →
    (Sys F V).Healthy (shapeProgress F V).toExternal K gst ⟨E, rho⟩ →
    (Sys F V).prog (shapeProgress F V) K cap idx ((Sys F V).ready K gst ⟨E, rho⟩)
      rho.horizon ⟨E, rho⟩ →
    (Sys F V).heal K cap idx gst ⟨E, rho⟩ ≤ t →
    t + (K.params.latency cap idx : Time) * E.ΔAC ≤ rho.horizon →
    (∃ v, rho.point.Ready ((Sys F V).cDur K ⟨E, rho⟩) v
      (t + (K.params.latency cap idx : Time) * E.ΔAC)) →
    ∃ B k, t < M.trace.time k ∧ ReadyProposal M.trace M.honest C.catchUp C.hold B k ∧
      M.trace.time k + C.margin ≤ t + (K.params.latency cap idx : Time) * E.ΔAC ∧
      AdmissibleProposal M K C B k

/-- At `fgHold = 0`, `ProposalWitnessRefinement` is its form without a release hold. -/
theorem proposalWitnessRefinement_iff_old
    (M : RunMap rho payload) (K : Contract ProgressReq) (C : ACCorrectLocal A M.signer) :
    ProposalWitnessRefinement (fgHold := 0) M K C ↔ ProposalWitnessRefinementOld M K C :=
  ⟨fun h => by cases h; constructor <;> assumption,
    fun h => by cases h; constructor <;> assumption⟩

/-- `ResetHealBudgetSupply` over a supplier without a release hold. -/
def ResetHealBudgetSupplyOld (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) : Prop :=
  rho.ExecutionValid → ¬ rho.HashCollision → ∀ cap idx gst,
  (cap = .available ∨ cap = .stable) →
  (Sys F V).Healthy (shapeProgress F V).toExternal K gst ⟨E, rho⟩ →
  (Sys F V).prog (shapeProgress F V) K cap idx ((Sys F V).ready K gst ⟨E, rho⟩)
    ((Sys F V).heal K cap idx gst ⟨E, rho⟩) ⟨E, rho⟩ →
  (Sys F V).heal K cap idx gst ⟨E, rho⟩ ≤ rho.horizon →
  ∃ a, Healing.Growing.IsReset M.trace M.honest gst a ∧ a ≤ rho.horizon ∧
    max gst 0 ≤ P.slotTime (P.slotOf a + C.healing.drain) ∧
    P.slotTime (P.slotOf a + C.healing.drain) + C.margin + 1 ≤
      (Sys F V).heal K cap idx gst ⟨E, rho⟩ ∧
    ∃ s₁ z k X, P.slotOf a + C.healing.drain ≤ s₁ ∧ AC.gbar gst + 4 * P.Δ ≤ P.slotTime s₁ ∧
      P.slotTime s₁ + 6 * P.Δ ≤ rho.horizon ∧
      P.slotTime s₁ + C.margin + 2 ≤ (Sys F V).heal K cap idx gst ⟨E, rho⟩ ∧
      HonestProposal M.trace M.honest M.proposer s₁ z k X

/-- At `fgHold = 0`, `ResetHealBudgetSupply` is its form without a release hold. -/
theorem resetHealBudgetSupply_iff_old
    (M : RunMap rho payload) (K : Contract ProgressReq) (C : ACCorrectLocal A M.signer) :
    ResetHealBudgetSupply (fgHold := 0) M K C ↔ ResetHealBudgetSupplyOld M K C :=
  Iff.rfl

/-- `OutageRecoveryBinding` over a supplier without a release hold. -/
structure OutageRecoveryBindingOld (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) : Prop where
  /-- One fixed local duration matches the same run's advertised recovery duration. -/
  duration : C.recovery = (K.params.recovery : Time) * E.ΔAC
  threshold : C.θ = K.params.θ
  catchUp : C.catchUp + 1 ≤ (Sys F V).cDur K ⟨E, rho⟩
  look : C.look = (Sys F V).aheadDur K ⟨E, rho⟩
  committeeLook : C.committeeLook = (Sys F V).committeeAheadDur K ⟨E, rho⟩
  eta : C.outageEta = (K.params.η : Time) * E.ΔAC
  lag : C.outageLag = (K.params.lag : Time) * E.ΔAC
  budget : C.outageBudget = (K.params.budget : Time) * E.ΔAC

/-- At `fgHold = 0`, `OutageRecoveryBinding` is its form without a release hold. -/
theorem outageRecoveryBinding_iff_old
    (M : RunMap rho payload) (K : Contract ProgressReq) (C : ACCorrectLocal A M.signer) :
    OutageRecoveryBinding (fgHold := 0) M K C ↔ OutageRecoveryBindingOld M K C :=
  ⟨fun h => by cases h; constructor <;> assumption,
    fun h => by cases h; constructor <;> assumption⟩

/-- `OutageServiceSupply` over a supplier without a release hold. -/
def OutageServiceSupplyOld (M : RunMap rho payload) (K : Contract ProgressReq)
    (C : ACCorrectLocal A M.signer) : Prop :=
  rho.ExecutionValid → ¬ rho.HashCollision → ∀ T b₀ b₁,
  (Sys F V).Outage (shapeProgress F V).toExternal K T b₀ b₁ ⟨E, rho⟩ →
  ACServiceBefore C M.trace M.honest E.ΔFG b₀ ∧ PostStopService M.trace M.honest b₁

/-- At `fgHold = 0`, `OutageServiceSupply` is its form without a release hold. -/
theorem outageServiceSupply_iff_old
    (M : RunMap rho payload) (K : Contract ProgressReq) (C : ACCorrectLocal A M.signer) :
    OutageServiceSupply (fgHold := 0) M K C ↔ OutageServiceSupplyOld M K C :=
  Iff.rfl

end Consensus.Goldilocks.Generic

end
