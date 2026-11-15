module
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.Generic.ReadPoint

@[expose] public section

/-! # Sleepy safety over the shared FG

These are supplier contracts, not proofs. The AC's induction is internal to its
event-safety discharge. All frames below are the run's own frames. Population and
committee retention windows are separate; neither look-ahead bounds the other.
-/

namespace Consensus.Goldilocks.Generic.SleepyLayer1

variable {P : Params} {A : NodeAC P} {sg : A.Msg → Fin P.n}

/-- AC-owned update results (vetoed or not) and optimistic confirmation events.
This is not a retained-output change or a healing origin. -/
structure Data (A : NodeAC P) where
  ConfirmedEvent : RunTrace A → Fin P.n → Nat → Nat → A.Blk → Prop

def EventWithin (D : Data A) (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (b t : Time) (B : A.Blk) : Prop :=
  ∃ x i s, x ∈ H (tr.time i) ∧ tr.time i ≤ t ∧ tr.time i ≤ b ∧
    D.ConfirmedEvent tr x i s B

/-- Whole-prefix ancestry, including confirmations before a restart. -/
def Anchored (D : Data A) (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (b t : Time) (B : A.Blk) : Prop :=
  B.root = P.genesisRoot ∨
    ∃ B', EventWithin D tr H b t B' ∧ Anc (tr.HonestBlocksAt H) B B'

/-- Conditional full-tree viability, not the frozen voter-tree witness. -/
def ViableAt (D : Data A) (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (b : Time) (y : Fin P.n) (i : Nat) (t : Time) : Prop :=
  (∀ B B', EventWithin D tr H b t B → EventWithin D tr H b t B' →
    Compatible (tr.HonestBlocksAt H) B B') →
  ∀ B, B ∈ (Node.frame (tr.state y i)).tree →
    (∀ B', EventWithin D tr H b t B' → Compatible (tr.HonestBlocksAt H) B B') →
    (Node.frame (tr.state y i)).Anc B (Node.frame (tr.state y i)).fcRoot ∨
      B ∈ (Node.frame (tr.state y i)).viableTree (Node.frame (tr.state y i)).tree

def AnchoredFrames (D : Data A) (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (b : Time) : Prop :=
  ∀ y i t, HonestReadPoint tr H b y i t →
    Anchored D tr H b t (tr.state y i).fg.F ∧
    Anchored D tr H b t (tr.state y i).fg.J ∧
    Anchored D tr H b t (Node.frame (tr.state y i)).fcRoot ∧
    ViableAt D tr H b y i t

def CommitteeWindow (C : ACCorrectLocal A sg) (p : EnvPoint (Fin P.n))
    (cm : Time → Finset (Fin P.n)) (b : Time) : Prop :=
  ∀ t d, 0 ≤ t → t ≤ d → d ≤ min b (p.lookAhead C.committeeLook t) →
    (cm t).Nonempty →
    let q := p.retain d
    C.θ * (((q.readyAt C.catchUp t ∩ cm t).card +
      (q.faultyAt t ∩ cm t).card : Nat) : ℚ) <
      ((q.readyAt C.catchUp t ∩ cm t).card : ℚ)

/-- Population counts at every time, using the population look-ahead. -/
def PopulationWindow (C : ACCorrectLocal A sg) (p : EnvPoint (Fin P.n))
    (b : Time) : Prop :=
  ∀ t d, 0 ≤ t → t ≤ d → d ≤ min b (p.lookAhead C.look t) →
    (p.retain d).ReadyAbove C.θ C.catchUp t

/-- Safety on actual composed runs; internal induction and gadget facts stay in
the instance proof. This does not assert safety for arbitrary frame sequences. -/
def EventSafety (C : ACCorrectLocal A sg) (D : Data A) : Prop :=
  ∀ cm proposer dg H tr ΔF b p,
    C.run.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    RunPointBinding tr H p → tr.SleepyPrefixAt H ΔF C.look b →
    CommitteeWindow C p cm b → PopulationWindow C p b → AnchoredFrames D tr H b →
    ∀ B B', EventWithin D tr H b b B → EventWithin D tr H b b B' →
      Compatible (tr.HonestBlocksAt H) B B'

/-- At a read boundary, the output is held at the explicit evaluation time.
Its ancestry uses the effective record or the frame floor. Held membership
makes the genesis-root case meaningful under honest-store coherence. -/
def OutputProvenance (C : ACCorrectLocal A sg) (D : Data A) : Prop :=
  ∀ cm proposer dg H tr b,
    C.run.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    ∀ y i t, HonestReadPoint tr H b y i t → ReadBoundary tr y i →
      confirmedRead tr y i t ∈ (tr.state y i).fg.tree ∧
      (Anchored D tr H b t (confirmedRead tr y i t) ∨
        Anc (tr.HonestBlocksAt H) (confirmedRead tr y i t) (tr.state y i).fg.F)

/-- Required separately for ReadySafe; event compatibility alone does not give
same-reader extension. Certificate discharge remains an instance obligation. -/
def Extension (C : ACCorrectLocal A sg) (D : Data A) : Prop :=
  ∀ cm proposer dg H tr ΔF b p,
    C.run.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    RunPointBinding tr H p → tr.SleepyPrefixAt H ΔF C.look b →
    CommitteeWindow C p cm b → PopulationWindow C p b → AnchoredFrames D tr H b →
    ∀ y i j t u, ReadyReadPoint tr H b C.catchUp y i t →
    ReadyReadPoint tr H b C.catchUp y j u → ReadBoundary tr y i → ReadBoundary tr y j →
    i ≤ j → t ≤ u →
      Anc (tr.HonestBlocksAt H) (confirmedRead tr y i t) (confirmedRead tr y j u)

/-- Proposal coverage at an actual read, with both retention windows and anchored frames.
Coverage does not produce the proposal witness. -/
def ProposalCoverage (C : ACCorrectLocal A sg) (D : Data A) : Prop :=
  ∀ cm proposer dg H tr ΔF b p,
    C.run.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    RunPointBinding tr H p → tr.SleepyPrefixAt H ΔF C.look b →
    CommitteeWindow C p cm b → PopulationWindow C p b → AnchoredFrames D tr H b →
    ∀ B k y j t, ReadyProposal tr H C.catchUp C.hold B k → 0 ≤ tr.time k →
    tr.time k + C.hold ≤ b → tr.time k ≤ b → tr.time k + C.margin ≤ t →
    ReadyReadPoint tr H b C.catchUp y j t → ReadBoundary tr y j → t < tr.time j →
      Anc (tr.HonestBlocksAt H) B (confirmedRead tr y j t)

/-- Route-1 source provenance without an invariant. The source is an ancestor
of a same-reporter event, possibly at the same cut, not necessarily that event's block. -/
def SourceProvenance (C : ACCorrectLocal A sg) (D : Data A) : Prop :=
  ∀ cm proposer dg H tr b,
    C.run.Run cm proposer dg H tr → Compose.NoCollRun dg tr → ∀ y i B,
    y ∈ H (tr.time i) → tr.time i ≤ b → ReportAt tr y i B →
    B.root = P.genesisRoot ∨ ∃ k s B', k ≤ i ∧ y ∈ H (tr.time k) ∧
      tr.time k ≤ b ∧ D.ConfirmedEvent tr y k s B' ∧ Anc (tr.HonestBlocksAt H) B B'

/-- Honest signed targets are anchored at their signing time, not just at a later read. -/
def SourcedRows (D : Data A) (tr : RunTrace A) (H : Time → Set (Fin P.n))
    (b t : Time) : Prop :=
  ∀ x k a, x ∈ H (tr.time k) → tr.SignAt x k a → tr.time k ≤ t → tr.time k ≤ b →
    ∃ E ∈ tr.HonestBlocksAt H, E.root = a.T ∧ Anchored D tr H b (tr.time k) E

/-- F1 target. The population quorum is an explicit premise, independent of the
committee window. This proposition is not a supplied theorem. -/
def CacheProvenance (C : ACCorrectLocal A sg) (D : Data A) : Prop :=
  ∀ cm proposer dg H tr b,
    C.run.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    ∀ y i t, HonestReadPoint tr H b y i t →
      2 * (H t)ᶜ.ncard < P.n → SourcedRows D tr H b t →
      Anchored D tr H b t (tr.state y i).fg.F ∧
      Anchored D tr H b t (tr.state y i).fg.J

/-- F2 target. The signed target is the entry ancestor of the actual toFG source,
not necessarily the source itself. The report precedes signing at the same time.
Source provenance then anchors that entry at the signing time. -/
def RowProvenance (C : ACCorrectLocal A sg) (D : Data A) : Prop :=
  SourceProvenance C D →
  ∀ cm proposer dg H tr b,
    C.run.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    ∀ x k a, x ∈ H (tr.time k) → tr.SignAt x k a → tr.time k ≤ b →
      ∃ j src E, j < k ∧ tr.time j = tr.time k ∧ ReportAt tr x j src ∧
        tr.CallAt x k (.fg (.attest src (some a))) ∧
        E ∈ (tr.state x k).fg.tree ∧ E.root = a.T ∧
        E.root = ((tr.state x k).fg.σ src.root).Th ∧
        Anc (tr.HonestBlocksAt H) E src ∧ Anchored D tr H b (tr.time k) E

/-- F3 target. Sourced rows and the population quorum feed FG geometry;
compatibility remains conditional inside ViableAt. -/
def ConditionalViability (C : ACCorrectLocal A sg) (D : Data A) : Prop :=
  ∀ cm proposer dg H tr b,
    C.run.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    ∀ y i t, HonestReadPoint tr H b y i t →
      2 * (H t)ᶜ.ncard < P.n → SourcedRows D tr H b t → ViableAt D tr H b y i t

/-- G1 target. No AC induction hypothesis: F1--F3 and route-1 provenance
anchor the actual frames, given the population quorum at each honest read. -/
def FramesFromSources (C : ACCorrectLocal A sg) (D : Data A) : Prop :=
  CacheProvenance C D → RowProvenance C D → ConditionalViability C D →
  SourceProvenance C D →
  ∀ cm proposer dg H tr b,
    C.run.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    (∀ y i t, HonestReadPoint tr H b y i t → 2 * (H t)ᶜ.ncard < P.n) →
    AnchoredFrames D tr H b

/-- G2 target. Agreement follows from event safety, output ancestry and anchored
frames. Extension is deliberately separate, for the ReadySafe assembly. -/
def ReadAgreement (C : ACCorrectLocal A sg) (D : Data A) : Prop :=
  EventSafety C D → OutputProvenance C D →
  ∀ cm proposer dg H tr ΔF b p,
    C.run.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    RunPointBinding tr H p → tr.SleepyPrefixAt H ΔF C.look b →
    CommitteeWindow C p cm b → PopulationWindow C p b → AnchoredFrames D tr H b →
    ∀ y z i j t u, ReadyReadPoint tr H b C.catchUp y i t →
      ReadyReadPoint tr H b C.catchUp z j u →
      ReadBoundary tr y i → ReadBoundary tr z j →
      Compatible (tr.HonestBlocksAt H) (confirmedRead tr y i t) (confirmedRead tr z j u)

/-- The committee count transports to every earlier retention charge. Its
look-ahead is independent of the population look-ahead. -/
def CommitteeTransport (C : ACCorrectLocal A sg) : Prop :=
  ∀ (p : EnvPoint (Fin P.n)) cm b c W,
    b ≤ p.horizon → C.catchUp ≤ c → C.committeeLook = W →
    0 ≤ C.θ → C.θ ≤ 1 →
    p.CommitteeSleepyOn cm C.θ 0 c W 0 b → CommitteeWindow C p cm b

/-- Population counts transport independently to every earlier retention charge. -/
def PopulationTransport (C : ACCorrectLocal A sg) : Prop :=
  ∀ (p : EnvPoint (Fin P.n)) b c W,
    b ≤ p.horizon → C.catchUp ≤ c → C.look = W →
    0 ≤ C.θ → C.θ ≤ 1 →
    p.SleepyOn C.θ c W 0 b → PopulationWindow C p b

/-- F5 target. A duplicate is already held; a fresh delivery needs all FG guards.
The source transition supplies transition success at the receiver only when
the parent states agree. The F-extension premise is supplied before this row is used. -/
def FrameAcceptance : Prop :=
  ∀ (src src' dst : Store P A.Payload) (B : A.Blk) (pr : Nat),
    src.onBlock B = some src' → B.parent = some pr →
    (dst.blocks B.root = some B ∨
      (dst.blocks B.root = none ∧ (dst.blocks pr).isSome ∧
        dst.σ pr = src.σ pr ∧ Anc (insert B dst.tree) dst.F B)) →
    B ∈ (dst.onBlock B |>.getD dst).tree

/-- Ready-read safety assembly: G2 supplies cross-reader agreement and the
separate extension row supplies monotonicity. No proposal or inclusion row is used. -/
def ReadyReadSafety (C : ACCorrectLocal A sg) (D : Data A) : Prop :=
  ReadAgreement C D → EventSafety C D → OutputProvenance C D → Extension C D →
  ∀ cm proposer dg H tr ΔF b p,
    C.run.Run cm proposer dg H tr → Compose.NoCollRun dg tr →
    RunPointBinding tr H p → tr.SleepyPrefixAt H ΔF C.look b →
    CommitteeWindow C p cm b → PopulationWindow C p b → AnchoredFrames D tr H b →
    (∀ y z i j t u, ReadyReadPoint tr H b C.catchUp y i t →
      ReadyReadPoint tr H b C.catchUp z j u →
      ReadBoundary tr y i → ReadBoundary tr z j →
      Compatible (tr.HonestBlocksAt H) (confirmedRead tr y i t) (confirmedRead tr z j u)) ∧
    (∀ y i j t u, ReadyReadPoint tr H b C.catchUp y i t →
      ReadyReadPoint tr H b C.catchUp y j u → ReadBoundary tr y i → ReadBoundary tr y j →
      i ≤ j → t ≤ u →
      Anc (tr.HonestBlocksAt H) (confirmedRead tr y i t) (confirmedRead tr y j u))

end Consensus.Goldilocks.Generic.SleepyLayer1

end
