module
public import AvailableChainFGCompose.Statements.Attempt
public import AvailableChainFGCompose.Statements.FinalityKernel

@[expose] public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot)
variable (O : FGObservationReads R) (T : FGTiming) (I : V2.D.Interface Prot)
variable (pair : Wire → NamedHeightPair) (Jst : Time) (leaseSlots deltaT : Nat)

def FrontierSeedQualification (T : FGTiming) (leaseSlots : Nat) (GST : Time)
    (u : Time) (q : Slot) : Prop :=
  (∃ β : Slot,
    u < T.proposal β ∧
    (∀ b, u < T.proposal b → β ≤ b) ∧
    T.proposal (β + 2 * leaseSlots - 1) < T.proposal q) ∨
  (∃ b : Slot,
    u ≤ T.vote b ∧
    (∀ i, u ≤ T.vote i → b ≤ i) ∧
    leaseSlots ≤ b + 1 ∧
    GST ≤ T.vote (b + 1 - leaseSlots) ∧
    T.proposal (b + leaseSlots) < T.proposal q)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces]
Blueprint 21:1333–1350; TF-SEED Q4.
DC: SAME an explicit equation adapter for the frozen two-arm seed premise. -/
theorem FrontierSeedQualification_def (T : FGTiming) (leaseSlots : Nat) (GST : Time)
    (u : Time) (q : Slot) : FrontierSeedQualification T leaseSlots GST u q ↔
  (∃ β : Slot,
    u < T.proposal β ∧
    (∀ b, u < T.proposal b → β ≤ b) ∧
    T.proposal (β + 2 * leaseSlots - 1) < T.proposal q) ∨
  (∃ b : Slot,
    u ≤ T.vote b ∧
    (∀ i, u ≤ T.vote i → b ≤ i) ∧
    leaseSlots ≤ b + 1 ∧
    GST ≤ T.vote (b + 1 - leaseSlots) ∧
    T.proposal (b + leaseSlots) < T.proposal q) := Iff.rfl

/-- The selected proposal supplies HEAD service on the actual joined reader scope.
The protocol keeps its lock, write, and exact-output clauses in its own producer. -/
def FrontierProposalService (q : Slot) (Q : Block) : Prop :=
  T.vote q ≤ rho.horizon → ∀ x ∈ rho.honest,
    AttemptJoinedAt E rho T x q (T.vote q) → headAtLabel R E rho T x q = some Q

/-- Continuing service stops at this endpoint, including covered opening sources. -/
def FrontierLocalService (q : Slot) (Q : Block) (Qfg : FGBlock (Fin n))
    (m : Nat) (v : Time) : Prop :=
  (∀ x s H, x ∈ rho.honest → q + 1 ≤ s → T.vote s ≤ v →
    headAtLabel R E rho T x s = some H → Block.Preceq Q H) ∧
  (∀ s B, q + 2 ≤ s → T.proposal s ≤ v → HonestProposal E rho I s B →
    Block.Preceq Q B.parent) ∧
  (∀ i x, x ∈ rho.honest → T.gate q + 4 * T.delta ≤ v →
    afterTicksIdx rho (T.gate q + 4 * T.delta) ≤ i → i ≤ timeIdx rho v →
    Block.Preceq Q (I.stable (rho.stateBefore E i x))) ∧
  (∀ s B, T.proposal q < T.proposal s → T.gate s ≤ v →
    HonestProposal E rho I s B → FrontierProposalService R E rho T s B) ∧
  (∀ r, q ≤ r * T.roundSlots → T.action r ≤ v →
    OpeningCovered R S E rho O.height T pair r Q ∧
    OpeningEntry R E rho O.height T r m ∧
    (∀ x K, x ∈ rho.honest → actionSourceFG R E rho T x r = some (some K) →
      (O.height K).T_h = (O.height Qfg).T_h) ∧
    ((∀ r', q ≤ r' * T.roundSlots → r ≤ r') →
      T.action r - T.gate q ≤ FGCompose.P T - 4 * T.delta))

/-- A saved seed keeps the actual proposal, phase, read cutoff, and local service. -/
def StrongServed (m : Nat) (t : Time) : Prop :=
  ∃ u J contested q Q Qfg,
    Jst ≤ u ∧ HonestProposal E rho I q Q ∧ R.erase Qfg = Q ∧
    (O.height Qfg).h = m ∧ FrontierProposalService R E rho T q Q ∧
    FrontierSeedQualification T leaseSlots E.t_GST u q ∧ u ≤ T.proposal q ∧
    PhaseInterval R E rho O u (T.gate q) m J contested ∧ T.gate q ≤ t ∧
    t ≤ rho.horizon ∧
    (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho t → x ∈ rho.honest →
      (R.core (rho.stateBefore E i x)).fg.h_max ≤ m) ∧
    FrontierLocalService R S E rho O T I pair q Q Qfg m t

theorem StrongServed_def (m : Nat) (t : Time) :
    StrongServed R S E rho O T I pair Jst leaseSlots m t ↔
  ∃ u J contested q Q Qfg,
    Jst ≤ u ∧ HonestProposal E rho I q Q ∧ R.erase Qfg = Q ∧
    (O.height Qfg).h = m ∧ FrontierProposalService R E rho T q Q ∧
    FrontierSeedQualification T leaseSlots E.t_GST u q ∧ u ≤ T.proposal q ∧
    PhaseInterval R E rho O u (T.gate q) m J contested ∧ T.gate q ≤ t ∧
    t ≤ rho.horizon ∧
    (∀ i x, timeIdx rho u ≤ i → i ≤ timeIdx rho t → x ∈ rho.honest →
      (R.core (rho.stateBefore E i x)).fg.h_max ≤ m) ∧
    FrontierLocalService R S E rho O T I pair q Q Qfg m t := Iff.rfl

/-- The repair threshold retains the strict proposal or inclusive first HEAD label. -/
inductive FrontierRepairStart (u : Time) : Slot → Prop where
  | two (β : Slot) (after : u < T.proposal β)
      (least : ∀ b, u < T.proposal b → β ≤ b) :
      FrontierRepairStart u (β + 2 * leaseSlots - 1)
  | one (b : Slot) (after : u ≤ T.vote b)
      (least : ∀ i, u ≤ T.vote i → b ≤ i) (window : leaseSlots ≤ b + 1)
      (sync : E.t_GST ≤ T.vote (b + 1 - leaseSlots)) :
      FrontierRepairStart u (b + leaseSlots)

/-- An arbitrary nonnegative allowance with its produced local repair service. -/
def FrontierRepairAllowance (G allowance u : Time) : Prop :=
  0 ≤ allowance ∧ ∃ l, FrontierRepairStart E T leaseSlots u l ∧
    (4 * T.delta ≤ G → ∀ v m J contested,
    Jst ≤ u → PhaseInterval R E rho O u v m J contested →
      (∀ s Q, T.proposal l < T.proposal s → T.gate s ≤ v →
        HonestProposal E rho I s Q → FrontierProposalService R E rho T s Q) ∧
      (u + allowance ≤ v → ∃ s Q,
        T.proposal l < T.proposal s ∧ T.gate s ≤ u + allowance ∧
        HonestProposal E rho I s Q ∧ FrontierProposalService R E rho T s Q))

/-- Frozen `Transfers` (ChannelProps:932) over generic reads: HEAD at later labels,
proposal parents from s + 2, and stable output from the gate cut, each through v. -/
def PhaseTransfers (s : Slot) (B : Block) (v : Time) : Prop :=
  (∀ x i H, x ∈ rho.honest → s + 1 ≤ i → T.vote i ≤ v →
    headAtLabel R E rho T x i = some H → Block.Preceq B H) ∧
  (∀ i Q, s + 2 ≤ i → T.proposal i ≤ v → HonestProposal E rho I i Q →
    Block.Preceq B Q.parent) ∧
  (∀ i x, x ∈ rho.honest → T.gate s + 4 * T.delta ≤ v →
    afterTicksIdx rho (T.gate s + 4 * T.delta) ≤ i → i ≤ timeIdx rho v →
    Block.Preceq B (I.stable (rho.stateBefore E i x)))

theorem PhaseTransfers_def (s : Slot) (B : Block) (v : Time) :
    PhaseTransfers R E rho T I s B v ↔
  (∀ x i H, x ∈ rho.honest → s + 1 ≤ i → T.vote i ≤ v →
    headAtLabel R E rho T x i = some H → Block.Preceq B H) ∧
  (∀ i Q, s + 2 ≤ i → T.proposal i ≤ v → HonestProposal E rho I i Q →
    Block.Preceq B Q.parent) ∧
  (∀ i x, x ∈ rho.honest → T.gate s + 4 * T.delta ≤ v →
    afterTicksIdx rho (T.gate s + 4 * T.delta) ≤ i → i ≤ timeIdx rho v →
    Block.Preceq B (I.stable (rho.stateBefore E i x))) := Iff.rfl

/-- Frozen `TPerm` (ChannelProps:955) with the protocol phase body as a parameter.
The body (SA fast write or synchronous-window slow gate) stays protocol-specific. -/
def PhasePermanence (body : Slot → Block → Prop) : Prop :=
  ∀ u v m J contested s B, Jst ≤ u → PhaseInterval R E rho O u v m J contested →
    u ≤ T.vote s → T.gate s ≤ v → body s B → PhaseTransfers R E rho T I s B v

theorem PhasePermanence_def (body : Slot → Block → Prop) :
    PhasePermanence R E rho O T I Jst body ↔
  ∀ u v m J contested s B, Jst ≤ u → PhaseInterval R E rho O u v m J contested →
    u ≤ T.vote s → T.gate s ≤ v → body s B → PhaseTransfers R E rho T I s B v := Iff.rfl

/-- Frozen `SeatCovers` and `CoveredByChild` (Fold.lean:63-74) at the progress kind. -/
def ProgressCoveredByChild (Ef : Electorate (Fin n)) (H : FGHeightView (Fin n))
    (X U : FGBlock (Fin n)) (y : Nat) : Prop :=
  ∃ Q : Finset (Fin n), Ef.q ≤ Ef.weightOf Q ∧ ∀ i ∈ Q,
    i ∈ (H X.parent).progress ∨ ∃ row ∈ X.rows, RowNames .progress row i y U

theorem ProgressCoveredByChild_def (Ef : Electorate (Fin n)) (H : FGHeightView (Fin n))
    (X U : FGBlock (Fin n)) (y : Nat) : ProgressCoveredByChild Ef H X U y ↔
  ∃ Q : Finset (Fin n), Ef.q ≤ Ef.weightOf Q ∧ ∀ i ∈ Q,
    i ∈ (H X.parent).progress ∨ ∃ row ∈ X.rows, RowNames .progress row i y U := Iff.rfl

/-- Frozen `foldTrichotomy p .progress` (Fold.lean:80). The target conjunct is vacuous
at the progress kind and is dropped; the progress age premise is unconditional. -/
def ProgressFoldAdvance (Ef : Electorate (Fin n)) (H : FGHeightView (Fin n))
    (δt : Nat) : Prop :=
  ∀ (y : Nat) (U X : FGBlock (Fin n)), X ≠ .genesis → EntryAt H U y →
    FGBlock.Preceq U X.parent →
    ((H X.parent).h = y → ProgressCoveredByChild Ef H X U y) →
    U.slot + δt ≤ X.slot → y + 1 ≤ (H X).h

theorem ProgressFoldAdvance_def (Ef : Electorate (Fin n)) (H : FGHeightView (Fin n))
    (δt : Nat) : ProgressFoldAdvance Ef H δt ↔
  ∀ (y : Nat) (U X : FGBlock (Fin n)), X ≠ .genesis → EntryAt H U y →
    FGBlock.Preceq U X.parent →
    ((H X.parent).h = y → ProgressCoveredByChild Ef H X U y) →
    U.slot + δt ≤ X.slot → y + 1 ≤ (H X).h := Iff.rfl

variable {Body : Type} (D : FGHistoryWireReads S) (Ef : Electorate (Fin n))
variable (family : Prot.Object → Prop) (timely : Prot.State → Prot.Object → Prop)
variable (decodeProposal : Prot.Object → Option (Slot × Body))
variable (bodyErase : Body → Block) (bodyRows : Body → List Wire)
variable (blockWireRows : Prot.State → List Wire)
variable (parentFG : Prot.State → Block → Option (FGBlock (Fin n)))
variable (parentHeight : Prot.State → Slot → FGBlock (Fin n) → Height × BlockId)
variable (validFor : Prot.State → Slot → FGBlock (Fin n) → Wire → Bool)

open Classical in
/-- This is the intermediate terminal-promotion goal. A later package proves it.
Fieldwise translation of FrontierSearchDefs:209. Recovery₂ is split into its generic
fields: delivery (the `family` objects within E.Δ, others within ΔF), E.Δ ≤ ΔF, gap,
valid, delta, fault, awake and 4Δ ≤ G. Two used effects replace protocol fields:
`Fintype.card V = n` (Base₂.linked.toCStar, read by healing_phase_extend_of_no_effective)
and the receipt hold (Base₂.receiptIdealization, read by healing_promotion_first_receipt
through ReceiverService.proposal). -/
def TerminalPromotionFact [Fintype V] (body : Slot → Block → Prop) (G ΔF : Time) : Prop :=
  Gen.V2.Duty.PartialSynchronyBy E rho (fun o => if family o then E.Δ else ΔF) →
  E.Δ ≤ ΔF →
  (∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon → ∃ s, t < V2.D.proposalTime I s ∧
    V2.D.proposalTime I s ≤ t + G ∧ Gen.V2.Duty.HonestSlot rho I s) →
  V2.D.ExecutionValid E rho → E.Δ = T.delta →
  (Gen.V2.Duty.faulty rho).card ≤ (n - 1) / 3 →
  (∀ v ∈ rho.honest, ∀ t, E.t_GST ≤ t → t ≤ rho.horizon → E.awake v t = true) →
  4 * T.delta ≤ G → Fintype.card V = n →
  (∀ o s N send freeze x, x ∈ rho.honest → decodeProposal o = some (s, N) →
    ReceiverService family timely E rho o send freeze x →
    ∃ Y ∈ (R.core (V2.D.Run.stateBeforeTime E rho freeze x)).fg.TF,
      R.erase Y = bodyErase N) →
  deltaT = 2 * T.roundSlots → LivenessBoundW T ΔF →
  (V2.D.NoRestart rho → FGRunOrderLaws E rho R) → RXing R E rho O →
  PhasePermanence R E rho O T I Jst body →
  TRowsReceipt R S E rho T blockWireRows ΔF →
  (∀ (r height : Nat) (U X : FGBlock (Fin n)),
    BatchPrem R S O T E rho I D Ef decodeProposal bodyErase bodyRows blockWireRows
      parentFG parentHeight validFor ΔF .progress r height U X →
    (O.height X.parent).h = height → ProgressCoveredByChild Ef O.height X U height) →
  ProgressFoldAdvance Ef O.height deltaT →
  Gen.Pure.FaultQ n (Gen.V2.Duty.faulty rho).card →
  (∃ Q : Finset (Fin n), (∀ i ∈ Q, safetyHolder S rho i ∈ rho.honest) ∧
    Ef.q ≤ Ef.weightOf Q) →
  ∀ r, T.action r + 2 * FGCompose.P T + Γ T G - 9 * T.delta ≤ rho.horizon →
  ∀ u m J contested l q Q height, Jst ≤ u →
    PhaseInterval R E rho O u (T.action r) m J contested →
    u ≤ T.proposal q → q ≤ r * T.roundSlots → T.proposal l < T.proposal q →
    HonestProposal E rho I q Q → FrontierProposalService R E rho T q Q →
    OpeningEntry R E rho O.height T r height →
    OpeningCovered R S E rho O.height T pair r Q →
    (∀ v, PhaseInterval R E rho O u v m J contested → ∀ s Q',
      T.proposal l < T.proposal s → T.gate s ≤ v → HonestProposal E rho I s Q' →
      FrontierProposalService R E rho T s Q') →
    (∃ i ev, afterTicksIdx rho (T.action r) ≤ i ∧ rho.events[i]? = some ev ∧
      EffectiveEvent R E rho O i ∧
      ev.time ≤ T.action r + 2 * FGCompose.P T + Γ T G - 9 * T.delta) ∨
    (∃ s X, HonestProposal E rho I s (R.erase X) ∧ X.slot = s ∧
      (r : Time) * FGCompose.P T + 2 * FGCompose.P T ≤ T.proposal s ∧
      T.proposal s ≤ T.action r + 2 * FGCompose.P T + Γ T G - 10 * T.delta ∧
      height + 1 ≤ (O.height X).h ∧
      (∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
        (fun nd => X ∈ (R.core nd).fg.TF) (T.proposal s + T.delta) y))

def FrontierSearchStart (i : Nat) (ev : V2.Event V Prot.Object) (m : Nat)
    (kind : PhaseKind) : Prop :=
  rho.events[i]? = some ev ∧ Jst ≤ ev.time ∧
  (EffectiveEvent R E rho O i ∨
    ∃ rG, Jst ≤ T.action rG ∧
      (∀ r, Jst ≤ T.action r → rG ≤ r) ∧
      ev.time = T.action (rG + 2) ∧ timeIdx rho ev.time = i + 1) ∧
  frontierAtIdx R E rho (i + 1) = m ∧ 1 ≤ m ∧
  AttemptPhaseAt R E rho O (i + 1) m kind

/-- Blueprint 21 HG.3. DC: SAME the public conclusion interface. -/
theorem FrontierSearchStart_def (i : Nat) (ev : V2.Event V Prot.Object) (m : Nat)
    (kind : PhaseKind) : FrontierSearchStart R E rho O T Jst i ev m kind ↔
  rho.events[i]? = some ev ∧ Jst ≤ ev.time ∧
  (EffectiveEvent R E rho O i ∨
    ∃ rG, Jst ≤ T.action rG ∧
      (∀ r, Jst ≤ T.action r → rG ≤ r) ∧
      ev.time = T.action (rG + 2) ∧ timeIdx rho ev.time = i + 1) ∧
  frontierAtIdx R E rho (i + 1) = m ∧ 1 ≤ m ∧
  AttemptPhaseAt R E rho O (i + 1) m kind := Iff.rfl

def FirstPhaseStopBy (i m : Nat) (deadline : Time) : Prop :=
  ∃ j ev, i < j ∧ rho.events[j]? = some ev ∧ ev.time ≤ deadline ∧
    EffectiveEvent R E rho O j ∧ frontierAtIdx R E rho (j + 1) = m ∧
    (∀ k, i < k → k < j → ¬ EffectiveEvent R E rho O k)

/-- Blueprint 21 HG.3. DC: SAME the public conclusion interface. -/
theorem FirstPhaseStopBy_def (i m : Nat) (deadline : Time) :
    FirstPhaseStopBy R E rho O i m deadline ↔
  ∃ j ev, i < j ∧ rho.events[j]? = some ev ∧ ev.time ≤ deadline ∧
    EffectiveEvent R E rho O j ∧ frontierAtIdx R E rho (j + 1) = m ∧
    (∀ k, i < k → k < j → ¬ EffectiveEvent R E rho O k) := Iff.rfl

/-- Blueprint 21 H.10/HG.3; HG.3 plan Q1.
DC: SAME a rise is the first effective event of the interrupted phase. -/
def FirstRiseStopBy (i m : Nat) (deadline : Time) : Prop :=
  ∃ j ev, i < j ∧ rho.events[j]? = some ev ∧ ev.time ≤ deadline ∧
    EffectiveEvent R E rho O j ∧ m < frontierAtIdx R E rho (j + 1) ∧
    (∀ k, i < k → k < j → ¬ EffectiveEvent R E rho O k)

/-- Blueprint 21 HG.3. DC: SAME the public conclusion interface. -/
theorem FirstRiseStopBy_def (i m : Nat) (deadline : Time) : FirstRiseStopBy R E rho O i m deadline ↔
  ∃ j ev, i < j ∧ rho.events[j]? = some ev ∧ ev.time ≤ deadline ∧
    EffectiveEvent R E rho O j ∧ m < frontierAtIdx R E rho (j + 1) ∧
    (∀ k, i < k → k < j → ¬ EffectiveEvent R E rho O k) := Iff.rfl

/-- Blueprint 21 HG.3; HG.3 plan Q1.
DC: SAME the two first-stop arms and a complete saved seed. -/
def FrontierHG3Result (i m : Nat) (start deadline : Time) : Prop :=
  FirstPhaseStopBy R E rho O i m deadline ∨
  FirstRiseStopBy R E rho O i m deadline ∨
  ∃ t, start ≤ t ∧ t ≤ deadline ∧ StrongServed R S E rho O T I pair Jst leaseSlots m t

/-- Blueprint 21 HG.3. DC: SAME the public conclusion interface. -/
theorem FrontierHG3Result_def (i m : Nat) (start deadline : Time) :
    FrontierHG3Result R S E rho O T I pair Jst leaseSlots i m start deadline ↔
  FirstPhaseStopBy R E rho O i m deadline ∨
  FirstRiseStopBy R E rho O i m deadline ∨
  ∃ t, start ≤ t ∧ t ≤ deadline ∧ StrongServed R S E rho O T I pair Jst leaseSlots m t := Iff.rfl

def interruptedRepairBudget (G ΔF ρbar : Time) (kind : PhaseKind) : Time :=
  match kind with
  | .gap => E_gF T ΔF G ρbar
  | .topJ => E_jF T ΔF G ρbar
  | .contest => ρbar + 3 * T.delta

/-- Blueprint 21 HG.3. DC: SAME gap deadline. -/
theorem interruptedRepairBudget_gap_def (G ΔF ρbar : Time) :
    interruptedRepairBudget T G ΔF ρbar .gap = E_gF T ΔF G ρbar := by rfl

/-- Blueprint 21 HG.3. DC: SAME top-J deadline, including epsF. -/
theorem interruptedRepairBudget_topJ_def (G ΔF ρbar : Time) :
    interruptedRepairBudget T G ΔF ρbar .topJ = E_jF T ΔF G ρbar := by rfl

/-- Blueprint 21 HG.3. DC: SAME contest deadline. -/
theorem interruptedRepairBudget_contest_def (G ΔF ρbar : Time) :
    interruptedRepairBudget T G ΔF ρbar .contest = ρbar + 3 * T.delta := by rfl

/-- Blueprint 21 H.10; plan gap 6.
DC: SAME the first actual effective event strictly after the start index. -/
def FirstEffectiveBy (i : Nat) (deadline : Time) : Prop :=
  ∃ j ev, i < j ∧ rho.events[j]? = some ev ∧ ev.time ≤ deadline ∧
    EffectiveEvent R E rho O j ∧
    (∀ k, i < k → k < j → ¬ EffectiveEvent R E rho O k)

/-- Blueprint 21 H.10; plan gap 6. DC: SAME actual first-event interface. -/
theorem FirstEffectiveBy_def (i : Nat) (deadline : Time) :
    FirstEffectiveBy R E rho O i deadline ↔
  ∃ j ev, i < j ∧ rho.events[j]? = some ev ∧ ev.time ≤ deadline ∧
    EffectiveEvent R E rho O j ∧
    (∀ k, i < k → k < j → ¬ EffectiveEvent R E rho O k) := Iff.rfl

/-- Blueprint 21 HG.1 and HG.4; plan §4.
DC: SAME a first frontier rise. Same-frontier events are permitted before it. -/
def FrontierRiseBy (i m : Nat) (deadline : Time) : Prop :=
  ∃ j ev, i < j ∧ rho.events[j]? = some ev ∧ ev.time ≤ deadline ∧
    m < frontierAtIdx R E rho (j + 1) ∧
    (∀ k, i + 1 ≤ k → k ≤ j → frontierAtIdx R E rho k ≤ m)

/-- Blueprint 21 HG.1/HG.4. DC: SAME first-rise interface. -/
theorem FrontierRiseBy_def (i m : Nat) (deadline : Time) :
    FrontierRiseBy R E rho i m deadline ↔
  ∃ j ev, i < j ∧ rho.events[j]? = some ev ∧ ev.time ≤ deadline ∧
    m < frontierAtIdx R E rho (j + 1) ∧
    (∀ k, i + 1 ≤ k → k ≤ j → frontierAtIdx R E rho k ≤ m) := Iff.rfl

/-- Blueprint 21 HG.4--HG.5 and H.11.
DC: SAME actual first honest row, including an earlier SO-COV emission. -/
def FirstHeightRowBy (m : Nat) (deadline : Time) : Prop :=
  ∃ r, HeightRow S E rho T (fun a => namedEntry (pair a)) r m ∧
    (∀ r', HeightRow S E rho T (fun a => namedEntry (pair a)) r' m → r ≤ r') ∧ T.action r ≤ deadline

/-- Blueprint 21 HG.4/H.11. DC: SAME first-row interface. -/
theorem FirstHeightRowBy_def (m : Nat) (deadline : Time) :
    FirstHeightRowBy S E rho T pair m deadline ↔
  ∃ r, HeightRow S E rho T (fun a => namedEntry (pair a)) r m ∧
    (∀ r', HeightRow S E rho T (fun a => namedEntry (pair a)) r' m → r ≤ r') ∧
    T.action r ≤ deadline := Iff.rfl

/-- Blueprint 21 HG.3; plan §3.3.
DC: SAME generic event start, full phase deadline and complete horizon guard. -/
def InterruptedRepairStatement (G ΔF ρbar : Time) : Prop :=
  deltaT = 2 * T.roundSlots → LivenessBoundW T ΔF →
  ∀ i ev m kind, FrontierSearchStart R E rho O T Jst i ev m kind →
    FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar (ev.time + 3 * T.delta) →
    ev.time + interruptedRepairBudget T G ΔF ρbar kind ≤ rho.horizon →
    FirstEffectiveBy R E rho O i
      (ev.time + interruptedRepairBudget T G ΔF ρbar kind) ∨
    FrontierRiseBy R E rho i m
      (ev.time + interruptedRepairBudget T G ΔF ρbar kind) ∨
    (∃ t, ev.time ≤ t ∧ t ≤ ev.time + interruptedRepairBudget T G ΔF ρbar kind ∧
      StrongServed R S E rho O T I pair Jst leaseSlots m t)

/-- Blueprint 21 HG.4; plan §3.3.
DC: SAME two independently guarded tasks from the current served start.
There is no no-effective-event premise and no second repair allowance. -/
def FrontierTailStatement (G ΔF : Time) : Prop :=
  deltaT = 2 * T.roundSlots → LivenessBoundW T ΔF →
  ∀ i ev m kind, FrontierSearchStart R E rho O T Jst i ev m kind →
    StrongServed R S E rho O T I pair Jst leaseSlots m ev.time →
    (ev.time + (2 * FGCompose.P T + Γ T G - 9 * T.delta) ≤ rho.horizon →
      FrontierRiseBy R E rho i m (ev.time + (2 * FGCompose.P T + Γ T G - 9 * T.delta))) ∧
    (ev.time + (FGCompose.P T - 4 * T.delta) ≤ rho.horizon →
      FirstHeightRowBy S E rho T pair m (ev.time + (FGCompose.P T - 4 * T.delta)))

/-- Blueprint 21 HG.5; plan §3.3.
DC: SAME one-frontier rise task, before the H.11 second task. -/
def frontierSearchRiseBudget (G ΔF ρbar : Time) : Time :=
  E_gF T ΔF G ρbar + E_jF T ΔF G ρbar + B_cF T ΔF G ρbar

/-- Blueprint 21 HG.5; plan §3.3.
DC: SAME one-frontier first-row task. -/
def frontierSearchRowBudget (G ΔF ρbar : Time) : Time :=
  E_gF T ΔF G ρbar + E_jF T ΔF G ρbar + D_cF T ρbar

/-- Blueprint 21 HG.5/H.11; plan §3.3.
DC: SAME inline cut/frontier/row cap. The second task is at M+1.
One rStar is quantified before both allowances, with each full horizon guard.
The first task also has its own independent rise horizon guard.
No reset witness, phase package, or downstream healing service is assumed. -/
def FrontierSearchStatement (G ΔF : Time) : Prop :=
  deltaT = 2 * T.roundSlots → LivenessBoundW T ΔF →
  ∀ rG u₀ M, Jst ≤ T.action rG →
    (∀ r, Jst ≤ T.action r → rG ≤ r) → u₀ = T.action (rG + 2) →
    Jst + 2 * FGCompose.P T ≤ u₀ → M = honestFrontier R E rho u₀ →
    (∀ j y r a h e t, HonestRowAt S E rho T j y r a →
      rho.events[j]? = some (.tick y t) → t ≤ u₀ →
      namedEntry (pair a) = some (h, e) → h ≤ M) →
    (∀ ρbar, (FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar u₀) →
      u₀ + frontierSearchRiseBudget T G ΔF ρbar ≤ rho.horizon →
      ∃ j ev, timeIdx rho u₀ ≤ j ∧ rho.events[j]? = some ev ∧
        ev.time ≤ u₀ + frontierSearchRiseBudget T G ΔF ρbar ∧
        M < frontierAtIdx R E rho (j + 1) ∧
        (∀ k, timeIdx rho u₀ ≤ k → k ≤ j → frontierAtIdx R E rho k ≤ M)) ∧
    ((∃ ρbar, (FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar u₀) ∧
      u₀ + frontierSearchRiseBudget T G ΔF ρbar +
        frontierSearchRowBudget T G ΔF ρbar ≤ rho.horizon) →
    ∃ rStar, HeightRow S E rho T (fun a => namedEntry (pair a)) rStar (M + 1) ∧
      (∀ r, HeightRow S E rho T (fun a => namedEntry (pair a)) r (M + 1) → rStar ≤ r) ∧
      ∀ ρbar, (FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar u₀) →
        u₀ + frontierSearchRiseBudget T G ΔF ρbar +
          frontierSearchRowBudget T G ΔF ρbar ≤ rho.horizon →
        ∃ j ev, timeIdx rho u₀ ≤ j ∧ rho.events[j]? = some ev ∧
          ev.time ≤ u₀ + frontierSearchRiseBudget T G ΔF ρbar ∧
          M < frontierAtIdx R E rho (j + 1) ∧
          (∀ k, timeIdx rho u₀ ≤ k → k ≤ j → frontierAtIdx R E rho k ≤ M) ∧
          T.action rStar ≤ ev.time + frontierSearchRowBudget T G ΔF ρbar)

/-- Blueprint 21:1695–1800; S5 F2, full HG.4.
DC: SAME expose the frozen conclusion contract for its producer. -/
theorem FrontierTailStatement_def (G ΔF : Time) :
    FrontierTailStatement R S E rho O T I pair Jst leaseSlots deltaT G ΔF ↔
  deltaT = 2 * T.roundSlots → LivenessBoundW T ΔF →
  ∀ i ev m kind, FrontierSearchStart R E rho O T Jst i ev m kind →
    StrongServed R S E rho O T I pair Jst leaseSlots m ev.time →
    (ev.time + (2 * FGCompose.P T + Γ T G - 9 * T.delta) ≤ rho.horizon →
      FrontierRiseBy R E rho i m (ev.time + (2 * FGCompose.P T + Γ T G - 9 * T.delta))) ∧
    (ev.time + (FGCompose.P T - 4 * T.delta) ≤ rho.horizon →
      FirstHeightRowBy S E rho T pair m (ev.time + (FGCompose.P T - 4 * T.delta))) := Iff.rfl

/-- Blueprint 21:1695–1800; S5 F3, full HG.5.
DC: SAME expose the frozen conclusion contract for its producer. -/
theorem FrontierSearchStatement_def (G ΔF : Time) :
    FrontierSearchStatement R S E rho O T I pair Jst leaseSlots deltaT G ΔF ↔
  deltaT = 2 * T.roundSlots → LivenessBoundW T ΔF →
  ∀ rG u₀ M, Jst ≤ T.action rG →
    (∀ r, Jst ≤ T.action r → rG ≤ r) → u₀ = T.action (rG + 2) →
    Jst + 2 * FGCompose.P T ≤ u₀ → M = honestFrontier R E rho u₀ →
    (∀ j y r a h e t, HonestRowAt S E rho T j y r a →
      rho.events[j]? = some (.tick y t) → t ≤ u₀ →
      namedEntry (pair a) = some (h, e) → h ≤ M) →
    (∀ ρbar, (FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar u₀) →
      u₀ + frontierSearchRiseBudget T G ΔF ρbar ≤ rho.horizon →
      ∃ j ev, timeIdx rho u₀ ≤ j ∧ rho.events[j]? = some ev ∧
        ev.time ≤ u₀ + frontierSearchRiseBudget T G ΔF ρbar ∧
        M < frontierAtIdx R E rho (j + 1) ∧
        (∀ k, timeIdx rho u₀ ≤ k → k ≤ j → frontierAtIdx R E rho k ≤ M)) ∧
    ((∃ ρbar, (FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar u₀) ∧
      u₀ + frontierSearchRiseBudget T G ΔF ρbar +
        frontierSearchRowBudget T G ΔF ρbar ≤ rho.horizon) →
    ∃ rStar, HeightRow S E rho T (fun a => namedEntry (pair a)) rStar (M + 1) ∧
      (∀ r, HeightRow S E rho T (fun a => namedEntry (pair a)) r (M + 1) → rStar ≤ r) ∧
      ∀ ρbar, (FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar u₀) →
        u₀ + frontierSearchRiseBudget T G ΔF ρbar +
          frontierSearchRowBudget T G ΔF ρbar ≤ rho.horizon →
        ∃ j ev, timeIdx rho u₀ ≤ j ∧ rho.events[j]? = some ev ∧
          ev.time ≤ u₀ + frontierSearchRiseBudget T G ΔF ρbar ∧
          M < frontierAtIdx R E rho (j + 1) ∧
          (∀ k, timeIdx rho u₀ ≤ k → k ≤ j → frontierAtIdx R E rho k ≤ M) ∧
          T.action rStar ≤ ev.time + frontierSearchRowBudget T G ΔF ρbar) := Iff.rfl

/-- Blueprint 21:1722–1800; S5 F3.
DC: SAME expose the frozen rise budget for arithmetic composition. -/
theorem frontierSearchRiseBudget_def (G ΔF ρbar : Time) :
    frontierSearchRiseBudget T G ΔF ρbar =
      E_gF T ΔF G ρbar + E_jF T ΔF G ρbar + B_cF T ΔF G ρbar := by
  exact Eq.refl _

/-- Blueprint 21:1722–1800; S5 F3.
DC: SAME expose the frozen row budget for arithmetic composition. -/
theorem frontierSearchRowBudget_def (G ΔF ρbar : Time) :
    frontierSearchRowBudget T G ΔF ρbar =
      E_gF T ΔF G ρbar + E_jF T ΔF G ρbar + D_cF T ρbar := by
  exact Eq.refl _


/-- Each frontier has at most these three phase charges. -/
def frontierSearch_phaseRank (kind : PhaseKind) : Nat :=
  match kind with | .gap => 0 | .topJ => 1 | .contest => 2

theorem frontierSearch_phaseRank_gap_def : frontierSearch_phaseRank .gap = 0 := rfl
theorem frontierSearch_phaseRank_topJ_def : frontierSearch_phaseRank .topJ = 1 := rfl
theorem frontierSearch_phaseRank_contest_def : frontierSearch_phaseRank .contest = 2 := rfl

/-- Blueprint 21:1722–1800; S5 F3 (FrontierSearchCompose:110).
DC: SAME the unused phase charges remain available until the terminal tail. -/
def frontierSearch_remaining (G ΔF ρbar tail : Time) (kind : PhaseKind) : Time :=
  (if frontierSearch_phaseRank kind = 0 then E_gF T ΔF G ρbar else 0) +
    (if frontierSearch_phaseRank kind = 2 then 0 else E_jF T ΔF G ρbar) +
    (ρbar + 3 * T.delta + tail)

/-- Blueprint 21:1722–1800; S5 F3. DC: SAME the arithmetic form (F-28 name). -/
theorem frontierSearch_remaining_def (G ΔF ρbar tail : Time) (kind : PhaseKind) :
    frontierSearch_remaining T G ΔF ρbar tail kind =
      (if frontierSearch_phaseRank kind = 0 then E_gF T ΔF G ρbar else 0) +
        (if frontierSearch_phaseRank kind = 2 then 0 else E_jF T ΔF G ρbar) +
        (ρbar + 3 * T.delta + tail) := rfl

/-! Start-family companion of `FrontierSearchStatement` (additive; lead ruling 2026-10-13).
The landed statement gives the repair allowance at the cut only. The phase tail reads it
at every actual phase start. This form fixes one allowance value and takes the semantic
allowance at `ev.time + 3Δ` for every actual start after `Jst + 2P`. The conclusion reads
only the nonnegativity of the allowance at the cut. The first row is the least one, so it
does not depend on the allowance. -/

/-- Blueprint 21 HG.5/H.11; plan §3.3.
DC: SAME the search conclusion of `FrontierSearchStatement` for one allowance value, under
the allowance at every actual phase start. Both complete horizon guards are retained. -/
def FrontierSearchFamilyStatement (G ΔF ρbar : Time) : Prop :=
  deltaT = 2 * T.roundSlots → LivenessBoundW T ΔF → 0 ≤ ρbar →
  (∀ i ev m kind, FrontierSearchStart R E rho O T Jst i ev m kind →
    Jst + 2 * FGCompose.P T ≤ ev.time →
    FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar (ev.time + 3 * T.delta)) →
  ∀ rG u₀ M, Jst ≤ T.action rG →
    (∀ r, Jst ≤ T.action r → rG ≤ r) → u₀ = T.action (rG + 2) →
    Jst + 2 * FGCompose.P T ≤ u₀ → M = honestFrontier R E rho u₀ →
    (∀ j y r a h e t, HonestRowAt S E rho T j y r a →
      rho.events[j]? = some (.tick y t) → t ≤ u₀ →
      namedEntry (pair a) = some (h, e) → h ≤ M) →
    (u₀ + frontierSearchRiseBudget T G ΔF ρbar ≤ rho.horizon →
      ∃ j ev, timeIdx rho u₀ ≤ j ∧ rho.events[j]? = some ev ∧
        ev.time ≤ u₀ + frontierSearchRiseBudget T G ΔF ρbar ∧
        M < frontierAtIdx R E rho (j + 1) ∧
        (∀ k, timeIdx rho u₀ ≤ k → k ≤ j → frontierAtIdx R E rho k ≤ M)) ∧
    (u₀ + frontierSearchRiseBudget T G ΔF ρbar +
        frontierSearchRowBudget T G ΔF ρbar ≤ rho.horizon →
      ∃ rStar, HeightRow S E rho T (fun a => namedEntry (pair a)) rStar (M + 1) ∧
        (∀ r, HeightRow S E rho T (fun a => namedEntry (pair a)) r (M + 1) → rStar ≤ r) ∧
        ∃ j ev, timeIdx rho u₀ ≤ j ∧ rho.events[j]? = some ev ∧
          ev.time ≤ u₀ + frontierSearchRiseBudget T G ΔF ρbar ∧
          M < frontierAtIdx R E rho (j + 1) ∧
          (∀ k, timeIdx rho u₀ ≤ k → k ≤ j → frontierAtIdx R E rho k ≤ M) ∧
          T.action rStar ≤ ev.time + frontierSearchRowBudget T G ΔF ρbar)

/-- Blueprint 21 HG.5/H.11. DC: SAME expose the companion contract for its producer. -/
theorem FrontierSearchFamilyStatement_def (G ΔF ρbar : Time) :
    FrontierSearchFamilyStatement R S E rho O T I pair Jst leaseSlots deltaT G ΔF ρbar ↔
  deltaT = 2 * T.roundSlots → LivenessBoundW T ΔF → 0 ≤ ρbar →
  (∀ i ev m kind, FrontierSearchStart R E rho O T Jst i ev m kind →
    Jst + 2 * FGCompose.P T ≤ ev.time →
    FrontierRepairAllowance R E rho O T I Jst leaseSlots G ρbar (ev.time + 3 * T.delta)) →
  ∀ rG u₀ M, Jst ≤ T.action rG →
    (∀ r, Jst ≤ T.action r → rG ≤ r) → u₀ = T.action (rG + 2) →
    Jst + 2 * FGCompose.P T ≤ u₀ → M = honestFrontier R E rho u₀ →
    (∀ j y r a h e t, HonestRowAt S E rho T j y r a →
      rho.events[j]? = some (.tick y t) → t ≤ u₀ →
      namedEntry (pair a) = some (h, e) → h ≤ M) →
    (u₀ + frontierSearchRiseBudget T G ΔF ρbar ≤ rho.horizon →
      ∃ j ev, timeIdx rho u₀ ≤ j ∧ rho.events[j]? = some ev ∧
        ev.time ≤ u₀ + frontierSearchRiseBudget T G ΔF ρbar ∧
        M < frontierAtIdx R E rho (j + 1) ∧
        (∀ k, timeIdx rho u₀ ≤ k → k ≤ j → frontierAtIdx R E rho k ≤ M)) ∧
    (u₀ + frontierSearchRiseBudget T G ΔF ρbar +
        frontierSearchRowBudget T G ΔF ρbar ≤ rho.horizon →
      ∃ rStar, HeightRow S E rho T (fun a => namedEntry (pair a)) rStar (M + 1) ∧
        (∀ r, HeightRow S E rho T (fun a => namedEntry (pair a)) r (M + 1) → rStar ≤ r) ∧
        ∃ j ev, timeIdx rho u₀ ≤ j ∧ rho.events[j]? = some ev ∧
          ev.time ≤ u₀ + frontierSearchRiseBudget T G ΔF ρbar ∧
          M < frontierAtIdx R E rho (j + 1) ∧
          (∀ k, timeIdx rho u₀ ≤ k → k ≤ j → frontierAtIdx R E rho k ≤ M) ∧
          T.action rStar ≤ ev.time + frontierSearchRowBudget T G ΔF ρbar) := Iff.rfl

end AvailableChain.FGCompose
end
