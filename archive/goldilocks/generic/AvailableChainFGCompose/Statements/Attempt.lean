module
public import AvailableChainFGCompose.Statements.PhaseReceipts -- shake: keep (receipt contract API)
public import AvailableChainFGCompose.Statements.Promotion

@[expose] public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG

/-- The two tasks in the frozen attempt table. -/
inductive AttemptTask | raise | firstRow

/-- The start is an event index. Its resulting prefix is start + 1. -/
structure AttemptKey where
  start : Nat
  frontier : Nat
  phase : PhaseKind
  task : AttemptTask
  served : Bool

/-- Protocol observations for exact gate service. These are reads, not service laws. -/
structure FGAttemptGateReads {In : Type} (P : V2.ProtocolSpecD In) where
  restartTime : P.State → Option Time
  preClock : P.State → Time → P.State
  saved : P.State → Slot → Option Block
  confirmation : P.State → Slot → Option Block
  blocked : P.State → Block → Bool
  writes : P.State → Slot → Option (List Block)

variable {In V : Type} {Prot : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads Prot n Base Proposal Wire) (S : FGSafetyReads Prot n Wire)
variable (E : Generic.Env V) (rho : V2.D.Run V Prot)
variable (O : FGObservationReads R) (T : FGTiming) (I : V2.D.Interface Prot)
variable (A : FGAttemptGateReads Prot) (pair : Wire → NamedHeightPair) (Jst : Time)

/-- Joined scope at the actual duty, including wake and restart cuts. -/
def AttemptJoinedAt (x : V) (s : Slot) (t : Time) : Prop :=
  E.awake x t = true ∧
  (∀ u, 0 < u → u ≤ t → V2.D.Wakes E x u → u ≤ slotStartZ T ((s : Int) - 1)) ∧
  (∀ u, 0 ≤ u → u ≤ t → V2.Event.restart x u ∈ rho.events →
    u ≤ slotStartZ T ((s : Int) - 1))

omit [DecidableEq V] in
theorem p0d4_AttemptJoinedAt_def (x : V) (s : Slot) (t : Time) :
    AttemptJoinedAt E rho T x s t = (
E.awake x t = true ∧
  (∀ u, 0 < u → u ≤ t → V2.D.Wakes E x u → u ≤ slotStartZ T ((s : Int) - 1)) ∧
  (∀ u, 0 ≤ u → u ≤ t → V2.Event.restart x u ∈ rho.events →
    u ≤ slotStartZ T ((s : Int) - 1))
    ) := rfl

/-- Enabled gate at its original event index. -/
def AttemptEnabledGate (j : Nat) (x : V) (s : Slot) : Prop :=
  rho.events[j]? = some (.tick x (T.gate s)) ∧
  match A.restartTime (rho.stateBefore E j x) with
  | none => True
  | some w => w ≤ slotStartZ T s

theorem p0d4_AttemptEnabledGate_def (j : Nat) (x : V) (s : Slot) :
    AttemptEnabledGate E rho T A j x s = (
rho.events[j]? = some (.tick x (T.gate s)) ∧
  match A.restartTime (rho.stateBefore E j x) with
  | none => True
  | some w => w ≤ slotStartZ T s
    ) := rfl

/-- The guard reads the pre-gate state. It keeps the original successful result. -/
def AttemptGatePassed (j : Nat) : Prop := ∃ x s,
  AttemptEnabledGate E rho T A j x s ∧
  let nd := A.preClock (rho.stateBefore E j x) (T.gate s)
  A.saved nd s = none ∧ ∃ B, A.confirmation nd s = some B ∧ A.blocked nd B = false

theorem p0d4_AttemptGatePassed_def (j : Nat) :
    AttemptGatePassed E rho T A j = (
∃ x s,
  AttemptEnabledGate E rho T A j x s ∧
  let nd := A.preClock (rho.stateBefore E j x) (T.gate s)
  A.saved nd s = none ∧ ∃ B, A.confirmation nd s = some B ∧ A.blocked nd B = false
    ) := rfl

/-- Caught-up readers retain the same earlier gate and awake interval. -/
def AttemptCaughtUp (x : V) (i : Nat) (t : Time) : Prop :=
  E.awake x t = true ∧
  match A.restartTime (rho.stateBefore E i x) with
  | none => True
  | some w => ∃ (s : Slot) (j : Nat), w ≤ slotStartZ T s ∧ T.gate s ≤ t ∧ j < i ∧
      AttemptEnabledGate E rho T A j x s ∧
      (∀ u, 0 ≤ u → slotStartZ T s ≤ u → u ≤ t → E.awake x u = true) ∧
      (∀ u, slotStartZ T s < u → u ≤ t → V2.Event.restart x u ∉ rho.events)

theorem p0d4_AttemptCaughtUp_def (x : V) (i : Nat) (t : Time) :
    AttemptCaughtUp E rho T A x i t = (
E.awake x t = true ∧
  match A.restartTime (rho.stateBefore E i x) with
  | none => True
  | some w => ∃ (s : Slot) (j : Nat), w ≤ slotStartZ T s ∧ T.gate s ≤ t ∧ j < i ∧
      AttemptEnabledGate E rho T A j x s ∧
      (∀ u, 0 ≤ u → slotStartZ T s ≤ u → u ≤ t → E.awake x u = true) ∧
      (∀ u, slotStartZ T s < u → u ≤ t → V2.Event.restart x u ∉ rho.events)
    ) := rfl

/-- The raw gate observation keeps both Option levels. -/
def AttemptGateResult (x : V) (s : Slot) : Option (Option Block) :=
  (preTick E rho x (T.gate s)).map fun nd =>
    let nd := A.preClock nd (T.gate s)
    match A.restartTime nd with
    | none => A.confirmation nd s
    | some w => if w ≤ slotStartZ T s then A.confirmation nd s else none

theorem p0d4_AttemptGateResult_def (x : V) (s : Slot) :
    AttemptGateResult E rho T A x s = (
(preTick E rho x (T.gate s)).map fun nd =>
    let nd := A.preClock nd (T.gate s)
    match A.restartTime nd with
    | none => A.confirmation nd s
    | some w => if w ≤ slotStartZ T s then A.confirmation nd s else none
    ) := rfl

/-- Full exact service: HEAD, raw gate, guard, write, stable output, and opening source. -/
def AttemptExactService (s : Slot) (Q : Block) : Prop :=
  (T.vote s ≤ rho.horizon → ∀ x ∈ rho.honest,
    AttemptJoinedAt E rho T x s (T.vote s) → headAtLabel R E rho T x s = some Q) ∧
  (T.gate s ≤ rho.horizon → ∀ x ∈ rho.honest,
    (x ∈ rho.honest ∧ AttemptCaughtUp E rho T A x
      (afterTicksIdx rho (T.gate s)) (T.gate s)) →
    AttemptGateResult E rho T A x s = some (some Q) ∧
    (∃ j, AttemptEnabledGate E rho T A j x s ∧ AttemptGatePassed E rho T A j) ∧
    (∃ nd, postClock E rho x (T.gate s) = some nd ∧ Q ∈ (A.writes nd s).getD []) ∧
    I.stable (afterTicks E rho (T.gate s) x) = Q ∧
    (∀ r, s = r * T.roundSlots →
      (actionSourceFG R E rho T x r).map (Option.map R.erase) = some (some Q)))

theorem p0d4_AttemptExactService_def (s : Slot) (Q : Block) :
    AttemptExactService R E rho T I A s Q = (
(T.vote s ≤ rho.horizon → ∀ x ∈ rho.honest,
    AttemptJoinedAt E rho T x s (T.vote s) → headAtLabel R E rho T x s = some Q) ∧
  (T.gate s ≤ rho.horizon → ∀ x ∈ rho.honest,
    (x ∈ rho.honest ∧ AttemptCaughtUp E rho T A x
      (afterTicksIdx rho (T.gate s)) (T.gate s)) →
    AttemptGateResult E rho T A x s = some (some Q) ∧
    (∃ j, AttemptEnabledGate E rho T A j x s ∧ AttemptGatePassed E rho T A j) ∧
    (∃ nd, postClock E rho x (T.gate s) = some nd ∧ Q ∈ (A.writes nd s).getD []) ∧
    I.stable (afterTicks E rho (T.gate s) x) = Q ∧
    (∀ r, s = r * T.roundSlots →
      (actionSourceFG R E rho T x r).map (Option.map R.erase) = some (some Q)))
    ) := rfl

/-- A served frontier uses a real named proposal and its complete exact service. -/
def ServedFrontier (m : Nat) (t : Time) : Prop := ∃ s Q Qfg,
  HonestProposal E rho I s Q ∧ R.erase Qfg = Q ∧ (O.height Qfg).h = m ∧
  T.gate s ≤ t ∧ AttemptExactService R E rho T I A s Q

theorem p0d4_ServedFrontier_def (m : Nat) (t : Time) :
    ServedFrontier R E rho O T I A m t = (
∃ s Q Qfg,
  HonestProposal E rho I s Q ∧ R.erase Qfg = Q ∧ (O.height Qfg).h = m ∧
  T.gate s ≤ t ∧ AttemptExactService R E rho T I A s Q
    ) := rfl

/-- Both frozen start alternatives and the actual post-event phase are retained. -/
def AttemptValid (k : AttemptKey) : Prop := ∃ ev,
  rho.events[k.start]? = some ev ∧ Jst ≤ ev.time ∧
  (EffectiveEvent R E rho O k.start ∨ ∃ rG, Jst ≤ T.action rG ∧
    (∀ r, Jst ≤ T.action r → rG ≤ r) ∧ ev.time = T.action (rG + 2) ∧
    timeIdx rho (T.action (rG + 2)) = k.start + 1) ∧
  k.frontier = frontierAtIdx R E rho (k.start + 1) ∧ 1 ≤ k.frontier ∧
  AttemptPhaseAt R E rho O (k.start + 1) k.frontier k.phase ∧
  (k.served = true ↔ ServedFrontier R E rho O T I A k.frontier ev.time) ∧
  (k.task = .firstRow → ∀ j y r a h e, j ≤ k.start → HonestRowAt S E rho T j y r a →
    namedEntry (pair a) = some (h, e) → h ≠ k.frontier)

theorem p0d4_AttemptValid_def (k : AttemptKey) :
    AttemptValid R S E rho O T I A pair Jst k = (
∃ ev,
  rho.events[k.start]? = some ev ∧ Jst ≤ ev.time ∧
  (EffectiveEvent R E rho O k.start ∨ ∃ rG, Jst ≤ T.action rG ∧
    (∀ r, Jst ≤ T.action r → rG ≤ r) ∧ ev.time = T.action (rG + 2) ∧
    timeIdx rho (T.action (rG + 2)) = k.start + 1) ∧
  k.frontier = frontierAtIdx R E rho (k.start + 1) ∧ 1 ≤ k.frontier ∧
  AttemptPhaseAt R E rho O (k.start + 1) k.frontier k.phase ∧
  (k.served = true ↔ ServedFrontier R E rho O T I A k.frontier ev.time) ∧
  (k.task = .firstRow → ∀ j y r a h e, j ≤ k.start → HonestRowAt S E rho T j y r a →
    namedEntry (pair a) = some (h, e) → h ≠ k.frontier)
    ) := rfl

/-- The repair allowance is explicit. The old protocol budget remains unchanged. -/
def attemptBudget (T : FGTiming) (G repairAllowance : Time) (k : AttemptKey) : Time :=
  match k.task, k.phase with
  | .raise, .contest => repairAllowance + 3 * FGCompose.P T + Γ T G - 10 * T.delta
  | .raise, _ => repairAllowance + 6 * FGCompose.P T + 2 * Γ T G - 18 * T.delta
  | .firstRow, .contest => repairAllowance + FGCompose.P T - T.delta
  | .firstRow, _ => repairAllowance + 4 * FGCompose.P T + Γ T G - 9 * T.delta

theorem p0d4_attemptBudget_def (T : FGTiming) (G repairAllowance : Time) (k : AttemptKey) :
    attemptBudget T G repairAllowance k = (
match k.task, k.phase with
  | .raise, .contest => repairAllowance + 3 * FGCompose.P T + Γ T G - 10 * T.delta
  | .raise, _ => repairAllowance + 6 * FGCompose.P T + 2 * Γ T G - 18 * T.delta
  | .firstRow, .contest => repairAllowance + FGCompose.P T - T.delta
  | .firstRow, _ => repairAllowance + 4 * FGCompose.P T + Γ T G - 9 * T.delta
    ) := rfl

/-- Stop at a strictly later event, by a phase event or the completed task. -/
def AttemptEndsBy (k : AttemptKey) (budget : Time) : Prop := ∃ ev,
  rho.events[k.start]? = some ev ∧ ∃ j ev', k.start < j ∧
  rho.events[j]? = some ev' ∧ ev'.time ≤ ev.time + budget ∧
  (EffectiveEvent R E rho O j ∨
    (k.task = .raise ∧ k.frontier < frontierAtIdx R E rho (j + 1)) ∨
    (k.task = .firstRow ∧ ∃ y r a e, HonestRowAt S E rho T j y r a ∧
      namedEntry (pair a) = some (k.frontier, e)))

theorem p0d4_AttemptEndsBy_def (k : AttemptKey) (budget : Time) :
    AttemptEndsBy R S E rho O T pair k budget = (
∃ ev,
  rho.events[k.start]? = some ev ∧ ∃ j ev', k.start < j ∧
  rho.events[j]? = some ev' ∧ ev'.time ≤ ev.time + budget ∧
  (EffectiveEvent R E rho O j ∨
    (k.task = .raise ∧ k.frontier < frontierAtIdx R E rho (j + 1)) ∨
    (k.task = .firstRow ∧ ∃ y r a e, HonestRowAt S E rho T j y r a ∧
      namedEntry (pair a) = some (k.frontier, e)))
    ) := rfl

/-- Later repair proposals retain their exact gate service. -/
def AttemptRepairAfter (l : Slot) (v : Time) : Prop := ∀ s Q,
  T.proposal l < T.proposal s → T.gate s ≤ v → HonestProposal E rho I s Q →
  AttemptExactService R E rho T I A s Q

theorem p0d4_AttemptRepairAfter_def (l : Slot) (v : Time) :
    AttemptRepairAfter R E rho T I A l v = (
∀ s Q,
  T.proposal l < T.proposal s → T.gate s ≤ v → HonestProposal E rho I s Q →
  AttemptExactService R E rho T I A s Q
    ) := rfl

/-- The local repair producer, at the first grid point strictly after u. -/
def AttemptRepairService (G repairAllowance : Time) (leaseSlots : Nat) : Prop :=
  4 * T.delta ≤ G → ∀ u v m J contested, Jst ≤ u → PhaseInterval R E rho O u v m J contested →
  ∀ β, u < T.proposal β → (∀ b, u < T.proposal b → β ≤ b) →
    AttemptRepairAfter R E rho T I A (β + 2 * leaseSlots - 1) v ∧
    (u + repairAllowance ≤ v → ∃ s Q,
      T.proposal (β + 2 * leaseSlots - 1) < T.proposal s ∧
      T.gate s ≤ u + repairAllowance ∧ HonestProposal E rho I s Q ∧
      AttemptExactService R E rho T I A s Q)

theorem p0d4_AttemptRepairService_def (G repairAllowance : Time) (leaseSlots : Nat) :
    AttemptRepairService R E rho O T I A Jst G repairAllowance leaseSlots = (
4 * T.delta ≤ G → ∀ u v m J contested, Jst ≤ u → PhaseInterval R E rho O u v m J contested →
  ∀ β, u < T.proposal β → (∀ b, u < T.proposal b → β ≤ b) →
    AttemptRepairAfter R E rho T I A (β + 2 * leaseSlots - 1) v ∧
    (u + repairAllowance ≤ v → ∃ s Q,
      T.proposal (β + 2 * leaseSlots - 1) < T.proposal s ∧
      T.gate s ≤ u + repairAllowance ∧ HonestProposal E rho I s Q ∧
      AttemptExactService R E rho T I A s Q)
    ) := rfl

/-- Selected opening coverage and source transfer at the actual action read. -/
def AttemptOpeningService : Prop :=
  ∀ u m J contested q Q Qfg r, Jst ≤ u → HonestProposal E rho I q Q →
    R.erase Qfg = Q → AttemptExactService R E rho T I A q Q →
    u ≤ T.proposal q → q ≤ r * T.roundSlots →
    PhaseInterval R E rho O u (T.action r) m J contested →
    OpeningCovered R S E rho O.height T pair r Q ∧
    (∀ x K, x ∈ rho.honest → actionSourceFG R E rho T x r = some (some K) →
      FGBlock.Preceq Qfg K ∧ (O.height K).h ≤ m)

theorem p0d4_AttemptOpeningService_def :
    AttemptOpeningService R S E rho O T I A pair Jst = (
∀ u m J contested q Q Qfg r, Jst ≤ u → HonestProposal E rho I q Q →
    R.erase Qfg = Q → AttemptExactService R E rho T I A q Q →
    u ≤ T.proposal q → q ≤ r * T.roundSlots →
    PhaseInterval R E rho O u (T.action r) m J contested →
    OpeningCovered R S E rho O.height T pair r Q ∧
    (∀ x K, x ∈ rho.honest → actionSourceFG R E rho T x r = some (some K) →
      FGBlock.Preceq Qfg K ∧ (O.height K).h ≤ m)
    ) := rfl

/-- Source transfer for the next opening keeps the actual earlier selected source. -/
def AttemptNextOpeningService : Prop :=
  ∀ u m J contested q Q Qfg r, Jst ≤ u → HonestProposal E rho I q Q →
    R.erase Qfg = Q → AttemptExactService R E rho T I A q Q →
    u ≤ T.proposal q → q ≤ r * T.roundSlots →
    PhaseInterval R E rho O u (T.action (r + 1)) m J contested →
    ∀ y K, y ∈ rho.honest → actionSourceFG R E rho T y r = some (some K) →
    ∀ x L, x ∈ rho.honest → actionSourceFG R E rho T x (r + 1) = some (some L) →
      FGBlock.Preceq K L ∧ (O.height L).h ≤ m

theorem p0d4_AttemptNextOpeningService_def :
    AttemptNextOpeningService R E rho O T I A Jst = (
∀ u m J contested q Q Qfg r, Jst ≤ u → HonestProposal E rho I q Q →
    R.erase Qfg = Q → AttemptExactService R E rho T I A q Q →
    u ≤ T.proposal q → q ≤ r * T.roundSlots →
    PhaseInterval R E rho O u (T.action (r + 1)) m J contested →
    ∀ y K, y ∈ rho.honest → actionSourceFG R E rho T y r = some (some K) →
    ∀ x L, x ∈ rho.honest → actionSourceFG R E rho T x (r + 1) = some (some L) →
      FGBlock.Preceq K L ∧ (O.height L).h ≤ m
    ) := rfl

/-- The selected proposal parent obeys the real proposer floor. -/
def AttemptProposalFloor : Prop :=
  ∀ u v m J contested q Q Qfg, Jst ≤ u → PhaseInterval R E rho O u v m J contested →
    u ≤ T.proposal q → T.gate q ≤ v → HonestProposal E rho I q Q → R.erase Qfg = Q →
    (if contested then m else m - 1) ≤ (O.height Qfg.parent).h

theorem p0d4_AttemptProposalFloor_def :
    AttemptProposalFloor R E rho O T I Jst = (
∀ u v m J contested q Q Qfg, Jst ≤ u → PhaseInterval R E rho O u v m J contested →
    u ≤ T.proposal q → T.gate q ≤ v → HonestProposal E rho I q Q → R.erase Qfg = Q →
    (if contested then m else m - 1) ≤ (O.height Qfg.parent).h
    ) := rfl

/-- Exact gate service supplies a held copy at the same gate, within the phase cut. -/
def AttemptGateCopy : Prop :=
  ∀ u v m J contested q Q Qfg, Jst ≤ u → PhaseInterval R E rho O u v m J contested →
    u ≤ T.proposal q → T.gate q ≤ v → HonestProposal E rho I q Q → R.erase Qfg = Q →
    AttemptExactService R E rho T I A q Q → ∃ i x,
      rho.idxBefore u ≤ i ∧ i ≤ timeIdx rho v ∧ x ∈ rho.honest ∧
      Qfg ∈ (R.core (rho.stateBefore E i x)).fg.TF

theorem p0d4_AttemptGateCopy_def :
    AttemptGateCopy R E rho O T I A Jst = (
∀ u v m J contested q Q Qfg, Jst ≤ u → PhaseInterval R E rho O u v m J contested →
    u ≤ T.proposal q → T.gate q ≤ v → HonestProposal E rho I q Q → R.erase Qfg = Q →
    AttemptExactService R E rho T I A q Q → ∃ i x,
      rho.idxBefore u ≤ i ∧ i ≤ timeIdx rho v ∧ x ∈ rho.honest ∧
      Qfg ∈ (R.core (rho.stateBefore E i x)).fg.TF
    ) := rfl

/-- Renewed promotion keeps its earlier event, strict receipt, and conditional gate service. -/
def AttemptRenewedPromotion (G : Time) : Prop :=
  ∀ r, T.action r + 2 * FGCompose.P T + Γ T G - 4 * T.delta ≤ rho.horizon →
  ∀ u m J contested l q Q height, Jst ≤ u →
    PhaseInterval R E rho O u (T.action r) m J contested →
    u ≤ T.proposal q → q ≤ r * T.roundSlots → T.proposal l < T.proposal q →
    HonestProposal E rho I q Q → AttemptExactService R E rho T I A q Q →
    OpeningEntry R E rho O.height T r height → OpeningCovered R S E rho O.height T pair r Q →
    (∀ v, PhaseInterval R E rho O u v m J contested →
      AttemptRepairAfter R E rho T I A l v) →
    (∃ i ev, afterTicksIdx rho (T.action r) ≤ i ∧ rho.events[i]? = some ev ∧
      EffectiveEvent R E rho O i ∧
      ev.time ≤ T.action r + 2 * FGCompose.P T + Γ T G - 9 * T.delta) ∨
    (∃ s X, HonestProposal E rho I s (R.erase X) ∧ X.slot = s ∧
      (r : Time) * FGCompose.P T + 2 * FGCompose.P T ≤ T.proposal s ∧
      T.proposal s ≤ T.action r + 2 * FGCompose.P T + Γ T G - 10 * T.delta ∧
      height + 1 ≤ (O.height X).h ∧
      (∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
        (fun nd => X ∈ (R.core nd).fg.TF) (T.proposal s + T.delta) y) ∧
      (PhaseInterval R E rho O u (T.gate s) m J contested →
        AttemptExactService R E rho T I A s (R.erase X) ∧
        T.gate s ≤ T.action r + 2 * FGCompose.P T + Γ T G - 4 * T.delta))

theorem p0d4_AttemptRenewedPromotion_def (G : Time) :
    AttemptRenewedPromotion R S E rho O T I A pair Jst G = (
∀ r, T.action r + 2 * FGCompose.P T + Γ T G - 4 * T.delta ≤ rho.horizon →
  ∀ u m J contested l q Q height, Jst ≤ u →
    PhaseInterval R E rho O u (T.action r) m J contested →
    u ≤ T.proposal q → q ≤ r * T.roundSlots → T.proposal l < T.proposal q →
    HonestProposal E rho I q Q → AttemptExactService R E rho T I A q Q →
    OpeningEntry R E rho O.height T r height → OpeningCovered R S E rho O.height T pair r Q →
    (∀ v, PhaseInterval R E rho O u v m J contested →
      AttemptRepairAfter R E rho T I A l v) →
    (∃ i ev, afterTicksIdx rho (T.action r) ≤ i ∧ rho.events[i]? = some ev ∧
      EffectiveEvent R E rho O i ∧
      ev.time ≤ T.action r + 2 * FGCompose.P T + Γ T G - 9 * T.delta) ∨
    (∃ s X, HonestProposal E rho I s (R.erase X) ∧ X.slot = s ∧
      (r : Time) * FGCompose.P T + 2 * FGCompose.P T ≤ T.proposal s ∧
      T.proposal s ≤ T.action r + 2 * FGCompose.P T + Γ T G - 10 * T.delta ∧
      height + 1 ≤ (O.height X).h ∧
      (∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
        (fun nd => X ∈ (R.core nd).fg.TF) (T.proposal s + T.delta) y) ∧
      (PhaseInterval R E rho O u (T.gate s) m J contested →
        AttemptExactService R E rho T I A s (R.erase X) ∧
        T.gate s ≤ T.action r + 2 * FGCompose.P T + Γ T G - 4 * T.delta))
    ) := rfl

/-- Terminal promotion uses the earlier event alternative or a strict held receipt. -/
def AttemptTerminalPromotion (G : Time) : Prop :=
  ∀ r, T.action r + 2 * FGCompose.P T + Γ T G - 9 * T.delta ≤ rho.horizon →
  ∀ u m J contested q Q height, Jst ≤ u →
    PhaseInterval R E rho O u (T.action r) m J contested →
    u ≤ T.proposal q → q ≤ r * T.roundSlots →
    OpeningEntry R E rho O.height T r height → OpeningCovered R S E rho O.height T pair r Q →
    (∃ i ev, afterTicksIdx rho (T.action r) ≤ i ∧ rho.events[i]? = some ev ∧
      EffectiveEvent R E rho O i ∧
      ev.time ≤ T.action r + 2 * FGCompose.P T + Γ T G - 9 * T.delta) ∨
    (∃ s X, HonestProposal E rho I s (R.erase X) ∧ X.slot = s ∧
      (r : Time) * FGCompose.P T + 2 * FGCompose.P T ≤ T.proposal s ∧
      T.proposal s ≤ T.action r + 2 * FGCompose.P T + Γ T G - 10 * T.delta ∧
      height + 1 ≤ (O.height X).h ∧
      (∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
        (fun nd => X ∈ (R.core nd).fg.TF) (T.proposal s + T.delta) y))

theorem p0d4_AttemptTerminalPromotion_def (G : Time) :
    AttemptTerminalPromotion R S E rho O T I pair Jst G = (
∀ r, T.action r + 2 * FGCompose.P T + Γ T G - 9 * T.delta ≤ rho.horizon →
  ∀ u m J contested q Q height, Jst ≤ u →
    PhaseInterval R E rho O u (T.action r) m J contested →
    u ≤ T.proposal q → q ≤ r * T.roundSlots →
    OpeningEntry R E rho O.height T r height → OpeningCovered R S E rho O.height T pair r Q →
    (∃ i ev, afterTicksIdx rho (T.action r) ≤ i ∧ rho.events[i]? = some ev ∧
      EffectiveEvent R E rho O i ∧
      ev.time ≤ T.action r + 2 * FGCompose.P T + Γ T G - 9 * T.delta) ∨
    (∃ s X, HonestProposal E rho I s (R.erase X) ∧ X.slot = s ∧
      (r : Time) * FGCompose.P T + 2 * FGCompose.P T ≤ T.proposal s ∧
      T.proposal s ≤ T.action r + 2 * FGCompose.P T + Γ T G - 10 * T.delta ∧
      height + 1 ≤ (O.height X).h ∧
      (∃ y, y ∈ rho.honest ∧ Gen.V2.Duty.HoldsBefore E rho
        (fun nd => X ∈ (R.core nd).fg.TF) (T.proposal s + T.delta) y))
    ) := rfl

end AvailableChain.FGCompose
end
