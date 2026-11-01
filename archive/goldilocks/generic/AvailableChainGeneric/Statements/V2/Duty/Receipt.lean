module
public import AvailableChainEngineV2.Conditions.Duty.DeliveryWindow
public import AvailableChainEngineV2.Laws.Duty.Hooks
public import AvailableChainEngineV2.Engine.Duty.Run -- shake: keep (re-export)
public import AvailableChainEngineV2.Conditions.Duty.Schedule -- shake: keep (re-export)
public import AvailableChainKitV2.DutyClockLaws
public import AvailableChainGeneric.Statements.V2.Duty.Reads

@[expose] public section

open AvailableChain AvailableChain.V2 AvailableChain.V2.D AvailableChain.V2.D.Engine

namespace AvailableChain.Gen.V2.Duty

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}

-- DC: Conditions.lean:114,122; same: Same emission or acceptance; GLY r3.19 S112.
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:21.
def Trigger (E : Generic.Env V) (rho : D.Run V P) (o : P.Object) (t : Time) : Prop :=
  (∃ v ∈ rho.honest, D.Run.emits E rho v o t) ∨
  (∃ v ∈ rho.honest, ∃ i, D.Run.acceptsAt E rho i v o t)

-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:26.
theorem Trigger_def (E : Generic.Env V) (rho : D.Run V P) (o : P.Object) (t : Time) :
    Trigger E rho o t =
      ((∃ v ∈ rho.honest, D.Run.emits E rho v o t) ∨
        (∃ v ∈ rho.honest, ∃ i, D.Run.acceptsAt E rho i v o t)) := rfl

-- DC: Conditions.lean:110,134; INTENTIONAL: One record for both regimes; GLY r3.19 S113.
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:34.
structure DeliveryWithin (E : Generic.Env V) (rho : D.Run V P)
    (dl : Time → Time) (cut : Time) : Prop where
  broadcast : ∀ v ∈ rho.honest, ∀ o t, D.Run.emits E rho v o t → ∀ w ∈ rho.honest,
    D.DeliveryDemand E rho v w o t dl cut
  relay : ∀ v ∈ rho.honest, ∀ i o t, D.Run.acceptsAt E rho i v o t → ∀ w ∈ rho.honest,
    D.DeliveryDemand E rho v w o t dl cut

-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:48.
structure TimelyClock (P : ProtocolSpecD In) (Timely : P.State → P.Object → Prop) where
  actTime : P.Object → Time
  clockOf : P.State → Time
  timely_iff : ∀ st o, Timely st o ↔ actTime o ≤ clockOf st
  clock : ClockLaws P
  clockOf_eq : ∀ st, clockOf st = clock.now st

-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:56.
structure AcceptanceLaw (P : ProtocolSpecD In) (Timely : P.State → P.Object → Prop)
    (Inv : P.State → Prop) : Prop where
  accepts : ∀ st o' o, Inv st → P.handles st o' o → P.wellFormed o = true →
    P.depsPresent st o = true → Timely st o →
    P.processed (P.process st o') o = true ∨ P.excludes (P.process st o') o = true

-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:65.
structure AdmitSound (P : ProtocolSpecD In) {Timely : P.State → P.Object → Prop}
    (C : TimelyClock P Timely) : Prop where
  timely : ∀ st o' o, 0 ≤ C.clockOf st → P.processed st o = false →
    P.processed (P.process st o') o = true → P.handles st o' o → Timely st o

set_option linter.unusedVariables false in
def ReadyTrigger (E : Generic.Env V) (rho : D.Run V P)
    (o : P.Object) (send : Time) (w : V) (a d : Time) : Prop :=
  ∃ v, v ∈ rho.honest ∧
    (D.Run.emits E rho v o send ∨
      ∃ i, D.Run.acceptsAt E rho i v o send) ∧
    D.LinkReadyOn E rho v w a d

def HistorySafeAt (E : Generic.Env V) (rho : D.Run V P)
    (w : V) (o : P.Object) (a : Time) : Prop :=
  D.ProcessedByActionCut E rho w o a →
    P.processed (D.Run.stateAfterRestartsAt E rho a w) o = true

set_option linter.unusedVariables false in
def ProcessedByDeadlineOfServiceStatement : Prop :=
  ∀ {V In : Type} [DecidableEq V] {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P)
    (Timely : P.State → P.Object → Prop) (Inv : P.State → Prop)
    (w : V) (o : P.Object) (a d : Time),
  ∀
    (hS : D.ScheduleWellFormed E rho) (had : a < d)
    (hService : D.DeliveryService E rho w o a d)
    (hHistory : HistorySafeAt E rho w o a)
    (hRF : D.restartFree rho w (D.Run.actionCut rho a) (D.Run.idxBefore rho d))
    (hHooks : D.HooksSound P)
    (hAccept : AcceptanceLaw P Timely Inv)
    (hReady : ∀ j t', a ≤ t' → t' < d → D.Run.handlesAt E rho j w o t' →
      Inv (D.Run.stateBefore E rho j w) ∧
      P.wellFormed o = true ∧
      P.depsPresent (D.Run.stateBefore E rho j w) o = true ∧
      Timely (D.Run.stateBefore E rho j w) o)
    (hNX : P.excludes (D.Run.stateBeforeTime E rho d w) o = false),
    P.processed (D.Run.stateBeforeTime E rho d w) o = true

set_option linter.unusedVariables false in
-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:79.
def TimelyOfClockStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ (C : TimelyClock P Timely),
  ∀ (hS : D.ScheduleWellFormed E rho),
  ∀ (w : V),
  ∀ (o : P.Object),
  ∀ (T : Time),
  ∀ (j i : Nat),
  ∀ (hact : C.actTime o ≤ T),
  ∀ (hj : rho.events[j]? = some (.tick w T)),
  ∀ (hji : j < i),
  ∀ (hrf : D.restartFree rho w j i),
    Timely (D.Run.stateBefore E rho i w) o

set_option linter.unusedVariables false in
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:96.
theorem TimelyOfClockStatement_def :
    TimelyOfClockStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
        (E : Generic.Env V) (rho : D.Run V P),
      ∀ {Timely : P.State → P.Object → Prop},
      ∀ (C : TimelyClock P Timely),
      ∀ (hS : D.ScheduleWellFormed E rho),
      ∀ (w : V),
      ∀ (o : P.Object),
      ∀ (T : Time),
      ∀ (j i : Nat),
      ∀ (hact : C.actTime o ≤ T),
      ∀ (hj : rho.events[j]? = some (.tick w T)),
      ∀ (hji : j < i),
      ∀ (hrf : D.restartFree rho w j i),
        Timely (D.Run.stateBefore E rho i w) o) := rfl

set_option linter.unusedVariables false in
-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:116.
def TimelyOfEmitStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ (C : TimelyClock P Timely),
  ∀ (o : P.Object),
  ∀ (t : Time),
  ∀ (ht : 0 ≤ t),
  ∀ (hpub : V2.PublicTime E (C.actTime o)),
  ∀ (hth : C.actTime o ≤ t),
    C.actTime o ≤ pubFloor E t

set_option linter.unusedVariables false in
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:129.
theorem TimelyOfEmitStatement_def :
    TimelyOfEmitStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
        (E : Generic.Env V) (rho : D.Run V P),
      ∀ {Timely : P.State → P.Object → Prop},
      ∀ (C : TimelyClock P Timely),
      ∀ (o : P.Object),
      ∀ (t : Time),
      ∀ (ht : 0 ≤ t),
      ∀ (hpub : V2.PublicTime E (C.actTime o)),
      ∀ (hth : C.actTime o ≤ t),
        C.actTime o ≤ pubFloor E t) := rfl

set_option linter.unusedVariables false in
-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:145.
def TimelyOfRelayStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ (C : TimelyClock P Timely),
  ∀ (hAS : AdmitSound P C),
  ∀ (hS : D.ScheduleWellFormed E rho),
  ∀ (hrestore : ∀ d t, C.clock.now (P.restore d t) = t),
  ∀ (hwake : ∀ u t, .restart u t ∈ rho.events → V2.PublicTime E t),
  ∀ (v : V),
  ∀ (i : Nat),
  ∀ (o : P.Object),
  ∀ (t : Time),
  ∀ (hacc : D.Run.acceptsAt E rho i v o t),
    C.actTime o ≤ pubFloor E t

set_option linter.unusedVariables false in
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:161.
theorem TimelyOfRelayStatement_def :
    TimelyOfRelayStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
        (E : Generic.Env V) (rho : D.Run V P),
      ∀ {Timely : P.State → P.Object → Prop},
      ∀ (C : TimelyClock P Timely),
      ∀ (hAS : AdmitSound P C),
      ∀ (hS : D.ScheduleWellFormed E rho),
      ∀ (hrestore : ∀ d t, C.clock.now (P.restore d t) = t),
      ∀ (hwake : ∀ u t, .restart u t ∈ rho.events → V2.PublicTime E t),
      ∀ (v : V),
      ∀ (i : Nat),
      ∀ (o : P.Object),
      ∀ (t : Time),
      ∀ (hacc : D.Run.acceptsAt E rho i v o t),
        C.actTime o ≤ pubFloor E t) := rfl

set_option linter.unusedVariables false in
-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:180.
def AcceptedByDeadlineStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P)
    (Timely : P.State → P.Object → Prop) (Inv : P.State → Prop)
    (dl : Time → Time) (cut : Time)
    (o : P.Object) (send a : Time) (w : V),
    DeliveryWithin E rho dl cut →
    ReadyTrigger E rho o send w a (dl a) →
    w ∈ rho.honest → send ≤ a → 0 ≤ a → a < dl a →
    dl a ≤ cut → dl a ≤ rho.horizon →
    HistorySafeAt E rho w o a →
    D.ScheduleWellFormed E rho →
    D.restartFree rho w (D.Run.actionCut rho a) (D.Run.idxBefore rho (dl a)) →
    D.HooksSound P → AcceptanceLaw P Timely Inv →
    (∀ j t', a ≤ t' → t' < dl a → D.Run.handlesAt E rho j w o t' →
      Inv (D.Run.stateBefore E rho j w) ∧
      P.wellFormed o = true ∧ P.depsPresent (D.Run.stateBefore E rho j w) o = true ∧
      Timely (D.Run.stateBefore E rho j w) o) →
    P.excludes (D.Run.stateBeforeTime E rho (dl a) w) o = false →
    P.processed (D.Run.stateBeforeTime E rho (dl a) w) o = true

set_option linter.unusedVariables false in
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:215.
theorem AcceptedByDeadlineStatement_def :
    AcceptedByDeadlineStatement =
  (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P)
    (Timely : P.State → P.Object → Prop) (Inv : P.State → Prop)
    (dl : Time → Time) (cut : Time)
    (o : P.Object) (send a : Time) (w : V),
    DeliveryWithin E rho dl cut →
    ReadyTrigger E rho o send w a (dl a) →
    w ∈ rho.honest → send ≤ a → 0 ≤ a → a < dl a →
    dl a ≤ cut → dl a ≤ rho.horizon →
    HistorySafeAt E rho w o a →
    D.ScheduleWellFormed E rho →
    D.restartFree rho w (D.Run.actionCut rho a) (D.Run.idxBefore rho (dl a)) →
    D.HooksSound P → AcceptanceLaw P Timely Inv →
    (∀ j t', a ≤ t' → t' < dl a → D.Run.handlesAt E rho j w o t' →
      Inv (D.Run.stateBefore E rho j w) ∧
      P.wellFormed o = true ∧ P.depsPresent (D.Run.stateBefore E rho j w) o = true ∧
      Timely (D.Run.stateBefore E rho j w) o) →
    P.excludes (D.Run.stateBeforeTime E rho (dl a) w) o = false →
    P.processed (D.Run.stateBeforeTime E rho (dl a) w) o = true) := by
  rfl

set_option linter.unusedVariables false in
-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:253.
def FirstAcceptOfProcessedStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ (w : V),
  ∀ (o : P.Object),
  ∀ (i₀ k : Nat),
  ∀ (hik : i₀ ≤ k),
  ∀ (hrf : D.restartFree rho w i₀ k),
  ∀ (h₀ : P.processed (D.Run.stateBefore E rho i₀ w) o = false),
  ∀ (hk : P.processed (D.Run.stateBefore E rho k w) o = true),
  ∀ (htick : ∀ i t, i₀ ≤ i → i < k → rho.events[i]? = some (.tick w t) →
      P.processed (D.Run.stateBefore E rho i w) o = false →
      P.processed (D.Run.stateBefore E rho (i + 1) w) o = false),
  ∀ (hdeliv : ∀ i o' t', i₀ ≤ i → i < k → rho.events[i]? = some (.deliver w o' t') →
      P.processed (D.Run.stateBefore E rho i w) o = false →
      P.processed (P.process (D.Run.stateBefore E rho i w) o') o = true →
      P.handles (D.Run.stateBefore E rho i w) o' o),
    ∃ i t', i₀ ≤ i ∧ i < k ∧ D.Run.acceptsAt E rho i w o t'

set_option linter.unusedVariables false in
-- Source: AvailableChainGeneric/Statements/V2/Receipt.lean:273.
theorem FirstAcceptOfProcessedStatement_def :
    FirstAcceptOfProcessedStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
        (E : Generic.Env V) (rho : D.Run V P),
      ∀ (w : V),
      ∀ (o : P.Object),
      ∀ (i₀ k : Nat),
      ∀ (hik : i₀ ≤ k),
      ∀ (hrf : D.restartFree rho w i₀ k),
      ∀ (h₀ : P.processed (D.Run.stateBefore E rho i₀ w) o = false),
      ∀ (hk : P.processed (D.Run.stateBefore E rho k w) o = true),
      ∀ (htick : ∀ i t, i₀ ≤ i → i < k → rho.events[i]? = some (.tick w t) →
          P.processed (D.Run.stateBefore E rho i w) o = false →
          P.processed (D.Run.stateBefore E rho (i + 1) w) o = false),
      ∀ (hdeliv : ∀ i o' t', i₀ ≤ i → i < k → rho.events[i]? = some (.deliver w o' t') →
          P.processed (D.Run.stateBefore E rho i w) o = false →
          P.processed (P.process (D.Run.stateBefore E rho i w) o') o = true →
          P.handles (D.Run.stateBefore E rho i w) o' o),
        ∃ i t', i₀ ≤ i ∧ i < k ∧ D.Run.acceptsAt E rho i w o t') := rfl

end AvailableChain.Gen.V2.Duty
