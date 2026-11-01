module
public import AvailableChainEngineV2.Conditions.DeliveryWindow
public import AvailableChainEngineV2.Laws.Hooks
public import AvailableChainEngineV2.Engine.Run -- shake: keep (re-export)
public import AvailableChainEngineV2.Conditions.Schedule -- shake: keep (re-export)
public import AvailableChainKitV2.ClockLaws
public import AvailableChainGeneric.Statements.V2.Reads

@[expose] public section

/-! Source: `claude-files/a0/generic-layer.md` (GLY), r3.13, §C.3.
Step-2 item I05. D01 requires closed Statement definitions.
The common binders are from GLY:1109–1110. -/

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

namespace AvailableChain.Gen.V2

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}

-- GLY:1123–1125.
/-- DC: Conditions.lean:114,122; same: Same emission or acceptance; GLY r3.19 S112. -/
def Trigger (E : Generic.Env V) (rho : Run V P) (o : P.Object) (t : Time) : Prop :=
  (∃ v ∈ rho.honest, Run.emits E rho v o t) ∨
  (∃ v ∈ rho.honest, ∃ i, Run.acceptsAt E rho i v o t)

-- GLY:1123–1125; BUILD §7.2 B3a requires this equation lemma.
theorem Trigger_def (E : Generic.Env V) (rho : Run V P) (o : P.Object) (t : Time) :
    Trigger E rho o t =
      ((∃ v ∈ rho.honest, Run.emits E rho v o t) ∨
        (∃ v ∈ rho.honest, ∃ i, Run.acceptsAt E rho i v o t)) := by
  rw [Trigger]

-- GLY:1127–1138.
/-- DC: Conditions.lean:110,134; INTENTIONAL: One record for both regimes; GLY r3.19 S113. -/
structure DeliveryWithin (E : Generic.Env V) (rho : V2.Run V P)
    (dl : Time → Time) (cut : Time) : Prop where
  broadcast : ∀ v ∈ rho.honest, ∀ o t, V2.Run.emits E rho v o t → ∀ w ∈ rho.honest,
    V2.DeliveryDemand E rho v w o t dl cut
  relay : ∀ v ∈ rho.honest, ∀ i o t, V2.Run.acceptsAt E rho i v o t → ∀ w ∈ rho.honest,
    V2.DeliveryDemand E rho v w o t dl cut

-- GLY:1140–1145.
structure TimelyClock (P : ProtocolSpec In) (Timely : P.State → P.Object → Prop) where
  actTime : P.Object → Time      -- the handler ADMISSION THRESHOLD (L19)
  clockOf : P.State → Time
  timely_iff : ∀ st o, Timely st o ↔ actTime o ≤ clockOf st
  clock : ClockLaws P            -- KitV2/ClockLaws.lean:18
  clockOf_eq : ∀ st, clockOf st = clock.now st

-- GLY:1147–1153.
structure AcceptanceLaw (P : ProtocolSpec In) (Timely : P.State → P.Object → Prop)
    (Inv : P.State → Prop) : Prop where
  accepts : ∀ st o' o, Inv st → P.handles st o' o → P.wellFormed o = true →
    P.depsPresent st o = true → Timely st o →
    P.processed (P.process st o') o = true ∨ P.excludes (P.process st o') o = true
  -- Negative controls of the r2 form: see below. `excludes_process` is NOT a
  -- field (L20): no generic lemma consumes it.

-- GLY:1155–1163.
structure AdmitSound (P : ProtocolSpec In) {Timely : P.State → P.Object → Prop}
    (C : TimelyClock P Timely) : Prop where
  timely : ∀ st o' o, 0 ≤ C.clockOf st → P.processed st o = false →
    P.processed (P.process st o') o = true → P.handles st o' o → Timely st o
  -- THE ONE WRITTEN FORM of AdmitSound (Opus m3). SYN §5, S3 and T7 cite this
  -- block and do not restate its binders.
  -- L30: the premise 0 ≤ C.clockOf st is needed (see "Negative clock" below).
  -- The `wellFormed o` conjunct of L19 is dropped: neither instance checks
  -- the full `wellFormed` in its handler (see "AdmitSound" below).

-- Keep every source binder name, including unused proof binders (D01).

-- GLY:1172–1176; common binders GLY:1109–1110.
set_option linter.unusedVariables false in
def ReadyTrigger (E : Generic.Env V) (rho : V2.Run V P)
    (o : P.Object) (send : Time) (w : V) (a d : Time) : Prop :=
  ∃ v, v ∈ rho.honest ∧
    (V2.Run.emits E rho v o send ∨
      ∃ i, V2.Run.acceptsAt E rho i v o send) ∧
    V2.LinkReadyOn E rho v w a d

def HistorySafeAt (E : Generic.Env V) (rho : V2.Run V P)
    (w : V) (o : P.Object) (a : Time) : Prop :=
  V2.ProcessedByActionCut E rho w o a →
    P.processed (V2.Run.stateAfterRestartsAt E rho a w) o = true

set_option linter.unusedVariables false in
def ProcessedByDeadlineOfServiceStatement : Prop :=
  ∀ {V In : Type} [DecidableEq V] {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : V2.Run V P)
    (Timely : P.State → P.Object → Prop) (Inv : P.State → Prop)
    (w : V) (o : P.Object) (a d : Time),
  ∀
    (hS : V2.ScheduleWellFormed E rho) (had : a < d)
    (hService : V2.DeliveryService E rho w o a d)
    (hHistory : HistorySafeAt E rho w o a)
    (hRF : V2.restartFree rho w (V2.Run.actionCut rho a) (V2.Run.idxBefore rho d))
    (hHooks : V2.HooksSound P)
    (hAccept : AcceptanceLaw P Timely Inv)
    (hReady : ∀ j t', a ≤ t' → t' < d → V2.Run.handlesAt E rho j w o t' →
      Inv (V2.Run.stateBefore E rho j w) ∧
      P.wellFormed o = true ∧
      P.depsPresent (V2.Run.stateBefore E rho j w) o = true ∧
      Timely (V2.Run.stateBefore E rho j w) o)
    (hNX : P.excludes (V2.Run.stateBeforeTime E rho d w) o = false),
    P.processed (V2.Run.stateBeforeTime E rho d w) o = true

set_option linter.unusedVariables false in
def TimelyOfClockStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ (C : TimelyClock P Timely),
  ∀ (hS : ScheduleWellFormed E rho),
  ∀ (w : V),
  ∀ (o : P.Object),
  ∀ (T : Time),
  ∀ (j i : Nat),
  ∀ (hact : C.actTime o ≤ T),
  ∀ (hj : rho.events[j]? = some (.tick w T)),
  ∀ (hji : j < i),
  ∀ (hrf : restartFree rho w j i),
    Timely (Run.stateBefore E rho i w) o

set_option linter.unusedVariables false in
theorem TimelyOfClockStatement_def :
    TimelyOfClockStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
        (E : Generic.Env V) (rho : Run V P),
      ∀ {Timely : P.State → P.Object → Prop},
      ∀ (C : TimelyClock P Timely),
      ∀ (hS : ScheduleWellFormed E rho),
      ∀ (w : V),
      ∀ (o : P.Object),
      ∀ (T : Time),
      ∀ (j i : Nat),
      ∀ (hact : C.actTime o ≤ T),
      ∀ (hj : rho.events[j]? = some (.tick w T)),
      ∀ (hji : j < i),
      ∀ (hrf : restartFree rho w j i),
        Timely (Run.stateBefore E rho i w) o) := by
  rw [TimelyOfClockStatement]

-- GLY:1177–1180; common binders GLY:1109–1110.
set_option linter.unusedVariables false in
def TimelyOfEmitStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ (C : TimelyClock P Timely),
  ∀ (o : P.Object),
  ∀ (t : Time),
  ∀ (ht : 0 ≤ t),
  ∀ (hpub : PublicTime E (C.actTime o)),
  ∀ (hth : C.actTime o ≤ t),
    C.actTime o ≤ pubFloor E t

set_option linter.unusedVariables false in
theorem TimelyOfEmitStatement_def :
    TimelyOfEmitStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
        (E : Generic.Env V) (rho : Run V P),
      ∀ {Timely : P.State → P.Object → Prop},
      ∀ (C : TimelyClock P Timely),
      ∀ (o : P.Object),
      ∀ (t : Time),
      ∀ (ht : 0 ≤ t),
      ∀ (hpub : PublicTime E (C.actTime o)),
      ∀ (hth : C.actTime o ≤ t),
        C.actTime o ≤ pubFloor E t) := by
  rw [TimelyOfEmitStatement]

-- GLY:1181–1185; common binders GLY:1109–1110.
set_option linter.unusedVariables false in
def TimelyOfRelayStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : Run V P),
  ∀ {Timely : P.State → P.Object → Prop},
  ∀ (C : TimelyClock P Timely),
  ∀ (hAS : AdmitSound P C),
  ∀ (hS : ScheduleWellFormed E rho),
  ∀ (hrestore : ∀ d t, C.clock.now (P.restore d t) = t),
  ∀ (hwake : ∀ u t, .restart u t ∈ rho.events → PublicTime E t),
  ∀ (v : V),
  ∀ (i : Nat),
  ∀ (o : P.Object),
  ∀ (t : Time),
  ∀ (hacc : Run.acceptsAt E rho i v o t),
    C.actTime o ≤ pubFloor E t

set_option linter.unusedVariables false in
theorem TimelyOfRelayStatement_def :
    TimelyOfRelayStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
        (E : Generic.Env V) (rho : Run V P),
      ∀ {Timely : P.State → P.Object → Prop},
      ∀ (C : TimelyClock P Timely),
      ∀ (hAS : AdmitSound P C),
      ∀ (hS : ScheduleWellFormed E rho),
      ∀ (hrestore : ∀ d t, C.clock.now (P.restore d t) = t),
      ∀ (hwake : ∀ u t, .restart u t ∈ rho.events → PublicTime E t),
      ∀ (v : V),
      ∀ (i : Nat),
      ∀ (o : P.Object),
      ∀ (t : Time),
      ∀ (hacc : Run.acceptsAt E rho i v o t),
        C.actTime o ≤ pubFloor E t) := by
  rw [TimelyOfRelayStatement]

-- GLY:1188–1215; common binders GLY:1109–1110.
set_option linter.unusedVariables false in
def AcceptedByDeadlineStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : V2.Run V P)
    (Timely : P.State → P.Object → Prop) (Inv : P.State → Prop)
    (dl : Time → Time) (cut : Time)
    (o : P.Object) (send a : Time) (w : V),
    DeliveryWithin E rho dl cut →
    ReadyTrigger E rho o send w a (dl a) →
    w ∈ rho.honest → send ≤ a → 0 ≤ a → a < dl a →
    dl a ≤ cut → dl a ≤ rho.horizon →
    HistorySafeAt E rho w o a →
    V2.ScheduleWellFormed E rho →
    V2.restartFree rho w (V2.Run.actionCut rho a) (V2.Run.idxBefore rho (dl a)) →
    V2.HooksSound P → AcceptanceLaw P Timely Inv →
    (∀ j t', a ≤ t' → t' < dl a → V2.Run.handlesAt E rho j w o t' →
      Inv (V2.Run.stateBefore E rho j w) ∧
      P.wellFormed o = true ∧ P.depsPresent (V2.Run.stateBefore E rho j w) o = true ∧
      Timely (V2.Run.stateBefore E rho j w) o) →
    P.excludes (V2.Run.stateBeforeTime E rho (dl a) w) o = false →
    P.processed (V2.Run.stateBeforeTime E rho (dl a) w) o = true

set_option linter.unusedVariables false in
theorem AcceptedByDeadlineStatement_def :
    AcceptedByDeadlineStatement =
  (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : V2.Run V P)
    (Timely : P.State → P.Object → Prop) (Inv : P.State → Prop)
    (dl : Time → Time) (cut : Time)
    (o : P.Object) (send a : Time) (w : V),
    DeliveryWithin E rho dl cut →
    ReadyTrigger E rho o send w a (dl a) →
    w ∈ rho.honest → send ≤ a → 0 ≤ a → a < dl a →
    dl a ≤ cut → dl a ≤ rho.horizon →
    HistorySafeAt E rho w o a →
    V2.ScheduleWellFormed E rho →
    V2.restartFree rho w (V2.Run.actionCut rho a) (V2.Run.idxBefore rho (dl a)) →
    V2.HooksSound P → AcceptanceLaw P Timely Inv →
    (∀ j t', a ≤ t' → t' < dl a → V2.Run.handlesAt E rho j w o t' →
      Inv (V2.Run.stateBefore E rho j w) ∧
      P.wellFormed o = true ∧ P.depsPresent (V2.Run.stateBefore E rho j w) o = true ∧
      Timely (V2.Run.stateBefore E rho j w) o) →
    P.excludes (V2.Run.stateBeforeTime E rho (dl a) w) o = false →
    P.processed (V2.Run.stateBeforeTime E rho (dl a) w) o = true) := by
  rfl

-- GLY:1218–1229; common binders GLY:1109–1110.
set_option linter.unusedVariables false in
def FirstAcceptOfProcessedStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : Run V P),
  ∀ (w : V),
  ∀ (o : P.Object),
  ∀ (i₀ k : Nat),
  ∀ (hik : i₀ ≤ k),
  ∀ (hrf : restartFree rho w i₀ k),
  ∀ (h₀ : P.processed (Run.stateBefore E rho i₀ w) o = false),
  ∀ (hk : P.processed (Run.stateBefore E rho k w) o = true),
  ∀ (htick : ∀ i t, i₀ ≤ i → i < k → rho.events[i]? = some (.tick w t) →
      P.processed (Run.stateBefore E rho i w) o = false →
      P.processed (Run.stateBefore E rho (i + 1) w) o = false),
  ∀ (hdeliv : ∀ i o' t', i₀ ≤ i → i < k → rho.events[i]? = some (.deliver w o' t') →
      P.processed (Run.stateBefore E rho i w) o = false →
      P.processed (P.process (Run.stateBefore E rho i w) o') o = true →
      P.handles (Run.stateBefore E rho i w) o' o),
    ∃ i t', i₀ ≤ i ∧ i < k ∧ Run.acceptsAt E rho i w o t'

set_option linter.unusedVariables false in
theorem FirstAcceptOfProcessedStatement_def :
    FirstAcceptOfProcessedStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
        (E : Generic.Env V) (rho : Run V P),
      ∀ (w : V),
      ∀ (o : P.Object),
      ∀ (i₀ k : Nat),
      ∀ (hik : i₀ ≤ k),
      ∀ (hrf : restartFree rho w i₀ k),
      ∀ (h₀ : P.processed (Run.stateBefore E rho i₀ w) o = false),
      ∀ (hk : P.processed (Run.stateBefore E rho k w) o = true),
      ∀ (htick : ∀ i t, i₀ ≤ i → i < k → rho.events[i]? = some (.tick w t) →
          P.processed (Run.stateBefore E rho i w) o = false →
          P.processed (Run.stateBefore E rho (i + 1) w) o = false),
      ∀ (hdeliv : ∀ i o' t', i₀ ≤ i → i < k → rho.events[i]? = some (.deliver w o' t') →
          P.processed (Run.stateBefore E rho i w) o = false →
          P.processed (P.process (Run.stateBefore E rho i w) o') o = true →
          P.handles (Run.stateBefore E rho i w) o' o),
        ∃ i t', i₀ ≤ i ∧ i < k ∧ Run.acceptsAt E rho i w o t') := by
  rw [FirstAcceptOfProcessedStatement]

end AvailableChain.Gen.V2
