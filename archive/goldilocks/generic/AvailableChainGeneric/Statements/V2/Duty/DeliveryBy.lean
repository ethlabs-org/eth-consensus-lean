module
public import AvailableChainGeneric.Statements.V2.Duty.Receipt -- shake: keep (re-export)
public import AvailableChainGeneric.Statements.V2.Duty.Regimes

@[expose] public section

open AvailableChain AvailableChain.V2 AvailableChain.V2.D AvailableChain.V2.D.Engine
open AvailableChain.Gen.Pure

namespace AvailableChain.Gen.V2.Duty

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}

-- DC: Generic/Conditions.lean:110; INTENTIONAL: The delay depends on the wire object.
structure PartialSynchronyBy (E : Generic.Env V) (rho : D.Run V P)
    (delayOf : P.Object → Time) : Prop where
  broadcast_emitted : ∀ v ∈ rho.honest, ∀ o t, D.Run.emits E rho v o t → ∀ w ∈ rho.honest,
    D.DeliveryDemand E rho v w o t (fun a => max a E.t_GST + delayOf o) rho.horizon
  relay_accepted : ∀ v ∈ rho.honest, ∀ i o t, D.Run.acceptsAt E rho i v o t → ∀ w ∈ rho.honest,
    D.DeliveryDemand E rho v w o t (fun a => max a E.t_GST + delayOf o) rho.horizon

-- DC: Generic/Conditions.lean:134; INTENTIONAL: The prefix uses the object's delay.
structure HealthyPrefixDeliveryBy (E : Generic.Env V) (rho : D.Run V P)
    (delayOf : P.Object → Time) (cut : Time) : Prop where
  broadcast_emitted : ∀ v ∈ rho.honest, ∀ o t, D.Run.emits E rho v o t → ∀ w ∈ rho.honest,
    D.DeliveryDemand E rho v w o t (fun a => a + delayOf o) cut
  relay_accepted : ∀ v ∈ rho.honest, ∀ i o t, D.Run.acceptsAt E rho i v o t → ∀ w ∈ rho.honest,
    D.DeliveryDemand E rho v w o t (fun a => a + delayOf o) cut

-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Delivery is required only on Q.
structure DeliveryWithinOn (E : Generic.Env V) (rho : D.Run V P)
    (Q : P.Object → Prop) (dl : Time → Time) (cut : Time) : Prop where
  broadcast : ∀ v ∈ rho.honest, ∀ o, Q o → ∀ t, D.Run.emits E rho v o t → ∀ w ∈ rho.honest,
    D.DeliveryDemand E rho v w o t dl cut
  relay : ∀ v ∈ rho.honest, ∀ i o, Q o → ∀ t, D.Run.acceptsAt E rho i v o t → ∀ w ∈ rho.honest,
    D.DeliveryDemand E rho v w o t dl cut

-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: The label window delivers only Q.
def LabelSyncOn (E : Generic.Env V) (rho : D.Run V P) (Q : P.Object → Prop)
    (vt dt : Time) : Prop :=
  ∃ dl cut, DeliveryWithinOn E rho Q dl cut ∧ Monotone dl ∧ (∀ t, t < dl t) ∧
    (∀ t, dl t ≤ max t vt + E.Δ) ∧ vt + E.Δ ≤ dt ∧ dt ≤ cut ∧ dt ≤ rho.horizon

-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Definition of the family label window.
theorem LabelSyncOn_def (E : Generic.Env V) (rho : D.Run V P) (Q : P.Object → Prop)
    (vt dt : Time) :
    LabelSyncOn E rho Q vt dt =
      (∃ dl cut, DeliveryWithinOn E rho Q dl cut ∧ Monotone dl ∧ (∀ t, t < dl t) ∧
        (∀ t, dl t ≤ max t vt + E.Δ) ∧ vt + E.Δ ≤ dt ∧ dt ≤ cut ∧ dt ≤ rho.horizon) := rfl

-- DC: Generic/Conditions.lean:134,169; INTENTIONAL: Family sync and the same point batch.
structure LabelFactsOn (E : Generic.Env V) (rho : D.Run V P) (Q : P.Object → Prop)
    (vt dt : Time) (h m : Nat) : Prop where
  sync : LabelSyncOn E rho Q vt dt
  batch : Batch h m

set_option linter.unusedVariables false in
-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Family delivery with exact delays.
def PartialSynchronyIffByConstStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  D.PartialSynchrony E rho ↔ PartialSynchronyBy E rho (fun _ => E.Δ)

set_option linter.unusedVariables false in
-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Family delivery with exact delays.
theorem PartialSynchronyIffByConstStatement_def :
    PartialSynchronyIffByConstStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  D.PartialSynchrony E rho ↔ PartialSynchronyBy E rho (fun _ => E.Δ)) := rfl

set_option linter.unusedVariables false in
-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Family delivery with exact delays.
def HealthyPrefixIffByConstStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ (cut : Time), D.HealthyPrefixDelivery E rho cut ↔
    HealthyPrefixDeliveryBy E rho (fun _ => E.Δ) cut

set_option linter.unusedVariables false in
-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Family delivery with exact delays.
theorem HealthyPrefixIffByConstStatement_def :
    HealthyPrefixIffByConstStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ (cut : Time), D.HealthyPrefixDelivery E rho cut ↔
    HealthyPrefixDeliveryBy E rho (fun _ => E.Δ) cut) := rfl

set_option linter.unusedVariables false in
-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Family delivery with exact delays.
def DeliveryWithinIffOnTrueStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ (dl : Time → Time) (cut : Time), DeliveryWithin E rho dl cut ↔
    DeliveryWithinOn E rho (fun _ => True) dl cut

set_option linter.unusedVariables false in
-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Family delivery with exact delays.
theorem DeliveryWithinIffOnTrueStatement_def :
    DeliveryWithinIffOnTrueStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ (dl : Time → Time) (cut : Time), DeliveryWithin E rho dl cut ↔
    DeliveryWithinOn E rho (fun _ => True) dl cut) := rfl

set_option linter.unusedVariables false in
-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Family delivery with exact delays.
def DeliveryWithinOnMonoStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {Q Q' : P.Object → Prop} {dl : Time → Time} {cut : Time},
  DeliveryWithinOn E rho Q dl cut → (∀ o, Q' o → Q o) →
    DeliveryWithinOn E rho Q' dl cut

set_option linter.unusedVariables false in
-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Family delivery with exact delays.
theorem DeliveryWithinOnMonoStatement_def :
    DeliveryWithinOnMonoStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {Q Q' : P.Object → Prop} {dl : Time → Time} {cut : Time},
  DeliveryWithinOn E rho Q dl cut → (∀ o, Q' o → Q o) →
    DeliveryWithinOn E rho Q' dl cut) := rfl

set_option linter.unusedVariables false in
-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Family delivery with exact delays.
def LabelSyncToOnStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ (Q : P.Object → Prop) (vt dt : Time),
  LabelSync E rho vt dt → LabelSyncOn E rho Q vt dt

set_option linter.unusedVariables false in
-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Family delivery with exact delays.
theorem LabelSyncToOnStatement_def :
    LabelSyncToOnStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ (Q : P.Object → Prop) (vt dt : Time),
  LabelSync E rho vt dt → LabelSyncOn E rho Q vt dt) := rfl

set_option linter.unusedVariables false in
-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Family delivery with exact delays.
def LabelFactsToOnStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ (Q : P.Object → Prop) (vt dt : Time) (h m : Nat),
  LabelFacts E rho vt dt h m → LabelFactsOn E rho Q vt dt h m

set_option linter.unusedVariables false in
-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Family delivery with exact delays.
theorem LabelFactsToOnStatement_def :
    LabelFactsToOnStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ (Q : P.Object → Prop) (vt dt : Time) (h m : Nat),
  LabelFacts E rho vt dt h m → LabelFactsOn E rho Q vt dt h m) := rfl

set_option linter.unusedVariables false in
-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Family delivery with exact delays.
def DeliveryWithinOnOfPartialSynchronyByStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {delayOf : P.Object → Time},
  PartialSynchronyBy E rho delayOf → ∀ (Q : P.Object → Prop) (δ : Time),
  (∀ o, Q o → delayOf o = δ) →
    DeliveryWithinOn E rho Q (fun t => max t E.t_GST + δ) rho.horizon

set_option linter.unusedVariables false in
-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Family delivery with exact delays.
theorem DeliveryWithinOnOfPartialSynchronyByStatement_def :
    DeliveryWithinOnOfPartialSynchronyByStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {delayOf : P.Object → Time},
  PartialSynchronyBy E rho delayOf → ∀ (Q : P.Object → Prop) (δ : Time),
  (∀ o, Q o → delayOf o = δ) →
    DeliveryWithinOn E rho Q (fun t => max t E.t_GST + δ) rho.horizon) := rfl

set_option linter.unusedVariables false in
-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Family delivery with exact delays.
def DeliveryWithinOnOfHealthyPrefixByStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {delayOf : P.Object → Time} (cut : Time),
  HealthyPrefixDeliveryBy E rho delayOf cut → ∀ (Q : P.Object → Prop) (δ : Time),
  (∀ o, Q o → delayOf o = δ) →
    DeliveryWithinOn E rho Q (fun t => t + δ) cut

set_option linter.unusedVariables false in
-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Family delivery with exact delays.
theorem DeliveryWithinOnOfHealthyPrefixByStatement_def :
    DeliveryWithinOnOfHealthyPrefixByStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {delayOf : P.Object → Time} (cut : Time),
  HealthyPrefixDeliveryBy E rho delayOf cut → ∀ (Q : P.Object → Prop) (δ : Time),
  (∀ o, Q o → delayOf o = δ) →
    DeliveryWithinOn E rho Q (fun t => t + δ) cut) := rfl

set_option linter.unusedVariables false in
-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Family delivery with exact delays.
def LabelSyncOnOfCleanCutByStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {delayOf : P.Object → Time} (Q : P.Object → Prop) (b₀ vt dt : Time),
  HealthyPrefixDeliveryBy E rho delayOf b₀ →
  (∀ o, Q o → delayOf o = E.Δ) →
  vt + E.Δ ≤ dt → dt ≤ b₀ → b₀ ≤ rho.horizon → LabelSyncOn E rho Q vt dt

set_option linter.unusedVariables false in
-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Family delivery with exact delays.
theorem LabelSyncOnOfCleanCutByStatement_def :
    LabelSyncOnOfCleanCutByStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {delayOf : P.Object → Time} (Q : P.Object → Prop) (b₀ vt dt : Time),
  HealthyPrefixDeliveryBy E rho delayOf b₀ →
  (∀ o, Q o → delayOf o = E.Δ) →
  vt + E.Δ ≤ dt → dt ≤ b₀ → b₀ ≤ rho.horizon → LabelSyncOn E rho Q vt dt) := rfl

set_option linter.unusedVariables false in
-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Family delivery with exact delays.
def LabelSyncOnOfRecoveryByStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {delayOf : P.Object → Time} (Q : P.Object → Prop) (vt dt : Time),
  PartialSynchronyBy E rho delayOf →
  (∀ o, Q o → delayOf o = E.Δ) →
  E.t_GST ≤ vt → vt + E.Δ ≤ dt → dt ≤ rho.horizon → LabelSyncOn E rho Q vt dt

set_option linter.unusedVariables false in
-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Family delivery with exact delays.
theorem LabelSyncOnOfRecoveryByStatement_def :
    LabelSyncOnOfRecoveryByStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {delayOf : P.Object → Time} (Q : P.Object → Prop) (vt dt : Time),
  PartialSynchronyBy E rho delayOf →
  (∀ o, Q o → delayOf o = E.Δ) →
  E.t_GST ≤ vt → vt + E.Δ ≤ dt → dt ≤ rho.horizon → LabelSyncOn E rho Q vt dt) := rfl

set_option linter.unusedVariables false in
-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Family delivery with exact delays.
def LabelFactsOnOfCleanCutByStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {delayOf : P.Object → Time} (Q : P.Object → Prop) (b₀ vt dt : Time) (h m : Nat),
  HealthyPrefixDeliveryBy E rho delayOf b₀ →
  (∀ o, Q o → delayOf o = E.Δ) →
  vt + E.Δ ≤ dt → dt ≤ b₀ → b₀ ≤ rho.horizon → Batch h m →
    LabelFactsOn E rho Q vt dt h m

set_option linter.unusedVariables false in
-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Family delivery with exact delays.
theorem LabelFactsOnOfCleanCutByStatement_def :
    LabelFactsOnOfCleanCutByStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {delayOf : P.Object → Time} (Q : P.Object → Prop) (b₀ vt dt : Time) (h m : Nat),
  HealthyPrefixDeliveryBy E rho delayOf b₀ →
  (∀ o, Q o → delayOf o = E.Δ) →
  vt + E.Δ ≤ dt → dt ≤ b₀ → b₀ ≤ rho.horizon → Batch h m →
    LabelFactsOn E rho Q vt dt h m) := rfl

set_option linter.unusedVariables false in
-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Family delivery with exact delays.
def LabelFactsOnOfRecoveryByStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {delayOf : P.Object → Time} (Q : P.Object → Prop) (vt dt : Time) (h m : Nat),
  PartialSynchronyBy E rho delayOf →
  (∀ o, Q o → delayOf o = E.Δ) →
  E.t_GST ≤ vt → vt + E.Δ ≤ dt → dt ≤ rho.horizon → Batch h m →
    LabelFactsOn E rho Q vt dt h m

set_option linter.unusedVariables false in
-- DC: Generic/Conditions.lean:110,134; INTENTIONAL: Family delivery with exact delays.
theorem LabelFactsOnOfRecoveryByStatement_def :
    LabelFactsOnOfRecoveryByStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P),
  ∀ {delayOf : P.Object → Time} (Q : P.Object → Prop) (vt dt : Time) (h m : Nat),
  PartialSynchronyBy E rho delayOf →
  (∀ o, Q o → delayOf o = E.Δ) →
  E.t_GST ≤ vt → vt + E.Δ ≤ dt → dt ≤ rho.horizon → Batch h m →
    LabelFactsOn E rho Q vt dt h m) := rfl

set_option linter.unusedVariables false in
-- DC: additive (no DC counterpart); reason: A larger family delay must be positive.
def DelayPosOfEnvLeStatement : Prop :=
  ∀ {V : Type} (E : Generic.Env V) {ΔF : Time}, E.Δ ≤ ΔF → 0 < ΔF

set_option linter.unusedVariables false in
-- DC: additive (no DC counterpart); reason: A larger family delay must be positive.
theorem DelayPosOfEnvLeStatement_def :
    DelayPosOfEnvLeStatement =
      (∀ {V : Type} (E : Generic.Env V) {ΔF : Time}, E.Δ ≤ ΔF → 0 < ΔF) := rfl

set_option linter.unusedVariables false in
-- DC: RawHeightCoverage:1011,1026; SAME mechanism: Receipt uses only the object's family.
def AcceptedByDeadlineOnStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P)
    (Timely : P.State → P.Object → Prop) (Inv : P.State → Prop)
    (Q : P.Object → Prop) (dl : Time → Time) (cut : Time)
    (o : P.Object) (send a : Time) (w : V),
    Q o →
    DeliveryWithinOn E rho Q dl cut →
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
-- DC: RawHeightCoverage:1011,1026; SAME mechanism: Receipt uses only the object's family.
theorem AcceptedByDeadlineOnStatement_def :
    AcceptedByDeadlineOnStatement =
  (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P)
    (Timely : P.State → P.Object → Prop) (Inv : P.State → Prop)
    (Q : P.Object → Prop) (dl : Time → Time) (cut : Time)
    (o : P.Object) (send a : Time) (w : V),
    Q o →
    DeliveryWithinOn E rho Q dl cut →
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

end AvailableChain.Gen.V2.Duty
