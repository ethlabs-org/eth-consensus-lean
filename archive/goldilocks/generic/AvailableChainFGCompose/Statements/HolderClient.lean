module
public import AvailableChainFGCompose.Statements.ExecutionBridges
public import AvailableChainFGCompose.Statements.RowPermission
public import AvailableChainFGCompose.Statements.SafetyStore

@[expose] public section

/-! X1c: client inputs, durable trace and exact-wire coverage at actual observation cuts.
The holder contract is the accepted `FGHolderClientLaws`; no population equivalence is used. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In} [DecidableEq V]
variable {n : Nat} {Wire Body : Type}
variable (S : FGSafetyReads P n Wire) (Ef : Electorate (Fin n)) (cfg : FGConfig)
variable (E : Generic.Env V) (rho : V2.D.Run V P) (O : FGExecutionObs V P)

/-- Both selection inputs come from the same drained duty state. -/
def obsSafetyInputAt (x : V) (j : Nat) :
    Option (Option (FGBlock (Fin n)) × HeadFields) :=
  match rho.events[j]? with
  | some (.tick y t) =>
    if y = x ∧ E.awake x t = true ∧ S.enabled t = true then
      some (S.inputs (obsDutyState O x j)) else none
  | _ => none

theorem obsSafetyInputAt_def (x : V) (j : Nat) :
    obsSafetyInputAt S E rho O x j =
      (match rho.events[j]? with
      | some (.tick y t) =>
        if y = x ∧ E.awake x t = true ∧ S.enabled t = true then
          some (S.inputs (obsDutyState O x j)) else none
      | _ => none) := rfl

/-- Exact self-visible releases at the event indices strictly below `k`. -/
def obsOwnReleasedBefore (x : V) (k : Nat) : List P.Object :=
  (List.range k).flatMap (obsOwnReleased O x)

omit [DecidableEq V] in
theorem obsOwnReleasedBefore_def (x : V) (k : Nat) :
    obsOwnReleasedBefore O x k = (List.range k).flatMap (obsOwnReleased O x) := rfl

/-- No slashable decoded pair among the holder's actual released wires. -/
def obsSafetyNoSlash (x : V) : Prop :=
  ∀ a b, (∃ t, obsEmits O rho x (S.encode a) t) →
    (∃ t, obsEmits O rho x (S.encode b) t) →
    ∀ u v, S.decode a = some u → S.decode b = some v → ¬ Slashable u v

omit [DecidableEq V] in
theorem obsSafetyNoSlash_def (x : V) :
    obsSafetyNoSlash S rho O x =
      (∀ a b, (∃ t, obsEmits O rho x (S.encode a) t) →
        (∃ t, obsEmits O rho x (S.encode b) t) →
        ∀ u v, S.decode a = some u → S.decode b = some v → ¬ Slashable u v) := rfl

/-- An honest action release retains its exact wire and event index. -/
def obsHonestRowAt (T : FGTiming) (j : Nat) (x : V) (r : Nat) (a : Wire) : Prop :=
  x ∈ rho.honest ∧ rho.events[j]? = some (.tick x (T.action r)) ∧
    S.encode a ∈ O.released x j

omit [DecidableEq V] in
theorem obsHonestRowAt_def (T : FGTiming) (j : Nat) (x : V) (r : Nat) (a : Wire) :
    obsHonestRowAt S rho O T j x r a =
      (x ∈ rho.honest ∧ rho.events[j]? = some (.tick x (T.action r)) ∧
        S.encode a ∈ O.released x j) := rfl

/-- The record and decoded release trace of one FG holder over its actual inputs. -/
def FGHolderClientTrace (holder : Fin n → V) : Prop :=
  ∀ i, holder i ∈ rho.honest → ∀ k,
    S.record (O.stateBefore k (holder i)) =
      clientRecordOnce Ef cfg i RecordOnce.initial
        ((List.range k).filterMap (obsSafetyInputAt S E rho O (holder i))) ∧
    (obsOwnReleasedBefore O (holder i) k).filterMap S.decodeObject =
      clientRunOnce Ef cfg i RecordOnce.initial
        ((List.range k).filterMap (obsSafetyInputAt S E rho O (holder i)))

theorem FGHolderClientTrace_def (holder : Fin n → V) :
    FGHolderClientTrace S Ef cfg E rho O holder =
      (∀ i, holder i ∈ rho.honest → ∀ k,
        S.record (O.stateBefore k (holder i)) =
          clientRecordOnce Ef cfg i RecordOnce.initial
            ((List.range k).filterMap (obsSafetyInputAt S E rho O (holder i))) ∧
        (obsOwnReleasedBefore O (holder i) k).filterMap S.decodeObject =
          clientRunOnce Ef cfg i RecordOnce.initial
            ((List.range k).filterMap (obsSafetyInputAt S E rho O (holder i)))) := rfl

/-- Current release or a strictly earlier exact-wire release of the same honest holder. -/
def FGHolderRowCoverage (T : FGTiming) (entry : Wire → Option (Height × BlockId))
    (x : V) (j r : Nat) (target : Height × BlockId) : Prop :=
  (∃ a, obsHonestRowAt S rho O T j x r a ∧ entry a = some target) ∨
    ∃ k rSent a, k < j ∧ rSent ≤ r ∧ obsHonestRowAt S rho O T k x rSent a ∧
      entry a = some target

omit [DecidableEq V] in
theorem FGHolderRowCoverage_def (T : FGTiming) (entry : Wire → Option (Height × BlockId))
    (x : V) (j r : Nat) (target : Height × BlockId) :
    FGHolderRowCoverage S rho O T entry x j r target =
      ((∃ a, obsHonestRowAt S rho O T j x r a ∧ entry a = some target) ∨
        ∃ k rSent a, k < j ∧ rSent ≤ r ∧ obsHonestRowAt S rho O T k x rSent a ∧
          entry a = some target) := rfl

variable (F : FGDependencyDriver V Body P) (T : V → FGDependencyTrace P.State)
variable (Op : V → Nat → FGDependencyOperation Body (FGReceiptToken V P.Object) P.Object)
variable (holder : Fin n → V)

/-- Driver trace obligation, bound to the canonical observation of this very run. -/
def SafetyClientTraceDriverStatement : Prop :=
  let O := driverFGExecutionObs E rho F T Op
  FGExecutionObsLaws E rho O → FGHolderClientLaws S Ef cfg E rho O holder →
    FGHolderClientTrace S Ef cfg E rho O holder

theorem SafetyClientTraceDriverStatement_def :
    SafetyClientTraceDriverStatement S Ef cfg E rho F T Op holder =
      (let O := driverFGExecutionObs E rho F T Op
       FGExecutionObsLaws E rho O → FGHolderClientLaws S Ef cfg E rho O holder →
         FGHolderClientTrace S Ef cfg E rho O holder) := rfl

/-- Honest-holder no-slash obligation, without a bijective runtime population. -/
def SafetyEmittedNoSlashDriverStatement : Prop :=
  let O := driverFGExecutionObs E rho F T Op
  FGExecutionObsLaws E rho O → FGHolderClientLaws S Ef cfg E rho O holder →
    FGSafetyWireLaws S → ∀ i, holder i ∈ rho.honest → obsSafetyNoSlash S rho O (holder i)

theorem SafetyEmittedNoSlashDriverStatement_def :
    SafetyEmittedNoSlashDriverStatement S Ef cfg E rho F T Op holder =
      (let O := driverFGExecutionObs E rho F T Op
       FGExecutionObsLaws E rho O → FGHolderClientLaws S Ef cfg E rho O holder →
         FGSafetyWireLaws S → ∀ i, holder i ∈ rho.honest →
           obsSafetyNoSlash S rho O (holder i)) := rfl

/-- Permission uses both duty inputs; prior sent keys require their exact-wire origin. -/
def RowPermissionCoveredDriverStatement (H : FGHeightView (Fin n))
    (timing : FGTiming) (entry : Wire → Option (Height × BlockId)) : Prop :=
  let O := driverFGExecutionObs E rho F T Op
  FGExecutionObsLaws E rho O → FGHolderClientLaws S Ef cfg E rho O holder →
  FGTimingLaws timing → FGRowPermissionWireLaws S entry → V2.D.ScheduleWellFormed E rho →
  (∀ C, ((derive Ef cfg C).h, (derive Ef cfg C).T_h.root) =
    ((H C).h, (H C).T_h.root)) →
  ∀ seat j r C, holder seat ∈ rho.honest →
    rho.events[j]? = some (.tick (holder seat) (timing.action r)) →
    FGRowPermissionInputs S H (obsDutyState O (holder seat) j) C →
    FGRowRecordHistory (S.record (obsDutyState O (holder seat) j)) →
    (∀ b ∈ (S.record (O.stateBefore j (holder seat))).sent,
      ∃ k rSent a, k < j ∧ obsHonestRowAt S rho O timing k (holder seat) rSent a ∧
        entry a = namedEntry b.1) →
    E.awake (holder seat) (timing.action r) = true →
    S.enabled (timing.action r) = true →
    FGHolderRowCoverage S rho O timing entry (holder seat) j r ((H C).h, (H C).T_h.root)

theorem RowPermissionCoveredDriverStatement_def (H : FGHeightView (Fin n))
    (timing : FGTiming) (entry : Wire → Option (Height × BlockId)) :
    RowPermissionCoveredDriverStatement S Ef cfg E rho F T Op holder H timing entry =
      (let O := driverFGExecutionObs E rho F T Op
       FGExecutionObsLaws E rho O → FGHolderClientLaws S Ef cfg E rho O holder →
       FGTimingLaws timing → FGRowPermissionWireLaws S entry →
       V2.D.ScheduleWellFormed E rho →
       (∀ C, ((derive Ef cfg C).h, (derive Ef cfg C).T_h.root) =
         ((H C).h, (H C).T_h.root)) →
       ∀ seat j r C, holder seat ∈ rho.honest →
         rho.events[j]? = some (.tick (holder seat) (timing.action r)) →
         FGRowPermissionInputs S H (obsDutyState O (holder seat) j) C →
         FGRowRecordHistory (S.record (obsDutyState O (holder seat) j)) →
         (∀ b ∈ (S.record (O.stateBefore j (holder seat))).sent,
           ∃ k rSent a, k < j ∧ obsHonestRowAt S rho O timing k (holder seat) rSent a ∧
             entry a = namedEntry b.1) →
         E.awake (holder seat) (timing.action r) = true →
         S.enabled (timing.action r) = true →
         FGHolderRowCoverage S rho O timing entry (holder seat) j r
           ((H C).h, (H C).T_h.root)) := rfl

end AvailableChain.FGCompose
end
