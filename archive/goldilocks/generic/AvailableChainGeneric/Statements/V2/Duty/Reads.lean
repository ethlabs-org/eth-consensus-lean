module
public import AvailableChainEngineV2.Engine.Duty.Run -- shake: keep (re-export)
public import AvailableChainEngineV2.Conditions.Duty.Schedule
public import AvailableChainEngineV2.Conditions.Duty.Interface

@[expose] public section

namespace AvailableChain.V2.D.Engine
end AvailableChain.V2.D.Engine

open AvailableChain AvailableChain.V2 AvailableChain.V2.D AvailableChain.V2.D.Engine

namespace AvailableChain.V2.D.Run

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}

-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Reads.lean:25.
def idxBefore (rho : D.Run V P) (t : Time) : Nat :=
  (rho.events.filter (fun e => decide (e.time < t))).length

omit [DecidableEq V] in
-- Source: AvailableChainGeneric/Statements/V2/Reads.lean:30.
theorem idxBefore_def (rho : D.Run V P) (t : Time) :
    idxBefore rho t = (rho.events.filter (fun e => decide (e.time < t))).length := rfl

-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Reads.lean:35.
def nthIdx? (rho : D.Run V P) (v : V) (k : Nat) : Option Nat :=
  ((rho.events.zipIdx.filter (fun e => decide (e.1.node = v)))[k]?).map Prod.snd

-- Source: AvailableChainGeneric/Statements/V2/Reads.lean:39.
theorem nthIdx?_def (rho : D.Run V P) (v : V) (k : Nat) :
    nthIdx? rho v k =
      ((rho.events.zipIdx.filter (fun e => decide (e.1.node = v)))[k]?).map Prod.snd := rfl

end AvailableChain.V2.D.Run

namespace AvailableChain.Gen.V2.Duty

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}

-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Reads.lean:51.
def pubFloor (E : Generic.Env V) (t : Time) : Time := (t / E.Δ) * E.Δ

omit [DecidableEq V] in
-- Source: AvailableChainGeneric/Statements/V2/Reads.lean:55.
theorem pubFloor_def (E : Generic.Env V) (t : Time) :
    pubFloor E t = (t / E.Δ) * E.Δ := rfl

-- DC: Conditions.lean:202,211; INTENTIONAL: Slot 0 has no proposal; GLY r3.19 S106.
-- Source: AvailableChainGeneric/Statements/V2/Reads.lean:61.
def HonestSlot (rho : D.Run V P) (I : D.Interface P) (s : Slot) : Prop :=
  0 < s ∧ D.proposerOf rho I s ∈ rho.honest

omit [DecidableEq V] in
-- Source: AvailableChainGeneric/Statements/V2/Reads.lean:66.
theorem HonestSlot_def (rho : D.Run V P) (I : D.Interface P) (s : Slot) :
    HonestSlot rho I s =
      (0 < s ∧ D.proposerOf rho I s ∈ rho.honest) := rfl

-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Reads.lean:72.
def HoldsBefore (E : Generic.Env V) (rho : D.Run V P) (Q : P.State → Prop)
    (d : Time) (x : V) : Prop :=
  Q (D.Run.stateBeforeTime E rho d x)

-- Source: AvailableChainGeneric/Statements/V2/Reads.lean:77.
theorem HoldsBefore_def (E : Generic.Env V) (rho : D.Run V P) (Q : P.State → Prop)
    (d : Time) (x : V) :
    HoldsBefore E rho Q d x = Q (D.Run.stateBeforeTime E rho d x) := rfl

-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Reads.lean:86.
def MonoAlong (Q : P.State → Prop) : Prop :=
  (∀ st t, Q st → Q (P.clock st t)) ∧
  (∀ st o, Q st → Q (P.process st o)) ∧
  (∀ st o, Q st → Q (P.recordOwn st o))

omit [DecidableEq V] in
-- Source: AvailableChainGeneric/Statements/V2/Reads.lean:93.
theorem MonoAlong_def (Q : P.State → Prop) :
    MonoAlong Q =
      ((∀ st t, Q st → Q (P.clock st t)) ∧
       (∀ st o, Q st → Q (P.process st o)) ∧
       (∀ st o, Q st → Q (P.recordOwn st o))) := rfl

-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Reads.lean:101.
def Pending (rho : D.Run V P) (deadline : Time) (served : Nat → Prop) (i : Nat) : Prop :=
  (∃ e, rho.events[i]? = some e ∧ deadline ≤ e.time) →
    ∃ j < i, (∃ e', rho.events[j]? = some e' ∧ e'.time < deadline) ∧ served j

omit [DecidableEq V] in
-- Source: AvailableChainGeneric/Statements/V2/Reads.lean:107.
theorem Pending_def (rho : D.Run V P) (deadline : Time) (served : Nat → Prop) (i : Nat) :
    Pending rho deadline served i =
      ((∃ e, rho.events[i]? = some e ∧ deadline ≤ e.time) →
        ∃ j < i, (∃ e', rho.events[j]? = some e' ∧ e'.time < deadline) ∧ served j) := rfl

set_option linter.unusedVariables false in
-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Reads.lean:116.
def StateBeforeIdxBeforeStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    (E : Generic.Env V) (rho : D.Run V P) (t : Time) (hS : D.ScheduleWellFormed E rho),
    D.Run.stateBefore E rho (D.Run.idxBefore rho t) = D.Run.stateBeforeTime E rho t

set_option linter.unusedVariables false in
-- Source: AvailableChainGeneric/Statements/V2/Reads.lean:122.
theorem StateBeforeIdxBeforeStatement_def :
    StateBeforeIdxBeforeStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
        (E : Generic.Env V) (rho : D.Run V P) (t : Time) (hS : D.ScheduleWellFormed E rho),
        D.Run.stateBefore E rho (D.Run.idxBefore rho t) = D.Run.stateBeforeTime E rho t) := rfl

set_option linter.unusedVariables false in
-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Reads.lean:131.
def HoldsBeforeIffExistsIdxStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
    {E : Generic.Env V} {rho : D.Run V P} {Q : P.State → Prop} {d : Time} {x : V}
    (hNR : D.NoRestart rho) (hS : D.ScheduleWellFormed E rho) (hmono : MonoAlong Q),
    HoldsBefore E rho Q d x ↔
      ∃ i ≤ rho.events.length,
        (∀ k < i, ∃ e, rho.events[k]? = some e ∧ e.time < d) ∧
        Q (D.Run.stateBefore E rho i x)

set_option linter.unusedVariables false in
-- Source: AvailableChainGeneric/Statements/V2/Reads.lean:142.
theorem HoldsBeforeIffExistsIdxStatement_def :
    HoldsBeforeIffExistsIdxStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}
        {E : Generic.Env V} {rho : D.Run V P} {Q : P.State → Prop} {d : Time} {x : V}
        (hNR : D.NoRestart rho) (hS : D.ScheduleWellFormed E rho) (hmono : MonoAlong Q),
        HoldsBefore E rho Q d x ↔
          ∃ i ≤ rho.events.length,
            (∀ k < i, ∃ e, rho.events[k]? = some e ∧ e.time < d) ∧
            Q (D.Run.stateBefore E rho i x)) := rfl

end AvailableChain.Gen.V2.Duty
