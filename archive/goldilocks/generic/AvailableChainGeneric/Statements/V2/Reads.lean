module
public import AvailableChainEngineV2.Engine.Run -- shake: keep (re-export)
public import AvailableChainEngineV2.Conditions.Schedule
public import AvailableChainEngineV2.Conditions.Interface

@[expose] public section

/-! Source keys: GLY is `claude-files/a0/generic-layer.md` r3.13;
P3 is `fgsa-f0-f2-plan-r3.5-2a9a5877.md`;
1cP is `claude-files/1c/plan.md` r3.3.
Step-2 item I03; rulings D01, D03, D11, and D12. -/

-- These EngineV2 imports contain no declarations in the KitV2 Engine namespace.
-- Register that namespace for the required open list without a KitV2 import.
namespace AvailableChain.V2.Engine
end AvailableChain.V2.Engine

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

namespace AvailableChain.V2.Run

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}

-- GLY:1116–1117 (plan citation GLY:1046–1047); namespace per D03.
def idxBefore (rho : Run V P) (t : Time) : Nat :=
  (rho.events.filter (fun e => decide (e.time < t))).length

-- GLY:1116–1117; equation export required by BUILD §7.2 B3a.
omit [DecidableEq V] in
theorem idxBefore_def (rho : Run V P) (t : Time) :
    idxBefore rho t = (rho.events.filter (fun e => decide (e.time < t))).length := by
  rw [idxBefore]

-- 1cP:832–833; namespace per D03.
def nthIdx? (rho : Run V P) (v : V) (k : Nat) : Option Nat :=
  ((rho.events.zipIdx.filter (fun e => decide (e.1.node = v)))[k]?).map Prod.snd

-- 1cP:832–833; equation export required by BUILD §7.2 B3a.
theorem nthIdx?_def (rho : Run V P) (v : V) (k : Nat) :
    nthIdx? rho v k =
      ((rho.events.zipIdx.filter (fun e => decide (e.1.node = v)))[k]?).map Prod.snd := by
  rw [nthIdx?]

end AvailableChain.V2.Run

namespace AvailableChain.Gen.V2

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}

-- GLY:1114 (plan citation GLY:1044).
def pubFloor (E : Generic.Env V) (t : Time) : Time := (t / E.Δ) * E.Δ

-- GLY:1114; equation export required by BUILD §7.2 B3a.
omit [DecidableEq V] in
theorem pubFloor_def (E : Generic.Env V) (t : Time) :
    pubFloor E t = (t / E.Δ) * E.Δ := by
  rw [pubFloor]

-- P3:1554–1555.
/-- DC: Conditions.lean:202,211; INTENTIONAL: Slot 0 has no proposal; GLY r3.19 S106. -/
def HonestSlot (rho : Run V P) (I : AvailableChain.V2.Interface P) (s : Slot) : Prop :=
  0 < s ∧ AvailableChain.V2.proposerOf rho I s ∈ rho.honest

-- P3:1554–1555; equation export required by BUILD §7.2 B3a.
omit [DecidableEq V] in
theorem HonestSlot_def (rho : Run V P) (I : AvailableChain.V2.Interface P) (s : Slot) :
    HonestSlot rho I s =
      (0 < s ∧ AvailableChain.V2.proposerOf rho I s ∈ rho.honest) := by
  rw [HonestSlot]

-- P3:1496.
def HoldsBefore (E : Generic.Env V) (rho : Run V P) (Q : P.State → Prop)
    (d : Time) (x : V) : Prop :=
  Q (AvailableChain.V2.Run.stateBeforeTime E rho d x)

-- P3:1496; equation export required by BUILD §7.2 B3a.
theorem HoldsBefore_def (E : Generic.Env V) (rho : Run V P) (Q : P.State → Prop)
    (d : Time) (x : V) :
    HoldsBefore E rho Q d x = Q (AvailableChain.V2.Run.stateBeforeTime E rho d x) := by
  rw [HoldsBefore]

-- GLY r3.16 READS; S3d §2.9 J-10 (a0-s3d-generic-forms-layout-r2.md:1000);
-- P3 r3.5.6:1662–1667 (F0.2 acceptsFinalBefore_of_idx).
-- A tick runs clock, then recordOwn. These local laws have no run argument
-- and impose no law on restore.
def MonoAlong (Q : P.State → Prop) : Prop :=
  (∀ st t, Q st → Q (P.clock st t)) ∧
  (∀ st o, Q st → Q (P.process st o)) ∧
  (∀ st o, Q st → Q (P.recordOwn st o))

-- Equation export required by BUILD §7.2 B3a.
omit [DecidableEq V] in
theorem MonoAlong_def (Q : P.State → Prop) :
    MonoAlong Q =
      ((∀ st t, Q st → Q (P.clock st t)) ∧
       (∀ st o, Q st → Q (P.process st o)) ∧
       (∀ st o, Q st → Q (P.recordOwn st o))) := by
  rw [MonoAlong]

-- P3:6438–6443; D12 removes the FG-SA arguments (p) and (c).
def Pending (rho : Run V P) (deadline : Time) (served : Nat → Prop) (i : Nat) : Prop :=
  (∃ e, rho.events[i]? = some e ∧ deadline ≤ e.time) →
    ∃ j < i, (∃ e', rho.events[j]? = some e' ∧ e'.time < deadline) ∧ served j

-- P3:6438–6443; equation export required by BUILD §7.2 B3a.
omit [DecidableEq V] in
theorem Pending_def (rho : Run V P) (deadline : Time) (served : Nat → Prop) (i : Nat) :
    Pending rho deadline served i =
      ((∃ e, rho.events[i]? = some e ∧ deadline ≤ e.time) →
        ∃ j < i, (∃ e', rho.events[j]? = some e' ∧ e'.time < deadline) ∧ served j) := by
  rw [Pending]

-- GLY:1118–1119 (plan citation GLY:1048–1050); closed statement per D01.
-- Keep the source binder name hS for the statement manifest.
set_option linter.unusedVariables false in
def StateBeforeIdxBeforeStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    (E : Generic.Env V) (rho : Run V P) (t : Time) (hS : ScheduleWellFormed E rho),
    Run.stateBefore E rho (Run.idxBefore rho t) = Run.stateBeforeTime E rho t

set_option linter.unusedVariables false in
theorem StateBeforeIdxBeforeStatement_def :
    StateBeforeIdxBeforeStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
        (E : Generic.Env V) (rho : Run V P) (t : Time) (hS : ScheduleWellFormed E rho),
        Run.stateBefore E rho (Run.idxBefore rho t) = Run.stateBeforeTime E rho t) := by
  rw [StateBeforeIdxBeforeStatement]

-- GLY r3.16 READS; S3d §2.9 J-10; P3 r3.5.6 F0.2. Closed statement per D01.
set_option linter.unusedVariables false in
def HoldsBeforeIffExistsIdxStatement : Prop :=
  ∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
    {E : Generic.Env V} {rho : Run V P} {Q : P.State → Prop} {d : Time} {x : V}
    (hNR : NoRestart rho) (hS : ScheduleWellFormed E rho) (hmono : MonoAlong Q),
    HoldsBefore E rho Q d x ↔
      ∃ i ≤ rho.events.length,
        (∀ k < i, ∃ e, rho.events[k]? = some e ∧ e.time < d) ∧
        Q (Run.stateBefore E rho i x)

-- Equation export required by BUILD §7.2 B3a; preserve the statement binders.
set_option linter.unusedVariables false in
theorem HoldsBeforeIffExistsIdxStatement_def :
    HoldsBeforeIffExistsIdxStatement =
      (∀ {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpec In}
        {E : Generic.Env V} {rho : Run V P} {Q : P.State → Prop} {d : Time} {x : V}
        (hNR : NoRestart rho) (hS : ScheduleWellFormed E rho) (hmono : MonoAlong Q),
        HoldsBefore E rho Q d x ↔
          ∃ i ≤ rho.events.length,
            (∀ k < i, ∃ e, rho.events[k]? = some e ∧ e.time < d) ∧
            Q (Run.stateBefore E rho i x)) := by
  rw [HoldsBeforeIffExistsIdxStatement]

end AvailableChain.Gen.V2
