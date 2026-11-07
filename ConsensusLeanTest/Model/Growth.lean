module
public import ConsensusLeanTest.Model.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
@[expose] public section

/-! # Key exposure at the arrival boundary

An unreleased signature is rejected before compromise, admitted at compromise,
and still subject to the selected-role credential, including inside a wrapper.
-/

namespace Consensus.Shape.Tests.Model.Growth
open Consensus.Model

/-- Key one is exposed at one; key zero remains honest. -/
def faults (t : Time) : Finset (Fin 2) := if 1 ≤ t then {1} else ∅

theorem faults_mono : Monotone faults := by
  intro a b hab
  unfold faults
  split_ifs with ha hb
  · exact Finset.Subset.refl _
  · exact False.elim (hb (ha.trans hab))
  · exact Finset.empty_subset _
  · exact Finset.Subset.refl _

/-- An adversarial object signed in a selected or unselected role. -/
def forged (role : Bool) : (protoOf family env).Object :=
  .mk (.signed 1 role) (.data ()) []

/-- An unsigned wrapper tests nested signatures under the same arrival-time rule. -/
def payload (nested role : Bool) : (protoOf family env).Object :=
  if nested then .mk .none (.data ()) [forged role] else forged role

def arrival (t : Time) (nested role : Bool) : Run family env :=
  Run.mk faults faults_mono 2 [.deliver 0 (payload nested role) t] (pkiFin 2) sel
    (fun _ _ => []) (fun _ _ => []) (fun _ => 0)

/-- At key exposure, no earlier honest release is required, even for a nested signature. -/
theorem arrival_at_compromise_unforgeable (nested role : Bool) :
    (arrival 1 nested role).Unforgeable := by
  intro i w o t he o' hc u hs hu
  have hi : i = 0 := by
    cases i with
    | zero => rfl
    | succ i => simp [arrival] at he
  subst i
  have he' : w = 0 ∧ o = payload nested role ∧ t = 1 := by
    simpa [arrival] using he.symm
  rcases he' with ⟨rfl, rfl, rfl⟩
  cases nested <;>
    simp [payload, forged, Obj.Contains, Obj.parts, Obj.parts.partsList] at hc <;>
    rcases hc with rfl | hc
  all_goals simp_all [Run.signerOf, payload, forged, Obj.signer?, Obj.auth, pkiFin,
    arrival, faults]
  all_goals
    apply hu
    apply Fin.ext
    simpa using (congrArg Fin.val hs).symm

/-- Before exposure the very same unreleased signature is rejected. -/
theorem arrival_before_compromise_rejected (nested : Bool) :
    ¬ (arrival 0 nested false).Unforgeable := by
  intro h
  have hc : Obj.Contains (payload nested false) (forged false) := by
    cases nested
    · exact .refl _
    · exact Obj.Contains.step (by simp [payload, Obj.carried]) (.refl _)
  obtain ⟨j, _, hj, _, _⟩ := h 0 0 _ 0 rfl _ hc 1 rfl
    (by simp [arrival, faults])
  omega

/-- Exposing key one does not select it for the singleton role owned by key zero. -/
theorem compromised_wrong_role_rejected (nested : Bool) :
    ¬ (arrival 1 nested true).Credentials := by
  intro h
  have hc : Obj.Contains (payload nested true) (forged true) := by
    cases nested
    · exact .refl _
    · exact Obj.Contains.step (by simp [payload, Obj.carried]) (.refl _)
  have hh := h 0 0 _ 1 rfl _ hc 1 true rfl
  simp [arrival, sel] at hh

/-- The credentialed object at exposure still satisfies the membership binding. -/
theorem compromised_selected_role_admitted (nested : Bool) :
    (arrival 1 nested false).Credentials := by
  intro i w o t he o' hc k r hs
  have hi : i = 0 := by
    cases i with
    | zero => rfl
    | succ i => simp [arrival] at he
  subst i
  have he' : w = 0 ∧ o = payload nested false ∧ t = 1 := by
    simpa [arrival] using he.symm
  rcases he' with ⟨rfl, rfl, rfl⟩
  cases nested <;>
    simp [payload, forged, Obj.Contains, Obj.parts, Obj.parts.partsList] at hc <;>
    rcases hc with rfl | hc
  all_goals try subst o'
  all_goals simp_all [Obj.auth, sel, arrival]
  all_goals obtain ⟨rfl, rfl⟩ := hs; exact Finset.mem_univ _

/-- A conflicting data bit, signed honestly once and contradicted after exposure. -/
def bitProto (pub : Public) : Protocol pub Unit :=
  { proto pub with
    Body := Bool
    decBody := inferInstance
    act := fun _ _ => ((), [(.data false, [])])
    gossip := fun _ _ => []
    process := fun _ _ _ => ()
    recordOwn := fun _ _ _ => ()
    dependencies := .trivial _
    isFGAtt := fun _ => False
    conflicts := fun a b => decide (a.msg ≠ b.msg) }

def bitFamily : ProtocolFamily schema := bitProto

def bitEnv : Env (Fin 2) := ⟨1, by decide, 1, by decide, fun _ _ => true⟩

def honestBit : (protoOf bitFamily bitEnv).Object :=
  .mk (.signed 1 false) (.data false) []

def forgedBit : (protoOf bitFamily bitEnv).Object :=
  .mk (.signed 1 false) (.data true) []

/-- Both keys tick before exposure; only key zero acts afterwards and receives the forgery. -/
def growthRun : Run bitFamily bitEnv :=
  Run.mk faults faults_mono 1
    [.tick 0 0, .tick 1 0, .tick 0 1, .deliver 0 forgedBit 1]
    (pkiFin 2) sel (fun _ _ => []) (fun _ _ => []) (fun _ => 0)

/-- Non-vacuity at L1: the honest release and the post-exposure forgery share a valid run. -/
theorem growth_run_valid : growthRun.ExecutionValid := by
  refine ⟨by decide, ?_, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [growthRun, Event.keyLe, Event.time, Event.phase]
  · intro e he
    simp only [growthRun, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> decide
  · intro e he
    simp only [growthRun, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> decide
  · intro v t ht hh hv _
    change t ≤ 1 at hh
    fin_cases v <;> interval_cases t <;> simp_all [growthRun, faults]
  · intro v t _; rfl
  · intro v o t _; rfl
  · intro v t he
    simp [growthRun] at he
  · intro v t _ _ _ h
    simp [Wakes, bitEnv] at h
  · intro i v o t he q hq u hu hs
    have hi : i < 4 := (List.getElem?_eq_some_iff.mp he).1
    interval_cases i <;> simp [growthRun] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have hq' : q = forgedBit := List.mem_singleton.mp hq
    subst q
    change some (1 : Fin 2) = some u at hu
    cases Option.some.inj hu
    exact False.elim (hs (by simp [growthRun, faults]))
  · intro r
    cases r
    · rfl
    · change ({0} : Finset (Fin 2)).card = min 1 2
      decide
  · intro i v o t he q hq k r ha
    have hi : i < 4 := (List.getElem?_eq_some_iff.mp he).1
    interval_cases i <;> simp [growthRun] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have hq' : q = forgedBit := List.mem_singleton.mp hq
    subst q
    simp only [forgedBit, Obj.auth] at ha
    obtain ⟨rfl, rfl⟩ := ha
    exact Finset.mem_univ _

/-- The exposed key really released the first bit before compromise. -/
theorem growth_run_honest_release : honestBit ∈ growthRun.releasesAt 1 := by
  decide

/-- Both the honest release and the conflicting forgery occur in honest historical views. -/
theorem growth_run_slashable : growthRun.Slashable growthRun.Observed 1 := by
  refine ⟨honestBit, ?_, forgedBit, ?_, rfl, rfl, by decide⟩
  · exact ⟨1, 2, by decide, by simp [EnvPoint.HonestAt, Run.point, growthRun, faults,
      Run.cutTime, Event.time], by
        change honestBit ∈ closure (growthRun.stateBefore 2 1).seen
        decide⟩
  · exact ⟨0, 4, by decide, by simp [EnvPoint.HonestAt, Run.point, growthRun, faults,
      Run.cutTime, Event.time], by
        change forgedBit ∈ closure (growthRun.stateBefore 4 0).seen
        decide⟩

/-- The same key cannot be convicted by the honest evidence collected before exposure. -/
theorem growth_run_nonframing_before :
    ¬ growthRun.Slashable
      {o | ∃ v i, i ≤ growthRun.events.length ∧ growthRun.cutTime i ≤ 0 ∧
        o ∈ growthRun.ViewIdx v i} 1 :=
  growthRun.honestNeverSlashed growth_run_valid 1 0
    (by simp [growthRun, faults])

/-- Compromise is not a restart: the exposed node's honest history remains in `seen`. -/
theorem compromise_preserves_seen :
    (growthRun.stateBefore 2 1).seen = (growthRun.stateBefore 4 1).seen ∧
      honestBit ∈ (growthRun.stateBefore 4 1).seen := by
  decide

end Consensus.Shape.Tests.Model.Growth
end
