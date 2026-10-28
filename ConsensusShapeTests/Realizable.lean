module
public import ConsensusShapeTests.Shape
public import Mathlib.Tactic
@[expose] public section

/-! # Realizability tests

* `coverage_keeps_selection`: `coverage` at a 3-node point with a selection
  that is *not* the extremal one (the proposer of every slot is key 2) returns
  a valid, collision-free run with exactly that selection.
* `contradictory_wf_not_realizable` (D-24): a structurally well-formed
  contract whose safety premise is `1 ≤ 0` is not realizable for any family:
  well-formedness is not non-vacuity. -/

namespace Consensus.Shape.Tests.Realizable
open Consensus Blocks Shape
open Consensus.Model (Public Key pubOf protoOf sysOf)
open Consensus.Shape.Tests.Shapes (schema trivialFamily)

/-- A contract with no specs (coverage does not look at the specs). -/
def emptyK : Contract schema ProgressReq := ⟨Unit, ⟨()⟩, 1, fun _ => none⟩

/-- Three validators, validator 0 faulty, everyone awake, `Δ = 1`, GST 0,
horizon 10, no submissions. -/
def point3 : EnvPoint (Fin 3) :=
  ⟨⟨1, by decide, 0, fun _ _ => true⟩, Finset.univ.erase 0, 10, fun _ _ => []⟩

/-- The identity PKI. -/
def key3 : Fin (Fintype.card (Fin 3)) ≃ Fin 3 := finCongr (Fintype.card_fin 3)

/-- Key 2 proposes at every slot; every key signs the committee kind; nobody
polls. -/
def sel3 : ShapeRole Unit → Finset (Fin (Fintype.card (Fin 3)))
  | .proposer _ => {⟨2, by simp⟩}
  | .duty _ _ => Finset.univ
  | .poll => ∅

theorem sel3_admits :
    ∀ r, ((protoOf (compiled trivialFamily) point3.env).selSpec r).Admits (sel3 r) := by
  intro r
  cases r with
  | proposer s =>
    change ({⟨2, by simp⟩} : Finset (Fin (Fintype.card (Fin 3)))).card =
      min 1 (Fintype.card (Fin 3))
    simp
  | duty s k => rfl
  | poll => rfl

/-- Coverage keeps a non-extremal selection. -/
theorem coverage_keeps_selection :
    ∃ rho : Model.Run (compiled trivialFamily) point3.env, rho.point = point3 ∧
      rho.key = key3 ∧ rho.sel = sel3 ∧ rho.sel (ShapeRole.proposer 7) = {⟨2, by simp⟩} ∧
      rho.ExecutionValid ∧ ¬ rho.HashCollision := by
  obtain ⟨rho, hp, hk, hs, hv, hn, -, -⟩ :=
    coverage trivialFamily emptyK .truth point3 (show (0 : Time) ≤ 10 by norm_num) key3 sel3
      sel3_admits (fun _ => 0) trivial
  exact ⟨rho, hp, hk, hs, by rw [hs]; rfl, hv, hn⟩

/-- A contract whose final safety premise is the contradiction `1 ≤ 0`. -/
def contradictoryK : Contract schema ProgressReq where
  Idx := Unit
  idx_nonempty := ⟨()⟩
  catchUp := 1
  spec
    | .final => some
        { safety := { premise := .le (.add .zero 1) .zero }
          live := ⟨fun _ => .truth, fun _ => .zero, fun _ => 0⟩ }
    | _ => none

/-- Well-formedness is not non-vacuity (D-24): `contradictoryK` is
well-formed, and no family realizes it. -/
theorem contradictory_wf_not_realizable :
    contradictoryK.WellFormed ∧
      ∀ (Info : Type) [DecidableEq Info] [Encodable Info] (F : ShapeFamily schema Info),
        ¬ contradictoryK.Realizable F := by
  refine ⟨⟨fun c s h => ?_⟩, fun Info _ _ F hR => ?_⟩
  · cases c
    · cases h
    · cases h
    · obtain rfl := Option.some.inj h
      exact ⟨⟨trivial, fun _ => trivial⟩, (fun _ h => nomatch h), fun _ => trivial,
        (fun _ h => nomatch h), (fun _ h => nomatch h), (fun _ h => nomatch h), fun _ => trivial,
        (fun _ h => nomatch h)⟩
  · obtain ⟨σ, n, E, rho, hw⟩ := hR.safety .final _ rfl
    have h := hw.premise
    change (0 : Time) + 1 ≤ 0 at h
    norm_num at h

end Consensus.Shape.Tests.Realizable

end
