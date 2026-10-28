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
  well-formedness is not non-vacuity.
* `confinedOutage_not_realizable`: a well-formed resilience premise that
  confines outages to a bounded period through a participation atom over a
  fixed time (`full` from time 100 on) is not realizable: resilience
  witnesses are needed at arbitrarily late protected reads.
* `allProposers_no_witness` (review B2): a family whose proposer selection is
  `.sized (max 1 n)` selects every key at every slot of a valid run, so on a
  run with a faulty validator its pattern recurrence fails as soon as one
  window fits in the horizon: such a progress requirement has no witness with
  a faulty validator. -/

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

/-- A resilience premise that confines outages to before time 100. -/
def confinedK : Contract schema ProgressReq where
  Idx := Unit
  idx_nonempty := ⟨()⟩
  catchUp := 1
  spec
    | .stable => some
        { safety := { premise := .truth }
          live := ⟨fun _ => .sync, fun _ => .zero, fun _ => 0⟩
          resilience := some (.throughout (.add .zero 100) .horizon .full) }
    | _ => none

/-- The confining premise is well-formed, and no family realizes it. -/
theorem confinedOutage_not_realizable :
    (Premise.throughout (.add .zero 100) .horizon .full : Premise ProgressReq).WellFormed ∧
      ∀ (Info : Type) [DecidableEq Info] [Encodable Info] (F : ShapeFamily schema Info),
        ¬ confinedK.Realizable F := by
  refine ⟨⟨trivial, trivial⟩, fun Info _ _ F hR => ?_⟩
  obtain ⟨σ, n, E, rho, hw, ha, hk⟩ := hR.resilience .stable _ _ rfl rfl 100
  obtain ⟨-, h01, -, h2H, ⟨v, hv, t, ht1, ht2, hsl⟩, -⟩ := ha
  have hΔ : (1 : Time) ≤ E.Δ := E.Δ_pos
  have h100 : (100 : Time) ≤ t := by
    have := le_max_left 0 E.gst
    push_cast at hk
    nlinarith
  have hfull := hw.premise t (by change (0 : Time) + 100 ≤ t; linarith)
    (by change t ≤ rho.horizon; linarith) v hv
  change E.awake v t = true at hfull
  rw [hfull] at hsl
  exact Bool.noConfusion hsl

/-- Review B2 regression: with `proposerSel := .sized (max 1 n)` every key is
selected at every slot of a valid run, so a faulty validator is always among
the proposers and `PatternRecurrence` (every selected key honest and ready)
fails whenever one window fits in the horizon. -/
theorem allProposers_no_witness {O : OutputSchema} {Info : Type} [DecidableEq Info]
    [Encodable Info] {F : ShapeFamily O Info}
    (hF : ∀ pub, (F pub).skel.proposerSel = .sized (max 1 pub.n))
    {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (rho : Model.Run (compiled F) E)
    (hsel : rho.SelValid) (hf : rho.point.faulty.Nonempty) (π : ProgressReq) (c start : Time)
    (hw : max start 0 + ((π.gap : Nat) : Time) * (F (pubOf E)).skel.grid.slotLen E.Δ ≤
      rho.horizon) :
    ¬ PatternRecurrence (R := ShapeRole (F (pubOf E)).skel.Kind) rho.point rho.key rho.sel
      ShapeRole.proposer (F (pubOf E)).skel.grid π c start := by
  intro h
  obtain ⟨f, hf⟩ := hf
  have hfh : f ∉ rho.honest := (Finset.mem_sdiff.mp hf).2
  obtain ⟨s, -, -, hall⟩ := h (max start 0) (le_max_left _ _) (le_max_right _ _) hw
  obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil _ π.pattern.nonempty
  have hadm := hsel (ShapeRole.proposer (s + j))
  change ((F (pubOf E)).skel.proposerSel).Admits (rho.sel (ShapeRole.proposer (s + j))) at hadm
  rw [hF] at hadm
  change (rho.sel (ShapeRole.proposer (s + j))).card = min (max 1 (Fintype.card V))
    (Fintype.card V) at hadm
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨f⟩
  rw [max_eq_right hn, min_self] at hadm
  have huniv : rho.sel (ShapeRole.proposer (s + j)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hadm, Fintype.card_fin])
  have hk : rho.key.symm f ∈ rho.sel (ShapeRole.proposer (s + j)) := by
    rw [huniv]; exact Finset.mem_univ _
  have := ((hall j hj).2 _ hk).1
  rw [Equiv.apply_symm_apply] at this
  exact hfh this

end Consensus.Shape.Tests.Realizable

end
