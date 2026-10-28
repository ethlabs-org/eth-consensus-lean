module
public import ConsensusShapeTests.Shape
public import Mathlib.Tactic
@[expose] public section

/-! # Coverage and progress-fit tests

* `coverage_keeps_selection`: `coverage` at a 3-node point with a selection
  that is *not* the extremal one (the proposer of every slot is key 2) returns
  a valid, collision-free run with exactly that selection, for every GST.
* `allProposers_no_witness` (review B2): a family whose proposer selection is
  `.sized (max 1 n)` selects every key at every slot of a valid run, so on a
  run with a faulty validator its pattern recurrence fails as soon as one
  whole window fits in `[start, stop]` and the horizon: such a progress
  requirement has no witness with a faulty validator.
* `allProposers_unfit`: acceptance rejects it up front (`ProgressFits` needs
  `.sized 1` for a recurrence).
* `noProgressFit`: a recurrence on a poll skeleton (no slot proposers) does
  not fit; `notReadyAtMost_fits` (round robin) fits every skeleton. -/

namespace Consensus.Shape.Tests.Realizable
open Consensus Blocks Shape
open Consensus.Model (Public Key pubOf protoOf sysOf)
open Consensus.Shape.Tests.Shapes (schema trivialFamily pollSkel pollShape)

/-- Three validators, validator 0 faulty, everyone awake, `Δ = 1`, horizon
10, no submissions. -/
def point3 : EnvPoint (Fin 3) :=
  ⟨⟨1, by decide, fun _ _ => true⟩, Finset.univ.erase 0, 10, fun _ _ => []⟩

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

/-- Coverage keeps a non-extremal selection, for every GST. -/
theorem coverage_keeps_selection (g : Time) :
    ∃ rho : Model.Run (compiled trivialFamily) point3.env, rho.point = point3 ∧
      rho.key = key3 ∧ rho.sel = sel3 ∧ rho.sel (ShapeRole.proposer 7) = {⟨2, by simp⟩} ∧
      rho.ExecutionValid ∧ ¬ rho.HashCollision ∧ CommLog.EagerFrom rho.point rho.log g := by
  obtain ⟨rho, hp, hk, hs, hv, hn, -, he⟩ :=
    coverage trivialFamily point3 (show (0 : Time) ≤ 10 by norm_num) key3 sel3 sel3_admits g
  exact ⟨rho, hp, hk, hs, by rw [hs]; rfl, hv, hn, he⟩

/-- Review B2 regression: with `proposerSel := .sized (max 1 n)` every key is
selected at every slot of a valid run, so a faulty validator is always among
the proposers and `PatternRecurrence` (every selected key honest and ready)
fails whenever one window fits in the horizon. -/
theorem allProposers_no_witness {O : OutputSchema} {Info : Type} [DecidableEq Info]
    [Encodable Info] {F : ShapeFamily O Info}
    (hF : ∀ pub, (F pub).skel.proposerSel = .sized (max 1 pub.n))
    {V : Type} [Fintype V] [DecidableEq V] {E : Env V} (rho : Model.Run (compiled F) E)
    (hsel : rho.SelValid) (hf : rho.point.faulty.Nonempty) (π : Recurrence) (c start stop : Time)
    (hs : max start 0 + (π.len : Time) * (F (pubOf E)).skel.grid.slotLen E.Δ ≤ stop)
    (hw : max start 0 + (π.len : Time) * (F (pubOf E)).skel.grid.slotLen E.Δ ≤ rho.horizon) :
    ¬ PatternRecurrence (R := ShapeRole (F (pubOf E)).skel.Kind) rho.point rho.key rho.sel
      ShapeRole.proposer (F (pubOf E)).skel.grid π c start stop := by
  intro h
  obtain ⟨f, hf⟩ := hf
  have hfh : f ∉ rho.honest := (Finset.mem_sdiff.mp hf).2
  obtain ⟨s, -, -, hall⟩ := h (max start 0) (le_max_left _ _) (le_max_right _ _) hs hw
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

/-- Acceptance rejects the all-proposers family up front: a recurrence
requirement does not fit `.sized (max 1 n)` once `n ≥ 2`. -/
theorem allProposers_unfit {O : OutputSchema} {Info : Type} [DecidableEq Info]
    [Encodable Info] {F : ShapeFamily O Info}
    (hF : ∀ pub, (F pub).skel.proposerSel = .sized (max 1 pub.n))
    (K : Contract O ProgressReq) (cap : Capability) (i : K.Idx) (ρ : Recurrence)
    (hK : K.progress cap i = .recur ρ) : ¬ K.ProgressFits F := by
  intro h
  have := h cap i ⟨2, 1, by decide⟩
  rw [hK] at this
  change (F ⟨2, 1, by decide⟩).skel.proposerSel = .sized 1 at this
  rw [hF] at this
  cases this

/-- A recurrence does not fit a poll skeleton (no slot proposers). -/
theorem noProgressFit (n : Nat) (ρ : Recurrence) : ¬ (ProgressReq.recur ρ).Fits (pollSkel n) := by
  intro h
  cases h

/-- No contract with a recurrence requirement fits the poll shape. -/
theorem noProgressFit_contract (K : Contract schema ProgressReq) (cap : Capability) (i : K.Idx)
    (ρ : Recurrence) (hK : K.progress cap i = .recur ρ) :
    ¬ K.ProgressFits (fun pub => pollShape pub) := by
  intro h
  have := h cap i ⟨1, 1, by decide⟩
  rw [hK] at this
  exact noProgressFit 1 ρ this

/-- A bound on the validators not ready fits every skeleton (round robin). -/
theorem notReadyAtMost_fits {n : Nat} (sk : Skeleton n) (m : ℕ+) :
    (ProgressReq.notReadyAtMost m).Fits sk := trivial

end Consensus.Shape.Tests.Realizable

end
