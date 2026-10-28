module
public import ConsensusProblem
public import Mathlib.Tactic
@[expose] public section

/-! # Layer-0 tests: premises, contracts, resilience

Well-formedness of the named terms and its limits, the extremal point, the
FG-SA cover counting step, the after-window part of resilience, and two
contract-level checks (zero escape; provided capability without a spec). -/

namespace Consensus.Shape.Tests.Premise

/-- The honest-majority sleepy term is well-formed. -/
theorem honestMajority_wellFormed : (Premise.honestMajority : Premise Unit).WellFormed := by
  refine ⟨trivial, trivial, ?_⟩
  change (0 : ℚ) ≤ 1 / 2 ∧ (1 / 2 : ℚ) < 1
  norm_num

/-- An inclusive fraction 1 is not well-formed (it would force no faults,
`EnvPoint.readyOfAllAtLeast_one_faulty_empty`). -/
theorem not_wellFormed_readyOfAll_one :
    ¬ (Premise.atTime .zero (.readyOfAll 1 true) : Premise Unit).WellFormed := by
  rintro ⟨_, h⟩
  exact lt_irrefl _ h

/-- The extremal point with four validators (one faulty) satisfies the
environment part of the honest-majority term when GST is at most 0. -/
theorem extremal_honestMajority (H g : Time) (submit : Fin 4 → Time → List Tx)
    (c : Time) (σ : Nat → Time) (hg : g ≤ 0) :
    (Premise.honestMajority : Premise Unit).evalEnv (EnvPoint.extremal 3 H g submit) c σ := by
  refine ⟨hg, trivial, fun t _ _ => ?_⟩
  change (EnvPoint.extremal 3 H g submit).ReadyAbove (1 / 2) c t
  unfold EnvPoint.ReadyAbove
  rw [EnvPoint.extremal_faulty, EnvPoint.extremal_readyAt]
  simp only [Finset.mem_univ, Finset.card_erase_of_mem, Finset.card_univ, Fintype.card_fin,
    Finset.card_singleton]
  norm_num

/-- The cover counting step on four validators: with `C` the ready set at the
outage start, one faulty validator and no uncovered wakers,
`2·|faulty ∪ W| < n`. -/
theorem coverMajority_outageE1_shape (H g : Time) (submit : Fin 4 → Time → List Tx)
    (c t : Time) :
    2 * ((EnvPoint.extremal 3 H g submit).faulty ∪ ∅).card < Fintype.card (Fin 4) := by
  have hR := EnvPoint.extremal_readyAt 3 H g submit c t
  refine (EnvPoint.extremal 3 H g submit).two_mul_card_faulty_union_lt
    (C := (EnvPoint.extremal 3 H g submit).readyAt c t) subset_rfl ?_
    (Finset.disjoint_empty_left _) ?_
  · intro v hv
    rw [hR] at hv
    exact hv
  · unfold EnvPoint.ReadyOfAll
    rw [hR]
    simp only [Finset.mem_univ, Finset.card_erase_of_mem, Finset.card_univ, Fintype.card_fin]
    norm_num

/-- Two nodes, always awake; the read of output `()` is `[1]` until cut 2
(time 2), then `[2]`. -/
def afterWindow : Trace Bool Nat Unit :=
  ⟨⟨⟨1, by decide, 0, fun _ _ => true⟩, Finset.univ, 2, fun _ _ => []⟩, 2,
    fun i => (i : Int), fun _ _ i => if i = 2 then [2] else [1]⟩

/-- The protected read at `T = 0` is a prefix of the reader's read at the outage
start `b₀ = 1`, but resilience fails: at the horizon `2 > b₀` the reader has
switched branch. The after-window part of `ProtectedThrough` has teeth. -/
theorem protected_after_window :
    afterWindow.readAt () true 0 <+: afterWindow.readAt () false 1 ∧
      ¬ afterWindow.ProtectedThrough 0 () () 0 1 := by
  refine ⟨by decide, fun h => ?_⟩
  have hp := h true (Finset.mem_univ _) 2 (by decide) (by decide) false (Finset.mem_univ _)
    (fun _ _ _ => rfl)
  revert hp
  decide

/-- One output serving every capability. -/
def oneOutput : OutputSchema := ⟨Unit, fun _ => some ()⟩

/-- A capability spec with escape `some 0` (which would make safety vacuous). -/
def zeroEscapeSpec : CapSpec Unit Unit :=
  { safety := { premise := .truth, escape := some 0 }
    live := ⟨fun _ => .truth, fun _ => .zero, fun _ => 0⟩ }

/-- A contract whose final capability has escape `some 0`. -/
def zeroEscape : Contract oneOutput Unit :=
  ⟨Unit, ⟨()⟩, 1, fun c => if c = .final then some zeroEscapeSpec else none⟩

/-- An escape `α = 0` is rejected by well-formedness. -/
theorem escape_zero_not_wellFormed : ¬ zeroEscape.WellFormed := by
  intro h
  have := (h.caps .final zeroEscapeSpec rfl).safetyEscape 0 rfl
  exact lt_irrefl _ this.1

/-- A provided final capability without a spec makes the headline unprovable
(not vacuous): `provided` fails. -/
theorem provided_mismatch {V : Type} [Fintype V] [DecidableEq V] {Prog : Type}
    (S : System V) (X : ExecProfile S Prog) (K : Contract S.schema Prog)
    (hS : (S.schema.output .final).isSome) (hK : K.spec .final = none) :
    ¬ ProblemClaims S X K := by
  intro h
  have := h.provided .final
  rw [hK, hS] at this
  exact Bool.noConfusion this

end Consensus.Shape.Tests.Premise
end
