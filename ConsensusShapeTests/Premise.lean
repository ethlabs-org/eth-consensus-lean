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
  norm_num [Premise.honestMajority, Premise.sleepy, Premise.always, Premise.WellFormed,
    TimeExpr.HorizonFree, TimeExpr.Fixed, EnvAtom.WellFormed]

/-- A fraction 1 of all validators ready is not well-formed (it would force no
faults). -/
theorem not_wellFormed_readyOfAll_one :
    ¬ (Premise.atTime .zero (.readyOfAll 1) : Premise Unit).WellFormed := by
  rintro ⟨_, h⟩
  exact lt_irrefl _ h.2

/-- An absolute fault bound of zero is not well-formed. -/
theorem not_wellFormed_faultsAtMost_zero :
    ¬ (Premise.atTime .zero (.faultsAtMost 0) : Premise Unit).WellFormed := by
  rintro ⟨_, h⟩
  simp [EnvAtom.WellFormed] at h

/-! ### No horizon or parameter caps -/

/-- A run-length cap (the time bomb: claims only for runs ending by `1000·Δ`)
is not well-formed. -/
theorem horizonCap_rejected :
    ¬ (Premise.conj (Premise.sleepy (1 / 2)) (.le .horizon (.addΔ .zero 1000)) :
      Premise Unit).WellFormed := by
  rintro ⟨-, h, -⟩
  exact h

/-- A parameter cap (resilience only for the read at time 0) is not
well-formed. -/
theorem protectedAtCap_rejected :
    ¬ (Premise.le .protectedAt .zero : Premise Unit).WellFormed := by
  rintro ⟨-, h⟩
  exact h trivial

/-- A parameter bounded by a fixed time through the GST is not well-formed
either. -/
theorem gstCap_rejected :
    ¬ (Premise.le .protectedAt (.addΔ .gst 1000) : Premise Unit).WellFormed := by
  rintro ⟨-, h⟩
  exact h trivial

/-- An atom required only at the horizon is not well-formed. -/
theorem atHorizon_rejected :
    ¬ (Premise.atTime .horizon .full : Premise Unit).WellFormed := by
  rintro ⟨h, -⟩
  exact h

/-- A liveness start at the horizon (vacuous liveness) is not well-formed. -/
theorem horizonStart_rejected :
    ¬ ({ safety := { premise := .truth }
         live := ⟨fun _ => .sync, fun _ => .horizon, fun _ => 0⟩ } :
        CapSpec Unit Unit).WellFormed := by
  intro h
  exact h.liveStart ()

/-- The outage window is well-formed, and its timing constraints survive
moving the parameters and the horizon later (`Premise.TimesHold.shift`). -/
theorem outageWindow_shift (p : EnvPoint (Fin 4)) (σ : Nat → Time) (d e : Time) (hd : 0 ≤ d)
    (he : 0 ≤ e) (h : (Premise.outageWindow 1 2 : Premise Unit).TimesHold p σ) :
    (Premise.outageWindow 1 2 : Premise Unit).TimesHold
      { p with horizon := p.horizon + d + e } (fun i => σ i + d) :=
  Premise.TimesHold.shift (by
    norm_num [Premise.outageWindow, Premise.WellFormed, TimeExpr.HorizonFree, TimeExpr.Fixed])
    hd he h

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
      ¬ afterWindow.ProtectedThrough 0 () () 0 1 1 := by
  refine ⟨by decide, fun h => ?_⟩
  have hp := h true (Finset.mem_univ _) 2 (by decide) (by decide) false (Finset.mem_univ _)
    (Or.inl fun _ _ _ => rfl)
  revert hp
  decide

/-- Reader `false` sleeps during the window `[1, 2)` and wakes at 2; from cut 4
on its read is empty. Resilience fails: with catch-up 0 it is caught up after
the window at time 4 (`2 ≤ 4 − 0 − 1`), so it is an eligible reader. Readers
waking after the outage are covered. -/
def wakeAfter : Trace Bool Nat Unit :=
  ⟨⟨⟨1, by decide, 0, fun v u => v || decide (u < 1 ∨ 2 ≤ u)⟩, Finset.univ, 5,
      fun _ _ => []⟩, 5,
    fun i => (i : Int), fun _ v i => if v then [1] else if 4 ≤ i then [] else [1]⟩

theorem protected_wake_after : ¬ wakeAfter.ProtectedThrough 0 () () 0 1 2 := by
  intro h
  have hr : wakeAfter.ResilienceReader 0 1 2 false 4 := by
    refine Or.inr ⟨by decide, fun u h1 _ => ?_⟩
    show (false || decide (u < 1 ∨ 2 ≤ u)) = true
    simp only [Bool.false_or, decide_eq_true_eq]
    right; norm_num at h1; linarith
  have hp := h true (Finset.mem_univ _) 4 (by decide) (by decide) false (Finset.mem_univ _) hr
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
