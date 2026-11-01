module
public import AvailableChainGeneric.Statements.Pure.FirstBad

public section

/-! P3 is `fgsa-f0-f2-plan-r3.5-2a9a5877.md`, Appendix A.1.
Step-2 item I02; ruling D02 requires these proofs now. -/

namespace AvailableChain.Gen.Pure

open AvailableChain

-- P3:6412–6413: strong induction from the rule alone.
theorem AGRule.holds {GR GT : Nat → Prop} (h : AGRule GR GT) : ∀ i, GR i ∧ GT i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    have hGT : ∀ j < i, GT j := fun j hj => (ih j hj).2
    have hGR : GR i := h.fg i hGT
    exact ⟨hGR, h.ac i hGR hGT⟩

-- P3:6418.
theorem firstFailure_holds {fail : Nat → Prop} (h : FirstFailure fail) : ∀ i, ¬ fail i := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih => exact h i ih

-- P3:6433–6434.
theorem WindowRule.holds {GRw GTw : Slot → Prop} (h : WindowRule GRw GTw) :
    ∀ s, GRw s ∧ GTw s := by
  exact AGRule.holds ⟨h.fg, h.ac⟩

end AvailableChain.Gen.Pure
