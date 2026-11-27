module
public import ConsensusLean.Instances.Goldilocks.Spec.FG.Store.View

public section

/-! # The shadow P-U frame key

The key records the maximum height and whether justification is one height below it.
Its arithmetic interface uses only monotone heights and `hj < hmax`, so it applies to
shadow executions without assuming any stock frame or run law.
-/

namespace Consensus.Goldilocks.Healing

open Classical in
/-- The shadow key: twice the maximum height, with one extra step in a top frame. -/
noncomputable def frameKey'' {P : Params} {ACP : Type} (st : Store P ACP) : Nat :=
  2 * st.hmax + if st.hmax = st.hj + 1 then 1 else 0

open Classical in
theorem frameKey''_def {P : Params} {ACP : Type} (st : Store P ACP) :
    frameKey'' st = 2 * st.hmax + if st.hmax = st.hj + 1 then 1 else 0 := by
  rfl

variable {P : Params} {ACP : Type} {a b : Store P ACP}

/-- Monotone store heights imply a monotone key; at fixed `hmax`, top cannot become gap. -/
theorem frameKey''_mono (hm : a.hmax ≤ b.hmax) (hj : a.hj ≤ b.hj)
    (hb : b.hj < b.hmax) : frameKey'' a ≤ frameKey'' b := by
  classical
  rw [frameKey''_def, frameKey''_def]
  split_ifs <;> omega

/-- Apply the arithmetic comparison to the stores along an honest node's cuts. -/
theorem frameKey''_monotone {st : Nat → Store P ACP}
    (hm : Monotone fun i => (st i).hmax) (hj : Monotone fun i => (st i).hj)
    (hlt : ∀ i, (st i).hj < (st i).hmax) : Monotone fun i => frameKey'' (st i) := by
  intro i j hij
  exact frameKey''_mono (hm hij) (hj hij) (hlt j)

/-- On two consecutive maximum heights, the key lies in four consecutive values. -/
theorem frameKey''_bounds {HZ : Nat} (hlo : HZ ≤ a.hmax) (hhi : a.hmax ≤ HZ + 1) :
    2 * HZ ≤ frameKey'' a ∧ frameKey'' a ≤ 2 * HZ + 3 := by
  classical
  rw [frameKey''_def]
  split_ifs <;> omega

/-- Equal keys are exactly equal maximum heights and equal top status. Applied pointwise,
this says that a constant key on a window is equivalent to constant `(M, isTop)`. -/
theorem frameKey''_eq_iff : frameKey'' a = frameKey'' b ↔
    a.hmax = b.hmax ∧ ((a.hmax = a.hj + 1) ↔ (b.hmax = b.hj + 1)) := by
  classical
  rw [frameKey''_def, frameKey''_def]
  split_ifs <;> simp_all <;> omega

end Consensus.Goldilocks.Healing

end
