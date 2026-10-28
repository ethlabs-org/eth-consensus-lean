module
public import ConsensusShape
public import Mathlib.Tactic
@[expose] public section

/-! # Tests of the Goldilocks value and sheet

* `reference_numbers`: the pinned formulas give the FG-SA paper's reference
  numbers (`reference_bounds`), and the heal and latency tables read them.
* `pp223_admissible`: the pinned numbers at `R = 2`, `lockK = 2`, `eta = 3`
  are admissible; `pp223_numbers`: catch-up `18`, lag `4`, budget `3`,
  look-back `η = 3`.
* `range_head_instance`: at `R = 2`, `gf = 1` the finality recurrence (`8`
  consecutive proposers per `2` slots) gives one honest head per `2` slots,
  losing `7` slots of span.
* `target_unfolds`: `GoldilocksTarget` is bindings, acceptance and extras
  (`rfl`).
* `stable_is_confirmed`: the schema aliases stable to confirmed (`rfl`). -/

namespace Consensus.Shape.Tests.Goldilocks

open Consensus Blocks Shape

/-- `R = 2`, `lockK = 2`, `eta = 3`. -/
def pp223 : FGSAParams := ⟨2, 2, 3, le_rfl, le_rfl, by decide⟩

/-- The reference numbers, and the heal and latency tables at them. -/
theorem reference_numbers :
    (⟨2, 2, 1, le_rfl, le_rfl, le_rfl⟩ : FGSAParams).bhf 2 = 295 ∧
      (⟨3, 2, 1, by decide, le_rfl, le_rfl⟩ : FGSAParams).bhf 2 = 343 ∧
      pp223.heal .available 2 = 29 + 295 ∧ pp223.heal .stable 2 = 29 + 295 ∧
      pp223.latency .available 2 = 14 ∧
      pp223.heal .final 1 = 29 + pp223.bhf 2 + pp223.wW 1 ∧
      pp223.latency .final 1 = 4 * 2 + 6 + pp223.wW 1 :=
  ⟨reference_bounds.1, reference_bounds.2.1, by decide, by decide, by decide, rfl, rfl⟩

/-- The pinned numbers are admissible at `⟨2, 2, 3⟩`. -/
theorem pp223_admissible : (goldilocksContract pp223).params.Admissible :=
  goldilocks_admissible pp223

/-- The pinned outage and catch-up numbers at `⟨2, 2, 3⟩`; standard
thresholds. -/
theorem pp223_numbers :
    (goldilocksContract pp223).params.catchUp = 18 ∧ (goldilocksContract pp223).params.lag = 4 ∧
      (goldilocksContract pp223).params.budget = 3 ∧ (goldilocksContract pp223).params.η = 3 ∧
      (goldilocksContract pp223).params.θ = 1 / 2 ∧ (goldilocksContract pp223).params.φ = 2 / 3 ∧
      (goldilocksContract pp223).params.cover = 1 / 2 ∧
      (goldilocksContract pp223).params.α = 1 / 3 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The finality recurrence at `R = 2`, `gf = 1`: `8` consecutive proposers
(span `7`) per window of `2` slots. -/
theorem finRec_shape :
    (pp223.finRec 1).pattern.span = 7 ∧ ((pp223.finRec 1).gap : Nat) = 2 := by
  refine ⟨?_, rfl⟩
  exact (Pattern.span_range _).trans rfl

/-- Head extraction at `R = 2`, `gf = 1`: one honest head per `2` slots, the
window's stop moved back by `7` slots. -/
theorem range_head_instance {V R : Type} [Fintype V] {p : EnvPoint V}
    {key : Fin (Fintype.card V) ≃ V} {sel : R → Finset (Fin (Fintype.card V))}
    {lead : Slot → R} {G : TimeGrid} {c start stop : Time}
    (h : PatternRecurrence p key sel lead G (pp223.finRec 1) c start stop) :
    PatternRecurrence p key sel lead G ⟨Pattern.single, 2⟩ c start
      (min stop p.horizon - 7 * G.slotLen p.env.Δ) :=
  range_head pp223 1 h

/-- The target is the bindings, acceptance at the pinned numbers, and the
extras. -/
theorem target_unfolds {Info : Type} [DecidableEq Info] [Encodable Info]
    (F : ShapeFamily goldilocksSchema Info) (pp : FGSAParams) :
    GoldilocksTarget F pp =
      (GoldilocksBindings F ∧ Accepted F (goldilocksContract pp) ∧ GoldilocksExtra F pp) :=
  rfl

/-- The schema aliases stable (and available) to confirmed. -/
theorem stable_is_confirmed :
    goldilocksSchema.output .stable = some GOut.confirmed ∧
      goldilocksSchema.output .available = some GOut.confirmed ∧
      goldilocksSchema.output .final = some GOut.finalized :=
  ⟨rfl, rfl, rfl⟩

end Consensus.Shape.Tests.Goldilocks

end
