module
public import ConsensusLean.Proofs.ComparisonCoverage.Slice1.Forgery
public import ConsensusLean.Proofs.ComparisonCoverage.Witness
public import ConsensusLean.Comparison.HealCoverage
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Slice 1 coverage: the forgery plan

`exists_plan`: for compromised validators `Apre` (forged before `b₁`) and `Apost` (forged from
`b₁` on), a selection and a forgery plan such that every forged key holds a credential for its role,
the selection is the extremal one on the proposer roles, every planned time is at or after its
role's floor, the plan injects each forged object at one time only, and the keys forged before
`b₁` (respectively from `b₁` through `H`) are exactly those of `Apre` (respectively `Apost`).

With no activity the plan is empty and the selection extremal. Otherwise the family has a
forgeable role (`ForgeableRole`):
* a poll role admitting every key: every forgery is signed in the poll role (no floor), those of
  `Apre` at `0` and those of `Apost` at `b₁` (with a tag, so a key in both lists forges two distinct
  objects);
* a committee kind `k₀` admitting any one key: the validator of key `j` forges at slot `j` (time
  `j·slotLen < b₁`) and at slot `P + j` (time `(P + j)·slotLen ≥ b₁`, `P = b₁`), in the duty role of
  that slot, whose floor is the slot's time; the selection of `k₀` at each forged slot is one
  containing its key. -/

namespace Consensus.Comparison

open Shape Blocks
open Consensus.Model (pubOf protoOf sysOf Obj Msg)

variable {V : Type} [Fintype V] [DecidableEq V] {O : OutputSchema} {Info : Type}
  [DecidableEq Info] [Countable Info]

/-- The plan entries of a list of validators: key, role, message, tag and time as functions of the
validator. -/
def planOf (key : Fin (Fintype.card V) ≃ V) {F : Model.ProtocolFamily O} {E : Env V}
    (rf : V → (protoOf F E).Role) (m : Msg (protoOf F E).Item (protoOf F E).Body) (tag : Bool)
    (tf : V → Time) (l : List V) : List (Forgery F E) :=
  l.map fun v => ⟨key.symm v, rf v, m, tag, tf v⟩

/-- The properties of a selection and a forgery plan for `Apre` before `b₁` and `Apost` from `b₁`
through `H`. -/
structure PlanProps (F : ChainShapeFamily O Info) (E : Env V) (key : Fin (Fintype.card V) ≃ V)
    (Apre Apost : List V) (b₁ H : Time)
    (sel : (protoOf (compiled F) E).Role → Finset (Fin (Fintype.card V)))
    (fs : List (Forgery (compiled F) E)) : Prop where
  admits : (protoOf (compiled F) E).SelAdmits sel
  proposer : ∀ s, sel (.proposer s) = extremalSel F E (.proposer s)
  cred : ∀ x ∈ fs, x.key ∈ sel x.role
  keys : ∀ x ∈ fs, key x.key ∈ Apre ∨ key x.key ∈ Apost
  time_range : ∀ x ∈ fs, 0 ≤ x.time ∧ x.time ≤ H
  floor_le : ∀ x ∈ fs, ∀ s, shapeRoleFloor F V E x.role = some s → s ≤ x.time
  unique : ∀ x ∈ fs, ∀ y ∈ fs, x.key = y.key → x.role = y.role → x.msg = y.msg →
    x.tag = y.tag → x.time = y.time
  pre : ((fs.filter fun x => decide (0 ≤ x.time ∧ x.time < b₁)).map fun x => key x.key).toFinset =
    Apre.toFinset
  post : ((fs.filter fun x => decide (b₁ ≤ x.time ∧ x.time < H + 1)).map
    fun x => key x.key).toFinset = Apost.toFinset

/-- The plan of two lists with times split at `b₁` has the activity sets of the lists. -/
private theorem plan_sets {F : Model.ProtocolFamily O} {E : Env V}
    (key : Fin (Fintype.card V) ≃ V) (rpre rpost : V → (protoOf F E).Role)
    (m : Msg (protoOf F E).Item (protoOf F E).Body) (tpre tpost : V → Time) (Apre Apost : List V)
    {b₁ H : Time} (hpre : ∀ v, 0 ≤ tpre v ∧ tpre v < b₁) (hpost : ∀ v, b₁ ≤ tpost v ∧ tpost v ≤ H) :
    (((planOf key rpre m false tpre Apre ++ planOf key rpost m true tpost Apost).filter
        fun x => decide (0 ≤ x.time ∧ x.time < b₁)).map fun x => key x.key).toFinset =
      Apre.toFinset ∧
    (((planOf key rpre m false tpre Apre ++ planOf key rpost m true tpost Apost).filter
        fun x => decide (b₁ ≤ x.time ∧ x.time < H + 1)).map fun x => key x.key).toFinset =
      Apost.toFinset := by
  constructor <;> ext v <;>
    simp only [planOf, List.mem_toFinset, List.mem_map, List.mem_filter, List.mem_append,
      decide_eq_true_eq]
  · constructor
    · rintro ⟨x, ⟨⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩, ht⟩, rfl⟩
      · simpa using hw
      · exact absurd ht.2 (not_lt.mpr (hpost w).1)
    · intro hv
      exact ⟨_, ⟨Or.inl ⟨v, hv, rfl⟩, hpre v⟩, by simp⟩
  · constructor
    · rintro ⟨x, ⟨⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩, ht⟩, rfl⟩
      · exact absurd ht.1 (not_le.mpr (hpre w).2)
      · simpa using hw
    · intro hv
      refine ⟨_, ⟨Or.inr ⟨v, hv, rfl⟩, (hpost v).1, ?_⟩, by simp⟩
      have := (hpost v).2
      dsimp only [Time] at *
      omega

/-- **A selection and a forgery plan** for `Apre` before `b₁` and `Apost` from `b₁` through `H`,
when there is no activity to forge or the family has a forgeable role, `b₁` exceeds `n` slot
lengths and `H` covers `n` slots past slot `b₁`. -/
theorem exists_plan (F : ChainShapeFamily O Info) (E : Env V) (key : Fin (Fintype.card V) ≃ V)
    (Apre Apost : List V) {b₁ H : Time}
    (hb : (Fintype.card V : Time) * (F (pubOf E)).skel.grid.slotLen < b₁)
    (hH : ((b₁.toNat + Fintype.card V : ℕ) : Time) * (F (pubOf E)).skel.grid.slotLen ≤ H)
    (hforge : (Apre = [] ∧ Apost = []) ∨ ForgeableRole F) :
    ∃ sel fs, PlanProps F E key Apre Apost b₁ H sel fs := by
  classical
  have hSL := (F (pubOf E)).skel.grid.slotLen_pos
  set SL := (F (pubOf E)).skel.grid.slotLen with hSLdef
  have hn0 : (0 : Time) ≤ (Fintype.card V : Time) := by positivity
  have hb0 : 0 < b₁ := lt_of_le_of_lt (mul_nonneg hn0 hSL.le) hb
  have hP : ((b₁.toNat : ℕ) : Time) = b₁ := Int.toNat_of_nonneg hb0.le
  rcases hforge with ⟨rfl, rfl⟩ | hforge
  · refine ⟨extremalSel F E, [], ⟨extremalSel_admits F E, fun _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩⟩ <;> simp
  obtain ⟨⟨m₀⟩, hroles⟩ := hforge (pubOf E)
  let m : Msg (protoOf (compiled F) E).Item (protoOf (compiled F) E).Body := m₀
  rcases hroles with hpoll | ⟨k₀, hk₀⟩
  · -- The poll role admits every key.
    obtain ⟨S, hS, hSu⟩ := hpoll Finset.univ
    let sel : (protoOf (compiled F) E).Role → Finset (Fin (Fintype.card V)) := fun r =>
      match r with
      | .poll => S
      | r => extremalSel F E r
    let rp : V → (protoOf (compiled F) E).Role := fun _ => ShapeRole.poll
    let fs := planOf key rp m false (fun _ => 0) Apre ++ planOf key rp m true (fun _ => b₁) Apost
    have hH' : b₁ ≤ H := by
      refine le_trans ?_ hH
      refine le_trans ?_ (le_mul_of_one_le_right (by positivity)
        (by dsimp only [Time] at *; omega))
      push_cast
      rw [hP]
      linarith
    obtain ⟨hpre, hpost⟩ := plan_sets (H := H) key rp rp m (fun _ => 0) (fun _ => b₁) Apre Apost
      (fun _ => ⟨le_rfl, hb0⟩) (fun _ => ⟨le_rfl, hH'⟩)
    refine ⟨sel, fs, ⟨fun r => ?_, fun s => ?_, ?_, ?_, ?_, ?_, ?_, hpre, hpost⟩⟩
    · cases r with
      | poll => exact hS
      | proposer s => exact extremalSel_admits F E _
      | duty s k => exact extremalSel_admits F E _
    · rfl
    · intro x hx
      simp only [fs, planOf, List.mem_append, List.mem_map] at hx
      rcases hx with ⟨v, -, rfl⟩ | ⟨v, -, rfl⟩ <;>
        exact hSu (Finset.mem_univ _)
    · intro x hx
      simp only [fs, planOf, List.mem_append, List.mem_map] at hx
      rcases hx with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ <;> simp [hv]
    · intro x hx
      simp only [fs, planOf, List.mem_append, List.mem_map] at hx
      rcases hx with ⟨v, -, rfl⟩ | ⟨v, -, rfl⟩
      · exact ⟨le_rfl, le_trans hb0.le hH'⟩
      · exact ⟨hb0.le, hH'⟩
    · intro x hx s hs
      simp only [fs, planOf, List.mem_append, List.mem_map] at hx
      rcases hx with ⟨v, -, rfl⟩ | ⟨v, -, rfl⟩ <;> simp [shapeRoleFloor, shapeFloor] at hs
    · intro x hx y hy _ _ _ ht
      simp only [fs, planOf, List.mem_append, List.mem_map] at hx hy
      rcases hx with ⟨v, -, rfl⟩ | ⟨v, -, rfl⟩ <;> rcases hy with ⟨w, -, rfl⟩ | ⟨w, -, rfl⟩ <;>
        simp_all
  · -- A committee kind admits any one key.
    have hn : Fintype.card V ≤ b₁.toNat := by
      have : (Fintype.card V : Time) < b₁ := lt_of_le_of_lt
        (le_mul_of_one_le_right hn0 (by dsimp only [Time] at *; omega)) hb
      dsimp only [Time] at *; omega
    let P := b₁.toNat
    let Sk : Fin (Fintype.card V) → Finset (Fin (Fintype.card V)) := fun j =>
      Classical.choose (hk₀ j)
    have hSk : ∀ j, ((F (pubOf E)).skel.kindSel k₀).Admits (Sk j) ∧ j ∈ Sk j := fun j =>
      Classical.choose_spec (hk₀ j)
    let slotKey : Slot → Option (Fin (Fintype.card V)) := fun s =>
      if h : s < Fintype.card V then some ⟨s, h⟩
      else if h' : P ≤ s ∧ s - P < Fintype.card V then some ⟨s - P, h'.2⟩ else none
    let sel : (protoOf (compiled F) E).Role → Finset (Fin (Fintype.card V)) := fun r =>
      match r with
      | .duty s k => if k = k₀ then (match slotKey s with
          | some j => Sk j
          | none => extremalSel F E (.duty s k)) else extremalSel F E (.duty s k)
      | r => extremalSel F E r
    have hsel_pre : ∀ j : Fin (Fintype.card V), j ∈ sel (.duty j.val k₀) := fun j => by
      simp only [sel, ↓reduceIte, slotKey, j.isLt, ↓reduceDIte]
      exact (hSk j).2
    have hsel_post : ∀ j : Fin (Fintype.card V), j ∈ sel (.duty (P + j.val) k₀) := fun j => by
      have h1 : ¬ P + j.val < Fintype.card V := by omega
      have h2 : P ≤ P + j.val ∧ P + j.val - P < Fintype.card V := ⟨by omega, by omega⟩
      have hk : slotKey (P + j.val) = some j := by
        simp only [slotKey, h1, h2, ↓reduceDIte, and_self, Option.some.injEq]
        exact Fin.ext (by simp)
      simp only [sel, ↓reduceIte, hk]
      exact (hSk j).2
    let rpre : V → (protoOf (compiled F) E).Role := fun v => .duty (key.symm v).val k₀
    let rpost : V → (protoOf (compiled F) E).Role := fun v => .duty (P + (key.symm v).val) k₀
    let tpre : V → Time := fun v => ((key.symm v).val : Time) * SL
    let tpost : V → Time := fun v => ((P + (key.symm v).val : ℕ) : Time) * SL
    have htpre : ∀ v, 0 ≤ tpre v ∧ tpre v < b₁ := fun v => by
      refine ⟨by positivity, lt_of_le_of_lt ?_ hb⟩
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (key.symm v).isLt.le) hSL.le
    have htpost : ∀ v, b₁ ≤ tpost v ∧ tpost v ≤ H := fun v => by
      refine ⟨?_, le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast
        (show P + (key.symm v).val ≤ b₁.toNat + Fintype.card V by omega)) hSL.le) hH⟩
      have : b₁ ≤ ((P + (key.symm v).val : ℕ) : Time) := by
        push_cast; rw [show ((P : ℕ) : Time) = b₁ from hP]
        exact le_add_of_nonneg_right (by positivity)
      exact le_trans this
        (le_mul_of_one_le_right (by positivity) (by dsimp only [Time] at *; omega))
    obtain ⟨hpre, hpost⟩ := plan_sets key rpre rpost m tpre tpost Apre Apost htpre htpost
    let fs := planOf key rpre m false tpre Apre ++ planOf key rpost m true tpost Apost
    refine ⟨sel, fs, ⟨fun r => ?_, fun s => ?_, ?_, ?_, ?_, ?_, ?_, hpre, hpost⟩⟩
    · cases r with
      | duty s k =>
        by_cases hk : k = k₀
        · subst hk
          cases hs : slotKey s with
          | none =>
            simp only [sel, ↓reduceIte, hs]
            exact extremalSel_admits F E (.duty s k)
          | some j =>
            simp only [sel, ↓reduceIte, hs]
            exact (hSk j).1
        · simp only [sel, hk, ↓reduceIte]
          exact extremalSel_admits F E (.duty s k)
      | proposer s => exact extremalSel_admits F E _
      | poll => exact extremalSel_admits F E _
    · rfl
    · intro x hx
      simp only [fs, planOf, List.mem_append, List.mem_map] at hx
      rcases hx with ⟨v, -, rfl⟩ | ⟨v, -, rfl⟩
      · exact hsel_pre _
      · exact hsel_post _
    · intro x hx
      simp only [fs, planOf, List.mem_append, List.mem_map] at hx
      rcases hx with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ <;> simp [hv]
    · intro x hx
      simp only [fs, planOf, List.mem_append, List.mem_map] at hx
      rcases hx with ⟨v, -, rfl⟩ | ⟨v, -, rfl⟩
      · exact ⟨(htpre v).1, le_trans (htpre v).2.le (le_trans (htpost v).1 (htpost v).2)⟩
      · exact ⟨le_trans hb0.le (htpost v).1, (htpost v).2⟩
    · intro x hx s hs
      simp only [fs, planOf, List.mem_append, List.mem_map] at hx
      rcases hx with ⟨v, -, rfl⟩ | ⟨v, -, rfl⟩ <;>
        simp only [shapeRoleFloor, shapeFloor, rpre, rpost, Option.some.injEq] at hs <;>
        subst hs <;> simp [TimeGrid.slotTime, tpre, tpost, SL]
    · intro x hx y hy hk _ _ ht
      simp only [fs, planOf, List.mem_append, List.mem_map] at hx hy
      rcases hx with ⟨v, -, rfl⟩ | ⟨v, -, rfl⟩ <;> rcases hy with ⟨w, -, rfl⟩ | ⟨w, -, rfl⟩ <;>
        simp only [Equiv.apply_eq_iff_eq] at hk <;> simp_all

end Consensus.Comparison

end
