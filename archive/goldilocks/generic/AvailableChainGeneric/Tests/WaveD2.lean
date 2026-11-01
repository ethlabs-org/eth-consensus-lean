module
public import AvailableChainGeneric.Proofs.Pure.OpeningAfterGate -- shake: keep (examples)
public import AvailableChainGeneric.Proofs.Pure.StageStops -- shake: keep (examples)
public import AvailableChainGeneric.Proofs.Pure.AdditiveStages -- shake: keep (examples)
public import AvailableChainGeneric.Proofs.Pure.PeriodicStages -- shake: keep (examples)
public import AvailableChainGeneric.Proofs.Pure.HeadAfterSettlement -- shake: keep (examples)
import Mathlib.Tactic.NormNum -- shake: keep (examples)
import Mathlib.Tactic.Linarith -- shake: keep (examples)

public section

namespace AvailableChain.Gen.Pure

open SlotGrid
open scoped BigOperators

/-! Consumer boundary checks: F5.HG.1/HG.3, H.10/H.11/H.11-Q and HG.7/HG.8a.
DC: additive (no DC counterpart); reason: these are the D2 kernel boundary cases. -/

-- Coincident gate and action: the inclusive action has zero delay.
example : 0 ≤ a 1 3 1 - d 1 3 ∧ a 1 3 1 - d 1 3 ≤ P 1 3 - 4 := by
  apply firstOpening_after_gate 1 3 3 1 (by norm_num) (by norm_num)
  constructor
  · norm_num [a_def, d_def, t_def, slotLen_def]
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    norm_num [a_def, d_def, t_def, slotLen_def]

-- The first gate at zero works with the minimum pure grid size R = 1.
example : 0 ≤ a 1 1 0 - d 1 0 ∧ a 1 1 0 - d 1 0 ≤ P 1 1 - 4 := by
  apply firstOpening_after_gate 1 1 0 0 (by norm_num) (by norm_num)
  exact ⟨le_refl _, fun j hj => by omega⟩

-- At the exact HEAD threshold, choose this label, not its successor.
example : t 1 1 = 4 * 1 * ((2 + 2 * 1 + 4 * 1 - 1) / (4 * 1)) := by
  apply firstHead_after 1 2 1 (by norm_num) (by norm_num)
  constructor
  · norm_num [v_def, t_def, slotLen_def]
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    norm_num [v_def, t_def, slotLen_def]

-- The lower domain boundary w + 2Δ = 0 selects label zero.
example : t 1 0 = 4 * 1 * ((-2 + 2 * 1 + 4 * 1 - 1) / (4 * 1)) := by
  apply firstHead_after 1 (-2) 0 (by norm_num) (by norm_num)
  exact ⟨by norm_num [v_def, t_def, slotLen_def], fun j hj => by omega⟩

-- The consumer bound permits equal lower and upper cuts.
example : t 1 1 ≤ 4 * 1 * ((2 + 2 * 1 + 4 * 1 - 1) / (4 * 1)) := by
  apply firstHead_after_bound 1 2 2 1 (by norm_num) (by norm_num) (le_refl _)
  constructor
  · norm_num [v_def, t_def, slotLen_def]
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    norm_num [v_def, t_def, slotLen_def]

-- An empty additive fold returns its start, including a negative start.
example (u : Int) :
    (List.finRange 0).foldl (fun x i => x + (Fin.elim0 i : Int)) u =
      u + ∑ i : Fin 0, (Fin.elim0 i : Int) := by
  exact compose_stages_add (fun _ x => x) Fin.elim0 (fun i => Fin.elim0 i) u

-- Nonnegative budgets bound a list that skips the middle stage.
example (u : Int) : ([0, 2] : List (Fin 3)).foldl
    (fun x i => x + (i.val : Int)) u ≤ u + ∑ i : Fin 3, (i.val : Int) := by
  exact compose_stages_add_bound (fun i x => x + (i.val : Int))
    (fun i => (i.val : Int)) (fun _ _ => rfl) (fun i => Int.natCast_nonneg i.val)
    [0, 2] (by decide) u

-- Negative budgets preserve full-fold equality.
example : (List.finRange 1).foldl (fun x _ => x + (-1 : Int)) 0 = 0 +
    ∑ _i : Fin 1, (-1 : Int) :=
  compose_stages_add (fun _ x => x + (-1)) (fun _ => -1) (fun _ _ => rfl) 0

-- A skipped negative budget would make the ordered bound false.
example : ¬ (([] : List (Fin 1)).foldl (fun x _ => x + (-1 : Int)) 0 ≤
    0 + ∑ _i : Fin 1, (-1 : Int)) := by norm_num

-- A negative quotient gives the same elapsed fold at residue 6.
example : (List.finRange 2).foldl (fun x _ => x + (3 : Int)) (-2) - (-2) =
    (List.finRange 2).foldl (fun x _ => x + (3 : Int)) 6 - 6 := by
  apply periodic_shift (fun _ x => x + 3) 8 1 (-2) (by norm_num)
    (by norm_num) (by norm_num)
  · intro i x y h; change x + 3 ≤ y + 3; omega
  · intro i x; omega
  · intro i x; omega
  · norm_num

-- The empty periodic fold also permits a negative period quotient.
example : (List.finRange 0).foldl (fun x _ => x) (-2 : Int) - (-2) =
    (List.finRange 0).foldl (fun x _ => x) 6 - 6 := by
  apply periodic_shift (fun _ x => x) 8 1 (-2) (by norm_num)
    (by norm_num) (by norm_num)
  · intro i; exact monotone_id
  · intro i x; exact le_refl x
  · intro i x; rfl
  · norm_num

-- The terminal stage is available without any supplier when n = 0.
example : ∃ e x : Nat, 0 ≤ e ∧ (0 : Int) ≤ 0 ∧ (0 : Int) ≤ (x : Int) ∧
    x ≤ (List.finRange 0).foldl (fun y i => (Fin.elim0 i : Nat → Nat) y) 0 ∧
    ((∃ _c : Fin 3, False) ∨ True) := by
  exact stage_or_stop (fun _ => 0) (fun x : Nat => (x : Int)) Fin.elim0
    (fun _ _ _ => True) (fun _ _ => False)
    (fun _ _ _ => le_refl _) (by intro x y h; change (x : Int) ≤ (y : Int); exact_mod_cast h)
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    (by intro c e e' he hs; exact hs) (fun i => Fin.elim0 i) 0 0 trivial (le_refl _)

-- A jump from stage 0 to stage 3 skips two stages at the same event time.
example : ∃ e x : Nat, 0 ≤ e ∧ (0 : Int) ≤ 0 ∧ (0 : Int) ≤ (x : Int) ∧
    x ≤ (List.finRange 3).foldl (fun y _ => y + 1) 0 ∧
    ((∃ _c : Fin 3, False) ∨ e = 1 ∧ x = 1) := by
  let stage := fun (i e x : Nat) =>
    (i = 0 ∧ e = 0 ∧ x = 0) ∨ (i = 3 ∧ e = 1 ∧ x = 1)
  have hstep : ∀ (i : Fin 3) (e x : Nat), stage i.val e x →
      (0 : Int) ≤ (x : Int) →
      ∃ e' y : Nat, e ≤ e' ∧ (0 : Int) ≤ (y : Int) ∧ y ≤ x + 1 ∧
        ((∃ _c : Fin 3, False) ∨
          ∃ j : Nat, i.val < j ∧ j ≤ 3 ∧ stage j e' y) := by
    intro i e x hs ht
    have hi := i.isLt
    rcases hs with ⟨hi0, he0, hx0⟩ | ⟨hi3, _⟩
    · subst e; subst x
      exact ⟨1, 1, by omega, by norm_num, le_refl _,
        Or.inr ⟨3, by omega, le_refl _, Or.inr ⟨rfl, rfl, rfl⟩⟩⟩
    · omega
  have h := stage_or_stop (fun _ => 0) (fun x : Nat => (x : Int))
    (fun (_ : Fin 3) x => x + 1) stage (fun _ _ => False)
    (fun _ _ _ => le_refl _) (by intro x y h; change (x : Int) ≤ (y : Int); exact_mod_cast h)
    (by intro i x y h; change x + 1 ≤ y + 1; omega) (by intro i x; omega)
    (by intro c e e' he hs; exact hs) hstep 0 0
    (Or.inl ⟨rfl, rfl, rfl⟩) (le_refl _)
  simpa only [stage, Nat.reduceEqDiff, false_and, false_or, true_and] using h

-- Every tag (0, 1 and 2) survives an equal-time supplier step.
example (tag : Fin 3) : ∃ e x : Nat, 0 ≤ e ∧ (0 : Int) ≤ 0 ∧
    (0 : Int) ≤ (x : Int) ∧ x ≤ (List.finRange 1).foldl (fun y _ => y + 1) 0 ∧
    ((∃ c : Fin 3, c = tag ∧ 1 ≤ e) ∨ False) := by
  let stage := fun (i e x : Nat) => i = 0 ∧ e = 0 ∧ x = 0
  have hstep : ∀ (i : Fin 1) (e x : Nat), stage i.val e x →
      (0 : Int) ≤ (x : Int) →
      ∃ e' y : Nat, e ≤ e' ∧ (0 : Int) ≤ (y : Int) ∧ y ≤ x + 1 ∧
        ((∃ c : Fin 3, c = tag ∧ 1 ≤ e') ∨
          ∃ j : Nat, i.val < j ∧ j ≤ 1 ∧ stage j e' y) := by
    intro i e x hs ht
    rcases hs with ⟨hi, he, hx⟩
    subst e; subst x
    exact ⟨1, 1, by omega, by norm_num, le_refl _, Or.inl ⟨tag, rfl, le_refl _⟩⟩
  have h := stage_or_stop (fun _ => 0) (fun x : Nat => (x : Int))
    (fun (_ : Fin 1) x => x + 1) stage (fun c e => c = tag ∧ 1 ≤ e)
    (fun _ _ _ => le_refl _) (by intro x y h; change (x : Int) ≤ (y : Int); exact_mod_cast h)
    (by intro i x y h; change x + 1 ≤ y + 1; omega) (by intro i x; omega)
    (by intro c e e' he hs; exact ⟨hs.1, hs.2.trans he⟩) hstep 0 0
    ⟨rfl, rfl, rfl⟩ (le_refl _)
  simpa only [stage, Nat.reduceEqDiff, false_and] using h

end AvailableChain.Gen.Pure
