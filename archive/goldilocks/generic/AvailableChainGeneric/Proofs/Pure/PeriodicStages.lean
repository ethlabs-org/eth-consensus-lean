module
public import AvailableChainGeneric.Statements.Pure.PeriodicStages
public import Mathlib.Data.Int.Basic -- shake: keep (re-export)
import Mathlib.Tactic.Ring -- shake: keep (re-export)
import Mathlib.Tactic.Linarith -- shake: keep (re-export)

public section

namespace AvailableChain.Gen.Pure

/-- The Euclidean residue cancels every integer period translation.
Consumers: F5.HG.7 and F5.HG.8a. Sources: 21:1695,1709–1717,2210–2217.
DC: additive (no DC counterpart); reason: fixed periodic deadlines are scalar helpers. -/
theorem periodic_shift : PeriodicShiftStatement := by
  rw [PeriodicShiftStatement_def]
  intro n f P Δ u₀ _hP _hres₀ _hresP _hmono _hext hf hres
  let F : Int → Int := fun x => (List.finRange n).foldl (fun x i => f i x) x
  have hfold : ∀ (xs : List (Fin n)) (x : Int),
      xs.foldl (fun x i => f i x) (x + P) = xs.foldl (fun x i => f i x) x + P := by
    intro xs x
    induction xs generalizing x with
    | nil => rfl
    | cons i xs ih => simpa only [List.foldl_cons, hf] using ih (f i x)
  have hF : ∀ x, F (x + P) = F x + P := hfold (List.finRange n)
  have hshift : ∀ (q x : Int), F (x + q * P) = F x + q * P := by
    intro q x
    induction q using Int.induction_on with
    | zero => simp
    | succ q ih =>
      have h := hF (x + (q : Int) * P)
      rw [show x + (q : Int) * P + P = x + ((q : Int) + 1) * P by ring] at h
      rw [h, ih]
      ring
    | pred q ih =>
      have h := hF (x + (-(q : Int) - 1) * P)
      rw [show x + (-(q : Int) - 1) * P + P = x + -(q : Int) * P by ring,
        ih] at h
      linarith
  have hu : u₀ = 6 * Δ + (u₀ / P) * P := by
    have h := Int.emod_add_mul_ediv u₀ P
    rw [hres] at h
    nlinarith
  change F u₀ - u₀ = F (6 * Δ) - 6 * Δ
  rw [hu, hshift]
  ring

end AvailableChain.Gen.Pure
