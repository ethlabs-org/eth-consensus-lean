module
public import AvailableChainSimplexFG.Client

public section

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG

private theorem d7r_height_pair_some_def (Λ : Record) (y : Nat) (T : BlockId)
    (fp : Option FinalityPair) : height_pair Λ (some (y, T)) fp =
      if Λ.timeout y then .vote y T true else
        match own_lock Λ y fp with
        | some locked => if locked = T then .vote y T false else .empty
        | none => match Λ.target y with
          | some recorded => if recorded = T then .vote y T false else .vote y T true
          | none => .vote y T false := rfl

private theorem d7r_own_lock_none (Λ : Record) (y : Nat) :
    own_lock Λ y none = Λ.lock y := rfl

private theorem d7r_own_lock_some (Λ : Record) (y : Nat) (f : FinalityPair) :
    own_lock Λ y (some f) = if f.height = y then some f.target else Λ.lock y := rfl

theorem high_record_target_choice_core (Λ : Record) (y : Nat) (T : BlockId)
    (fp : Option FinalityPair)
    (ht : Λ.target y = none ∨ Λ.target y = some T)
    (hn : Λ.timeout y = false)
    (hl : Λ.lock y = none ∨ Λ.lock y = some T)
    (hf : ∀ f, fp = some f → f.height = y → f.target = T) :
    height_pair Λ (some (y, T)) fp = .vote y T false := by
  have hol : own_lock Λ y fp = none ∨ own_lock Λ y fp = some T := by
    cases hp : fp with
    | none => simpa only [d7r_own_lock_none, hp] using hl
    | some f =>
      by_cases hy : f.height = y
      · right; simp only [d7r_own_lock_some, hy, ite_true, hf f hp hy]
      · simpa only [d7r_own_lock_some, hp, hy, ite_false] using hl
  rw [d7r_height_pair_some_def]
  simp only [hn, Bool.false_eq_true, ite_false]
  rcases hol with hol | hol
  · rw [hol]
    rcases ht with ht | ht <;> simp [ht]
  · simp [hol]

end AvailableChain.FGCompose
end
