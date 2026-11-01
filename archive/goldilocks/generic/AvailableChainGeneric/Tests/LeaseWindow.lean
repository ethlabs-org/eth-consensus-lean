module
public import AvailableChainGeneric -- shake: keep (examples)

public section

set_option linter.privateModule false

namespace AvailableChain.Gen.AC.Tests

open AvailableChain

-- The last window label w+k=s+1 still supplies a result.
example (B : Block) :
    Block.Compatible (Lease.target (B, 2, (4 : Time))) B := by
  by_contra hconf
  refine slow_window_conflict_absurd [(B, 2, (4 : Time))]
    (fun w C => w = 2 ∧ C = B) (fun w => (w : Time)) 3 2 B
    ?_ ?_ ?_ ?_ (B, 2, (4 : Time)) (by simp) ?_ hconf
  · intro a b hab
    change (a : Int) ≤ (b : Int)
    exact_mod_cast hab
  · intro lease hm
    have he : lease = (B, 2, (4 : Time)) := by simpa using hm
    subst lease
    exact ⟨2, B, by decide, by change (4 : Int) ≤ 4; rfl,
      ⟨rfl, rfl⟩, Pure.block_preceq_refl B⟩
  · intro w hws hwindow
    have hw : w = 2 := by omega
    exact ⟨B, ⟨hw, rfl⟩, Pure.block_preceq_refl B⟩
  · intro w _ _ C D hC hD
    rw [hC.2, hD.2]
    exact Pure.block_compatible_of_common (Pure.block_preceq_refl B)
      (Pure.block_preceq_refl B)
  · change (3 : Int) < 4
    decide

-- A row is removed when d=expiry w=expiry c=t.
example {n : Nat} (st : GridCO.State n) (B : Block) (g : Nat) (d : Time) :
    (B, g, d) ∉ (GridCO.expire st d).obligations := by
  exact expire_by_threshold st (fun _ => d) 0 0 B g d d
    (fun _ _ _ => le_refl d) (le_refl 0) (le_refl d) (le_refl d)

end AvailableChain.Gen.AC.Tests
