module
public import ConsensusLean.Init
public import Mathlib.Data.Set.Card

public section

/-! # Goldilocks Obligations: an honest key exists under the fault bound

A key set `H` of `n > 0` keys whose complement meets the fault bound `3·|Hᶜ| ≤ n − 1` is not
empty: an empty `H` has `3n ≤ n − 1`. The fault bound is the `faults` field of the shared reset
premises, of one honest set or of the honest set at one time. -/

namespace Consensus.Goldilocks.Obligations

/-- **An honest key exists**: `3·|Hᶜ| ≤ n − 1` with `0 < n` makes `H` nonempty. -/
theorem nonempty_of_fault_bound {n : Nat} {H : Set (Fin n)} (hf : 3 * Hᶜ.ncard ≤ n - 1)
    (hn : 0 < n) : H.Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  rw [hne, Set.compl_empty, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hf
  omega

end Consensus.Goldilocks.Obligations

end
