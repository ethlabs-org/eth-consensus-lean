module
public import AvailableChainGeneric.Statements.Pure.AdditiveStages
public import AvailableChainGeneric.Proofs.Pure.Stages

public section

namespace AvailableChain.Gen.Pure

open scoped BigOperators

/-- The full fold equals the sum of its additive budgets.
Consumers: F5.H.10, H.11, HG.6 and H.11-Q. Sources: 21:1293–1318,1619–1622,1654–1663,2429–2439.
DC: additive (no DC counterpart); reason: ordered deadline sums are a new scalar helper. -/
theorem compose_stages_add : ComposeStagesAddStatement := by
  rw [ComposeStagesAddStatement_def]
  intro α _ n f c hf u
  have hsum : ∀ (xs : List (Fin n)) (u : α),
      xs.foldl (fun x i => f i x) u = u + (xs.map c).sum := by
    intro xs u
    induction xs generalizing u with
    | nil => simp
    | cons i xs ih =>
      rw [List.foldl_cons, ih, hf, List.map_cons, List.sum_cons, add_assoc]
  rw [hsum, Fin.sum_univ_def]

/-- D1 ordered-fold comparison bounds the visited additive stages.
Consumers: F5.H.10, H.11, HG.6 and H.11-Q. Sources: 21:1293–1318,1619–1622,1654–1663,2429–2439.
DC: additive (no DC counterpart); reason: ordered deadline sums are a new scalar helper. -/
theorem compose_stages_add_bound : OrderedStagesAddBoundStatement := by
  rw [OrderedStagesAddBoundStatement_def]
  intro n f c hf hc vis hvis u
  have hmono : ∀ i, Monotone (f i) := by
    intro i x y hxy
    rw [hf, hf]
    omega
  have hext : ∀ i x, x ≤ f i x := by
    intro i x
    rw [hf]
    exact le_add_of_nonneg_right (hc i)
  have hbound := foldl_le_finRange f hmono hext vis hvis u
  rwa [compose_stages_add f c hf u] at hbound

end AvailableChain.Gen.Pure
