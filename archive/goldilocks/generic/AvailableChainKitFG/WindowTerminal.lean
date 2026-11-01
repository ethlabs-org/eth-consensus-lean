module
public import AvailableChainKitFG.WindowRetention
public import AvailableChainKitFG.WindowEntriesDef
public import AvailableChainKitFG.WindowViewsDef

public section

namespace AvailableChain.KitFG.Window

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.SimplexFG.Window

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- Terminal scalar bounds at the active finality and height views preserve
the key. The supplier uses the bounds at each intermediate child. -/
theorem terminal_retained_scalarW (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (hne : ¬ E.IsQuorum ∅) (hK : 2 ≤ K) (A P : FGBlock V)
    (hAP : FGBlock.Preceq A P) (y : Height) (U : FGBlock V)
    (retained : RetainedW E cfg K A y U) (above : (certificateFinality E cfg K P).h_F < y)
    (near : (certificateHeight E cfg K P).h_j < y + K) : RetainedW E cfg K P y U := by
  obtain ⟨e, he, hej, heX⟩ := retained
  obtain ⟨d, hd, hdj, hdX, _⟩ := window_retained_of_scalar E cfg K hne hK
    A P hAP e he
    (by simpa only [certificateFinality_def,
      projectFinality_def, hej] using above)
    (by simpa only [certificateHeight_def, projectHeight_def, hej] using near)
  exact ⟨d, hd, hdj.trans hej, hdX.trans heX⟩

/-- Fewer than K newer births up to the terminal parent preserve the key.
The finite set can overestimate the births; certificate heights need no gap bound. -/
theorem terminal_retained_birthsW (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (hne : ¬ E.IsQuorum ∅) (hK : 2 ≤ K) (A P : FGBlock V)
    (hAP : FGBlock.Preceq A P) (y : Height) (U : FGBlock V)
    (retained : RetainedW E cfg K A y U) (above : (certificateFinality E cfg K P).h_F < y)
    (births : Finset (FGBlock V)) (few : births.card < K)
    (cover : ∀ C j X, FGBlock.Preceq C P → y < j →
      JustificationBirth E (certificateHeight E cfg K) C j X → C ∈ births) :
    RetainedW E cfg K P y U := by
  obtain ⟨e, he, hej, heX⟩ := retained
  obtain ⟨d, hd, hdj, hdX, _⟩ := window_retained_of_few_births E cfg K hne hK
    A P hAP e he
    (by simpa only [certificateFinality_def,
      projectFinality_def, hej] using above)
    births few
    (by simpa only [hej] using cover)
  exact ⟨d, hd, hdj.trans hej, hdX.trans heX⟩

/-- A finality deletion covers the key. The same scalar bound also excludes
capacity eviction, without a premise that finality stays below the key. -/
theorem terminal_retained_or_coveredW (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (hne : ¬ E.IsQuorum ∅) (hK : 2 ≤ K) (A P : FGBlock V)
    (hAP : FGBlock.Preceq A P) (y : Height) (U : FGBlock V)
    (retained : RetainedW E cfg K A y U) (near : (certificateHeight E cfg K P).h_j < y + K) :
    RetainedW E cfg K P y U ∨ CoveredW E cfg K P y U := by
  obtain ⟨e, he, hej, heX⟩ := retained
  have result := window_retained_or_covered E cfg K hne hK A P hAP e he
    (by simpa only [certificateHeight_def, projectHeight_def, hej] using near)
  rw [hej, heX] at result
  rcases result with ⟨d, hd, hdj, hdX, _⟩ | covered
  · exact Or.inl ⟨d, hd, hdj, hdX⟩
  · exact Or.inr covered

/-- The paper causal cap permits at most one greater certificate height.
The active window's capacity and retained-or-covered supplier close F8-W. -/
theorem terminalRetentionW (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (hne : ¬ E.IsQuorum ∅) (hK : 2 ≤ K)
    (A P : FGBlock V) (d : Nat) (U : FGBlock V)
    (ancestry : FGBlock.Preceq A P) (retained : RetainedW E cfg K A (d + 1) U)
    (latest : ((certificateHeight E cfg K A).h_j,
      (certificateHeight E cfg K A).J) = (d + 1, U))
    (cap : (certificateHeight E cfg K P).h ≤ d + 3) :
    RetainedW E cfg K P (d + 1) U ∨ CoveredW E cfg K P (d + 1) U := by
  have below := (windowHeightLaws E cfg K hK).justified_below_height P
  have latestHeight := congrArg Prod.fst latest
  simp only [certificateHeight_def, projectHeight_def] at cap latestHeight
  change (derive E cfg K P).h_j < (derive E cfg K P).h at below
  have one : (derive E cfg K P).h_j ≤ (derive E cfg K A).h_j + 1 := by
    rw [latestHeight]
    exact Nat.le_of_lt_succ (below.trans_le cap)
  apply terminal_retained_or_coveredW E cfg K hne hK A P ancestry (d + 1) U retained
  simp only [certificateHeight_def, projectHeight_def]
  rw [latestHeight] at one
  exact one.trans_lt (Nat.add_lt_add_left
    (Nat.lt_of_lt_of_le (by decide : 1 < 2) hK) (d + 1))

end AvailableChain.KitFG.Window
end
