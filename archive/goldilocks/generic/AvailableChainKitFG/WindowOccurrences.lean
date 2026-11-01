module
public import AvailableChainKitFG.WindowRetention -- shake: keep (re-export)
public import AvailableChainKitFG.WindowEntriesDef

public section

namespace AvailableChain.KitFG.Window

open AvailableChain.SimplexFG hiding process_row process_height_events transition derive
open AvailableChain.SimplexFG.Window

variable {V : Type} [DecidableEq V] [Fintype V] [RowCodec V]

/-- Exact finality rows add bits at the active parent view. Either R6W arm
has this effect; no height-match premise is required. -/
theorem entry_bit_insertW (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (hne : ¬ E.IsQuorum ∅) (hK : 2 ≤ K) (P : FGBlock V)
    (s : Slot) (r_s : BlockId) (x : Nat) (rs : List (Row V)) (j : Height)
    (U : FGBlock V) (hp : RetainedW E cfg K P j U)
    (hc : RetainedW E cfg K (.node P s r_s x rs) j U)
    (a : Row V) (ha : a ∈ rs)
    (matchRow : a.finality_pair = some ⟨j, U.root⟩) :
    EntryBitW E cfg K (.node P s r_s x rs) j U a.signer := by
  obtain ⟨e, he, hej, heX⟩ := hp
  obtain ⟨d, hd, hdj, hdX⟩ := hc
  exact ⟨d, hd, hdj, hdX, window_bit_add_of_row E cfg K hne hK
    P s r_s x rs e d he hd (hdj.trans hej.symm) (hdX.trans heX.symm) a ha
    (by simpa only [hej, heX] using matchRow)⟩

/-- Retention of the exact key preserves its bits at the active model view. -/
theorem entry_bit_persistW (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (hne : ¬ E.IsQuorum ∅) (hK : 2 ≤ K) (A B : FGBlock V)
    (hAB : FGBlock.Preceq A B) (j : Height) (U : FGBlock V) (i : V)
    (bit : EntryBitW E cfg K A j U i) (retained : RetainedW E cfg K B j U) :
    EntryBitW E cfg K B j U i := by
  obtain ⟨e, he, hej, heX, hi⟩ := bit
  obtain ⟨d, hd, hdj, hdX⟩ := retained
  exact ⟨d, hd, hdj, hdX, window_bit_retained E cfg K hne hK
    A B hAB e d he hd (hej.trans hdj.symm) (heX.trans hdX.symm) hi⟩

/-- An occurrence strictly after a retained anchor contributes its bit when
the exact key is still retained at the endpoint. -/
theorem entry_bit_occurrenceW (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (hne : ¬ E.IsQuorum ∅) (hK : 2 ≤ K) (A B C : FGBlock V)
    (hAB : StrictPrefix A B) (hBC : FGBlock.Preceq B C)
    (j : Height) (U : FGBlock V) (ha : RetainedW E cfg K A j U)
    (hc : RetainedW E cfg K C j U) (a : Row V) (hr : a ∈ B.rows)
    (matchRow : a.finality_pair = some ⟨j, U.root⟩) : EntryBitW E cfg K C j U a.signer := by
  have hAC : FGBlock.Preceq A C := preceq_trans (StrictPrefix_def A B ▸ hAB).1 hBC
  obtain ⟨e, he, hej, heX⟩ := ha
  obtain ⟨d, hd, hdj, hdX⟩ := hc
  exact ⟨d, hd, hdj, hdX, (window_bits_accumulate E cfg K hne hK
    A C hAC e d he hd (hdj.trans hej.symm) (hdX.trans heX.symm)).2 B hAB hBC a hr
    (by simpa only [hej, heX] using matchRow)⟩

/-- The model history keeps all three cases. Eviction has an actual removal
step with K newer entries. A later endpoint can instead cover an evicted key. -/
theorem entry_historyW (E : Electorate V) (cfg : FGConfig) (K : Nat)
    (hne : ¬ E.IsQuorum ∅) (hK : 2 ≤ K) (A B : FGBlock V)
    (hAB : FGBlock.Preceq A B) (j : Height) (U : FGBlock V)
    (retained : RetainedW E cfg K A j U) :
    RetainedW E cfg K B j U ∨
    (¬ RetainedW E cfg K B j U ∧ CoveredW E cfg K B j U) ∨
    (¬ RetainedW E cfg K B j U ∧ ¬ CoveredW E cfg K B j U ∧
      (derive E cfg K B).h_F < j ∧
      ∃ P s r_s x rs, FGBlock.Preceq A P ∧ FGBlock.Preceq (.node P s r_s x rs) B ∧
        RetainedW E cfg K P j U ∧ ¬ RetainedW E cfg K (.node P s r_s x rs) j U ∧
        (derive E cfg K (.node P s r_s x rs)).W.length = K ∧
        ∃ C, FGBlock.Preceq C P ∧
          JustificationBirth E (certificateHeight E cfg K) C j U ∧
          ∀ d ∈ (derive E cfg K (.node P s r_s x rs)).W, j < d.j ∧
            ∃ D, StrictPrefix C D ∧ FGBlock.Preceq D (.node P s r_s x rs) ∧
              JustificationBirth E (certificateHeight E cfg K) D d.j d.X) := by
  obtain ⟨e, he, hej, heX⟩ := retained
  have history := window_entry_history E cfg K hne hK A B hAB e he
  rw [hej, heX] at history
  rcases history with ⟨d, hd, hj, hX, _⟩ | covered | evicted
  · exact Or.inl ⟨d, hd, hj, hX⟩
  · exact Or.inr (Or.inl covered)
  · exact Or.inr (Or.inr evicted)

end AvailableChain.KitFG.Window
end
