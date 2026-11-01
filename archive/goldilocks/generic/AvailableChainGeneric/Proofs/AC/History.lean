module
public import AvailableChainGeneric.Statements.AC.History
public import AvailableChainGeneric.Proofs.Pure.BlockOrder

public section

namespace AvailableChain.Gen.AC

open AvailableChain AvailableChain.V2 AvailableChain.V2.Engine

/-- Preservation and transfer give honest history and continuation.
Source: step4b-plan.md, S4b-10, Q6 A.
Proof: AvailableChainGridCO/Proofs/HistoryInduction.lean:35–53;
use the adopted Pure transitivity theorem from S4b-09. -/
theorem genuine_history_induction {V : Type} (honest : V → Prop)
    (result : Slot → V → Option Block) (next : Slot → V → Block) (r : Slot)
    (preserve : ∀ s, s < r → GenuineContinues honest result next s →
      ∀ source, honest source → ∀ b, result s source = some b →
        ∀ reader, honest reader → ∃ c,
          result (s + 1) reader = some c ∧ Block.Preceq b c)
    (transfer : ∀ s, s ≤ r → GenuineExtends honest result s →
      GenuineContinues honest result next s) :
    GenuineExtends honest result r ∧ GenuineContinues honest result next r := by
  induction r with
  | zero =>
    have history : GenuineExtends honest result 0 := by
      intro s hs
      exact (Nat.not_lt_zero s hs).elim
    exact ⟨history, transfer 0 (le_refl _) history⟩
  | succ r ih =>
    obtain ⟨history, continuation⟩ := ih
      (fun s hs => preserve s (hs.trans (Nat.lt_succ_self r)))
      (fun s hs => transfer s (hs.trans (Nat.le_succ r)))
    have step := preserve r (Nat.lt_succ_self r) continuation
    have history' : GenuineExtends honest result (r + 1) := by
      intro s hs source hsource b hb reader hreader
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hs) with rfl | hlt
      · exact step source hsource b hb reader hreader
      · obtain ⟨d, hd, hbd⟩ := history s hlt source hsource b hb reader hreader
        obtain ⟨c, hc, hdc⟩ := step reader hreader d hd reader hreader
        exact ⟨c, hc, Pure.block_preceq_trans hbd hdc⟩
    exact ⟨history', transfer (r + 1) (le_refl _) history'⟩

end AvailableChain.Gen.AC
