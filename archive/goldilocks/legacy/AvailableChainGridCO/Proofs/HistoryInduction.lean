module
public import AvailableChainGridCO.Proofs.History

@[expose] public section
namespace AvailableChain.GridCO

/-- The ordered part of clean history. Results are supplied by the run,
not by a freely chosen chain of stored blocks. -/
def GenuineExtends {V : Type} (honest : V → Prop)
    (result : Slot → V → Option Block) (r : Slot) : Prop :=
  ∀ s, s < r → ∀ source, honest source → ∀ b,
    result s source = some b → ∀ reader, honest reader →
      ∃ c, result r reader = some c ∧ Block.Preceq b c

/-- Accessible continuation of a genuine result at the next HEAD.
The HEAD is the actual choice, including any protocol-specific roots. -/
def GenuineContinues {V : Type} (honest : V → Prop)
    (result : Slot → V → Option Block) (next : Slot → V → Block) (r : Slot) : Prop :=
  ∀ source, honest source → ∀ b, result r source = some b →
    ∀ reader, honest reader → Block.Preceq b (next r reader)

/-- The common SA/Grid CO clean induction. Receipt transfer supplies
`transfer`; delivery of the next honest batch supplies `preserve`.
Protocol-specific roots belong in `transfer`, after ordered history is
available. There is no arbitrary path or whole-run projection premise. -/
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
        exact ⟨c, hc, prefix_trans b d c hbd hdc⟩
    exact ⟨history', transfer (r + 1) (le_refl _) history'⟩

end AvailableChain.GridCO
end
