module
public import AvailableChainPCSAProofs.Proofs.Foundations.Output
public import AvailableChainPCSAProofs.Proofs.Clean.CutReads

public section

/-! C6 CleanOutputs: concrete receipt and count support. -/
namespace AvailableChain.PCSA
/-- The available output is S or the selected PC target. -/
theorem pcsa_confirmed_source (st : State n) :
    confirmed st = st.base.stableRecord ∨
      ∃ B, pcTarget? st = some B ∧ confirmed st = B := by
  cases ht : pcTarget? st with
  | none =>
    left
    rw [confirmed_eq_pcFloor, ht, Gen.Pure.pcFloor_none]
  | some B =>
    have he : confirmed st = Gen.Pure.pcFloor st.base.stableRecord (some B) := by
      rw [confirmed_eq_pcFloor, ht]
    rcases Gen.Pure.pcFloor_some_eq_or st.base.stableRecord B with hs | hb
    · exact Or.inl (he.trans hs)
    · exact Or.inr ⟨B, rfl, he.trans hb⟩
end AvailableChain.PCSA

end
