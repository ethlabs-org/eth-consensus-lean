module
public import AvailableChainPCSA.Model.Store
public import AvailableChainGeneric.Proofs.Pure.PCFloor

public section

/-! The PC-SA output floor (pcsa34-r4.3 §3.2). -/

namespace AvailableChain.PCSA
variable {n : Nat}

/-- The available output is the Generic PC floor. -/
theorem confirmed_eq_pcFloor (st : State n) :
    confirmed st = Gen.Pure.pcFloor st.base.stableRecord (pcTarget? st) := by
  unfold confirmed
  rw [Gen.Pure.pcFloor_def]
  cases pcTarget? st <;> rfl

/-- The strong output is below the available output in every store. -/
theorem strong_preceq_confirmed (st : State n) : Block.Preceq (strong st) (confirmed st) := by
  rw [confirmed_eq_pcFloor]
  unfold strong
  cases h : pcTarget? st with
  | none => exact Gen.Pure.block_genesis_preceq _
  | some b => exact Gen.Pure.target_preceq_pcFloor _ _

/-- Finality is below the output when S extends F and PC targets are F-compatible. -/
theorem finalized_preceq_confirmed (st : State n)
    (hS : Block.Preceq (eraseFG st.fg.F) st.base.stableRecord)
    (hpc : ∀ b, pcTarget? st = some b → Block.Compatible (eraseFG st.fg.F) b) :
    Block.Preceq (eraseFG st.fg.F) (confirmed st) := by
  rw [confirmed_eq_pcFloor]
  exact Gen.Pure.preceq_pcFloor hS hpc

end AvailableChain.PCSA
end
