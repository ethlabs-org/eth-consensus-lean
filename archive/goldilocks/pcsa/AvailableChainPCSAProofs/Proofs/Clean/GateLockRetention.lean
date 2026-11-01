module
public import AvailableChainPCSAProofs.Proofs.Clean.ClockLockRetention
public import AvailableChainPCSAProofs.Proofs.Clean.LockOrigins
public import AvailableChainPCSAProofs.Proofs.Clean.LockRetention

public section

/-! C6 GateLockRetention: concrete receipt and count support. -/
namespace AvailableChain.PCSA
variable {n : Nat}
/-- A gate can renew a row but cannot remove its target. -/
theorem pcsa_gate_keep_lock_target (p : Params) (st : State n) (anchor : Block)
    (cs : List (PC n)) (rank : Option PCRank) (s : Slot)
    (row : Block × Nat × Time) (hr : row ∈ st.base.obligations) :
    ∃ row' ∈ (gateFrom p anchor cs rank st s).base.obligations, row'.1 = row.1 := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams anchor (actView st) s with
  | none => exact ⟨row, hr, rfl⟩
  | some X =>
    dsimp only
    split
    · exact ⟨row, hr, rfl⟩
    · apply List.foldlRecOn (motive := fun acc : State n =>
        ∃ r ∈ acc.base.obligations, r.1 = row.1)
      · exact ⟨row, hr, rfl⟩
      · intro acc ha b _
        apply List.foldlRecOn (motive := fun acc : State n =>
          ∃ r ∈ acc.base.obligations, r.1 = row.1)
        · exact ha
        · intro acc' hh g _
          obtain ⟨r, hr, he⟩ := hh
          obtain ⟨r', hr', he'⟩ := pcsa_write_lock_keep_target acc' b g _ rank r hr
          exact ⟨r', hr', he'.trans he⟩
/-- A stage-one gate step preserves each existing lock target. -/
theorem pcsa_gateStep_keep_lock_target (p : Params) (st : State p.n) (s : Slot)
    (row : Block × Nat × Time) (hr : row ∈ st.base.obligations) :
    ∃ row' ∈ (gateStep p st s).base.obligations, row'.1 = row.1 := by
  rw [gateStep_def, pcsa_normalize_locks]
  split
  · exact ⟨row, hr, rfl⟩
  · exact pcsa_gate_keep_lock_target p st _ _ _ s row hr
/-- A live lock target survives the clock if its release count stays below its level. -/
theorem pcsa_clock_keep_lock_target (p : Params) (st : State p.n) (t : Time)
    (row : Block × Nat × Time) (hr : row ∈ st.base.obligations) (ht : t < row.2.2)
    (hrelease : ∀ s, t = SA.releaseTime p.toParams s →
      GridCO.releaseCount p.toParams.engine (actView (clock p st t)) s row.1 < row.2.1) :
    ∃ row' ∈ (clock p st t).base.obligations, row'.1 = row.1 := by
  have hpre := pcsa_clockPre_keep_lock p st t row hr ht hrelease
  delta clock
  dsimp only
  split
  · exact pcsa_gateStep_keep_lock_target p _ _ row hpre
  · exact ⟨row, hpre, rfl⟩
end AvailableChain.PCSA

end
