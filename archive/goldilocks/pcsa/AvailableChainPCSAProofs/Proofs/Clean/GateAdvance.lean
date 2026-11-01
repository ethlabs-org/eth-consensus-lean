module
public import AvailableChainPCSAProofs.Proofs.Clean.GenuineKeys
public import AvailableChainPCSAProofs.Proofs.Foundations.Duties
public import AvailableChainPCSAProofs.Proofs.Clean.JointAux
public import AvailableChainPCSAProofs.Proofs.Clean.RecordOrder
public import AvailableChainPCSAProofs.Proofs.Clean.LockEvents
public import AvailableChainPCSAProofs.Proofs.Clean.CutReads

public section

/-! C6 GateAdvance: concrete receipt and count support. -/
namespace AvailableChain.PCSA
variable {n : Nat}
private theorem inclusion_normalize_record (st : State n) (hf : st.fg.F = .genesis) :
    (normalizeS st).base.stableRecord = st.base.stableRecord := by
  delta normalizeS
  split
  · rfl
  · rename_i hn
    rw [hf] at hn
    exact (hn (Gen.Pure.block_genesis_preceq _)).elim
/-- With a clear lock guard, the gate's S update covers its raw result. -/
theorem pcsa_gate_record_covers_result (p : Params) (st : State n) (anchor : Block)
    (cs : List (PC n)) (rank : Option PCRank) (s : Slot) (X : Block)
    (hX : SA.Root.confirmationFrom p.toParams anchor (actView st) s = some X)
    (hg : st.base.obligations.any (fun row => st.base.now < row.2.2 &&
      !Block.compatible row.1 X) = false) :
    Block.Preceq X (gateFrom p anchor cs rank st s).base.stableRecord := by
  rw [gateFrom_def]
  dsimp only
  rw [hX]
  dsimp only
  rw [ite_eq_right (Bool.eq_false_iff.mp hg)]
  apply List.foldlRecOn (motive := fun acc : State n => Block.Preceq X acc.base.stableRecord)
  · change Block.Preceq X (GridCO.advance st.base.stableRecord X)
    delta GridCO.advance
    split
    · exact (by assumption)
    · exact Gen.Pure.block_preceq_refl _
  · intro acc ha b _
    apply List.foldlRecOn (motive := fun acc : State n => Block.Preceq X acc.base.stableRecord)
    · exact ha
    · intro acc' ha' g _
      exact ha'
/-- A fresh stage-one gate with a clear guard covers its raw result in S. -/
theorem pcsa_gateStep_record_covers_result (p : Params) (st : State p.n) (s : Slot) (X : Block)
    (hf : st.fg.F = .genesis) (hfresh : (GridCO.savedGenuine st.base s).isSome = false)
    (hX : SA.Root.confirmationFrom p.toParams (eraseFG st.fg.F) (actView st) s = some X)
    (hg : st.base.obligations.any (fun row => st.base.now < row.2.2 &&
      !Block.compatible row.1 X) = false) :
    Block.Preceq X (gateStep p st s).base.stableRecord := by
  rw [gateStep_def]
  dsimp only
  rw [ite_eq_right (Bool.eq_false_iff.mp hfresh)]
  rw [inclusion_normalize_record _ (by rw [(gateFrom_pc_frame _ _ _ _ _ _).2]; exact hf)]
  exact pcsa_gate_record_covers_result p st _ _ _ s X hX hg
/-- The full clock at a fresh gate covers the raw result in its post-clock record. -/
theorem pcsa_clock_gate_record_covers_result (p : Params) (st : State p.n) (s : Slot) (X : Block)
    (hf : st.fg.F = .genesis)
    (hfresh : (GridCO.savedGenuine (clockPre p st (SA.gateTime p.toParams s)).base s).isSome =
      false)
    (hX : SA.Root.confirmationFrom p.toParams (eraseFG (clockPre p st (SA.gateTime p.toParams
      s)).fg.F)
      (actView (clockPre p st (SA.gateTime p.toParams s))) s = some X)
    (hg : (clockPre p st (SA.gateTime p.toParams s)).base.obligations.any
      (fun row => (clockPre p st (SA.gateTime p.toParams s)).base.now < row.2.2 &&
        !Block.compatible row.1 X) = false) :
    Block.Preceq X (clock p st (SA.gateTime p.toParams s)).base.stableRecord := by
  have he := Run.clock_early_succ p st s
  rw [Run.earlyTime_succ_eq_gateTime] at he
  rw [he]
  apply pcsa_gateStep_record_covers_result p _ s X _ hfresh hX hg
  rw [(clockPre_output_fields p st _).1]
  exact hf
end AvailableChain.PCSA

end
