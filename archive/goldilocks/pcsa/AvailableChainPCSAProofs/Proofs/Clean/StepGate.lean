module
public import AvailableChainPCSAProofs.Proofs.Foundations.Locks
public import AvailableChainPCSA.Model.Clock
public import AvailableChainGeneric.Proofs.Pure.BlockOrder

public section

/-! Gate consequences of the previous clean chain facts
(pcsa34-r4.3 §5.2.2(e)). OPEN: the joint run induction must supply these
compatibility facts at each gate input. -/

namespace AvailableChain.PCSA

open Gen.Pure

/-- PCs compatible with the result permit every prefix lock write,
regardless of the gate rank. -/
theorem pcsa_clean_lock_write (cs : List (PC n)) (rank : Option PCRank) (X b : Block)
    (hpc : ∀ pc ∈ cs, Block.Compatible pc.target X) (hb : Block.Preceq b X) :
    leaseWriteOK cs rank b = true := by
  apply (leaseWriteOK_iff cs rank b).mpr
  intro pc hp _
  rw [block_compatible_comm]
  apply block_compatible_of_preceq_compatible hb
  change Block.compatible X pc.target = true
  rw [block_compatible_comm]
  exact hpc pc hp

/-- Compatibility of every live lock makes the whole-result guard pass. -/
theorem pcsa_clean_gate_guard (st : State n) (X : Block)
    (h : ∀ row ∈ st.base.obligations, st.base.now < row.2.2 → Block.Compatible row.1 X) :
    st.base.obligations.any (fun row => st.base.now < row.2.2 &&
      !Block.compatible row.1 X) = false := by
  apply List.any_eq_false.mpr
  intro row hr
  by_cases hl : st.base.now < row.2.2
  · simp only [hl, decide_true, Bool.true_and,
      show Block.compatible row.1 X = true from h row hr hl, Bool.not_true,
      Bool.false_eq_true, not_false_eq_true]
  · simp only [hl, decide_false, Bool.false_and, Bool.false_eq_true, not_false_eq_true]

/-- A compatible PC preserves every lock during its deletion step. -/
theorem pcsa_clean_delete_locks (st : State n) (pc : PC n)
    (h : ∀ row ∈ st.base.obligations, Block.Compatible pc.target row.1) :
    (deleteConflictingLeases st pc).base.obligations = st.base.obligations := by
  rw [deleteConflictingLeases_def]
  apply List.filter_eq_self.mpr
  intro row hr
  simp only [show Block.compatible pc.target row.1 = true from h row hr,
    Bool.not_true, Bool.and_false, Bool.not_false]

/-- Once the guard passes, the gate writes exactly the advanced result to S.
The later lock writes preserve that value. -/
theorem pcsa_clean_gate_record (p : Params) (st : State n) (s : Slot) (a X : Block)
    (cs : List (PC n)) (rank : Option PCRank)
    (hr : SA.Root.confirmationFrom p.toParams a (actView st) s = some X)
    (hl : ∀ row ∈ st.base.obligations, st.base.now < row.2.2 → Block.Compatible row.1 X) :
    (gateFrom p a cs rank st s).base.stableRecord = GridCO.advance st.base.stableRecord X := by
  have hg := pcsa_clean_gate_guard st X hl
  rw [gateFrom_def]
  dsimp only
  rw [hr]
  dsimp only
  rw [hg]
  simp only [Bool.false_eq_true, ite_false]
  apply List.foldlRecOn (motive := fun acc : State n =>
    acc.base.stableRecord = GridCO.advance st.base.stableRecord X)
  · rfl
  · intro acc h b _
    apply List.foldlRecOn (motive := fun acc : State n =>
      acc.base.stableRecord = GridCO.advance st.base.stableRecord X)
    · exact h
    · intro acc' h' g _
      exact h'

end AvailableChain.PCSA
end
