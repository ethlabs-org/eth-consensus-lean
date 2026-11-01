module
public import AvailableChainPCSAProofs.Proofs.Foundations.Output
public import AvailableChainPCSAProofs.Proofs.Foundations.Rank
public import AvailableChainPCSAProofs.Proofs.Foundations.AckPool
public import AvailableChainPCSAProofs.Proofs.Foundations.Snapshot
public import AvailableChainPCSA.Statements.Invariants
public import AvailableChainFGSA.Proofs.Nesting

public section

/-! Completed-event output invariants (pcsa34-r4.3 §3.2, R7). -/

namespace AvailableChain.PCSA
variable {n : Nat}

/-- The two store premises used by the Generic floor nesting theorem. -/
def OutputSafe (st : State n) : Prop :=
  Block.Preceq (eraseFG st.fg.F) st.base.stableRecord ∧
    ∀ c ∈ st.pcs, Block.Compatible c.target (eraseFG st.fg.F)

/-- Normalization supplies the S bound and keeps PC compatibility. -/
theorem normalizeS_outputSafe (st : State n)
    (h : ∀ c ∈ st.pcs, Block.Compatible c.target (eraseFG st.fg.F)) :
    OutputSafe (normalizeS st) := by
  unfold normalizeS
  split
  · exact ⟨by assumption, h⟩
  · exact ⟨Gen.Pure.block_preceq_refl _, h⟩

/-- Reconciliation restores both output premises. -/
theorem reconcile_outputSafe (st : State n) : OutputSafe (reconcile st) := by
  apply normalizeS_outputSafe
  intro c hc
  exact (List.mem_filter.mp hc).2

/-- Admission of a valid PC preserves the output premises. -/
theorem installPC_outputSafe (st : State n) (c : PC n) (h : OutputSafe st)
    (hv : pcValid st c = true) : OutputSafe (installPC st c) := by
  unfold installPC deleteConflictingLeases
  split
  · exact h
  · refine ⟨h.1, ?_⟩
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact h.2 d hd
    · have he := List.mem_singleton.mp hd
      subst d
      exact (Bool.and_eq_true_iff.mp hv).2

/-- PC collection preserves the output premises. -/
theorem collectPCs_outputSafe (st : State n) (h : OutputSafe st) :
    OutputSafe (collectPCs st) :=
  collectPCs_invariant OutputSafe installPC_outputSafe st h

/-- Raw ack pooling preserves the output premises. -/
theorem poolAckRaw_outputSafe (st : State n) (a : AckWire n) (h : OutputSafe st) :
    OutputSafe (poolAckRaw st a) := by
  obtain ⟨hp, _, hb, hf⟩ := poolAckRaw_frame st a
  dsimp only [OutputSafe] at h ⊢
  simpa only [hp, hb, hf] using h

/-- Checked ack pooling preserves the output premises. -/
theorem poolAck_outputSafe (p : Params) (st : State p.n) (a : AckWire p.n)
    (h : OutputSafe st) : OutputSafe (poolAck p st a) := by
  delta poolAck
  cases hdecode : a.decode? <;> dsimp only
  rotate_left
  · rename_i v
    rcases v with ⟨_, _, _⟩
    split
    · exact h
    · split <;> exact h
  · exact h

/-- Row admission does not change either output premise. -/
theorem admitRow_outputSafe (p : Params) (st : State p.n) (a : RowWire p.n)
    (h : OutputSafe st) : OutputSafe (admitRow p st a) := by
  delta admitRow
  cases hdecode : a.decode? <;> dsimp only
  rotate_left
  · split <;> exact h
  · exact h

/-- A batch of raw acks preserves the output premises. -/
theorem fold_poolAckRaw_outputSafe (st : State n) (as : List (AckWire n)) (h : OutputSafe st) :
    OutputSafe (as.foldl poolAckRaw st) :=
  List.foldlRecOn as poolAckRaw h (fun acc ha a _ => poolAckRaw_outputSafe acc a ha)

/-- A row batch preserves the output premises. -/
theorem fold_admitRow_outputSafe (p : Params) (st : State p.n) (as : List (RowWire p.n))
    (h : OutputSafe st) : OutputSafe (as.foldl (admitRow p) st) :=
  List.foldlRecOn as (admitRow p) h (fun acc ha a _ => admitRow_outputSafe p acc a ha)

/-- Every completed delivery preserves output nesting premises. -/
theorem process_outputSafe (p : Params) (st : State p.n) (o : Wire p.n) (h : OutputSafe st) :
    OutputSafe (process p st o) := by
  delta process
  cases hd : o.decode with
  | some msg => cases msg with
    | vote s i r =>
      dsimp only
      refine ⟨?_, h.2⟩
      change Block.Preceq (eraseFG st.fg.F) (GridCO.admitVote _ _ _).stableRecord
      rw [GridCO.admitVote_stable]
      exact h.1
    | row i body =>
      dsimp only
      exact admitRow_outputSafe p st _ h
    | block s N =>
      dsimp only
      delta admitBlock
      split
      · exact h
      · cases hP : parentFG st N.erase
        · exact h
        · dsimp only
          split
          · apply fold_admitRow_outputSafe
            apply collectPCs_outputSafe
            apply fold_poolAckRaw_outputSafe
            cases N.pc <;> dsimp only <;> split_ifs <;>
              first
              | exact reconcile_outputSafe _
              | (dsimp only [OutputSafe] at h ⊢; simpa only [deleteConflictingLeases_def,
                  FGSA.admitProposal_stable] using h)
              | (delta OutputSafe; simp_all only [deleteConflictingLeases_def,
                  FGSA.admitProposal_stable]; exact h)
          · exact h
    | ack s i r =>
      dsimp only
      exact collectPCs_outputSafe _ (poolAck_outputSafe p st _ h)
    | pc d =>
      dsimp only
      unfold admitPC
      split
      · exact collectPCs_outputSafe _ (fold_poolAckRaw_outputSafe st _ h)
      · exact h
  | none =>
    exact h

/-- Every completed tick preserves output nesting premises. -/
theorem clock_outputSafe (p : Params) (st : State p.n) (t : Time) (h : OutputSafe st) :
    OutputSafe (clock p st t) := by
  have hc : OutputSafe (clockPre p st t) := by
    dsimp only [OutputSafe] at h ⊢
    simpa only [clockPre_pcs, (clockPre_output_fields p st t).1,
      (clockPre_output_fields p st t).2] using h
  unfold clock
  dsimp only
  split
  · unfold gateStep
    apply normalizeS_outputSafe
    split
    · exact hc.2
    · intro c hc'
      obtain ⟨hp, hf⟩ := gateFrom_pc_frame p _ _ _ (clockPre p st t) _
      rw [hp] at hc'
      rw [hf]
      exact hc.2 c hc'
  · exact hc

/-- The local store transition system preserves the output premises. -/
theorem reachable_outputSafe (p : Params) (st : State p.n) (h : Reachable p st) :
    OutputSafe st := by
  induction h with
  | init => exact ⟨Gen.Pure.block_preceq_refl _, by dsimp only [initial]; simp⟩
  | tick t _ ih => exact clock_outputSafe p _ t ih
  | deliver o _ ih => exact process_outputSafe p _ o ih

/-- Reachable stores satisfy the complete output nesting conclusion. -/
theorem reachable_outputNesting (p : Params) (st : State p.n) (h : Reachable p st) :
    Block.Preceq (strong st) (confirmed st) ∧
      Block.Preceq (eraseFG st.fg.F) (confirmed st) := by
  obtain ⟨hS, hpc⟩ := reachable_outputSafe p st h
  refine ⟨strong_preceq_confirmed st, finalized_preceq_confirmed st hS ?_⟩
  intro b hb
  unfold pcTarget? latestPC at hb
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp hb
  exact (Gen.Pure.block_compatible_iff_preceq_or _ _).mpr
    ((Gen.Pure.block_compatible_iff_preceq_or _ _).mp (hpc c (bestPC_mem _ c hc))).symm

end AvailableChain.PCSA
end
