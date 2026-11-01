module
public import AvailableChainPCSAProofs.Proofs.Foundations.Run

public section

/-! C6 StoreOrigins: concrete receipt and count support. -/
namespace AvailableChain.PCSA
variable {n : Nat}
private def RecordOrigin (st st' : State n) : Prop :=
  st'.base.stableRecord = st.base.stableRecord ∨
    (¬ Block.Preceq (eraseFG st'.fg.F) st.base.stableRecord ∧
      st'.base.stableRecord = eraseFG st'.fg.F)
private theorem record_grid_vote (q : GridCO.Params) (v : GridCO.State n .root)
    (o : GridCO.Wire n .root) :
    (GridCO.admitVote q v o).stableRecord = v.stableRecord := by
  delta GridCO.admitVote
  cases o.auth <;> cases o.payload <;> dsimp only
  all_goals first | rfl | (split <;> rfl)
private theorem record_grid_proposal (q : GridCO.Params) (v : GridCO.State n .root)
    (o : GridCO.Wire n .root) (B : Block) (raw : List (GridCO.HeadWire n .root)) :
    (GridCO.admitProposal q v o B raw).stableRecord = v.stableRecord := by
  delta GridCO.admitProposal
  cases o.auth <;> dsimp only
  all_goals first
    | rfl
    | (split
       · rfl
       · apply List.foldlRecOn
           (motive := fun acc : GridCO.State n .root => acc.stableRecord = v.stableRecord)
         · rfl
         · intro acc hh a _
           exact (record_grid_vote q acc (GridCO.fromHead a)).trans hh)
private theorem record_row (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).base.stableRecord = st.base.stableRecord ∧
      (admitRow p st a).fg = st.fg := by
  delta admitRow
  cases a.decode? with
  | none => exact ⟨rfl, rfl⟩
  | some v => dsimp only; split <;> exact ⟨rfl, rfl⟩
private theorem record_raw (st : State n) (a : AckWire n) :
    (poolAckRaw st a).base.stableRecord = st.base.stableRecord ∧
      (poolAckRaw st a).fg = st.fg := by
  delta poolAckRaw
  cases a.decode? with
  | none => exact ⟨rfl, rfl⟩
  | some v => dsimp only; split <;> exact ⟨rfl, rfl⟩
private theorem record_pool (p : Params) (st : State p.n) (a : AckWire p.n) :
    (poolAck p st a).base.stableRecord = st.base.stableRecord := by
  delta poolAck
  cases a.decode? with
  | none => rfl
  | some v =>
    rcases v with ⟨_, _, _⟩
    dsimp only
    split
    · rfl
    · split <;> rfl
private theorem record_collect (st : State n) :
    (collectPCs st).base.stableRecord = st.base.stableRecord ∧ (collectPCs st).fg = st.fg := by
  refine ⟨?_, (collectPCs_frame st).2.2.2.2⟩
  apply collectPCs_preserves (fun st => st.base.stableRecord)
  intro acc C
  rw [installPC_def]
  split <;> rfl
private theorem record_rows (p : Params) (st : State p.n) (rows : List (RowWire p.n)) :
    (rows.foldl (admitRow p) st).base.stableRecord = st.base.stableRecord ∧
      (rows.foldl (admitRow p) st).fg = st.fg := by
  apply List.foldlRecOn (motive := fun acc : State p.n =>
    acc.base.stableRecord = st.base.stableRecord ∧ acc.fg = st.fg)
  · exact ⟨rfl, rfl⟩
  · intro acc hh a _
    exact ⟨((record_row p acc a).1).trans hh.1, ((record_row p acc a).2).trans hh.2⟩
private theorem record_raws (st : State n) (acks : List (AckWire n)) :
    (acks.foldl poolAckRaw st).base.stableRecord = st.base.stableRecord ∧
      (acks.foldl poolAckRaw st).fg = st.fg := by
  apply List.foldlRecOn (motive := fun acc : State n =>
    acc.base.stableRecord = st.base.stableRecord ∧ acc.fg = st.fg)
  · exact ⟨rfl, rfl⟩
  · intro acc hh a _
    exact ⟨((record_raw acc a).1).trans hh.1, ((record_raw acc a).2).trans hh.2⟩
private theorem record_reconcile (st : State n) :
    (reconcile st).fg = st.fg ∧ RecordOrigin st (reconcile st) := by
  delta reconcile normalizeS RecordOrigin
  dsimp only
  split
  · exact ⟨rfl, Or.inl rfl⟩
  · rename_i hn
    exact ⟨rfl, Or.inr ⟨hn, rfl⟩⟩
private theorem record_block (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) : RecordOrigin st (admitBlock p st s N) := by
  delta admitBlock
  split
  · exact Or.inl rfl
  · cases parentFG st N.erase with
    | none => exact Or.inl rfl
    | some P =>
      dsimp only
      split
      · let st1 : State p.n := { st with
          base := GridCO.admitProposal p.toParams.engine st.base
            (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead) }
        let st2 := match N.pc with
          | none => st1
          | some C => if pcValid st1 C && !st1.pcs.any
              (fun d => d.slot == C.slot && d.target == C.target)
            then deleteConflictingLeases st1 C else st1
        let st3 : State p.n := { st2 with
          fg := FGSA.Window.on_block p p.K_W st2.fg (fgBlock P N.erase N.rows)
          proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
        let st4 := if st3.fg.F = st.fg.F then st3 else reconcile st3
        let out := N.rows.foldl (admitRow p) (collectPCs (N.pcAcks.foldl poolAckRaw st4))
        change RecordOrigin st out
        have hb : st1.base.stableRecord = st.base.stableRecord :=
          record_grid_proposal p.toParams.engine st.base _ _ _
        have h3 : st3.base.stableRecord = st.base.stableRecord := by
          change st2.base.stableRecord = st.base.stableRecord
          dsimp only [st2]
          cases N.pc <;> dsimp only
          all_goals first | exact hb | (split <;> exact hb)
        have hS : out.base.stableRecord = st4.base.stableRecord :=
          (record_rows p _ N.rows).1.trans
            ((record_collect _).1.trans (record_raws st4 N.pcAcks).1)
        have hFG : out.fg = st4.fg :=
          (record_rows p _ N.rows).2.trans
            ((record_collect _).2.trans (record_raws st4 N.pcAcks).2)
        delta RecordOrigin
        rw [hS, hFG]
        dsimp only [st4]
        split
        · exact Or.inl h3
        · have hr := record_reconcile st3
          rw [hr.1]
          have hh : RecordOrigin st3 (reconcile st3) := hr.2
          delta RecordOrigin at hh
          rwa [hr.1, h3] at hh
      · exact Or.inl rfl
/-- A delivery keeps S or normalizes it to finality when the old S excludes that finality. -/
theorem pcsa_process_record_origin (p : Params) (st : State p.n) (o : Wire p.n) :
    (process p st o).base.stableRecord = st.base.stableRecord ∨
      (¬ Block.Preceq (eraseFG (process p st o).fg.F) st.base.stableRecord ∧
        (process p st o).base.stableRecord = eraseFG (process p st o).fg.F) := by
  change RecordOrigin st (process p st o)
  delta process
  cases o.decode with
  | none => exact Or.inl rfl
  | some msg => cases msg with
    | vote s i r => exact Or.inl (record_grid_vote p.toParams.engine st.base _)
    | row i body => exact Or.inl (record_row p st _).1
    | ack s i r => exact Or.inl ((record_collect _).1.trans (record_pool p st _))
    | pc C =>
      dsimp only
      delta admitPC
      split
      · exact Or.inl ((record_collect _).1.trans (record_raws st C.acks).1)
      · exact Or.inl rfl
    | block s N => exact record_block p st s N
/-- A delivery whose finality stays at genesis cannot change S. -/
theorem pcsa_process_record_of_genesis (p : Params) (st : State p.n) (o : Wire p.n)
    (hf : (process p st o).fg.F = .genesis) :
    (process p st o).base.stableRecord = st.base.stableRecord := by
  rcases pcsa_process_record_origin p st o with hs | ⟨hn, _⟩
  · exact hs
  · rw [hf] at hn
    exact (hn (Gen.Pure.block_genesis_preceq _)).elim
/-- Before its first gate, a clock keeps S. -/
theorem pcsa_clock_record_before_first_gate (p : Params) (st : State p.n) (t : Time)
    (ht : t < SA.gateTime p.toParams 0) :
    (clock p st t).base.stableRecord = st.base.stableRecord := by
  have hzero : SA.gateTime p.toParams 0 = 6 * p.Δ := by
    change 4 * p.Δ * (0 : Int) + 6 * p.Δ = _
    ring
  rw [hzero] at ht
  delta clock
  dsimp only
  split
  · rename_i hg
    have hn := of_decide_eq_true (Bool.and_eq_true_iff.mp hg).1
    linarith
  · exact (clockPre_output_fields p st t).2
end AvailableChain.PCSA

end
