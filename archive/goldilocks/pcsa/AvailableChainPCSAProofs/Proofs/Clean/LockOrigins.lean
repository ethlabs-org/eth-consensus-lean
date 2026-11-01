module
public import AvailableChainPCSAProofs.Proofs.Foundations.Run
public import AvailableChainPCSAProofs.Proofs.Foundations.Locks

public section

/-! C6 LockOrigins: concrete receipt and count support. -/
namespace AvailableChain.PCSA
variable {n : Nat}
/-- Vote admission preserves all lock rows. -/
theorem pcsa_admit_vote_locks (q : GridCO.Params) (v : GridCO.State n .root)
    (o : GridCO.Wire n .root) : (GridCO.admitVote q v o).obligations = v.obligations := by
  delta GridCO.admitVote
  cases o.auth <;> cases o.payload <;> dsimp only
  all_goals first | rfl | (split <;> rfl)
/-- Base proposal admission preserves all lock rows. -/
theorem pcsa_admit_proposal_locks (q : GridCO.Params) (v : GridCO.State n .root)
    (o : GridCO.Wire n .root) (B : Block) (raw : List (GridCO.HeadWire n .root)) :
    (GridCO.admitProposal q v o B raw).obligations = v.obligations := by
  delta GridCO.admitProposal
  cases o.auth <;> dsimp only
  all_goals first
    | rfl
    | (split
       · rfl
       · apply List.foldlRecOn
           (motive := fun acc : GridCO.State n .root => acc.obligations = v.obligations)
         · rfl
         · intro acc hh a _
           exact (pcsa_admit_vote_locks q acc (GridCO.fromHead a)).trans hh)
/-- Row admission preserves all lock rows. -/
theorem pcsa_admit_row_locks (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).base.obligations = st.base.obligations := by
  delta admitRow
  cases a.decode? with
  | none => rfl
  | some v => dsimp only; split <;> rfl
/-- Raw ack pooling preserves all lock rows. -/
theorem pcsa_pool_raw_ack_locks (st : State n) (a : AckWire n) :
    (poolAckRaw st a).base.obligations = st.base.obligations := by
  delta poolAckRaw
  cases a.decode? with
  | none => rfl
  | some v => dsimp only; split <;> rfl
/-- Checked ack pooling preserves all lock rows. -/
theorem pcsa_pool_ack_locks (p : Params) (st : State p.n) (a : AckWire p.n) :
    (poolAck p st a).base.obligations = st.base.obligations := by
  delta poolAck
  cases a.decode? with
  | none => rfl
  | some v =>
    rcases v with ⟨_, _, _⟩
    dsimp only
    split
    · rfl
    · split <;> rfl
/-- Row admission preserves all lock rows. -/
theorem pcsa_admit_rows_locks (p : Params) (st : State p.n) (rows : List (RowWire p.n)) :
    (rows.foldl (admitRow p) st).base.obligations = st.base.obligations := by
  apply List.foldlRecOn (motive := fun acc : State p.n => acc.base.obligations =
    st.base.obligations)
  · rfl
  · intro acc hh a _
    exact (pcsa_admit_row_locks p acc a).trans hh
/-- Raw ack pooling preserves all lock rows. -/
theorem pcsa_pool_raw_acks_locks (st : State n) (acks : List (AckWire n)) :
    (acks.foldl poolAckRaw st).base.obligations = st.base.obligations := by
  apply List.foldlRecOn (motive := fun acc : State n => acc.base.obligations = st.base.obligations)
  · rfl
  · intro acc hh a _
    exact (pcsa_pool_raw_ack_locks acc a).trans hh
/-- Record normalization preserves all lock rows. -/
theorem pcsa_normalize_locks (st : State n) :
    (normalizeS st).base.obligations = st.base.obligations := by
  delta normalizeS
  split <;> rfl
private theorem locks_reconcile (st : State n) :
    (reconcile st).base.obligations ⊆ st.base.obligations := by
  delta reconcile
  rw [pcsa_normalize_locks]
  intro row hr
  exact (List.mem_filter.mp hr).1
private theorem locks_collect (st : State n) :
    (collectPCs st).base.obligations ⊆ st.base.obligations := by
  apply collectPCs_invariant (fun acc => acc.base.obligations ⊆ st.base.obligations)
  · intro acc C hh _
    rw [installPC_def]
    split
    · exact hh
    · intro row hr
      exact hh (List.mem_filter.mp hr).1
  · exact List.Subset.refl _
private theorem locks_block (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) : (admitBlock p st s N).base.obligations ⊆ st.base.obligations := by
  delta admitBlock
  split
  · exact List.Subset.refl _
  · cases parentFG st N.erase with
    | none => exact List.Subset.refl _
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
        change (N.rows.foldl (admitRow p) (collectPCs (N.pcAcks.foldl poolAckRaw
          st4))).base.obligations ⊆ _
        have h1 : st1.base.obligations = st.base.obligations :=
          pcsa_admit_proposal_locks p.toParams.engine st.base _ _ _
        have h3 : st3.base.obligations ⊆ st.base.obligations := by
          change st2.base.obligations ⊆ st.base.obligations
          dsimp only [st2]
          cases N.pc with
          | none => intro row hr; exact h1 ▸ hr
          | some C =>
            dsimp only
            split
            · intro row hr
              exact h1 ▸ (deleteConflictingLeases_subset st1 C hr)
            · intro row hr
              exact h1 ▸ hr
        have h4 : st4.base.obligations ⊆ st.base.obligations := by
          dsimp only [st4]
          split
          · exact h3
          · exact List.Subset.trans (locks_reconcile st3) h3
        rw [pcsa_admit_rows_locks]
        intro row hr
        have hm := locks_collect _ hr
        rw [pcsa_pool_raw_acks_locks] at hm
        exact h4 hm
      · exact List.Subset.refl _
/-- Deliveries can remove locks but cannot create a new lock row. -/
theorem pcsa_process_locks_subset (p : Params) (st : State p.n) (o : Wire p.n) :
    (process p st o).base.obligations ⊆ st.base.obligations := by
  delta process
  cases o.decode with
  | none => exact List.Subset.refl _
  | some msg => cases msg with
    | vote s i r =>
      change (GridCO.admitVote _ st.base _).obligations ⊆ st.base.obligations
      rw [pcsa_admit_vote_locks]
    | row i body => rw [pcsa_admit_row_locks]
    | ack s i r =>
      change (collectPCs (poolAck p st _)).base.obligations ⊆ st.base.obligations
      intro row hr
      have hm := locks_collect _ hr
      rwa [pcsa_pool_ack_locks] at hm
    | pc C =>
      dsimp only
      delta admitPC
      split
      · intro row hr
        have hm := locks_collect _ hr
        rwa [pcsa_pool_raw_acks_locks] at hm
      · exact List.Subset.refl _
    | block s N => exact locks_block p st s N
/-- Expiry and release before a gate only remove lock rows. -/
theorem pcsa_clockPre_locks_subset (p : Params) (st : State p.n) (t : Time) :
    (clockPre p st t).base.obligations ⊆ st.base.obligations := by
  delta clockPre
  dsimp only
  split <;> split <;> split
  all_goals intro row hr
  all_goals first
    | exact (List.mem_filter.mp hr).1
    | exact (List.mem_filter.mp (List.mem_filter.mp hr).1).1
/-- Before the first gate, a clock cannot create a lock row. -/
theorem pcsa_clock_locks_before_first_gate (p : Params) (st : State p.n) (t : Time)
    (ht : t < SA.gateTime p.toParams 0) :
    (clock p st t).base.obligations ⊆ st.base.obligations := by
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
  · exact pcsa_clockPre_locks_subset p st t
end AvailableChain.PCSA

end
