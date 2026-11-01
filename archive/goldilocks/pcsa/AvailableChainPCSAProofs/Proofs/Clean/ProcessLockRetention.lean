module
public import AvailableChainPCSAProofs.Proofs.Clean.LockOrigins
public import AvailableChainPCSAProofs.Proofs.Clean.LockRetention
public import AvailableChainPCSAProofs.Proofs.Clean.RelayFrames
public import AvailableChainPCSAProofs.Proofs.Clean.ProposalStore

public section

/-! C6 ProcessLockRetention: concrete receipt and count support. -/
namespace AvailableChain.PCSA
open CleanPCRelay
variable {n : Nat}
/-- Stage-one reconciliation keeps every lock row. -/
theorem pcsa_reconcile_locks_genesis (st : State n) (hf : st.fg.F = .genesis) :
    (reconcile st).base.obligations = st.base.obligations := by
  delta reconcile
  rw [pcsa_normalize_locks]
  apply List.filter_eq_self.mpr
  intro row _
  exact pcsa_activeCompatible_genesis st hf row.1
/-- An admitted proposal keeps a lock if all resulting held and carried PCs are compatible. -/
theorem pcsa_admit_block_keep_lock (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (row : Block × Nat × Time) (hr : row ∈ st.base.obligations)
    (hf : (admitBlock p st s N).fg.F = .genesis)
    (hpcs : ∀ C ∈ (admitBlock p st s N).pcs, Block.Compatible C.target row.1)
    (hcar : ∀ r C, C ∈ carriedPCs (admitBlock p st s N) r → Block.Compatible C.target row.1) :
    row ∈ (admitBlock p st s N).base.obligations := by
  by_cases hn : namedParentHeld st N = true
  · cases hp : parentFG st N.erase with
    | none =>
      have hout : admitBlock p st s N = st := by
        delta admitBlock
        rw [hn]
        change (match parentFG st N.erase with | none => st | some P => _) = st
        rw [hp]
      rw [hout]
      exact hr
    | some P =>
      by_cases ha : blockAccepted p st s N P = true
      · let st1 : State p.n := { st with
          base := GridCO.admitProposal p.toParams.engine st.base
            (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead) }
        let st2 := match N.pc with
          | none => st1
          | some C => if pcValid st1 C && !st1.pcs.any
              (fun old => old.slot == C.slot && old.target == C.target)
            then deleteConflictingLeases st1 C else st1
        let st3 : State p.n := { st2 with
          fg := FGSA.Window.on_block p p.K_W st2.fg (fgBlock P N.erase N.rows)
          proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
        let st4 := if st3.fg.F = st.fg.F then st3 else reconcile st3
        let out := N.rows.foldl (admitRow p) (collectPCs (N.pcAcks.foldl poolAckRaw st4))
        have hout : admitBlock p st s N = out := by
          delta admitBlock
          rw [hn]
          change (match parentFG st N.erase with | none => st | some P => _) = out
          rw [hp]
          change (if blockAccepted p st s N P then _ else st) = out
          rw [ite_eq_left ha]
          rfl
        rw [hout] at hf hpcs hcar ⊢
        have hfg : out.fg = st3.fg := by
          change (N.rows.foldl (admitRow p) (collectPCs (N.pcAcks.foldl poolAckRaw st4))).fg = _
          rw [(pcsa_fold_admitRow_frame p _ N.rows).2.2.2.2.1,
            (collectPCs_frame _).2.2.2.2, (pcsa_fold_poolAckRaw_frame st4 N.pcAcks).2.2.2.1]
          dsimp only [st4]
          split
          · rfl
          · exact (pcsa_reconcile_frame st3).2.2.2.2.1
        have hf3 : st3.fg.F = .genesis := by rwa [hfg] at hf
        have hblocks : out.base.blocks = st1.base.blocks := by
          change (N.rows.foldl (admitRow p) (collectPCs (N.pcAcks.foldl poolAckRaw
            st4))).base.blocks = _
          rw [(pcsa_fold_admitRow_frame p _ N.rows).2.2.2.2.2,
            (collectPCs_frame _).2.1, (pcsa_fold_poolAckRaw_frame st4 N.pcAcks).2.2.2.2.1]
          have h4 : st4.base.blocks = st3.base.blocks := by
            dsimp only [st4]
            split
            · rfl
            · exact (pcsa_reconcile_frame st3).2.2.2.2.2
          rw [h4]
          change st2.base.blocks = st1.base.blocks
          dsimp only [st2]
          cases N.pc with
          | none => rfl
          | some C => dsimp only; split <;> rfl
        have hprops : out.proposals = st.proposals ++ [⟨.proposer s, .proposal N⟩] := by
          rw [← hout]
          exact pcsa_clean_admitBlock_proposals p st s N P hn hp ha
        have hrow1 : row ∈ st1.base.obligations := by
          change row ∈ (GridCO.admitProposal p.toParams.engine st.base _ _ _).obligations
          rw [pcsa_admit_proposal_locks]
          exact hr
        have hrow2 : row ∈ st2.base.obligations := by
          dsimp only [st2]
          cases hNp : N.pc with
          | none => exact hrow1
          | some C =>
            dsimp only
            split
            · rename_i hvalid
              apply deleteConflictingLeases_keep st1 C row hrow1
              apply hcar N.slot C
              have hvc := (Bool.and_eq_true_iff.mp hvalid).1
              have hw := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hvc).1).1
              have hb := of_decide_eq_true (Bool.and_eq_true_iff.mp
                (Bool.and_eq_true_iff.mp hvc).1).2
              apply List.mem_filter.mpr
              refine ⟨List.mem_filterMap.mpr ⟨⟨.proposer s, .proposal N⟩, ?_, ?_⟩, ?_⟩
              · rw [hprops]
                exact List.mem_append_right _ (List.mem_singleton_self _)
              · change (if N.slot = N.slot then N.pc else none) = some C
                rw [ite_eq_left rfl, hNp]
              · apply Bool.and_eq_true_iff.mpr
                refine ⟨Bool.and_eq_true_iff.mpr ⟨hw, ?_⟩,
                  pcsa_activeCompatible_genesis out hf C.target⟩
                apply decide_eq_true
                rwa [hblocks]
            · exact hrow1
        have hrow4 : row ∈ st4.base.obligations := by
          dsimp only [st4]
          split
          · exact hrow2
          · rw [pcsa_reconcile_locks_genesis st3 hf3]
            exact hrow2
        change row ∈ (N.rows.foldl (admitRow p) (collectPCs (N.pcAcks.foldl poolAckRaw
          st4))).base.obligations
        rw [pcsa_admit_rows_locks]
        apply pcsa_collect_keep_lock
        · rw [pcsa_pool_raw_acks_locks]
          exact hrow4
        · intro C hC
          apply hpcs C
          change C ∈ (N.rows.foldl (admitRow p) (collectPCs (N.pcAcks.foldl poolAckRaw st4))).pcs
          rw [(pcsa_fold_admitRow_frame p _ N.rows).1]
          exact hC
      · have hout : admitBlock p st s N = st := by
          delta admitBlock
          rw [hn]
          change (match parentFG st N.erase with | none => st | some P => _) = st
          rw [hp]
          change (if blockAccepted p st s N P then _ else st) = st
          rw [ite_eq_right ha]
        rw [hout]
        exact hr
  · have hout : admitBlock p st s N = st := by
      delta admitBlock
      rw [Bool.eq_false_iff.mpr hn]
      rfl
    rw [hout]
    exact hr
end AvailableChain.PCSA

namespace AvailableChain.PCSA
/-- Every stage-one delivery keeps a lock compatible with all resulting held and carried PCs. -/
theorem pcsa_process_keep_lock (p : Params) (st : State p.n) (o : Wire p.n)
    (row : Block × Nat × Time) (hr : row ∈ st.base.obligations)
    (hf : (process p st o).fg.F = .genesis)
    (hpcs : ∀ C ∈ (process p st o).pcs, Block.Compatible C.target row.1)
    (hcar : ∀ s C, C ∈ carriedPCs (process p st o) s → Block.Compatible C.target row.1) :
    row ∈ (process p st o).base.obligations := by
  delta process at hf hpcs hcar ⊢
  cases hd : o.decode with
  | none => exact hr
  | some msg =>
    rw [hd] at hf hpcs hcar
    cases msg with
    | vote s i r =>
      change row ∈ (GridCO.admitVote p.toParams.engine st.base _).obligations
      rw [pcsa_admit_vote_locks]
      exact hr
    | row i body =>
      rw [pcsa_admit_row_locks]
      exact hr
    | ack s i r =>
      apply pcsa_collect_keep_lock
      · rw [pcsa_pool_ack_locks]
        exact hr
      · exact hpcs
    | pc C =>
      dsimp only at hf hpcs hcar ⊢
      delta admitPC at hf hpcs hcar ⊢
      split
      · rename_i hw
        rw [ite_eq_left hw] at hpcs
        apply pcsa_collect_keep_lock
        · rw [pcsa_pool_raw_acks_locks]
          exact hr
        · exact hpcs
      · exact hr
    | block s N => exact pcsa_admit_block_keep_lock p st s N row hr hf hpcs hcar
end AvailableChain.PCSA

end
