module
public import AvailableChainSAPC.Proofs.RecentArchive
public import AvailableChainGridCO.Proofs.ReceiptOrigins

@[expose] public section
namespace AvailableChain.SAPC
open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- A receipt handler stamps new base entries with its input clock. -/
theorem process_base_stamp_origin (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    (∀ row ∈ (process p st o).base.blockStamp,
      row ∈ st.base.blockStamp ∨ row.2 = st.base.now) ∧
    (∀ row ∈ (process p st o).base.voteStamp,
      row ∈ st.base.voteStamp ∨ row.2 = st.base.now) := by
  have h := process_base_invariant p (fun acc => acc.now = st.base.now ∧
      (∀ row ∈ acc.blockStamp, row ∈ st.base.blockStamp ∨ row.2 = st.base.now) ∧
      (∀ row ∈ acc.voteStamp, row ∈ st.base.voteStamp ∨ row.2 = st.base.now))
    (by
      intro acc head h
      unfold GridCO.admitVote
      split
      · dsimp only
        split
        · exact h
        · refine ⟨h.1, h.2.1, ?_⟩
          intro row hr
          rcases List.mem_append.mp hr with hr | hr
          · exact h.2.2 row hr
          · exact Or.inr ((List.mem_singleton.mp hr) ▸ h.1)
      · exact h)
    (by
      intro acc proposal b h
      unfold GridCO.admitProposal
      dsimp only
      split <;> split
      all_goals first | exact h | skip
      all_goals
        refine ⟨h.1, ?_, h.2.2⟩
        intro row hr
        rcases List.mem_append.mp hr with hr | hr
        · exact h.2.1 row hr
        · have he : row = (b, acc.now) := List.mem_singleton.mp hr
          exact Or.inr (he ▸ h.1)) st o
    ⟨rfl, fun _ hr => Or.inl hr, fun _ hr => Or.inl hr⟩
  exact h.2

/-- Base stamp rows always name stored receipts. -/
theorem base_stamp_rows_stored {V : Type} [DecidableEq V] (p : Params)
    (events : List (Event V (sapc p).Object)) (v : V) :
    (∀ row ∈ ((events.foldl World.step World.init) v).base.blockStamp,
      row.1 ∈ ((events.foldl World.step World.init) v).base.blocks) ∧
    (∀ row ∈ ((events.foldl World.step World.init) v).base.voteStamp,
      row.1 ∈ ((events.foldl World.step World.init) v).base.votes) := by
  apply fold_invariant p (fun st =>
    (∀ row ∈ st.base.blockStamp, row.1 ∈ st.base.blocks) ∧
    (∀ row ∈ st.base.voteStamp, row.1 ∈ st.base.votes))
  · simp [initial, GridCO.initial]
  · intro st t h
    have hd := clock_receiptData p st t
    have hb := congrArg (fun d => d.1) hd
    have hbs := congrArg (fun d => d.2.1) hd
    have hv := congrArg (fun d => d.2.2.1) hd
    have hvs := congrArg (fun d => d.2.2.2) hd
    dsimp only [GridCO.receiptData] at hb hbs hv hvs
    simpa only [hb, hbs, hv, hvs] using h
  · apply process_base_invariant p (fun st =>
      (∀ row ∈ st.blockStamp, row.1 ∈ st.blocks) ∧
      (∀ row ∈ st.voteStamp, row.1 ∈ st.votes))
    · intro st o h
      unfold GridCO.admitVote
      split
      · dsimp only
        split
        · exact h
        · refine ⟨h.1, ?_⟩
          intro row hr
          rcases List.mem_append.mp hr with hr | hr
          · exact List.mem_append_left _ (h.2 row hr)
          · simp only [List.mem_singleton] at hr
            simp [hr]
      · exact h
    · intro st o b h
      unfold GridCO.admitProposal
      dsimp only
      split <;> split
      all_goals first | exact h | skip
      all_goals
        refine ⟨?_, h.2⟩
        intro row hr
        rcases List.mem_append.mp hr with hr | hr
        · exact List.mem_append_left _ (h.1 row hr)
        · simp only [List.mem_singleton] at hr
          simp [hr]

/-- A stamp before a public cutoff cannot have been added after that
cutoff. This includes carried signatures and sleeping readers. -/
theorem base_early_stamps_at_input {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (cut : Time) (hpub : PublicTime E cut) (hz : 0 ≤ cut) (index : Nat) (v : V) :
    (∀ row ∈ (Run.stateBefore (sapc p) rho index v).base.blockStamp, row.2 < cut →
      row ∈ (Run.stateBeforeTime (sapc p) rho cut v).base.blockStamp) ∧
    (∀ row ∈ (Run.stateBefore (sapc p) rho index v).base.voteStamp, row.2 < cut →
      row ∈ (Run.stateBeforeTime (sapc p) rho cut v).base.voteStamp) := by
  induction index with
  | zero =>
      have hp := stateBefore_base_receiptPrefix p rho (Nat.zero_le
        (rho.events.filter (fun e => decide (e.time ≤ cut - 1))).length) v
      rw [← time_input_eq_event_prefix p E rho hs] at hp
      exact ⟨fun _ hm _ => hp.blockStamp.subset hm, fun _ hm _ => hp.voteStamp.subset hm⟩
  | succ index ih =>
      cases he : rho.events[index]? with
      | none => simpa [Run.stateBefore, List.take_add_one, he] using ih
      | some e =>
          by_cases ht : e.time < cut
          · have hp := stateBefore_base_receiptPrefix p rho
              (Nat.succ_le_of_lt ((index_lt_read_length_iff hs (cut - 1) he).mpr
                (Int.le_sub_one_iff.mpr ht))) v
            rw [← time_input_eq_event_prefix p E rho hs] at hp
            exact ⟨fun _ hm _ => hp.blockStamp.subset hm, fun _ hm _ => hp.voteStamp.subset hm⟩
          · rw [stateBefore_succ_event he]
            cases e with
            | tick w t =>
                by_cases hv : v = w
                · subst w
                  simp only [World.step, Function.update_self]
                  have hd := clock_receiptData p (Run.stateBefore (sapc p) rho index v) t
                  have hb := congrArg (fun d => d.2.1) hd
                  have hv := congrArg (fun d => d.2.2.2) hd
                  dsimp only [GridCO.receiptData] at hb hv
                  change (∀ row ∈
                    (clock p (Run.stateBefore (sapc p) rho index v) t).base.blockStamp, _ → _) ∧
                    (∀ row ∈
                      (clock p (Run.stateBefore (sapc p) rho index v) t).base.voteStamp, _ → _)
                  simpa only [hb, hv] using ih
                · simpa only [World.step, Function.update_of_ne hv] using ih
            | deliver w o t =>
                by_cases hv : v = w
                · subst w
                  simp only [World.step, Function.update_self]
                  have hn := delivery_now_ge_public p E rho hs he hpub hz (le_of_not_gt ht)
                  have hor := process_base_stamp_origin p (Run.stateBefore (sapc p) rho index v) o
                  constructor
                  · intro row hm hlt
                    rcases hor.1 row hm with hm | heq
                    · exact ih.1 row hm hlt
                    · exact (not_lt.mpr hn (heq ▸ hlt)).elim
                  · intro row hm hlt
                    rcases hor.2 row hm with hm | heq
                    · exact ih.2 row hm hlt
                    · exact (not_lt.mpr hn (heq ▸ hlt)).elim
                · simpa only [World.step, Function.update_of_ne hv] using ih

/-- An early base receipt was already stored at the strict cutoff. -/
theorem base_early_receipts_at_input {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (cut : Time) (hpub : PublicTime E cut) (hz : 0 ≤ cut) (index : Nat) (v : V) :
    (∀ b ∈ (Run.stateBefore (sapc p) rho index v).base.blocks,
      GridCO.stampBlock (Run.stateBefore (sapc p) rho index v).base b < cut →
      b ∈ (Run.stateBeforeTime (sapc p) rho cut v).base.blocks) ∧
    (∀ o ∈ (Run.stateBefore (sapc p) rho index v).base.votes,
      GridCO.stampVote (Run.stateBefore (sapc p) rho index v).base o < cut →
      o ∈ (Run.stateBeforeTime (sapc p) rho cut v).base.votes) := by
  have hstamp := base_receiptStamped_at_fold p (rho.events.take index) v
  have hstored := base_stamp_rows_stored p
    (rho.events.filter (fun e => decide (e.time < cut))) v
  have hor := base_early_stamps_at_input p E rho hs cut hpub hz index v
  exact ⟨fun b hb ht => hstored.1 _ (hor.1 _
      (GridCO.stampBlock_mem_of_stored _ hstamp b hb) ht),
    fun o ho ht => hstored.2 _ (hor.2 _
      (GridCO.stampVote_mem_of_stored _ hstamp o ho) ht)⟩

end AvailableChain.SAPC
end
