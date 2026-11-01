module
public import AvailableChainGridCO.Proofs.Paths

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

private theorem admitVote_stamp_origin (p : Params) {n : Nat} (st : State n)
    (parent o : Wire n) (t : Time) (hm : (o, t) ∈ (admitVote p st parent).voteStamp) :
    (o, t) ∈ st.voteStamp ∨
      t = st.now ∧ o ∉ st.votes ∧ o = parent ∧ ∃ B, o.payload = .head B := by
  unfold admitVote at hm
  split at hm
  · rename_i r i B ha hp
    dsimp only at hm
    split at hm
    · exact Or.inl hm
    · rename_i hgood
      rcases List.mem_append.mp hm with hm | hm
      · exact Or.inl hm
      · have he : o = parent ∧ t = st.now := by simpa using hm
        obtain ⟨rfl, rfl⟩ := he
        refine Or.inr ⟨rfl, ?_, rfl, B, hp⟩
        intro hold
        simp [hold] at hgood
  · exact Or.inl hm

private theorem fold_stamp_origin (p : Params) {n : Nat} (raw : List (HeadWire n))
    (st : State n) (o : Wire n) (t : Time)
    (hm : (o, t) ∈ (raw.foldl (fun acc row => admitVote p acc (fromHead row)) st).voteStamp) :
    (o, t) ∈ st.voteStamp ∨
      t = st.now ∧ o ∉ st.votes ∧ o ∈ raw.map fromHead ∧ ∃ B, o.payload = .head B := by
  induction raw generalizing st with
  | nil => exact Or.inl hm
  | cons row raw ih =>
      rcases ih _ hm with hm | ⟨ht, hn, hr, hb⟩
      · rcases admitVote_stamp_origin p st (fromHead row) o t hm with hm | ⟨ht, hn, he, hb⟩
        · exact Or.inl hm
        · exact Or.inr ⟨ht, hn, List.mem_cons.mpr (Or.inl he), hb⟩
      · exact Or.inr ⟨by simpa [admitVote_now] using ht,
          fun h => hn (admitVote_votes_subset p st _ h), List.mem_cons_of_mem _ hr, hb⟩

private theorem fold_vote_blocks (p : Params) {n : Nat} (raw : List (HeadWire n))
    (st : State n) :
    (raw.foldl (fun acc row => admitVote p acc (fromHead row)) st).blocks = st.blocks := by
  induction raw generalizing st with
  | nil => rfl
  | cons row raw ih => rw [List.foldl_cons, ih, admitVote_blocks]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A new HEAD stamp comes from a called handler at the current local
clock. This includes raw HEADs in an admitted proposal. -/
theorem process_vote_stamp_origin (p : Params) {n : Nat} (st : State n)
    (parent o : Wire n) (t : Time) (hm : (o, t) ∈ (process p st parent).voteStamp) :
    (o, t) ∈ st.voteStamp ∨
      t = st.now ∧ o ∉ st.votes ∧ handles p st parent o ∧ ∃ B, o.payload = .head B := by
  unfold process at hm
  split at hm
  · rcases admitVote_stamp_origin p st parent o t hm with hm | ⟨ht, hn, he, hb⟩
    · exact Or.inl hm
    · exact Or.inr ⟨ht, hn, Or.inl he.symm, hb⟩
  · rename_i s B raw support ha hp
    unfold admitProposal at hm
    simp only [ha] at hm
    split at hm
    all_goals first
      | exact Or.inl hm
      | rename_i hgood
        rcases fold_stamp_origin p raw _ o t hm with hm | ⟨ht, hn, hr, hb⟩
        · exact Or.inl hm
        · refine Or.inr ⟨ht, hn, Or.inr ?_, hb⟩
          simp only [hp]
          refine ⟨?_, ?_, hr⟩
          · intro hold; simp [hold] at hgood
          · simp only [process, ha, hp, admitProposal]
            simp only [hgood, Bool.false_eq_true, ite_false]
            rw [fold_vote_blocks]
            simp
  · exact Or.inl hm

private def VoteStampsStored {n : Nat} (st : State n) : Prop :=
  ∀ o t, (o, t) ∈ st.voteStamp → o ∈ st.votes

private theorem admitVote_stamps_stored (p : Params) {n : Nat} (st : State n)
    (parent : Wire n) (h : VoteStampsStored st) : VoteStampsStored (admitVote p st parent) := by
  unfold admitVote
  split
  · dsimp only
    split
    · exact h
    · intro o t hm
      rcases List.mem_append.mp hm with hm | hm
      · exact List.mem_append_left _ (h o t hm)
      · have he : o = parent ∧ t = st.now := by simpa using hm
        simp [he.1]
  · exact h

private theorem fold_stamps_stored (p : Params) {n : Nat} (raw : List (HeadWire n))
    (st : State n) (h : VoteStampsStored st) :
    VoteStampsStored (raw.foldl (fun acc row => admitVote p acc (fromHead row)) st) := by
  induction raw generalizing st with
  | nil => exact h
  | cons row raw ih => exact ih _ (admitVote_stamps_stored p st _ h)

private theorem process_stamps_stored (p : Params) {n : Nat} (st : State n)
    (parent : Wire n) (h : VoteStampsStored st) : VoteStampsStored (process p st parent) := by
  unfold process
  split
  · exact admitVote_stamps_stored p st parent h
  · unfold admitProposal
    dsimp only
    split <;> split
    all_goals first | exact h | exact fold_stamps_stored p _ _ h
  · exact h

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Every HEAD stamp in a reachable state names a stored HEAD. -/
theorem run_vote_stamps_stored {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (index : Nat) (reader : V) :
    ∀ o t, (o, t) ∈ (Run.stateBefore (gridCO p) rho index reader).voteStamp →
      o ∈ (Run.stateBefore (gridCO p) rho index reader).votes := by
  change VoteStampsStored _
  induction index with
  | zero => simp [VoteStampsStored, Run.stateBefore, World.init, gridCO, initial]
  | succ index ih =>
      cases hi : rho.events[index]? with
      | none => simpa [Run.stateBefore, List.take_add_one, hi] using ih
      | some e =>
          rw [stateBefore_succ_event hi]
          cases e with
          | tick v t =>
              by_cases hv : reader = v
              · subst v
                have hd := clock_receiptData p (Run.stateBefore (gridCO p) rho index reader) t
                have hv := congrArg (fun x => x.2.2.1) hd
                have hs := congrArg (fun x => x.2.2.2) hd
                dsimp only [receiptData] at hv hs
                simp only [World.step, Function.update_self]
                change VoteStampsStored (clock p _ t)
                simpa only [VoteStampsStored, hv, hs] using ih
              · simpa [World.step, hv] using ih
          | deliver v o t =>
              by_cases hv : reader = v
              · subst v; simpa [World.step] using! process_stamps_stored p _ o ih
              · simpa [World.step, hv] using ih

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A receipt stamp identifies an earlier acceptance and its exact local
clock. No assumption about the signer's honesty is needed. -/
theorem stored_head_stamp_source {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (index : Nat) (reader : V) (o : Wire p.n) (stamp : Time)
    (hm : (o, stamp) ∈ (Run.stateBefore (gridCO p) rho index reader).voteStamp) :
    ∃ j < index, ∃ t,
      Run.acceptsAt (gridCO p) rho j reader o t ∧
      stamp = (Run.stateBefore (gridCO p) rho j reader).now := by
  induction index with
  | zero => simp [Run.stateBefore, World.init, gridCO, initial] at hm
  | succ index ih =>
      cases hi : rho.events[index]? with
      | none =>
          have hm' : (o, stamp) ∈ (Run.stateBefore (gridCO p) rho index reader).voteStamp := by
            simpa [Run.stateBefore, List.take_add_one, hi] using hm
          obtain ⟨j, hj, rest⟩ := ih hm'
          exact ⟨j, by omega, rest⟩
      | some e =>
          have hpost := stateBefore_succ_event hi
          rw [hpost] at hm
          cases e with
          | tick v t =>
              have hm' : (o, stamp) ∈ (Run.stateBefore (gridCO p) rho index reader).voteStamp := by
                by_cases hv : reader = v
                · subst v
                  have hd := congrArg (fun x => x.2.2.2)
                    (clock_receiptData p (Run.stateBefore (gridCO p) rho index reader) t)
                  dsimp only [receiptData] at hd
                  simp only [World.step, Function.update_self] at hm
                  change (o, stamp) ∈ (clock p _ t).voteStamp at hm
                  simpa only [hd] using hm
                · simpa [World.step, hv] using hm
              obtain ⟨j, hj, rest⟩ := ih hm'
              exact ⟨j, by omega, rest⟩
          | deliver v parent t =>
              by_cases hv : reader = v
              · subst v
                have hm' : (o, stamp) ∈
                    (process p (Run.stateBefore (gridCO p) rho index reader) parent).voteStamp := by
                  simpa [World.step] using! hm
                rcases process_vote_stamp_origin p _ parent o stamp hm' with
                  hold | ⟨ht, hn, hh, B, hb⟩
                · obtain ⟨j, hj, rest⟩ := ih hold
                  exact ⟨j, by omega, rest⟩
                · refine ⟨index, by omega, t, ⟨⟨parent, hi, hh⟩, ?_, ?_⟩, ht⟩
                  · simpa [gridCO, processed, hb] using hn
                  · have hstored := run_vote_stamps_stored p rho (index + 1) reader o stamp
                      (by rw [hpost]; exact hm)
                    simpa [gridCO, processed, hb] using hstored
              · obtain ⟨j, hj, rest⟩ := ih (by simpa [World.step, hv] using hm)
                exact ⟨j, by omega, rest⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A stored HEAD's selected first stamp is an actual receipt row. -/
theorem stampVote_mem_of_stored {n : Nat} (st : State n) (hs : ReceiptStamped st)
    (o : Wire n) (hm : o ∈ st.votes) : (o, stampVote st o) ∈ st.voteStamp := by
  obtain ⟨t, ht⟩ := hs.2 o hm
  unfold stampVote
  cases hf : st.voteStamp.find? (fun row => row.1 == o) with
  | none => have h := List.find?_eq_none.mp hf (o, t) ht; simp at h
  | some row =>
      have he : row.1 = o := by simpa using List.find?_some hf
      have hh := List.mem_of_find?_eq_some hf
      rw [← he]
      exact hh

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A stamp below a public cutoff proves an acceptance strictly before
that cutoff. The scheduled local tick excludes a late receipt with an
old stamp, including at a sleeping reader. -/
theorem stored_head_accepted_before {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (index : Nat) (reader : V) (o : Wire p.n) (cut : Time)
    (hpub : PublicTime E cut) (hzero : 0 ≤ cut)
    (hm : o ∈ (Run.stateBefore (gridCO p) rho index reader).votes)
    (ht : stampVote (Run.stateBefore (gridCO p) rho index reader) o < cut) :
    ∃ j < index, ∃ t, Run.acceptsAt (gridCO p) rho j reader o t ∧ t < cut := by
  obtain ⟨j, hj, t, ha, he⟩ := stored_head_stamp_source p rho index reader o _
    (stampVote_mem_of_stored _ (run_receiptStamped p rho index reader) o hm)
  refine ⟨j, hj, t, ha, ?_⟩
  by_contra hn
  obtain ⟨parent, hp, _⟩ := ha.1
  have hb := delivery_now_ge_public p E rho hs hp hpub hzero (le_of_not_gt hn)
  rw [he] at ht
  exact (not_lt.mpr hb) ht

private theorem fold_vote_blockStamp (p : Params) {n : Nat} (raw : List (HeadWire n))
    (st : State n) :
    (raw.foldl (fun acc row => admitVote p acc (fromHead row)) st).blockStamp =
      st.blockStamp := by
  induction raw generalizing st with
  | nil => rfl
  | cons row raw ih =>
      rw [List.foldl_cons, ih]
      unfold admitVote
      split
      · dsimp only; split <;> rfl
      · rfl

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A new block stamp is the stamp of the directly admitted proposal. -/
theorem process_block_stamp_origin (p : Params) {n : Nat} (st : State n)
    (o : Wire n) (B : Block) (t : Time) (hm : (B, t) ∈ (process p st o).blockStamp) :
    (B, t) ∈ st.blockStamp ∨
      t = st.now ∧ B ∉ st.blocks ∧ B ∈ (process p st o).blocks ∧
        ∃ raw support, o.payload = .proposal B raw support := by
  unfold process at hm
  split at hm
  · unfold admitVote at hm
    split at hm
    · dsimp only at hm; split at hm <;> exact Or.inl hm
    · exact Or.inl hm
  · rename_i s target raw support ha hp
    unfold admitProposal at hm
    simp only [ha] at hm
    split at hm
    · exact Or.inl hm
    · rename_i hgood
      rw [fold_vote_blockStamp] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact Or.inl hm
      · have he : B = target ∧ t = st.now := by simpa using hm
        obtain ⟨rfl, rfl⟩ := he
        refine Or.inr ⟨rfl, ?_, ?_, raw, support, hp⟩
        · intro hold; simp [hold] at hgood
        · simp only [process, ha, hp, admitProposal, hgood, Bool.false_eq_true, ite_false]
          rw [fold_vote_blocks]
          simp
  · exact Or.inl hm

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Every stored non-genesis block stamp comes from an earlier accepted
proposal, with the exact source clock preserved in the stamp. -/
theorem stored_block_stamp_source {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (index : Nat) (reader : V) (B : Block) (stamp : Time)
    (hn : B ≠ .genesis)
    (hm : (B, stamp) ∈ (Run.stateBefore (gridCO p) rho index reader).blockStamp) :
    ∃ j < index, ∃ t o raw support,
      o.payload = .proposal B raw support ∧
      Run.acceptsAt (gridCO p) rho j reader o t ∧
      stamp = (Run.stateBefore (gridCO p) rho j reader).now := by
  induction index with
  | zero => simp [Run.stateBefore, World.init, gridCO, initial, hn] at hm
  | succ index ih =>
      cases hi : rho.events[index]? with
      | none =>
          obtain ⟨j, hj, rest⟩ := ih (by
            simpa [Run.stateBefore, List.take_add_one, hi] using hm)
          exact ⟨j, by omega, rest⟩
      | some e =>
          have hpost := stateBefore_succ_event hi
          rw [hpost] at hm
          cases e with
          | tick v t =>
              have hm' : (B, stamp) ∈
                  (Run.stateBefore (gridCO p) rho index reader).blockStamp := by
                by_cases hv : reader = v
                · subst v
                  have hd := congrArg (fun x => x.2.1)
                    (clock_receiptData p (Run.stateBefore (gridCO p) rho index reader) t)
                  dsimp only [receiptData] at hd
                  simp only [World.step, Function.update_self] at hm
                  change (B, stamp) ∈ (clock p _ t).blockStamp at hm
                  simpa only [hd] using hm
                · simpa [World.step, hv] using hm
              obtain ⟨j, hj, rest⟩ := ih hm'
              exact ⟨j, by omega, rest⟩
          | deliver v o t =>
              by_cases hv : reader = v
              · subst v
                have hm' : (B, stamp) ∈
                    (process p (Run.stateBefore (gridCO p) rho index reader) o).blockStamp := by
                  simpa [World.step] using! hm
                rcases process_block_stamp_origin p _ o B stamp hm' with
                  hold | ⟨ht, habsent, hstored, raw, support, hb⟩
                · obtain ⟨j, hj, rest⟩ := ih hold
                  exact ⟨j, by omega, rest⟩
                · refine ⟨index, by omega, t, o, raw, support, hb,
                    ⟨⟨o, hi, Or.inl rfl⟩, ?_, ?_⟩, ht⟩
                  · simpa [gridCO, processed, hb, blockKnown] using habsent
                  · rw [hpost]
                    simpa [World.step, gridCO, processed, hb, blockKnown] using hstored
              · obtain ⟨j, hj, rest⟩ := ih (by simpa [World.step, hv] using hm)
                exact ⟨j, by omega, rest⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A stored block's selected first stamp is an actual receipt row. -/
theorem stampBlock_mem_of_stored {n : Nat} (st : State n) (hs : ReceiptStamped st)
    (B : Block) (hm : B ∈ st.blocks) : (B, stampBlock st B) ∈ st.blockStamp := by
  obtain ⟨t, ht⟩ := hs.1 B hm
  unfold stampBlock
  cases hf : st.blockStamp.find? (fun row => row.1 == B) with
  | none => have h := List.find?_eq_none.mp hf (B, t) ht; simp at h
  | some row =>
      have he : row.1 = B := by simpa using List.find?_some hf
      have hh := List.mem_of_find?_eq_some hf
      rw [← he]
      exact hh

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
An early block stamp gives an accepted proposal strictly before the
public cutoff. This applies separately to every block in a resolved path. -/
theorem stored_block_accepted_before {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (index : Nat) (reader : V) (B : Block) (cut : Time)
    (hn : B ≠ .genesis) (hpub : PublicTime E cut) (hzero : 0 ≤ cut)
    (hm : B ∈ (Run.stateBefore (gridCO p) rho index reader).blocks)
    (ht : stampBlock (Run.stateBefore (gridCO p) rho index reader) B < cut) :
    ∃ j < index, ∃ t o raw support,
      o.payload = .proposal B raw support ∧
      Run.acceptsAt (gridCO p) rho j reader o t ∧ t < cut := by
  obtain ⟨j, hj, t, o, raw, support, hp, ha, he⟩ :=
    stored_block_stamp_source p rho index reader B _ hn
      (stampBlock_mem_of_stored _ (run_receiptStamped p rho index reader) B hm)
  refine ⟨j, hj, t, o, raw, support, hp, ha, ?_⟩
  by_contra hh
  obtain ⟨parent, hd, _⟩ := ha.1
  have hb := delivery_now_ge_public p E rho hs hd hpub hzero (le_of_not_gt hh)
  rw [he] at ht
  exact (not_lt.mpr hb) ht

end AvailableChain.GridCO
end
