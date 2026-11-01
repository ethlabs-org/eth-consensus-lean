module
public import AvailableChainGridCO.Proofs.Receipts

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

private theorem fold_votes_blocks (p : Params) {n : Nat} (raw : List (HeadWire n))
    (st : State n) :
    (raw.foldl (fun acc row => admitVote p acc (fromHead row)) st).blocks = st.blocks := by
  induction raw generalizing st with
  | nil => rfl
  | cons row raw ih => rw [List.foldl_cons, ih, admitVote_blocks]

-- ROOT-DIGEST-2 option 3: keep the statement matcher in a private helper.
private theorem resolvedBefore_block_local {n : Nat} (st : State n) (o : Wire n)
    (cutoff : Time) :
    resolvedBefore st o cutoff = (match headTarget? o with
      | none => false
      | some B => blockKnown st B && B.slot ≤ (headLabel? o).getD 0 &&
          stampVote st o < cutoff && stampBlock st B < cutoff) :=
  resolvedBefore_block st o cutoff

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A new stored block is the block of the directly delivered proposal. -/
theorem process_new_block (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (B : Block) (hn : B ∉ st.blocks) (hm : B ∈ (process p st o).blocks) :
    ∃ raw support, o.payload = .proposal B raw support := by
  unfold process at hm
  split at hm
  · exact (hn (by simpa [admitVote_blocks] using hm)).elim
  · rename_i slot target raw support ha hp
    unfold admitProposal at hm
    dsimp only at hm
    split at hm <;> split at hm
    all_goals first
      | exact (hn hm).elim
      | rw [fold_votes_blocks] at hm
        have he : B = target := by simpa [hn] using hm
        exact ⟨raw, support, by simpa [he] using hp⟩
  · exact (hn hm).elim

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Admission rejects a new block whose slot is ahead of the local clock. -/
theorem process_new_block_slot (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (B : Block) (hn : B ∉ st.blocks) (hm : B ∈ (process p st o).blocks) :
    B.slot ≤ (st.now / (4 * p.Δ)).toNat := by
  unfold process at hm
  split at hm
  · exact (hn (by simpa [admitVote_blocks] using hm)).elim
  · rename_i slot target raw support ha hp
    unfold admitProposal at hm
    dsimp only at hm
    split at hm <;> split at hm
    all_goals first
      | exact (hn hm).elim
      | rename_i hgood
        rw [fold_votes_blocks] at hm
        have he : B = target := by simpa [hn] using hm
        rw [he]
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, not_or,
          Bool.not_eq_false, decide_eq_false_iff_not] at hgood
        have hb : ¬ target.slot > (st.now / (4 * p.Δ)).toNat := by tauto
        exact le_of_not_gt hb
  · exact (hn hm).elim

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Every non-genesis stored block has an earlier accepted proposal at
that reader. This is the path source needed by accepted-object relay. -/
theorem stored_block_accepted {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (index : Nat) (reader : V) (B : Block)
    (hn : B ≠ .genesis)
    (hm : B ∈ (Run.stateBefore (gridCO p) rho index reader).blocks) :
    ∃ j < index, ∃ t o raw support,
      rho.events[j]? = some (.deliver reader o t) ∧
      o.payload = .proposal B raw support ∧
      Run.acceptsAt (gridCO p) rho j reader o t := by
  induction index with
  | zero => simp [Run.stateBefore, World.init, gridCO, initial, hn] at hm
  | succ index ih =>
      by_cases hold : B ∈ (Run.stateBefore (gridCO p) rho index reader).blocks
      · obtain ⟨j, hj, rest⟩ := ih hold
        exact ⟨j, by omega, rest⟩
      · cases hi : rho.events[index]? with
        | none => simp [Run.stateBefore, List.take_add_one, hi] at hm; exact (hold hm).elim
        | some e =>
            have hpost := stateBefore_succ_event hi
            rw [hpost] at hm
            cases e with
            | tick v t =>
                by_cases hv : reader = v
                · subst v
                  have he := congrArg Prod.fst
                    (clock_receiptData p (Run.stateBefore (gridCO p) rho index reader) t)
                  have hm' : B ∈
                      (clock p (Run.stateBefore (gridCO p) rho index reader) t).blocks := by
                    simpa only [World.step, Function.update_self] using! hm
                  simp only [receiptData] at he
                  rw [he] at hm'
                  exact (hold hm').elim
                · exact (hold (by simpa [World.step, hv] using hm)).elim
            | deliver v o t =>
                by_cases hv : reader = v
                · subst v
                  have hnew : B ∈
                      (process p (Run.stateBefore (gridCO p) rho index reader) o).blocks := by
                    simpa [World.step] using! hm
                  obtain ⟨raw, support, hp⟩ := process_new_block p _ o B hold hnew
                  refine ⟨index, by omega, t, o, raw, support, hi, hp, ?_⟩
                  refine ⟨⟨o, hi, Or.inl rfl⟩, ?_, ?_⟩
                  · simpa [gridCO, processed, hp, blockKnown] using hold
                  · rw [hpost]
                    simpa [World.step, gridCO, processed, hp, blockKnown] using hnew
                · exact (hold (by simpa [World.step, hv] using hm)).elim

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The stored path before a HEAD cannot contain a future-slot block. -/
theorem stored_before_head_slot_le {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (reader : V) (B : Block)
    (hm : B ∈ (Run.stateBeforeTime (gridCO p) rho (voteTime p r) reader).blocks) :
    B.slot ≤ r := by
  by_cases hg : B = .genesis
  · simp [hg, Block.slot]
  rw [time_input_eq_event_prefix p E rho hs] at hm
  obtain ⟨i, hil, t, o, raw, support, hi, hp, ha⟩ :=
    stored_block_accepted p rho _ reader B hg hm
  have ht : t < voteTime p r :=
    Int.le_sub_one_iff.mp ((index_lt_read_length_iff hs (voteTime p r - 1) hi).mp hil)
  have hn : B ∉ (Run.stateBefore (gridCO p) rho i reader).blocks := by
    simpa [gridCO, processed, hp, blockKnown] using ha.2.1
  have hb : B ∈ (process p (Run.stateBefore (gridCO p) rho i reader) o).blocks := by
    have h := ha.2.2
    rw [stateBefore_succ_event hi] at h
    simpa [World.step, gridCO, processed, hp, blockKnown] using h
  apply (process_new_block_slot p _ o B hn hb).trans
  apply Int.toNat_le.mpr
  apply (Int.ediv_le_iff_le_mul (by linarith [p.deltaPos])).mpr
  have hnow := (stateBefore_now_le_event p E rho hs hi reader).trans_lt ht
  dsimp [voteTime, proposalTime] at hnow
  nlinarith [p.deltaPos]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Every reader's clock is at most the time of a completed event. -/
theorem stateAfter_now_le_event {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    {i : Nat} {e : Event V (gridCO p).Object}
    (hi : rho.events[i]? = some e) (reader : V) :
    (Run.stateBefore (gridCO p) rho (i + 1) reader).now ≤ e.time := by
  set_option backward.isDefEq.respectTransparency false in
  have h := stateBefore_now_le_event p E rho hs hi reader
  rw [stateBefore_succ_event hi]
  cases e with
  | tick v t =>
      by_cases hv : reader = v
      · subst v; simp [World.step, gridCO, clock_now, Event.time]
      · simpa [World.step, hv] using! h
  | deliver v o t =>
      by_cases hv : reader = v
      · subst v; simpa [World.step, gridCO, process_now] using! h
      · simpa [World.step, hv] using h

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A block already stored after an event before the cutoff retains an
early block stamp at each later strict read. The event can be at any node. -/
theorem stored_block_stamp_before_cut {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    {i : Nat} {e : Event V (gridCO p).Object} {reader : V} {B : Block}
    {early cut : Time} (hi : rho.events[i]? = some e)
    (hm : B ∈ (Run.stateBefore (gridCO p) rho (i + 1) reader).blocks)
    (ht : e.time < early) (hcut : early ≤ cut) :
    B ∈ (Run.stateBeforeTime (gridCO p) rho cut reader).blocks ∧
      stampBlock (Run.stateBeforeTime (gridCO p) rho cut reader) B < early := by
  have hp : ReceiptPrefix (Run.stateBefore (gridCO p) rho (i + 1) reader)
      (Run.stateBeforeTime (gridCO p) rho cut reader) := by
    rw [time_input_eq_event_prefix p E rho hs]
    apply stateBefore_receiptPrefix
    exact Nat.succ_le_of_lt ((index_lt_read_length_iff hs (cut - 1) hi).mpr
      (Int.le_sub_one_iff.mpr (ht.trans_le hcut)))
  refine ⟨hp.blocks.subset hm, ?_⟩
  rw [hp.stampBlock (run_receiptStamped p rho (i + 1) reader) B hm]
  exact ((run_stampsBounded p E rho hs (i + 1) reader).stampBlock_le B).trans_lt
    ((stateAfter_now_le_event p E rho hs hi reader).trans_lt ht)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Genesis is always stored with its original zero stamp. -/
theorem genesis_stored_at_time {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (cut : Time) (reader : V) :
    Block.genesis ∈ (Run.stateBeforeTime (gridCO p) rho cut reader).blocks ∧
      stampBlock (Run.stateBeforeTime (gridCO p) rho cut reader) .genesis = 0 := by
  rw [time_input_eq_event_prefix p E rho hs]
  have hp := stateBefore_receiptPrefix p rho (Nat.zero_le
    (rho.events.filter (fun e => decide (e.time ≤ cut - 1))).length) reader
  have hm : Block.genesis ∈ (Run.stateBefore (gridCO p) rho 0 reader).blocks := by
    simp [Run.stateBefore, World.init, gridCO, initial]
  exact ⟨hp.blocks.subset hm, (hp.stampBlock (run_receiptStamped p rho 0 reader) _ hm)⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A dependency-ready proposal call stores its block once its slot is public. -/
theorem handled_proposal_stored {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hx : ExecutionValid (gridCO p) E rho) (hΔ : E.Δ = p.Δ)
    (j : Nat) (v : V) (o : Wire p.n) (B : Block)
    (raw support : List (HeadWire p.n)) (t : Time)
    (hp : o.payload = .proposal B raw support)
    (hh : Run.handlesAt (gridCO p) rho j v o t)
    (hlo : proposalTime p B.slot ≤ t) :
    B ∈ (Run.stateBefore (gridCO p) rho (j + 1) v).blocks := by
  obtain ⟨parent, hj, hh⟩ := hh
  have he := handles_proposal_direct p _ parent o B raw support hp hh
  subst parent
  have hw := hx.wire j v o t hj
  have hd := hx.deps j v o t hj
  have hf := hx.fresh j v o t hj
  have ha : o.auth = .proposer B.slot := by
    cases ha : o.auth <;> simp only [gridCO, wellFormed, ha, hp] at hw
    all_goals first
      | contradiction
      | simp only [Bool.and_eq_true, beq_iff_eq] at hw
        rw [hw.1.1.1.1]
  have hw' := hw
  simp only [gridCO, wellFormed, ha, hp, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at hw'
  have hparent : B.parent.slot < B.slot := hw'.1.1.2
  have hpub : PublicTime E (proposalTime p B.slot) := by
    refine ⟨4 * B.slot, ?_⟩
    simp only [proposalTime, hΔ, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hz : 0 ≤ proposalTime p B.slot := by
    unfold proposalTime
    exact mul_nonneg (by linarith [p.deltaPos]) (Int.natCast_nonneg _)
  have hnow := delivery_now_ge_public p E rho hx.toScheduleWellFormed hj hpub hz hlo
  have hslot : B.slot ≤ ((Run.stateBefore (gridCO p) rho j v).now / (4 * p.Δ)).toNat := by
    have hdiv : (B.slot : Int) ≤ (Run.stateBefore (gridCO p) rho j v).now / (4 * p.Δ) := by
      apply (Int.le_ediv_iff_mul_le (by linarith [p.deltaPos])).mpr
      simpa [proposalTime, mul_comm] using hnow
    exact (Int.le_toNat (by omega)).mpr hdiv
  have hdep : B.parent ∈ (Run.stateBefore (gridCO p) rho j v).blocks := by
    simpa [gridCO, depsPresent, hp, blockKnown] using hd
  have hnew : B ∉ (Run.stateBefore (gridCO p) rho j v).blocks := by
    simpa [gridCO, processed, hp, blockKnown] using hf
  rw [stateBefore_succ_event hj]
  simp only [World.step, Function.update_self]
  change B ∈ (process p _ o).blocks
  simp only [process, ha, hp, admitProposal, not_lt.mpr hslot, decide_false,
    blockKnown, hdep, decide_true, Bool.not_true, hnew, hparent, beq_self_eq_true,
    Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  rw [fold_votes_blocks]
  simp

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Source acceptance and the public schedule exclude a future block at
any later checked handler call. There is no lower block admission window. -/
theorem accepted_proposal_handled_stored {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hx : ExecutionValid (gridCO p) E rho) (hΔ : E.Δ = p.Δ)
    (i j : Nat) (source reader : V) (o : Wire p.n) (B : Block)
    (raw support : List (HeadWire p.n)) (t t' : Time)
    (hp : o.payload = .proposal B raw support)
    (ha : Run.acceptsAt (gridCO p) rho i source o t)
    (hh : Run.handlesAt (gridCO p) rho j reader o t') (htt : t ≤ t') :
    B ∈ (Run.stateBefore (gridCO p) rho (j + 1) reader).blocks := by
  obtain ⟨parent, hi, hhandle⟩ := ha.1
  have he := handles_proposal_direct p _ parent o B raw support hp hhandle
  subst parent
  have hn : B ∉ (Run.stateBefore (gridCO p) rho i source).blocks := by
    simpa [gridCO, processed, hp, blockKnown] using ha.2.1
  have hm : B ∈ (process p (Run.stateBefore (gridCO p) rho i source) o).blocks := by
    have h := ha.2.2
    rw [stateBefore_succ_event hi] at h
    simpa [World.step, gridCO, processed, hp, blockKnown] using h
  have hslot := process_new_block_slot p _ o B hn hm
  have hw := hx.wire i source o t hi
  have hpos : 0 < B.slot := by
    cases h_auth : o.auth <;> simp only [gridCO, wellFormed, h_auth, hp] at hw
    all_goals first
      | contradiction
      | simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
        have he : _ = B.slot := hw.1.1.1.1
        have hlt := hw.1.1.2
        rw [he] at hlt
        exact Nat.zero_lt_of_lt hlt
  have hdiv : (B.slot : Int) ≤ (Run.stateBefore (gridCO p) rho i source).now / (4 * p.Δ) := by
    have hn : 0 ≤ (Run.stateBefore (gridCO p) rho i source).now / (4 * p.Δ) := by
      by_contra hneg
      have hz := Int.toNat_eq_zero.mpr (le_of_lt (lt_of_not_ge hneg))
      have hzero : B.slot ≤ 0 := hslot.trans_eq hz
      exact (Nat.not_lt_of_ge hzero) hpos
    exact (Int.le_toNat hn).mp hslot
  have htime := (Int.le_ediv_iff_mul_le (by linarith [p.deltaPos])).mp hdiv
  have hnow := stateBefore_now_le_event p E rho hx.toScheduleWellFormed hi source
  apply handled_proposal_stored p E rho hx hΔ j reader o B raw support t' hp hh
  dsimp [proposalTime]
  change (Run.stateBefore (gridCO p) rho i source).now ≤ t at hnow
  nlinarith

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Any path block stored before the HEAD time relays before the early
cutoff of a synchronous label. Both delivery regimes use receipt relay. -/
theorem synchronous_block_path_at_gate {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : EarlyDelivery p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (B : Block) (hm : B ∈ (Run.stateBeforeTime (gridCO p) rho (voteTime p r) source).blocks)
    (hx : ∀ o : Wire p.n, (∃ raw support, o.payload = .proposal B raw support) →
      ∀ u, u ≤ earlyTime p r →
        (gridCO p).excludes (Run.stateBeforeTime (gridCO p) rho u reader) o = false) :
    B ∈ (gateInput p rho r reader).blocks ∧
      stampBlock (gateInput p rho r reader) B < earlyTime p r := by
  have hsched := hsync.execution.toScheduleWellFormed
  have hearly : earlyTime p r ≤ gateTime p r := by
    dsimp [earlyTime, gateTime]; linarith [p.deltaPos]
  by_cases hg : B = .genesis
  · subst B
    obtain ⟨hm, ht⟩ := genesis_stored_at_time p E rho hsched (gateTime p r) reader
    refine ⟨hm, ?_⟩
    change stampBlock (Run.stateBeforeTime (gridCO p) rho (gateTime p r) reader) .genesis < _
    rw [ht]
    have hnat := Int.natCast_nonneg r
    dsimp [earlyTime, proposalTime]
    nlinarith [p.deltaPos]
  rw [time_input_eq_event_prefix p E rho hsched] at hm
  obtain ⟨index, hindex, t, o, raw, support, hi, hp, ha⟩ :=
    stored_block_accepted p rho _ source B hg hm
  have ht : t < voteTime p r := by
    have h := (index_lt_read_length_iff hsched (voteTime p r - 1) hi).mp hindex
    exact Int.le_sub_one_iff.mp h
  by_cases hknown : processed (Run.stateBefore (gridCO p) rho (index + 1) reader) o = true
  · have hm : B ∈ (Run.stateBefore (gridCO p) rho (index + 1) reader).blocks := by
      simpa [processed, hp, blockKnown] using hknown
    exact stored_block_stamp_before_cut p E rho hsched hi hm
      (ht.trans (by dsimp [voteTime, earlyTime]; linarith [p.deltaPos])) hearly
  have hmissing : processed (Run.stateBefore (gridCO p) rho (index + 1) reader) o = false :=
    Bool.eq_false_iff.mpr hknown
  have hdeadline : t + E.Δ ≤ earlyTime p r := by
    rw [hΔ]
    dsimp [voteTime, earlyTime] at ht ⊢
    linarith
  have hrelay : ∃ j t', Run.handlesAt (gridCO p) rho j reader o t' ∧ t ≤ t' ∧
      t' < earlyTime p r := by
    rcases hsync.delivery with ⟨hgst, relay⟩ | ⟨cut, hcut, relay⟩
    · have hd : max t E.t_GST + E.Δ ≤ earlyTime p r := by
        rw [← max_add_add_right]
        refine max_le hdeadline ?_
        rw [hΔ]
        dsimp [earlyTime]
        linarith [p.deltaPos]
      obtain ⟨t', htt, ht', j, hj⟩ := relay.relay source hs index o t ha reader hr hmissing
        (hd.trans hsync.horizon) (hx o ⟨raw, support, hp⟩ _ hd)
      exact ⟨j, t', hj, htt, ht'.trans_le hd⟩
    · obtain ⟨t', htt, ht', j, hj⟩ := relay.relay source hs index o t ha reader hr hmissing
        (hdeadline.trans hcut) (hx o ⟨raw, support, hp⟩ _ hdeadline)
      exact ⟨j, t', hj, htt, ht'.trans_le hdeadline⟩
  obtain ⟨j, t', hh, htt, ht'⟩ := hrelay
  have hm := accepted_proposal_handled_stored p E rho hsync.execution hΔ
    index j source reader o B raw support t t' hp ha hh htt
  obtain ⟨parent, hj, _⟩ := hh
  exact stored_block_stamp_before_cut p E rho hsched hj hm ht' hearly

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Early HEAD receipt and early target-path relay together give a resolved
honest HEAD at the gate. The caller supplies the target of the honest walk. -/
theorem synchronous_honest_head_resolved {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : EarlyDelivery p E rho r)
    (i : Fin p.n) (B : Block) (hh : rho.seatOf r i ∈ rho.honest)
    (he : Run.emits (gridCO p) E rho (rho.seatOf r i)
      ⟨.seat r i, .head B⟩ (voteTime p r))
    (hm : B ∈ (Run.stateBeforeTime (gridCO p) rho (voteTime p r) (rho.seatOf r i)).blocks)
    (hslot : B.slot ≤ r) (reader : V) (hr : reader ∈ rho.honest) :
    (⟨.seat r i, .head B⟩ : Wire p.n) ∈ earlyVotes p (gateInput p rho r reader) r := by
  obtain ⟨hv, hstamp⟩ := synchronous_honest_head_at_gate p E rho hΔ r hsync i B hh he reader hr
  obtain ⟨hb, hbstamp⟩ := synchronous_block_path_at_gate p E rho hΔ r hsync
    (rho.seatOf r i) reader hh hr B hm
    (fun o ⟨raw, support, hp⟩ u _ => proposal_not_excluded p rho reader o B raw support hp u)
  simp [earlyVotes, votesAt, hv, headLabel?, resolvedBefore_block_local, headTarget?, blockKnown,
    hb, hslot, hstamp, hbstamp]

end AvailableChain.GridCO
end
