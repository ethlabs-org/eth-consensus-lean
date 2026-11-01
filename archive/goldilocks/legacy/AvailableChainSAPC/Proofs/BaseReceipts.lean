module
public import AvailableChainSAPC.Proofs.ClockBounds
public import AvailableChainSAPC.Proofs.Paths
public import AvailableChainGridCO.Proofs.Receipts

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- The base cache uses the shared receipt invariant, including carried
HEADs and PC envelopes. No projection of a complete run is assumed. -/
theorem base_receiptStamped_at_fold {V : Type} [DecidableEq V] (p : Params)
    (events : List (Event V (sapc p).Object)) (v : V) :
    GridCO.ReceiptStamped ((events.foldl World.step World.init) v).base := by
  apply fold_invariant p (fun st => GridCO.ReceiptStamped st.base)
  · exact GridCO.initial_stamped p.n
  · intro st t h
    exact GridCO.stamped_of_data_eq (clock_receiptData p st t) h
  · exact process_base_invariant p GridCO.ReceiptStamped
      (GridCO.admitVote_stamped p.engine)
      (fun st o b => GridCO.admitProposal_stamped p.engine st o b [])

theorem process_base_receiptPrefix (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    GridCO.ReceiptPrefix st.base (process p st o).base := by
  apply process_base_invariant p (GridCO.ReceiptPrefix st.base)
  · intro acc head h
    exact h.trans (GridCO.admitVote_receiptPrefix p.engine acc head)
  · intro acc proposal b h
    exact h.trans (GridCO.admitProposal_receiptPrefix p.engine acc proposal b [])
  · exact .refl _

/-- Base receipts and both first-stamp lists grow by append. -/
theorem stateBefore_base_receiptPrefix {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (sapc p)) {i j : Nat} (hij : i ≤ j) (v : V) :
    GridCO.ReceiptPrefix (Run.stateBefore (sapc p) rho i v).base
      (Run.stateBefore (sapc p) rho j v).base := by
  have hc (st : State p.n) (t : Time) :
      GridCO.ReceiptPrefix st.base (clock p st t).base :=
    GridCO.receiptPrefix_of_data_eq (clock_receiptData p st t)
  constructor
  · exact stateBefore_field_prefix (P := sapc p) (fun st => st.base.blocks)
      (fun st t => (hc st t).blocks)
      (fun st o => (process_base_receiptPrefix p st o).blocks) rho hij v
  · exact stateBefore_field_prefix (P := sapc p) (fun st => st.base.blockStamp)
      (fun st t => (hc st t).blockStamp)
      (fun st o => (process_base_receiptPrefix p st o).blockStamp) rho hij v
  · exact stateBefore_field_prefix (P := sapc p) (fun st => st.base.votes)
      (fun st t => (hc st t).votes)
      (fun st o => (process_base_receiptPrefix p st o).votes) rho hij v
  · exact stateBefore_field_prefix (P := sapc p) (fun st => st.base.voteStamp)
      (fun st t => (hc st t).voteStamp)
      (fun st o => (process_base_receiptPrefix p st o).voteStamp) rho hij v

theorem base_stampsBounded_before {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho) (i : Nat) (v : V) :
    GridCO.StampsBounded (Run.stateBefore (sapc p) rho i v).base := by
  set_option backward.isDefEq.respectTransparency false in
  apply stateBefore_invariant (engineClock p) E rho hs (fun st => GridCO.StampsBounded st.base)
  · simp [sapc, initial, GridCO.initial, GridCO.StampsBounded]
  · intro st t ht h
    have he := clock_receiptData p st t
    have hb := congrArg (fun data => data.2.1) he
    have hv := congrArg (fun data => data.2.2.2) he
    change (clock p st t).base.blockStamp = st.base.blockStamp at hb
    change (clock p st t).base.voteStamp = st.base.voteStamp at hv
    change GridCO.StampsBounded (clock p st t).base
    simp only [GridCO.StampsBounded, hb, hv, clock_now]
    exact ⟨fun row hr => (h.1 row hr).trans ht, fun row hr => (h.2 row hr).trans ht⟩
  · exact process_base_invariant p GridCO.StampsBounded
      (GridCO.admitVote_stampsBounded p.engine)
      (fun st o b => GridCO.admitProposal_stampsBounded p.engine st o b [])

theorem delivery_base_prefix_before_cut {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    {i : Nat} {v : V} {o : Wire p.n} {t cut : Time}
    (hi : rho.events[i]? = some (.deliver v o t)) (ht : t < cut) :
    GridCO.ReceiptPrefix (Run.stateBefore (sapc p) rho (i + 1) v).base
      (Run.stateBeforeTime (sapc p) rho cut v).base := by
  rw [time_input_eq_event_prefix p E rho hs]
  exact stateBefore_base_receiptPrefix p rho
    (Nat.succ_le_of_lt ((index_lt_read_length_iff hs (cut - 1) hi).mpr
      (Int.le_sub_one_iff.mpr ht))) v

theorem stored_base_head_stamp_before_cut {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    {i : Nat} {reader : V} {parent : Wire p.n} {o : GridCO.Wire p.n} {t early cut : Time}
    (hi : rho.events[i]? = some (.deliver reader parent t))
    (hm : o ∈ (Run.stateBefore (sapc p) rho (i + 1) reader).base.votes)
    (ht : t < early) (hcut : early ≤ cut) :
    o ∈ (Run.stateBeforeTime (sapc p) rho cut reader).base.votes ∧
      GridCO.stampVote (Run.stateBeforeTime (sapc p) rho cut reader).base o < early := by
  have hp := delivery_base_prefix_before_cut p E rho hs hi (ht.trans_le hcut)
  refine ⟨hp.votes.subset hm, ?_⟩
  rw [hp.stampVote (base_receiptStamped_at_fold p _ reader) o hm]
  have hb := (base_stampsBounded_before p E rho hs (i + 1) reader).stampVote_le o
  have hn : (Run.stateBefore (sapc p) rho (i + 1) reader).base.now ≤ t := by
    rw [stateBefore_succ_event hi]
    simpa [World.step, sapc, process_now] using! stateBefore_now_le_event p E rho hs hi reader
  exact (hb.trans hn).trans_lt ht

/-- Complete admitted paths inherit a bound on all base stamps. -/
theorem pathBefore_of_pathKnown {n : Nat} (st : State n) (cut : Time)
    (hbound : GridCO.StampsBounded st.base) (ht : st.base.now < cut)
    (b : Block) (hb : pathKnown st b = true) : pathBefore st cut b = true := by
  induction b with
  | genesis =>
      exact Bool.and_eq_true_iff.mpr
        ⟨hb, by simpa using (hbound.stampBlock_le _).trans_lt ht⟩
  | node parent s r_s root ih =>
      have hp := Bool.and_eq_true_iff.mp hb
      exact Bool.and_eq_true_iff.mpr
        ⟨Bool.and_eq_true_iff.mpr ⟨hp.1, by simpa using (hbound.stampBlock_le _).trans_lt ht⟩,
          ih hp.2⟩

/-- Once a path meets a cutoff, later clock changes and receipts cannot
change that fact. Each block has a stored first stamp. -/
theorem pathBefore_mono {n : Nat} (before after : State n)
    (hp : GridCO.ReceiptPrefix before.base after.base)
    (hs : GridCO.ReceiptStamped before.base) (cut : Time) (b : Block)
    (hb : pathBefore before cut b = true) : pathBefore after cut b = true := by
  have hblock (b : Block) (hk : GridCO.blockKnown before.base b = true)
      (ht : GridCO.stampBlock before.base b < cut) :
      GridCO.blockKnown after.base b = true ∧ GridCO.stampBlock after.base b < cut := by
    have hm : b ∈ before.base.blocks := by simpa [GridCO.blockKnown] using hk
    exact ⟨by simpa [GridCO.blockKnown] using hp.blocks.subset hm,
      by rwa [hp.stampBlock hs b hm]⟩
  induction b with
  | genesis =>
      simpa only [pathBefore, Bool.and_eq_true_iff, decide_eq_true_eq] using
        hblock .genesis (Bool.and_eq_true_iff.mp hb).1
          (by simpa using (Bool.and_eq_true_iff.mp hb).2)
  | node parent s r_s root ih =>
      simp only [pathBefore, Bool.and_eq_true_iff, decide_eq_true_eq] at hb ⊢
      exact ⟨hblock _ hb.1.1 hb.1.2, ih hb.2⟩

/-- A stored tip supplies its whole path before the delivery deadline,
including dependencies admitted at earlier events. -/
theorem stored_path_before_cut {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    {i : Nat} {v : V} {o : Wire p.n} {b : Block} {t early cut : Time}
    (hi : rho.events[i]? = some (.deliver v o t))
    (hm : b ∈ (Run.stateBefore (sapc p) rho (i + 1) v).base.blocks)
    (ht : t < early) (hcut : early ≤ cut) :
    pathBefore (Run.stateBeforeTime (sapc p) rho cut v) early b = true := by
  apply pathBefore_mono _ _ (delivery_base_prefix_before_cut p E rho hs hi (ht.trans_le hcut))
    (base_receiptStamped_at_fold p _ v)
  apply pathBefore_of_pathKnown _ early (base_stampsBounded_before p E rho hs (i + 1) v)
    _ b (stored_pathKnown_at_fold p _ v b hm)
  have hn : (Run.stateBefore (sapc p) rho (i + 1) v).base.now ≤ t := by
    rw [stateBefore_succ_event hi]
    simpa [World.step, sapc, process_now] using! stateBefore_now_le_event p E rho hs hi v
  exact hn.trans_lt ht

theorem accepted_path_before_cut {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (index : Nat) (v : V) (o : Wire p.n) (b : Block) (raw support : List (HeadWire p.n))
    (c : Option (PC p.n)) (hp : o.payload = .proposal b raw support c) (t early cut : Time)
    (ha : Run.acceptsAt (sapc p) rho index v o t) (ht : t < early) (hcut : early ≤ cut) :
    pathBefore (Run.stateBeforeTime (sapc p) rho cut v) early b = true := by
  obtain ⟨parent, hi, _⟩ := ha.1
  exact stored_path_before_cut p E rho hs hi
    (by simpa [sapc, processed, hp, GridCO.blockKnown] using ha.2.2) ht hcut

end AvailableChain.SAPC
end
