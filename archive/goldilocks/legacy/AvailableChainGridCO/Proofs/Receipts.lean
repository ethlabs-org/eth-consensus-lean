module
public import AvailableChainGridCO.Proofs.ClockBounds

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- Receipt lists grow by append. In particular, a later receipt cannot
replace the first stamp of an already stored object. -/
structure ReceiptPrefix {n : Nat} (a b : State n) : Prop where
  blocks : a.blocks <+: b.blocks
  blockStamp : a.blockStamp <+: b.blockStamp
  votes : a.votes <+: b.votes
  voteStamp : a.voteStamp <+: b.voteStamp

theorem ReceiptPrefix.refl {n : Nat} (st : State n) : ReceiptPrefix st st :=
  ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _⟩

theorem ReceiptPrefix.trans {n : Nat} {a b c : State n}
    (hab : ReceiptPrefix a b) (hbc : ReceiptPrefix b c) : ReceiptPrefix a c :=
  ⟨hab.blocks.trans hbc.blocks, hab.blockStamp.trans hbc.blockStamp,
    hab.votes.trans hbc.votes, hab.voteStamp.trans hbc.voteStamp⟩

theorem receiptPrefix_of_data_eq {n : Nat} {a b : State n}
    (he : receiptData b = receiptData a) : ReceiptPrefix a b := by
  have ⟨h1, h2, h3, h4⟩ : b.blocks = a.blocks ∧ b.blockStamp = a.blockStamp ∧
      b.votes = a.votes ∧ b.voteStamp = a.voteStamp := by simpa [receiptData] using he
  constructor <;> simp_all

theorem admitVote_receiptPrefix (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    ReceiptPrefix st (admitVote p st o) := by
  unfold admitVote
  split
  · dsimp only
    split
    · exact .refl _
    · constructor <;> simp
  · exact .refl _

private theorem fold_admitVote_receiptPrefix (p : Params) {n : Nat}
    (raw : List (HeadWire n)) (st : State n) :
    ReceiptPrefix st (raw.foldl (fun acc row => admitVote p acc (fromHead row)) st) := by
  induction raw generalizing st with
  | nil => exact .refl _
  | cons row raw ih => exact (admitVote_receiptPrefix p st (fromHead row)).trans (ih _)

theorem admitProposal_receiptPrefix (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (b : Block) (raw : List (HeadWire n)) : ReceiptPrefix st (admitProposal p st o b raw) := by
  unfold admitProposal
  dsimp only
  split_ifs
  · exact .refl _
  · refine ReceiptPrefix.trans ?_ (fold_admitVote_receiptPrefix p _ _)
    constructor <;> simp

theorem process_receiptPrefix (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    ReceiptPrefix st (process p st o) := by
  unfold process
  split
  · exact admitVote_receiptPrefix p st o
  · exact admitProposal_receiptPrefix p st o _ _
  · exact .refl _

/-- Every event retains receipt lists in their original order. -/
theorem stateBefore_receiptPrefix {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) {i j : Nat} (hij : i ≤ j) (v : V) :
    ReceiptPrefix (Run.stateBefore (gridCO p) rho i v)
      (Run.stateBefore (gridCO p) rho j v) := by
  induction j with
  | zero => rw [Nat.le_zero.mp hij]; exact .refl _
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with he | hlt
      · subst i; exact .refl _
      · apply (ih (by omega)).trans
        cases hj : rho.events[j]? with
        | none =>
            have he : Run.stateBefore (gridCO p) rho (j + 1) =
                Run.stateBefore (gridCO p) rho j := by
              simp [Run.stateBefore, List.take_add_one, hj]
            rw [he]; exact .refl _
        | some e =>
            rw [stateBefore_succ_event hj]
            cases e with
            | tick u t =>
                by_cases hv : v = u
                · subst u
                  simpa [World.step] using!
                    receiptPrefix_of_data_eq (clock_receiptData p _ t)
                · simpa [World.step, hv] using ReceiptPrefix.refl
                    (Run.stateBefore (gridCO p) rho j v)
            | deliver u o t =>
                by_cases hv : v = u
                · subst u
                  simpa [World.step] using! process_receiptPrefix p
                    (Run.stateBefore (gridCO p) rho j v) o
                · simpa [World.step, hv] using ReceiptPrefix.refl
                    (Run.stateBefore (gridCO p) rho j v)

theorem stamp_eq_of_prefix {α : Type} [BEq α] [LawfulBEq α]
    (xs ys : List (α × Time)) (x : α) (a b : Time)
    (hp : xs <+: ys) (hm : ∃ t, (x, t) ∈ xs) :
    ((ys.find? (fun row => row.1 == x)).map Prod.snd).getD b =
      ((xs.find? (fun row => row.1 == x)).map Prod.snd).getD a := by
  obtain ⟨tail, rfl⟩ := hp
  obtain ⟨t, ht⟩ := hm
  cases hf : xs.find? (fun row => row.1 == x) with
  | none =>
      have hh := List.find?_eq_none.mp hf (x, t) ht
      simp at hh
  | some row => simp [List.find?_append, hf]

theorem ReceiptPrefix.stampVote {n : Nat} {a b : State n}
    (hp : ReceiptPrefix a b) (ha : ReceiptStamped a) (o : Wire n) (ho : o ∈ a.votes) :
    stampVote b o = stampVote a o :=
  stamp_eq_of_prefix _ _ _ _ _ hp.voteStamp (ha.2 o ho)

theorem ReceiptPrefix.stampBlock {n : Nat} {a b : State n}
    (hp : ReceiptPrefix a b) (ha : ReceiptStamped a) (B : Block) (hb : B ∈ a.blocks) :
    stampBlock b B = stampBlock a B :=
  stamp_eq_of_prefix _ _ _ _ _ hp.blockStamp (ha.1 B hb)

/-- Every receipt stamp is at most the local clock. -/
def StampsBounded {n : Nat} (st : State n) : Prop :=
  (∀ row ∈ st.blockStamp, row.2 ≤ st.now) ∧
  (∀ row ∈ st.voteStamp, row.2 ≤ st.now)

theorem admitVote_stampsBounded (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (h : StampsBounded st) : StampsBounded (admitVote p st o) := by
  unfold admitVote
  split
  · dsimp only
    split
    · exact h
    · refine ⟨h.1, ?_⟩
      intro row hr
      rcases List.mem_append.mp hr with hr | hr
      · exact h.2 row hr
      · have he : row = (o, st.now) := by simpa using hr
        simp [he]
  · exact h

private theorem fold_admitVote_stampsBounded (p : Params) {n : Nat}
    (raw : List (HeadWire n)) (st : State n) (h : StampsBounded st) :
    StampsBounded (raw.foldl (fun acc row => admitVote p acc (fromHead row)) st) := by
  induction raw generalizing st with
  | nil => exact h
  | cons row raw ih => exact ih _ (admitVote_stampsBounded p st (fromHead row) h)

theorem admitProposal_stampsBounded (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (b : Block) (raw : List (HeadWire n)) (h : StampsBounded st) :
    StampsBounded (admitProposal p st o b raw) := by
  unfold admitProposal
  dsimp only
  split_ifs
  · exact h
  · apply fold_admitVote_stampsBounded
    refine ⟨?_, h.2⟩
    intro row hr
    rcases List.mem_append.mp hr with hr | hr
    · exact h.1 row hr
    · simp only [List.mem_singleton] at hr
      simp [hr]

private theorem process_stampsBounded (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (h : StampsBounded st) : StampsBounded (process p st o) := by
  unfold process
  split
  · exact admitVote_stampsBounded p st o h
  · exact admitProposal_stampsBounded p st o _ _ h
  · exact h

/-- Receipt stamps remain bounded at every reachable event prefix. -/
theorem run_stampsBounded {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho) (i : Nat) (v : V) :
    StampsBounded (Run.stateBefore (gridCO p) rho i v) := by
  set_option backward.isDefEq.respectTransparency false in
  induction i with
  | zero => simp [Run.stateBefore, World.init, gridCO, initial, StampsBounded]
  | succ i ih =>
      cases hi : rho.events[i]? with
      | none => simpa [Run.stateBefore, List.take_add_one, hi] using ih
      | some e =>
          rw [stateBefore_succ_event hi]
          cases e with
          | tick u t =>
              by_cases hv : v = u
              · subst u
                simp only [World.step, Function.update_self]
                have hb := stateBefore_now_le_event p E rho hs hi v
                have hdata := clock_receiptData p (Run.stateBefore (gridCO p) rho i v) t
                have hstamps : (clock p (Run.stateBefore (gridCO p) rho i v) t).blockStamp =
                    (Run.stateBefore (gridCO p) rho i v).blockStamp ∧
                    (clock p (Run.stateBefore (gridCO p) rho i v) t).voteStamp =
                    (Run.stateBefore (gridCO p) rho i v).voteStamp := by
                  exact ⟨congrArg (fun x => x.2.1) hdata, congrArg (fun x => x.2.2.2) hdata⟩
                change StampsBounded (clock p _ t)
                simp only [StampsBounded, hstamps.1, hstamps.2, clock_now]
                exact ⟨fun row hr => (ih.1 row hr).trans hb,
                  fun row hr => (ih.2 row hr).trans hb⟩
              · simpa [World.step, hv] using ih
          | deliver u o t =>
              by_cases hv : v = u
              · subst u
                simpa [World.step] using! process_stampsBounded p _ o ih
              · simpa [World.step, hv] using ih

private theorem find_stamp_le {α : Type} [BEq α] (xs : List (α × Time)) (x : α)
    (now : Time) (h : ∀ row ∈ xs, row.2 ≤ now) :
    ((xs.find? (fun row => row.1 == x)).map Prod.snd).getD now ≤ now := by
  cases hf : xs.find? (fun row => row.1 == x) with
  | none => simp
  | some row => exact h row (List.mem_of_find?_eq_some hf)

theorem StampsBounded.stampVote_le {n : Nat} {st : State n}
    (h : StampsBounded st) (o : Wire n) : stampVote st o ≤ st.now :=
  find_stamp_le _ _ _ h.2

theorem StampsBounded.stampBlock_le {n : Nat} {st : State n}
    (h : StampsBounded st) (B : Block) : stampBlock st B ≤ st.now :=
  find_stamp_le _ _ _ h.1

/-- The strict time read is the public read at the preceding integer time. -/
theorem time_input_eq_event_prefix {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho) (t : Time) :
    Run.stateBeforeTime (gridCO p) rho t = Run.stateBefore (gridCO p) rho
      (rho.events.filter (fun e => decide (e.time ≤ t - 1))).length := by
  rw [stateBeforeTime_eq_readAt_pred, readAt_eq_stateBefore hs]

/-- A completed delivery before a cutoff is included in its strict time read. -/
theorem delivery_prefix_before_cut {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    {i : Nat} {reader : V} {o : Wire p.n} {t cut : Time}
    (hi : rho.events[i]? = some (.deliver reader o t)) (ht : t < cut) :
    ReceiptPrefix (Run.stateBefore (gridCO p) rho (i + 1) reader)
      (Run.stateBeforeTime (gridCO p) rho cut reader) := by
  rw [time_input_eq_event_prefix p E rho hs]
  apply stateBefore_receiptPrefix
  exact Nat.succ_le_of_lt ((index_lt_read_length_iff hs (cut - 1) hi).mpr
    (Int.le_sub_one_iff.mpr ht))

/-- A stored HEAD received before a cutoff keeps its stamp below that cutoff
at every later strict read. This says nothing yet about its target path. -/
theorem stored_head_stamp_before_cut {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    {i : Nat} {reader : V} {parent o : Wire p.n} {t early cut : Time}
    (hi : rho.events[i]? = some (.deliver reader parent t))
    (hm : o ∈ (Run.stateBefore (gridCO p) rho (i + 1) reader).votes)
    (ht : t < early) (hcut : early ≤ cut) :
    o ∈ (Run.stateBeforeTime (gridCO p) rho cut reader).votes ∧
      stampVote (Run.stateBeforeTime (gridCO p) rho cut reader) o < early := by
  have hp := delivery_prefix_before_cut p E rho hs hi (ht.trans_le hcut)
  refine ⟨hp.votes.subset hm, ?_⟩
  rw [hp.stampVote (run_receiptStamped p rho (i + 1) reader) o hm]
  have hb := (run_stampsBounded p E rho hs (i + 1) reader).stampVote_le o
  have hn : (Run.stateBefore (gridCO p) rho (i + 1) reader).now ≤ t := by
    rw [stateBefore_succ_event hi]
    simpa [World.step, gridCO, process_now] using! stateBefore_now_le_event p E rho hs hi reader
  exact (hb.trans hn).trans_lt ht

/-- The complete honest HEAD batch has early vote stamps at the gate.
Block-path receipt remains the only local resolution input to supply. -/
theorem synchronous_honest_head_at_gate {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : EarlyDelivery p E rho r)
    (i : Fin p.n) (B : Block) (hh : rho.seatOf r i ∈ rho.honest)
    (he : Run.emits (gridCO p) E rho (rho.seatOf r i)
      ⟨.seat r i, .head B⟩ (voteTime p r))
    (reader : V) (hr : reader ∈ rho.honest) :
    (⟨.seat r i, .head B⟩ : Wire p.n) ∈ (gateInput p rho r reader).votes ∧
      stampVote (gateInput p rho r reader) ⟨.seat r i, .head B⟩ < earlyTime p r := by
  obtain ⟨index, t, _, ht, ⟨parent, hi, _⟩, hm⟩ :=
    synchronous_honest_head_stored_early p E rho hΔ r hsync i B hh he reader hr
  exact stored_head_stamp_before_cut p E rho hsync.execution.toScheduleWellFormed hi hm ht
    (by dsimp [earlyTime, gateTime]; linarith [p.deltaPos])

end AvailableChain.GridCO
end
