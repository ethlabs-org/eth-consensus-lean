module
public import AvailableChainSAPC.Proofs.ClockBounds
public import AvailableChainSAPC.Proofs.HeadStamps

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

def HeadStampsBounded {n : Nat} (st : State n) : Prop :=
  ∀ row ∈ st.headStamp, row.2 ≤ st.base.now

theorem receiveHead_stampsBounded (p : Params) {n : Nat} (st : State n) (o : HeadWire n)
    (h : HeadStampsBounded st) : HeadStampsBounded (receiveHead p st o) := by
  unfold HeadStampsBounded
  rw [receiveHead_now]
  unfold receiveHead
  split
  · dsimp only
    split
    · exact h
    · split
      · exact h
      · intro row hr
        rcases List.mem_append.mp hr with hold | hnew
        · exact h row hold
        · simp only [List.mem_singleton] at hnew
          simp [hnew]
  · exact h

private theorem receiveHeads_stampsBounded (p : Params) {n : Nat}
    (xs : List (HeadWire n)) (st : State n) (h : HeadStampsBounded st) :
    HeadStampsBounded (xs.foldl (receiveHead p) st) := by
  induction xs generalizing st with
  | nil => exact h
  | cons x xs ih => exact ih _ (receiveHead_stampsBounded p st x h)

private theorem collectPCs_stampsBounded (p : Params) {n : Nat}
    (st : State n) (h : HeadStampsBounded st) : HeadStampsBounded (collectPCs p st) := by
  simpa only [HeadStampsBounded, collectPCs_headStamp, collectPCs_base] using h

theorem process_stampsBounded (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (h : HeadStampsBounded st) : HeadStampsBounded (process p st o) := by
  unfold process
  split
  · exact collectPCs_stampsBounded p _ (receiveHead_stampsBounded p st _ h)
  · unfold admitProposal
    split
    · apply collectPCs_stampsBounded
      apply receiveHeads_stampsBounded
      simpa only [HeadStampsBounded, proposalBase_now] using h
    · exact h
  · split
    · apply collectPCs_stampsBounded
      exact receiveHeads_stampsBounded p _ st h
    · exact h
  · exact h

theorem headStampsBounded_before {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho) (i : Nat) (v : V) :
    HeadStampsBounded (Run.stateBefore (sapc p) rho i v) := by
  set_option backward.isDefEq.respectTransparency false in
  apply stateBefore_invariant (engineClock p) E rho hs HeadStampsBounded
  · simp [sapc, initial, HeadStampsBounded]
  · intro st t ht h
    change HeadStampsBounded (clock p st t)
    simp only [HeadStampsBounded, clock_headStamp, clock_now]
    exact fun row hr => (h row hr).trans ht
  · exact process_stampsBounded p

theorem HeadStampsBounded.stampHead_le {n : Nat} {st : State n}
    (h : HeadStampsBounded st) (o : HeadWire n) : stampHead st o ≤ st.base.now := by
  unfold stampHead
  cases hf : st.headStamp.find? (fun row => row.1 == o) with
  | none => simp
  | some row => exact h row (List.mem_of_find?_eq_some hf)

/-- A complete signature received before an early cutoff retains its
first stamp below that cutoff at every later strict input. -/
theorem stored_head_stamp_before_cut {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    {i : Nat} {reader : V} {parent : Wire p.n} {o : HeadWire p.n} {t early cut : Time}
    (hi : rho.events[i]? = some (.deliver reader parent t))
    (hm : o ∈ (Run.stateBefore (sapc p) rho (i + 1) reader).receivedHeads)
    (ht : t < early) (hcut : early ≤ cut) :
    o ∈ (Run.stateBeforeTime (sapc p) rho cut reader).receivedHeads ∧
      stampHead (Run.stateBeforeTime (sapc p) rho cut reader) o < early := by
  rw [time_input_eq_event_prefix p E rho hs]
  have hidx : i + 1 ≤ (rho.events.filter (fun e => decide (e.time ≤ cut - 1))).length :=
    Nat.succ_le_of_lt ((index_lt_read_length_iff hs (cut - 1) hi).mpr
      (Int.le_sub_one_iff.mpr (ht.trans_le hcut)))
  refine ⟨stateBefore_archive_mono p rho hidx reader hm, ?_⟩
  rw [stampHead_eq_at_later_input p rho hidx reader o hm]
  have hb := (headStampsBounded_before p E rho hs (i + 1) reader).stampHead_le o
  have hn : (Run.stateBefore (sapc p) rho (i + 1) reader).base.now ≤ t := by
    rw [stateBefore_succ_event hi]
    simpa [World.step, sapc, process_now] using! stateBefore_now_le_event p E rho hs hi reader
  exact (hb.trans hn).trans_lt ht

/-- The early handler bridge includes the raw receipt stamp. The path
and the quorum count remain separate obligations. -/
theorem early_handled_head_at_cut {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hΔ : E.Δ = p.Δ) (index : Nat) (reader : V) (r : Slot) (i : Fin p.n)
    (data : HeadData) (t cut : Time) (hlo : voteTime p r ≤ t) (hhi : t < earlyTime p r)
    (hcut : earlyTime p r ≤ cut)
    (hh : Run.handlesAt (sapc p) rho index reader (fromHead ⟨.seat r i, data⟩) t) :
    (⟨.seat r i, data⟩ : HeadWire p.n) ∈
        (Run.stateBeforeTime (sapc p) rho cut reader).receivedHeads ∧
      stampHead (Run.stateBeforeTime (sapc p) rho cut reader) ⟨.seat r i, data⟩ <
        earlyTime p r := by
  obtain ⟨parent, hp, hcall⟩ := hh
  exact stored_head_stamp_before_cut p E rho hs hp
    (early_handled_head_archived p E rho hs hΔ index reader r i data t hlo hhi
      ⟨parent, hp, hcall⟩) hhi hcut

end AvailableChain.SAPC
end
