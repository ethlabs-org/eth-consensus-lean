module
public import AvailableChainSAPC.Proofs.BaseReceipts
public import AvailableChainSAPC.Proofs.Cap

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- Every internal base key has an original complete archived signature. -/
def BaseArchived {n : Nat} (st : State n) : Prop :=
  ∀ o ∈ st.base.votes, ∃ h ∈ st.receivedHeads, baseWire h = o

private theorem admitVote_baseArchived (p : Params) {n : Nat} (st : State n)
    (h : BaseArchived st) (o : HeadWire n) (ho : o ∈ st.receivedHeads) :
    BaseArchived { st with base := GridCO.admitVote p.engine st.base (baseWire o) } := by
  intro key hk
  rcases GridCO.admitVote_mem_origin p.engine st.base (baseWire o) key hk with hold | rfl
  · exact h key hold
  · exact ⟨o, ho, rfl⟩

theorem receiveHead_baseArchived (p : Params) {n : Nat} (st : State n) (o : HeadWire n)
    (h : BaseArchived st) : BaseArchived (receiveHead p st o) := by
  unfold receiveHead
  split
  · dsimp only
    split
    · exact h
    · split
      · exact admitVote_baseArchived p st h o (by assumption)
      · apply admitVote_baseArchived
        · intro key hk
          obtain ⟨head, hm, he⟩ := h key hk
          exact ⟨head, List.mem_append_left _ hm, he⟩
        · exact List.mem_append_right _ (List.mem_singleton_self o)
  · exact h

theorem proposalBase_votes (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (b : Block) (raw support : List (HeadWire n)) :
    (proposalBase p st o b raw support).votes = st.base.votes := by
  unfold proposalBase GridCO.admitProposal
  dsimp only
  split_ifs <;> rfl

theorem process_baseArchived (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (h : BaseArchived st) : BaseArchived (process p st o) := by
  have hfold (xs : List (HeadWire n)) (st : State n) (h : BaseArchived st) :
      BaseArchived (xs.foldl (receiveHead p) st) := by
    induction xs generalizing st with
    | nil => exact h
    | cons x xs ih => exact ih _ (receiveHead_baseArchived p st x h)
  have hcollect (st : State n) (h : BaseArchived st) : BaseArchived (collectPCs p st) := by
    simpa only [BaseArchived, collectPCs_base, collectPCs_archive] using h
  unfold process
  split
  · exact hcollect _ (receiveHead_baseArchived p st _ h)
  · unfold admitProposal
    split
    · apply hcollect
      apply hfold
      simpa only [BaseArchived, proposalBase_votes] using h
    · exact h
  · split
    · exact hcollect _ (hfold _ st h)
    · exact h
  · exact h

theorem baseArchived_at_fold {V : Type} [DecidableEq V] (p : Params)
    (events : List (Event V (sapc p).Object)) (v : V) :
    BaseArchived ((events.foldl World.step World.init) v) := by
  apply fold_invariant p BaseArchived
  · simp [BaseArchived, initial, GridCO.initial]
  · intro st t h
    have he : (clock p st t).base.votes = st.base.votes :=
      congrArg (fun data => data.2.2.1) (clock_receiptData p st t)
    simpa only [BaseArchived, he, clock_archive] using h
  · exact process_baseArchived p

theorem baseArchived_head {n : Nat} (st : State n) (h : BaseArchived st)
    (r : Slot) (i : Fin n) (b : Block)
    (hb : (⟨.seat r i, .head b⟩ : GridCO.Wire n) ∈ st.base.votes) :
    ∃ data, (⟨.seat r i, data⟩ : HeadWire n) ∈ st.receivedHeads ∧ data.target = b := by
  obtain ⟨head, hm, he⟩ := h _ hb
  have ha : head.auth = .seat r i := congrArg Signed.auth he
  have ht : head.payload.target = b := by
    have hp := congrArg Signed.payload he
    exact GridCO.Msg.head.inj hp
  exact ⟨head.payload, by simpa only [← ha] using hm, ht⟩

theorem base_honest_heads_equal {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho) (st : State p.n)
    (hbase : BaseArchived st) (hauth : ArchiveAuthenticated p E rho st)
    (a b : GridCO.Wire p.n) (r : Slot) (i : Fin p.n)
    (ha : a ∈ st.base.votes) (hb : b ∈ st.base.votes)
    (hal : GridCO.headLabel? a = some r) (hbl : GridCO.headLabel? b = some r)
    (hai : GridCO.headSeat? a = some i) (hbi : GridCO.headSeat? b = some i)
    (hh : rho.seatOf r i ∈ rho.honest) : a = b := by
  obtain ⟨a, rfl⟩ := GridCO.head_wire_shape a r i hal hai
  obtain ⟨b, rfl⟩ := GridCO.head_wire_shape b r i hbl hbi
  obtain ⟨da, hma, hta⟩ := baseArchived_head st hbase r i a ha
  obtain ⟨db, hmb, htb⟩ := baseArchived_head st hbase r i b hb
  have he := authenticated_heads_equal p E rho hs st st hauth hauth r i da db hma hmb hh
  have ht : a = b := hta.symm.trans ((congrArg HeadData.target he).trans htb)
  rw [ht]

/-- Honest cached base keys cannot equivocate, even when faulty receipts
contain extra targets or ack-only variants. -/
theorem base_honest_not_equivocating {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (index : Nat) (v : V) (r : Slot) (i : Fin p.n) (hh : rho.seatOf r i ∈ rho.honest) :
    GridCO.equivocates (GridCO.votesAt (Run.stateBefore (sapc p) rho index v).base r) i =
      false := by
  apply GridCO.equivocates_false_of_unique
  intro a ha b hb
  obtain ⟨ha, hai⟩ := List.mem_filter.mp ha
  obtain ⟨hb, hbi⟩ := List.mem_filter.mp hb
  obtain ⟨ha, hal⟩ := List.mem_filter.mp ha
  obtain ⟨hb, hbl⟩ := List.mem_filter.mp hb
  exact base_honest_heads_equal p E rho hx.toScheduleWellFormed _
    (baseArchived_at_fold p _ v)
    (archive_authenticated_before p E rho hx.toUnforgeableSignatures index v)
    a b r i ha hb (by simpa using hal) (by simpa using hbl)
    (by simpa using hai) (by simpa using hbi) hh

/-- A healthy early handler call stores the exact honest base key. The
shared two-target cap cannot reject an honest seat. -/
theorem early_honest_base_head_stored {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (index : Nat) (v : V) (r : Slot) (i : Fin p.n) (data : HeadData)
    (hh : rho.seatOf r i ∈ rho.honest) (t : Time)
    (hlo : voteTime p r ≤ t) (hhi : t < earlyTime p r)
    (hhandle : Run.handlesAt (sapc p) rho index v (fromHead ⟨.seat r i, data⟩) t) :
    baseWire ⟨.seat r i, data⟩ ∈ (Run.stateBefore (sapc p) rho (index + 1) v).base.votes := by
  obtain ⟨parent, he, hcall⟩ := hhandle
  have hl := head_delivery_current_label p E rho hx.toScheduleWellFormed hΔ he hlo hhi
  have hor := handled_head_base_mem_or_equivocates p
    (Run.stateBefore (sapc p) rho index v) parent r i data (by rw [hl]; omega) (by rw [hl]) hcall
  have hn := base_honest_not_equivocating p E rho hx (index + 1) v r i hh
  rw [stateBefore_succ_event he]
  rw [stateBefore_succ_event he] at hn
  simp only [World.step, sapc, Function.update_self] at hn ⊢
  exact hor.resolve_right (by intro heq; exact Bool.noConfusion (hn.symm.trans heq))

theorem early_honest_base_head_at_cut {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hx : ExecutionValid (sapc p) E rho)
    (hΔ : E.Δ = p.Δ) (index : Nat) (v : V) (r : Slot) (i : Fin p.n) (data : HeadData)
    (hh : rho.seatOf r i ∈ rho.honest) (t cut : Time)
    (hlo : voteTime p r ≤ t) (hhi : t < earlyTime p r) (hcut : earlyTime p r ≤ cut)
    (hhandle : Run.handlesAt (sapc p) rho index v (fromHead ⟨.seat r i, data⟩) t) :
    baseWire ⟨.seat r i, data⟩ ∈ (Run.stateBeforeTime (sapc p) rho cut v).base.votes ∧
      GridCO.stampVote (Run.stateBeforeTime (sapc p) rho cut v).base
        (baseWire ⟨.seat r i, data⟩) < earlyTime p r := by
  obtain ⟨parent, he, hcall⟩ := hhandle
  exact stored_base_head_stamp_before_cut p E rho hx.toScheduleWellFormed he
    (early_honest_base_head_stored p E rho hx hΔ index v r i data hh t hlo hhi
      ⟨parent, he, hcall⟩) hhi hcut

/-- Outgoing views carry only original signatures from the archive. -/
theorem originalHeads_archived {n : Nat} (st : State n) (keys : List (GridCO.Wire n)) :
    originalHeads st keys ⊆ st.receivedHeads := by
  intro o ho
  obtain ⟨key, _, hf⟩ := List.mem_filterMap.mp ho
  exact List.mem_of_find?_eq_some hf

/-- Erasing outgoing ack fields recovers every cached base key, in the
same order. Selecting original signatures cannot drop a participant. -/
theorem originalHeads_base_keys {n : Nat} (st : State n) (h : BaseArchived st)
    (keys : List (GridCO.Wire n)) (hk : keys ⊆ st.base.votes) :
    (originalHeads st keys).map baseWire = keys := by
  induction keys with
  | nil => rfl
  | cons key keys ih =>
      obtain ⟨o, ho, he⟩ := h key (hk (List.mem_cons_self))
      cases hf : st.receivedHeads.find? (fun o => baseWire o == key) with
      | none =>
          have hn := List.find?_eq_none.mp hf o ho
          simp [he] at hn
      | some head =>
          have heq : baseWire head = key := by simpa using List.find?_some hf
          simp only [originalHeads, List.filterMap_cons, hf, List.map_cons, heq]
          exact congrArg (List.cons key) (ih (fun x hx => hk (List.mem_cons_of_mem _ hx)))

/-- A declared support subset remains a subset when complete original
signatures replace internal keys. Resolution is not recomputed. -/
theorem originalHeads_subset {n : Nat} (st : State n) (raw support : List (GridCO.Wire n))
    (hs : support ⊆ raw) : originalHeads st support ⊆ originalHeads st raw :=
  List.filterMap_subset _ hs

theorem proposer_original_base_keys {n : Nat} (st : State n) (h : BaseArchived st) (r : Slot) :
    (originalHeads st (GridCO.proposerView st.base r)).map baseWire =
      GridCO.proposerView st.base r ∧
    (originalHeads st (GridCO.proposerSupportView st.base r)).map baseWire =
      GridCO.proposerSupportView st.base r := by
  constructor
  · exact originalHeads_base_keys st h _ (fun _ ho => (List.mem_filter.mp ho).1)
  · exact originalHeads_base_keys st h _
      (fun _ ho => (List.mem_filter.mp (List.mem_filter.mp ho).1).1)

end AvailableChain.SAPC
end
