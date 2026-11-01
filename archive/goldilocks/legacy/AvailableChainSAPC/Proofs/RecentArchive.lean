module
public import AvailableChainSAPC.Proofs.BaseArchive
public import AvailableChainSAPC.Proofs.FrozenViews
public import AvailableChainSAPC.Proofs.CertificateRelay

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic AvailableChain.Engine

/-- A recent archived signature has a base receipt or two-target evidence.
Old archive entries need not have an ordinary receipt. -/
def RecentArchive (p : Params) {n : Nat} (st : State n) : Prop :=
  ∀ r i data, (⟨.seat r i, data⟩ : HeadWire n) ∈ st.receivedHeads →
    (st.base.now / (4 * p.Δ)).toNat - 1 ≤ r →
    baseWire ⟨.seat r i, data⟩ ∈ st.base.votes ∨
      GridCO.equivocates (GridCO.votesAt st.base r) i = true

private theorem recentArchive_mono (p : Params) {n : Nat} (a b : State n)
    (ha : b.receivedHeads = a.receivedHeads) (hv : a.base.votes ⊆ b.base.votes)
    (ht : a.base.now ≤ b.base.now) (h : RecentArchive p a) : RecentArchive p b := by
  intro r i data hm hr
  have hd := Int.toNat_le_toNat (Int.ediv_le_ediv (c := 4 * p.Δ) (by linarith [p.deltaPos]) ht)
  rcases h r i data (ha ▸ hm) (by omega) with hk | he
  · exact Or.inl (hv hk)
  · exact Or.inr (GridCO.equivocates_mono _ _ i
      (fun o ho => List.mem_filter.mpr ⟨hv (List.mem_filter.mp ho).1,
        (List.mem_filter.mp ho).2⟩) he)

theorem receiveHead_recentArchive (p : Params) {n : Nat} (st : State n)
    (o : HeadWire n) (h : RecentArchive p st) : RecentArchive p (receiveHead p st o) := by
  intro r i data hm hr
  rw [receiveHead_now] at hr
  have hv : st.base.votes ⊆ (receiveHead p st o).base.votes := by
    rw [receiveHead_base]
    exact (GridCO.admitVote_receiptPrefix p.engine st.base (baseWire o)).votes.subset
  by_cases hold : (⟨.seat r i, data⟩ : HeadWire n) ∈ st.receivedHeads
  · rcases h r i data hold hr with hk | he
    · exact Or.inl (hv hk)
    · exact Or.inr (GridCO.equivocates_mono _ _ i
        (fun key hk => List.mem_filter.mpr ⟨hv (List.mem_filter.mp hk).1,
          (List.mem_filter.mp hk).2⟩) he)
  · have he := (receiveHead_archive_origin p st o _ hm).resolve_left hold
    subst o
    have hhi : r ≤ (st.base.now / (4 * p.Δ)).toNat := by
      by_contra hn
      have hh : (st.base.now / (4 * p.Δ)).toNat < r := Nat.lt_of_not_ge hn
      simp only [receiveHead, hh, ↓reduceIte] at hm
      exact hold hm
    exact receiveHead_base_mem_or_equivocates p st r i data hr hhi

theorem process_recentArchive (p : Params) {n : Nat} (st : State n)
    (o : Wire n) (h : RecentArchive p st) : RecentArchive p (process p st o) := by
  have hf (st : State n) (xs : List (HeadWire n)) (h : RecentArchive p st) :
      RecentArchive p (xs.foldl (receiveHead p) st) := by
    induction xs generalizing st with
    | nil => exact h
    | cons x xs ih => exact ih _ (receiveHead_recentArchive p st x h)
  have hc (st : State n) (h : RecentArchive p st) : RecentArchive p (collectPCs p st) := by
    simpa only [RecentArchive, collectPCs_base, collectPCs_archive] using h
  unfold process
  split
  · exact hc _ (receiveHead_recentArchive p st _ h)
  · unfold admitProposal
    split
    · apply hc
      apply hf
      simpa only [RecentArchive, proposalBase_now, proposalBase_votes, GridCO.votesAt] using h
    · exact h
  · split
    · apply hc
      exact hf st _ h
    · exact h
  · exact h

theorem clock_recentArchive (p : Params) {n : Nat} (st : State n) (t : Time)
    (ht : st.base.now ≤ t) (h : RecentArchive p st) : RecentArchive p (clock p st t) := by
  apply recentArchive_mono p st _ (clock_archive p st t)
  · rw [show (clock p st t).base.votes = st.base.votes from
      congrArg (fun d => d.2.2.1) (clock_receiptData p st t)]
  · rwa [clock_now]
  · exact h

theorem recentArchive_before {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (index : Nat) (v : V) : RecentArchive p (Run.stateBefore (sapc p) rho index v) := by
  apply stateBefore_invariant (engineClock p) E rho hs (RecentArchive p)
  · simp [RecentArchive, sapc, initial]
  · exact clock_recentArchive p
  · exact process_recentArchive p

theorem recentArchive_beforeTime {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (t : Time) (v : V) : RecentArchive p (Run.stateBeforeTime (sapc p) rho t v) := by
  rw [time_input_eq_event_prefix p E rho hs]
  exact recentArchive_before p E rho hs _ v

/-- A strict positive-time input has only earlier clock and receipt stamps. -/
theorem time_input_now_lt {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (t : Time) (ht : 0 < t) (v : V) :
    (Run.stateBeforeTime (sapc p) rho t v).base.now < t := by
  rw [time_input_eq_event_prefix p E rho hs]
  rcases stateBefore_now_source (engineClock p) rho
    (rho.events.filter (fun e : Event V (sapc p).Object => decide (e.time ≤ t - 1))).length v
      with hz | ⟨j, hj, he⟩
  · change (Run.stateBefore (sapc p) rho _ v).base.now = 0 at hz
    rwa [hz]
  · exact Int.le_sub_one_iff.mp ((index_lt_read_length_iff hs (t - 1) he).mp hj)

/-- Before the next-but-one proposal, a raw archived HEAD is still
represented in the ordinary cache. This does not assume an honest seat. -/
theorem archived_base_at_cut {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (cut : Time) (hzero : 0 < cut) (r : Slot)
    (hcut : cut ≤ proposalTime p (r + 2)) (v : V) (i : Fin p.n) (data : HeadData)
    (hm : (⟨.seat r i, data⟩ : HeadWire p.n) ∈
      (Run.stateBeforeTime (sapc p) rho cut v).receivedHeads) :
    baseWire ⟨.seat r i, data⟩ ∈
        GridCO.votesAt (Run.stateBeforeTime (sapc p) rho cut v).base r ∨
      GridCO.equivocates (GridCO.votesAt
        (Run.stateBeforeTime (sapc p) rho cut v).base r) i = true := by
  have hn := (time_input_now_lt p E rho hs cut hzero v).trans_le hcut
  have hcurrent : ((Run.stateBeforeTime (sapc p) rho cut v).base.now /
      (4 * p.Δ)).toNat ≤ r + 1 := by
    apply Int.toNat_le.mpr
    apply (Int.ediv_le_iff_le_mul (by linarith [p.deltaPos])).mpr
    change _ < 4 * p.Δ * ((r + 2 : Nat) : Time) at hn
    push_cast at hn ⊢
    nlinarith
  rcases recentArchive_beforeTime p E rho hs cut v r i data hm (by omega) with hk | he
  · exact Or.inl (List.mem_filter.mpr ⟨hk, by simp [baseWire, baseHead,
      GridCO.fromHead, GridCO.headLabel?]⟩)
  · exact Or.inr he

/-- First stamps in a strict input precede its positive cutoff. -/
theorem time_input_stamps_lt {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (cut : Time) (hc : 0 < cut) (v : V) :
    (∀ o, GridCO.stampVote (Run.stateBeforeTime (sapc p) rho cut v).base o < cut) ∧
      (∀ b, GridCO.stampBlock (Run.stateBeforeTime (sapc p) rho cut v).base b < cut) := by
  have ht := time_input_now_lt p E rho hs cut hc v
  rw [time_input_eq_event_prefix p E rho hs] at ht ⊢
  have hb := base_stampsBounded_before p E rho hs
    (rho.events.filter (fun e : Event V (sapc p).Object => decide (e.time ≤ cut - 1))).length v
  exact ⟨fun o => (hb.stampVote_le o).trans_lt ht,
    fun b => (hb.stampBlock_le b).trans_lt ht⟩

theorem base_freezeView_at_input {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (v : V) :
    let st := (Run.stateBeforeTime (sapc p) rho (freezeTime p r) v).base
    (GridCO.freezeView p.engine st r).1 = GridCO.votesAt st r ∧
      (GridCO.freezeView p.engine st r).2.2 = st.blocks := by
  have hp : 0 < freezeTime p r := by
    change 0 < 4 * p.Δ * (r : Time) + 3 * p.Δ
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  have ht := time_input_stamps_lt p E rho hs _ hp v
  dsimp only [GridCO.freezeView]
  constructor <;> apply List.filter_eq_self.mpr
  · intro o _; exact decide_eq_true (ht.1 o)
  · intro b _; exact decide_eq_true (ht.2 b)

theorem time_input_base_receiptPrefix {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (a b : Time) (hab : a ≤ b) (v : V) :
    GridCO.ReceiptPrefix (Run.stateBeforeTime (sapc p) rho a v).base
      (Run.stateBeforeTime (sapc p) rho b v).base := by
  rw [time_input_eq_event_prefix p E rho hs, time_input_eq_event_prefix p E rho hs]
  exact stateBefore_base_receiptPrefix p rho
    (read_length_mono (rho := rho) (a - 1) (b - 1) (sub_le_sub_right hab 1)) v

/-- Relay of a complete signature supplies the ordinary two-copy
alternative at a recent strict input, even if it was already archived. -/
theorem read_head_base_relay {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho) (source deadline : Time)
    (ht : source < deadline) (hz : 0 < deadline) (r : Slot)
    (hd : deadline ≤ proposalTime p (r + 2)) (hrelay : RelayBy p rho source deadline)
    (v w : V) (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (i : Fin p.n) (data : HeadData)
    (ho : (⟨.seat r i, data⟩ : HeadWire p.n) ∈
      (Run.readAt (sapc p) rho source v).receivedHeads) :
    baseWire ⟨.seat r i, data⟩ ∈
        GridCO.votesAt (Run.stateBeforeTime (sapc p) rho deadline w).base r ∨
      GridCO.equivocates (GridCO.votesAt
        (Run.stateBeforeTime (sapc p) rho deadline w).base r) i = true :=
  archived_base_at_cut p E rho hs deadline hz r hd w i data
    (read_head_relay p E rho hs source deadline ht hrelay v w hv hw _ ho)

end AvailableChain.SAPC
end
