module
public import AvailableChainSAPC.Proofs.BaseViews

@[expose] public section
namespace AvailableChain.SAPC

/-- Every detected same-label base equivocation has two distinct target
signatures in the raw archive. Ack fields play no part in this count. -/
theorem view_equivocation_archived {n : Nat} (st : State n)
    (r : Slot) (i : Fin n) (xs : List (GridCO.Wire n))
    (harchive : ∀ o ∈ xs, ∃ h ∈ st.receivedHeads, baseWire h = o)
    (hlabel : ∀ o ∈ xs, GridCO.headLabel? o = some r)
    (he : GridCO.equivocates xs i = true) : i ∈ archiveEquivocators st r := by
  have hcard : 1 < (GridCO.seatVotes xs i).toFinset.card := by
    have heq : (GridCO.seatVotes xs i).eraseDups.toFinset =
        (GridCO.seatVotes xs i).toFinset := by ext o; simp
    rw [← heq, List.toFinset_card_of_nodup (GridCO.eraseDups_nodup _)]
    exact of_decide_eq_true he
  obtain ⟨a, ha, b, hb, hne⟩ := Finset.one_lt_card.mp hcard
  obtain ⟨ham, hai⟩ := List.mem_filter.mp (List.mem_toFinset.mp ha)
  obtain ⟨hbm, hbi⟩ := List.mem_filter.mp (List.mem_toFinset.mp hb)
  obtain ⟨a, rfl⟩ := GridCO.head_wire_shape a r i (hlabel a ham) (by simpa using hai)
  obtain ⟨b, rfl⟩ := GridCO.head_wire_shape b r i (hlabel b hbm) (by simpa using hbi)
  have source (b : Block) (hm : (⟨.seat r i, .head b⟩ : GridCO.Wire n) ∈ xs) :
      ∃ data, (⟨.seat r i, data⟩ : HeadWire n) ∈ st.receivedHeads ∧ data.target = b := by
    obtain ⟨head, hh, he⟩ := harchive _ hm
    have ha : head.auth = .seat r i := congrArg Signed.auth he
    have ht : head.payload.target = b := GridCO.Msg.head.inj (congrArg Signed.payload he)
    exact ⟨head.payload, by simpa only [← ha] using hh, ht⟩
  obtain ⟨da, hda, hta⟩ := source a ham
  obtain ⟨db, hdb, htb⟩ := source b hbm
  have hab : a ≠ b := by intro heq; exact hne (by rw [heq])
  simp only [archiveEquivocators, List.mem_filter, List.mem_dedup,
    List.mem_filterMap, decide_eq_true_eq]
  refine ⟨⟨⟨.seat r i, da⟩, ⟨hda, by simp [headLabel?]⟩, rfl⟩, ?_⟩
  rw [← List.card_toFinset]
  apply Finset.one_lt_card.mpr
  refine ⟨a, ?_, b, ?_, hab⟩
  · apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    exact ⟨⟨.seat r i, da⟩, by simp [hda, headLabel?, headSeat?], hta⟩
  · apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    exact ⟨⟨.seat r i, db⟩, by simp [hdb, headLabel?, headSeat?], htb⟩

theorem base_equivocation_archived {n : Nat} (st : State n) (hbase : BaseArchived st)
    (r : Slot) (i : Fin n) (xs : List (GridCO.Wire n)) (hsub : xs ⊆ st.base.votes)
    (hlabel : ∀ o ∈ xs, GridCO.headLabel? o = some r)
    (he : GridCO.equivocates xs i = true) : i ∈ archiveEquivocators st r :=
  view_equivocation_archived st r i xs (fun o ho => hbase o (hsub ho)) hlabel he

/-- Active mode bounds detected archive equivocators at each label. The
actual fault count can exceed f; no honest-support premise is used. -/
theorem active_archive_count_le (p : Params) {n : Nat} (st : State n) (r : Slot)
    (hactive : capBroken p st = false) : (archiveEquivocators st r).length ≤ pcFaultCap p := by
  by_contra hn
  have hlt : pcFaultCap p < (archiveEquivocators st r).length := by omega
  have hpos : 0 < (archiveEquivocators st r).length := by omega
  obtain ⟨i, hi⟩ := List.length_pos_iff_exists_mem.mp hpos
  have hm := (List.mem_filter.mp hi).1
  obtain ⟨o, ho, _⟩ := List.mem_filterMap.mp (List.mem_dedup.mp hm)
  have hl : headLabel? o = some r := by simpa using (List.mem_filter.mp ho).2
  have htrue : capBroken p st = true :=
    List.any_eq_true.mpr ⟨r, List.mem_filterMap.mpr ⟨o, (List.mem_filter.mp ho).1, hl⟩,
      decide_eq_true hlt⟩
  simp [hactive] at htrue

def detectedSeats {n : Nat} (xs : List (GridCO.Wire n)) : Finset (Fin n) :=
  (xs.filterMap GridCO.headSeat?).toFinset.filter (fun i => GridCO.equivocates xs i = true)

theorem active_view_count_le (p : Params) {n : Nat} (st : State n)
    (r : Slot) (xs : List (GridCO.Wire n))
    (harchive : ∀ o ∈ xs, ∃ h ∈ st.receivedHeads, baseWire h = o)
    (hlabel : ∀ o ∈ xs, GridCO.headLabel? o = some r)
    (hactive : capBroken p st = false) : (detectedSeats xs).card ≤ pcFaultCap p := by
  calc
    (detectedSeats xs).card ≤ (archiveEquivocators st r).toFinset.card := by
      apply Finset.card_le_card
      intro i hi
      exact List.mem_toFinset.mpr (view_equivocation_archived st r i xs harchive hlabel
        (Finset.mem_filter.mp hi).2)
    _ = (archiveEquivocators st r).length :=
      List.toFinset_card_of_nodup (archiveEquivocators_nodup st r)
    _ ≤ pcFaultCap p := active_archive_count_le p st r hactive

theorem active_base_count_le (p : Params) {n : Nat} (st : State n)
    (hbase : BaseArchived st) (r : Slot) (xs : List (GridCO.Wire n))
    (hsub : xs ⊆ st.base.votes) (hlabel : ∀ o ∈ xs, GridCO.headLabel? o = some r)
    (hactive : capBroken p st = false) : (detectedSeats xs).card ≤ pcFaultCap p :=
  active_view_count_le p st r xs (fun o ho => hbase o (hsub ho)) hlabel hactive

theorem active_proposer_count_le {V : Type} [DecidableEq V] (p : Params)
    (events : List (AvailableChain.Generic.Event V (sapc p).Object)) (v : V) (r : Slot)
    (hactive : capBroken p ((events.foldl AvailableChain.Generic.World.step
      AvailableChain.Generic.World.init) v) = false) :
    (detectedSeats (GridCO.proposerView ((events.foldl AvailableChain.Generic.World.step
      AvailableChain.Generic.World.init) v).base r)).card ≤ pcFaultCap p := by
  apply active_base_count_le p _ (baseArchived_at_fold p events v) (r - 1) _
    (fun _ ho => (List.mem_filter.mp ho).1) _ hactive
  intro o ho
  simpa using (List.mem_filter.mp ho).2

/-- The live mode test also bounds the full frozen/proposal merge. This
includes carried keys omitted by the two-target cache. -/
theorem active_voter_count_le {V : Type} [DecidableEq V] (p : Params)
    (events : List (AvailableChain.Generic.Event V (sapc p).Object)) (v : V) (s : Slot)
    (hactive : capBroken p ((events.foldl AvailableChain.Generic.World.step
      AvailableChain.Generic.World.init) v) = false) :
    (detectedSeats (GridCO.voterView p.engine ((events.foldl AvailableChain.Generic.World.step
      AvailableChain.Generic.World.init) v).base s)).card ≤ pcFaultCap p := by
  apply active_view_count_le p _ (s - 1) _
  · exact voterView_archived p _ (baseArchived_at_fold p events v)
      (frozenViewsStored_at_fold p events v) (proposalViewsArchived_at_fold p events v) s
  · exact voterView_label p _ (frozenViewsStored_at_fold p events v) s
  · exact hactive

end AvailableChain.SAPC
end
