module
public import AvailableChainGridCO.Proofs.ReceiptRelay
public import AvailableChainGridCO.Proofs.Support

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A synchronous label supplies actual calls before the requested cutoff. -/
theorem synchronous_receipt_before {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (r : Slot)
    (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (index : Nat) (o : Wire p.n) (t cut : Time)
    (ha : Run.acceptsAt (gridCO p) rho index source o t)
    (hm : processed (Run.stateBefore (gridCO p) rho (index + 1) reader) o = false)
    (hd : t + E.Δ ≤ cut) (hg : proposalTime p r + E.Δ ≤ cut)
    (hc : cut ≤ gateTime p r)
    (hx : ∀ u, u ≤ cut →
        (gridCO p).excludes (Run.stateBeforeTime (gridCO p) rho u reader) o = false) :
    ∃ t', t ≤ t' ∧ t' < cut ∧ ∃ j, Run.handlesAt (gridCO p) rho j reader o t' := by
  rcases hsync.2.2.2 with ⟨hgst, relay⟩ | ⟨endTime, hend, relay⟩
  · have hbound : max t E.t_GST + E.Δ ≤ cut := by
      rw [← max_add_add_right]
      exact max_le hd (by linarith)
    obtain ⟨t', htt, ht', j, hj⟩ := relay.relay source hs index o t ha reader hr hm
      (hbound.trans (hc.trans hsync.2.2.1)) (hx _ hbound)
    exact ⟨t', htt, ht'.trans_le hbound, j, hj⟩
  · obtain ⟨t', htt, ht', j, hj⟩ := relay.relay source hs index o t ha reader hr hm
      (hd.trans (hc.trans hend)) (hx _ hd)
    exact ⟨t', htt, ht'.trans_le hd, j, hj⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Exact block transport follows from the checked causal handler bridge. -/
theorem synchronous_accepted_block_before {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ) (r : Slot)
    (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (index : Nat) (o : Wire p.n) (t cut : Time)
    {B : Block} {raw support : List (HeadWire p.n)} (hp : o.payload = .proposal B raw support)
    (ha : Run.acceptsAt (gridCO p) rho index source o t)
    (hd : t + E.Δ ≤ cut) (hg : proposalTime p r + E.Δ ≤ cut)
    (hc : cut ≤ gateTime p r) :
    ∃ j e, rho.events[j]? = some e ∧ e.time < cut ∧
      processed (Run.stateBefore (gridCO p) rho (j + 1) reader) o = true := by
  have ht : t < cut := by linarith [E.Δ_pos]
  obtain ⟨parent, hi, _⟩ := ha.1
  by_cases hk : processed (Run.stateBefore (gridCO p) rho (index + 1) reader) o = true
  · exact ⟨index, .deliver source parent t, hi, ht, hk⟩
  obtain ⟨t', htt, ht', j, hh⟩ := synchronous_receipt_before p E rho r hsync
    source reader hs hr index o t cut ha (Bool.eq_false_iff.mpr hk) hd hg hc
    (fun u _ => proposal_not_excluded p rho reader o B raw support hp u)
  have hm := accepted_proposal_handled_stored p E rho hsync.1 hΔ index j source reader
    o B raw support t t' hp ha hh htt
  obtain ⟨parent', hj, _⟩ := hh
  exact ⟨j, .deliver reader parent' t', hj, ht', by simpa [processed, hp, blockKnown] using hm⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Every label-`r` HEAD of a strict read at `u ≤ cut` is in each later read
with a stamp before `cut`. -/
private theorem time_read_votesAt_stamped {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho) (reader : V)
    (r : Slot) (u cut read : Time) (hu : u ≤ cut) (hread : cut ≤ read) :
    votesAt (Run.stateBeforeTime (gridCO p) rho u reader) r ⊆
      stampedVotes (Run.stateBeforeTime (gridCO p) rho read reader) r cut := by
  intro q hq
  obtain ⟨hm, hl⟩ := List.mem_filter.mp hq
  rw [time_input_eq_event_prefix p E rho hs] at hm
  obtain ⟨k, hk⟩ : ∃ k, k = (rho.events.filter (fun e => decide (e.time ≤ u - 1))).length :=
    ⟨_, rfl⟩
  rw [← hk] at hm
  cases k with
  | zero => simp [Run.stateBefore, World.init, gridCO, initial] at hm
  | succ k =>
      have hlt : k < rho.events.length := by
        have := List.length_filter_le (fun e => decide (e.time ≤ u - 1)) rho.events
        omega
      have he : rho.events[k]? = some rho.events[k] := List.getElem?_eq_getElem hlt
      have hle := (index_lt_read_length_iff hs (u - 1) he).mp (by omega)
      obtain ⟨hm', hstamp⟩ := stored_vote_stamp_before_cut p E rho hs he hm
        (show rho.events[k].time < cut by linarith) hread
      exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hm', hl⟩, by simpa using hstamp⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
HEAD relay gives membership or equivocation within the admission window. -/
theorem synchronous_accepted_head_before {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ) (r : Slot)
    (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (index : Nat) (o : Wire p.n) (B : Block) (t cut read : Time)
    (hb : o.payload = .head B) (hl : headLabel? o = some r)
    (ha : Run.acceptsAt (gridCO p) rho index source o t)
    (hd : t + E.Δ ≤ cut) (hg : proposalTime p r + E.Δ ≤ cut)
    (hc : cut ≤ gateTime p r) (hread : cut ≤ read) :
    ∀ i, headSeat? o = some i →
      o ∈ stampedVotes (Run.stateBeforeTime (gridCO p) rho read reader) r cut ∨
      equivocates (stampedVotes
        (Run.stateBeforeTime (gridCO p) rho read reader) r cut) i = true := by
  intro i hi
  have he : o = ⟨.seat r i, .head B⟩ := by
    cases o with
    | mk auth payload => cases auth <;> cases payload <;> simp_all [headLabel?, headSeat?]
  subst o
  have hsched := hsync.1.toScheduleWellFormed
  have hwin : cut ≤ proposalTime p (r + 2) :=
    hc.trans (by dsimp [gateTime, proposalTime]; nlinarith [p.deltaPos])
  rcases head_not_excluded_or_equivocates p E rho hsched reader r i B cut hwin with
    hx | ⟨u, hu, heq⟩
  · apply accepted_head_receipt_before p E rho hsched hΔ
      index source reader r i B t cut read ha (by linarith [E.Δ_pos]) hread hwin
    intro hm
    exact synchronous_receipt_before p E rho r hsync source reader hs hr index _ t cut
      ha hm hd hg hc hx
  · exact Or.inr (equivocates_mono _ _ i
      (time_read_votesAt_stamped p E rho hsched reader r u cut read hu hread) heq)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Every early HEAD settles in each honest late pool as that vote or
equivocation evidence for its seat. -/
theorem synchronous_early_vote_late {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (o : Wire p.n) (ho : o ∈ earlyVotes p (gateInput p rho r source) r) :
    ∀ i, headSeat? o = some i →
      o ∈ lateVotes p (gateInput p rho r reader) r ∨
      equivocates (lateVotes p (gateInput p rho r reader) r) i = true := by
  obtain ⟨hraw, hres⟩ := List.mem_filter.mp ho
  obtain ⟨hm, hl⟩ := List.mem_filter.mp hraw
  have hhead : ∃ B, o.payload = .head B := by
    cases ho : o.payload <;> simp_all [headLabel?]
  obtain ⟨B, hb⟩ := hhead
  have ht : stampVote (gateInput p rho r source) o < earlyTime p r := by
    simp only [resolvedBefore_block, headTarget?, hb, Bool.and_eq_true, decide_eq_true_eq] at hres
    exact hres.1.2
  have hpub : PublicTime E (earlyTime p r) := by
    refine ⟨4 * r + 2, ?_⟩
    simp only [earlyTime, proposalTime, hΔ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hz : 0 ≤ earlyTime p r := by
    dsimp [earlyTime, proposalTime]
    nlinarith [p.deltaPos, Int.natCast_nonneg r]
  change o ∈ (Run.stateBeforeTime (gridCO p) rho (gateTime p r) source).votes at hm
  change stampVote (Run.stateBeforeTime (gridCO p) rho (gateTime p r) source) o < _ at ht
  rw [time_input_eq_event_prefix p E rho hsync.1.toScheduleWellFormed] at hm ht
  obtain ⟨index, _, t, ha, ht⟩ := stored_head_accepted_before p E rho
    hsync.1.toScheduleWellFormed _ source o (earlyTime p r) hpub hz hm ht
  have hc : freezeTime p r ≤ gateTime p r := by
    dsimp [freezeTime, gateTime]; linarith [p.deltaPos]
  have hg : proposalTime p r + E.Δ ≤ freezeTime p r := by
    rw [hΔ]; dsimp [freezeTime]; linarith [p.deltaPos]
  have hsettle := synchronous_accepted_head_before p E rho hΔ r hsync source reader hs hr
    index o B t (freezeTime p r) (gateTime p r) hb (by simpa using hl) ha
    (by rw [hΔ]; dsimp [earlyTime, freezeTime] at *; linarith) hg hc hc
  intro i hi
  have hsub : stampedVotes (gateInput p rho r reader) r (freezeTime p r) ⊆
      lateVotes p (gateInput p rho r reader) r := by
    intro q hq
    obtain ⟨hm, ht⟩ := List.mem_filter.mp hq
    exact List.mem_filter.mpr ⟨hm, by simpa using (of_decide_eq_true ht).trans_le hc⟩
  rcases hsettle i hi with hm | he
  · exact Or.inl (hsub hm)
  · exact Or.inr (equivocates_mono _ _ i hsub he)


/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A surviving early HEAD excludes any different late HEAD from its seat. -/
theorem cleanSupport_eq_of_late_same_seat (p : Params) {n : Nat} (st : State n)
    (r : Slot) (i : Fin n) (a b : Wire n)
    (ha : a ∈ cleanSupport p st r) (hb : b ∈ lateVotes p st r)
    (hia : headSeat? a = some i) (hib : headSeat? b = some i) : a = b := by
  obtain ⟨haearly, hclean⟩ := List.mem_filter.mp ha
  have halabel : headLabel? a = some r := by
    simpa using (List.mem_filter.mp (List.mem_filter.mp haearly).1).2
  have hblabel : headLabel? b = some r := by
    simpa using (List.mem_filter.mp (List.mem_filter.mp hb).1).2
  have hsame : sameSeat b a = true := by
    rcases a with ⟨aa, ap⟩
    rcases b with ⟨ba, bp⟩
    cases aa <;> cases ap <;> cases ba <;> cases bp <;>
      simp_all [headLabel?, headSeat?, sameSeat]
  by_contra hne
  have hany : (lateVotes p st r).any (fun u => sameSeat u a && u != a) = true :=
    List.any_eq_true.mpr ⟨b, hb, by simp [hsame, Ne.symm hne]⟩
  simp [hany] at hclean

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Surviving support excludes equivocation in its own late pool. -/
theorem cleanSupport_not_equivocating (p : Params) {n : Nat} (st : State n)
    (r : Slot) (o : Wire n) (i : Fin n) (hi : headSeat? o = some i)
    (ho : o ∈ cleanSupport p st r) : equivocates (lateVotes p st r) i = false := by
  apply equivocates_false_of_unique
  intro a ha b hb
  obtain ⟨ha, hai⟩ := List.mem_filter.mp ha
  obtain ⟨hb, hbi⟩ := List.mem_filter.mp hb
  exact (cleanSupport_eq_of_late_same_seat p st r i o a ho ha hi
    (by simpa using hai)).symm.trans
    (cleanSupport_eq_of_late_same_seat p st r i o b ho hb hi (by simpa using hbi))

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Genuine prefix support seats appear in every honest late pool. -/
theorem synchronous_support_subset_late {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest) (B : Block) :
    prefixSupportSeats p (gateInput p rho r source) r B ⊆
      lateSeats p (gateInput p rho r reader) r := by
  intro i hi
  obtain ⟨o, ho, hseat, _⟩ := prefixSupportSeats_witness p _ r B i hi
  rcases synchronous_early_vote_late p E rho hΔ r hsync source reader hs hr o
      (List.mem_filter.mp ho).1 i hseat with hm | he
  · exact List.mem_toFinset.mpr (List.mem_dedup.mpr (List.mem_filterMap.mpr ⟨o, hm, hseat⟩))
  · have hp : 0 < (seatVotes (lateVotes p (gateInput p rho r reader) r) i).eraseDups.length := by
      have := of_decide_eq_true he
      omega
    obtain ⟨q, hq⟩ := List.length_pos_iff_exists_mem.mp hp
    obtain ⟨hm, hi⟩ := List.mem_filter.mp (List.mem_eraseDups.mp hq)
    exact List.mem_toFinset.mpr (List.mem_dedup.mpr
      (List.mem_filterMap.mpr ⟨q, hm, by simpa using hi⟩))

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Conflicting genuine prefixes at different readers have disjoint
surviving support sets. Relay makes a shared conflicting seat fail the
source reader's late equivocation test. -/
theorem synchronous_support_disjoint {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r)
    (source reader : V) (hs : source ∈ rho.honest) (hr : reader ∈ rho.honest)
    (B C : Block) (hc : Block.compatible B C = false) :
    Disjoint (prefixSupportSeats p (gateInput p rho r source) r B)
      (prefixSupportSeats p (gateInput p rho r reader) r C) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨o, ho, hseat, target, ht, hp⟩ := prefixSupportSeats_witness p _ r B i hi
  obtain ⟨q, hq, hseat', target', ht', hp'⟩ := prefixSupportSeats_witness p _ r C i hj
  have hlate := synchronous_early_vote_late p E rho hΔ r hsync reader source hr hs q
    (List.mem_filter.mp hq).1 i hseat'
  have hlate := hlate.resolve_right (by
    rw [cleanSupport_not_equivocating p _ r o i hseat ho]
    decide)
  have he := cleanSupport_eq_of_late_same_seat p _ r i o q ho hlate hseat hseat'
  subst q
  have he' := Option.some.inj (ht.symm.trans ht')
  subst target'
  have hcompat := ancestors_compatible B C target hp hp'
  change Block.compatible B C = true at hcompat
  rw [hc] at hcompat
  contradiction

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The engine and receipt relay establish cross-view seat alignment. -/
theorem sameLabelSeatAlignment_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hsync : SynchronousLabel p E rho r) : SameLabelSeatAlignment p rho r := by
  intro u hu v hv B C _ _
  refine ⟨prefixSupportSeats p (gateInput p rho r u) r B,
    prefixSupportSeats p (gateInput p rho r v) r C,
    (prefixSupport_eq_card p _ r B).symm, (prefixSupport_eq_card p _ r C).symm, ?_, ?_, ?_⟩
  · exact Finset.union_subset (prefixSupportSeats_subset_late p _ r B)
      (synchronous_support_subset_late p E rho hΔ r hsync v u hv hu C)
  · exact Finset.union_subset (synchronous_support_subset_late p E rho hΔ r hsync u v hu hv B)
      (prefixSupportSeats_subset_late p _ r C)
  · exact synchronous_support_disjoint p E rho hΔ r hsync u v hu hv B C

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Same-label compatibility follows from the engine, the label's relay
premises, and matching time units. -/
theorem sameLabel_from_engine {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p)) (hΔ : E.Δ = p.Δ) :
    ∀ r, SynchronousLabel p E rho r → ∀ u ∈ rho.honest, ∀ v ∈ rho.honest,
      ∀ B C, confirmation p (gateInput p rho r u) r = some B →
        confirmation p (gateInput p rho r v) r = some C →
        Block.compatible B C = true := by
  intro r hsync
  exact same_label_from_alignment p rho r (sameLabelSeatAlignment_from_engine p E rho hΔ r hsync)

end AvailableChain.GridCO
end
