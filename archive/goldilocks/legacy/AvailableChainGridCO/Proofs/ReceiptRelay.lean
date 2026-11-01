module
public import AvailableChainGridCO.Proofs.ReceiptOrigins

@[expose] public section
namespace AvailableChain.GridCO
set_option linter.unusedSectionVars false
variable [LeasePolicy]
open AvailableChain.Generic AvailableChain.Statements.Generic

/-- A HEAD stored after any event before a cutoff retains an early stamp.
The event can belong to a different reader. -/
theorem stored_vote_stamp_before_cut {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    {index : Nat} {e : Event V (gridCO p).Object} {reader : V} {o : Wire p.n}
    {early cut : Time} (hi : rho.events[index]? = some e)
    (hm : o ∈ (Run.stateBefore (gridCO p) rho (index + 1) reader).votes)
    (ht : e.time < early) (hcut : early ≤ cut) :
    o ∈ (Run.stateBeforeTime (gridCO p) rho cut reader).votes ∧
      stampVote (Run.stateBeforeTime (gridCO p) rho cut reader) o < early := by
  have hp : ReceiptPrefix (Run.stateBefore (gridCO p) rho (index + 1) reader)
      (Run.stateBeforeTime (gridCO p) rho cut reader) := by
    rw [time_input_eq_event_prefix p E rho hs]
    apply stateBefore_receiptPrefix
    exact Nat.succ_le_of_lt ((index_lt_read_length_iff hs (cut - 1) hi).mpr
      (Int.le_sub_one_iff.mpr (ht.trans_le hcut)))
  refine ⟨hp.votes.subset hm, ?_⟩
  rw [hp.stampVote (run_receiptStamped p rho (index + 1) reader) o hm]
  exact ((run_stampsBounded p E rho hs (index + 1) reader).stampVote_le o).trans_lt
    ((stateAfter_now_le_event p E rho hs hi reader).trans_lt ht)

/-- The strict receipt pool includes only votes stamped before the cutoff. -/
def stampedVotes {n : Nat} (st : State n) (r : Slot) (cut : Time) : List (Wire n) :=
  (votesAt st r).filter (fun o => stampVote st o < cut)

/-- Public ticks put a causal in-window receipt in the current or previous label. -/
theorem receipt_current_window {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hs : ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ)
    {j : Nat} {v : V} {parent : Wire p.n} {r : Slot} {t : Time}
    (hj : rho.events[j]? = some (.deliver v parent t))
    (hlo : proposalTime p r ≤ t) (hhi : t < proposalTime p (r + 2)) :
    ((Run.stateBefore (gridCO p) rho j v).now / (4 * p.Δ)).toNat - 1 ≤ r ∧
    r ≤ ((Run.stateBefore (gridCO p) rho j v).now / (4 * p.Δ)).toNat := by
  have hpub : PublicTime E (proposalTime p r) := by
    refine ⟨4 * r, ?_⟩
    simp only [proposalTime, hΔ, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hz : 0 ≤ proposalTime p r := by
    unfold proposalTime
    exact mul_nonneg (by linarith [p.deltaPos]) (Int.natCast_nonneg _)
  have hl := delivery_now_ge_public p E rho hs hj hpub hz hlo
  have hh := (stateBefore_now_le_event p E rho hs hj v).trans_lt hhi
  have hd : 0 < 4 * p.Δ := by linarith [p.deltaPos]
  have hlow : (r : Int) ≤ (Run.stateBefore (gridCO p) rho j v).now / (4 * p.Δ) := by
    apply (Int.le_ediv_iff_mul_le hd).mpr
    simpa [proposalTime, mul_comm] using hl
  have hupp : (Run.stateBefore (gridCO p) rho j v).now / (4 * p.Δ) < (r : Int) + 2 := by
    apply (Int.ediv_lt_iff_lt_mul hd).mpr
    simpa [proposalTime, Nat.cast_add, Nat.cast_ofNat, mul_comm] using hh
  constructor
  · apply Nat.sub_le_iff_le_add.mpr
    apply Int.toNat_le.mpr
    push_cast
    exact Int.le_of_lt_add_one hupp
  · exact (Int.le_toNat (by omega)).mpr hlow

/-- A checked in-window call leaves the exact vote or two stamped copies.
The strict cutoff applies to every copy in the equivocation evidence. -/
theorem handled_head_stamped_or_equivocates {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hs : ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ)
    (j : Nat) (v : V) (r : Slot) (i : Fin p.n) (B : Block) (t cut read : Time)
    (hh : Run.handlesAt (gridCO p) rho j v ⟨.seat r i, .head B⟩ t)
    (hlo : proposalTime p r ≤ t) (hhi : t < proposalTime p (r + 2))
    (ht : t < cut) (hc : cut ≤ read) :
    (⟨.seat r i, .head B⟩ : Wire p.n) ∈
        stampedVotes (Run.stateBeforeTime (gridCO p) rho read v) r cut ∨
      equivocates (stampedVotes (Run.stateBeforeTime (gridCO p) rho read v) r cut) i = true := by
  obtain ⟨parent, hj, hhandle⟩ := hh
  obtain ⟨hlo, hhi⟩ := receipt_current_window p E rho hs hΔ hj hlo hhi
  have halt := handled_head_mem_or_equivocates p
    (Run.stateBefore (gridCO p) rho j v) parent r i B hlo hhi hhandle
  have hpost : Run.stateBefore (gridCO p) rho (j + 1) v =
      process p (Run.stateBefore (gridCO p) rho j v) parent := by
    rw [stateBefore_succ_event hj]
    simp [World.step, gridCO]
  rw [← hpost] at halt
  have hsub : votesAt (Run.stateBefore (gridCO p) rho (j + 1) v) r ⊆
      stampedVotes (Run.stateBeforeTime (gridCO p) rho read v) r cut := by
    intro o ho
    obtain ⟨hm, hl⟩ := List.mem_filter.mp ho
    obtain ⟨hm, hstamp⟩ := stored_vote_stamp_before_cut p E rho hs hj hm ht hc
    exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hm, hl⟩, by simpa using hstamp⟩
  rcases halt with hm | he
  · left
    exact hsub (List.mem_filter.mpr ⟨hm, by simp [headLabel?]⟩)
  · exact Or.inr (equivocates_mono _ _ i hsub he)

/-- A newly accepted HEAD has reached the proposal time of its label. -/
theorem accepted_head_time_lower {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hs : ScheduleWellFormed E rho) (index : Nat) (v : V)
    (o : Wire p.n) (r : Slot) (B : Block) (t : Time)
    (hl : headLabel? o = some r) (hb : o.payload = .head B)
    (ha : Run.acceptsAt (gridCO p) rho index v o t) :
    proposalTime p r ≤ t := by
  obtain ⟨parent, hi, _⟩ := ha.1
  have hnonneg := (hs.in_horizon _ (List.mem_of_getElem? hi)).1
  change 0 ≤ t at hnonneg
  by_cases hr : r = 0
  · simpa [proposalTime, hr] using hnonneg
  have hn : o ∉ (Run.stateBefore (gridCO p) rho index v).votes := by
    simpa [gridCO, processed, hb] using ha.2.1
  have hm : o ∈ (process p (Run.stateBefore (gridCO p) rho index v) parent).votes := by
    have h := ha.2.2
    rw [stateBefore_succ_event hi] at h
    simpa [gridCO, World.step, processed, hb] using h
  have hslot := (process_new_head_label p _ parent o r hl hm).resolve_left hn
  have hdiv : (r : Int) ≤ (Run.stateBefore (gridCO p) rho index v).now / (4 * p.Δ) := by
    have hz : 0 ≤ (Run.stateBefore (gridCO p) rho index v).now / (4 * p.Δ) := by
      by_contra hneg
      have he := Int.toNat_eq_zero.mpr (le_of_lt (lt_of_not_ge hneg))
      exact hr (Nat.eq_zero_of_le_zero (hslot.trans_eq he))
    exact (Int.le_toNat hz).mp hslot
  have htime := (Int.le_ediv_iff_mul_le (by linarith [p.deltaPos])).mp hdiv
  have hnow := stateBefore_now_le_event p E rho hs hi v
  change (Run.stateBefore (gridCO p) rho index v).now ≤ t at hnow
  dsimp [proposalTime]
  nlinarith

/-- Receipt relay yields exact membership or equivocation before a strict
cutoff within the label's admission window. Prior membership needs no call. -/
theorem accepted_head_receipt_before {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hs : ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ)
    (index : Nat) (source reader : V) (r : Slot) (i : Fin p.n) (B : Block)
    (t cut read : Time)
    (ha : Run.acceptsAt (gridCO p) rho index source ⟨.seat r i, .head B⟩ t)
    (ht : t < cut) (hc : cut ≤ read) (hwindow : cut ≤ proposalTime p (r + 2))
    (hrelay : processed (Run.stateBefore (gridCO p) rho (index + 1) reader)
        ⟨.seat r i, .head B⟩ = false →
      ∃ t', t ≤ t' ∧ t' < cut ∧
        ∃ j, Run.handlesAt (gridCO p) rho j reader ⟨.seat r i, .head B⟩ t') :
    (⟨.seat r i, .head B⟩ : Wire p.n) ∈
        stampedVotes (Run.stateBeforeTime (gridCO p) rho read reader) r cut ∨
      equivocates (stampedVotes
        (Run.stateBeforeTime (gridCO p) rho read reader) r cut) i = true := by
  by_cases hm : processed (Run.stateBefore (gridCO p) rho (index + 1) reader)
      ⟨.seat r i, .head B⟩ = true
  · obtain ⟨parent, hi, _⟩ := ha.1
    have hmem : (⟨.seat r i, .head B⟩ : Wire p.n) ∈
        (Run.stateBefore (gridCO p) rho (index + 1) reader).votes := by
      simpa [processed] using hm
    obtain ⟨hm, hstamp⟩ := stored_vote_stamp_before_cut p E rho hs hi hmem ht hc
    exact Or.inl (List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨hm, by simp [headLabel?]⟩,
      by simpa using hstamp⟩)
  · obtain ⟨t', htt, ht', j, hh⟩ := hrelay (Bool.eq_false_iff.mpr hm)
    have hlo := accepted_head_time_lower p E rho hs index source _ r B t rfl rfl ha
    exact handled_head_stamped_or_equivocates p E rho hs hΔ j reader r i B t' cut read hh
      (hlo.trans htt) (ht'.trans_le hwindow) ht' hc

end AvailableChain.GridCO
end
