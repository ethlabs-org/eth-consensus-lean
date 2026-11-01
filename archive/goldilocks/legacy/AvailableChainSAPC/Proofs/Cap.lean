module
public import AvailableChainSAPC.Proofs.Authentication

@[expose] public section
namespace AvailableChain.SAPC

open AvailableChain.Generic AvailableChain.Statements.Generic

theorem head_auth_of_label_seat {n : Nat} (o : HeadWire n) (r : Slot) (i : Fin n)
    (hr : headLabel? o = some r) (hi : headSeat? o = some i) : o.auth = .seat r i := by
  cases o with
  | mk auth payload => cases auth <;> simp_all [headLabel?, headSeat?]

theorem archiveEquivocators_nodup {n : Nat} (st : State n) (r : Slot) :
    (archiveEquivocators st r).Nodup := List.Nodup.filter _ (List.nodup_dedup _)

private theorem dedup_length_mono {α : Type} [DecidableEq α] (xs ys : List α)
    (hsub : xs ⊆ ys) : xs.dedup.length ≤ ys.dedup.length := by
  rw [← List.card_toFinset, ← List.card_toFinset]
  apply Finset.card_le_card
  intro x hx
  exact List.mem_toFinset.mpr (hsub (List.mem_toFinset.mp hx))

theorem archiveEquivocators_mono {n : Nat} (before after : State n) (r : Slot)
    (hsub : before.receivedHeads ⊆ after.receivedHeads) :
    archiveEquivocators before r ⊆ archiveEquivocators after r := by
  intro i hi
  simp only [archiveEquivocators, List.mem_filter, List.mem_dedup,
    List.mem_filterMap, decide_eq_true_eq] at hi ⊢
  obtain ⟨⟨o, ho, hseat⟩, hcount⟩ := hi
  refine ⟨⟨o, ⟨hsub ho.1, ho.2⟩, hseat⟩, hcount.trans ?_⟩
  apply dedup_length_mono
  intro b hb
  simp only [List.mem_map, List.mem_filter] at hb ⊢
  obtain ⟨o, ⟨⟨hm, hl⟩, hs⟩, he⟩ := hb
  exact ⟨o, ⟨⟨hsub hm, hl⟩, hs⟩, he⟩

theorem capBroken_mono (p : Params) {n : Nat} (before after : State n)
    (hsub : before.receivedHeads ⊆ after.receivedHeads)
    (h : capBroken p before = true) : capBroken p after = true := by
  obtain ⟨r, hr, hcount⟩ := List.any_eq_true.mp h
  apply List.any_eq_true.mpr
  refine ⟨r, ?_, ?_⟩
  · obtain ⟨o, ho, he⟩ := List.mem_filterMap.mp hr
    exact List.mem_filterMap.mpr ⟨o, hsub ho, he⟩
  · have hlen : (archiveEquivocators before r).length ≤
        (archiveEquivocators after r).length := by
      rw [← List.toFinset_card_of_nodup (archiveEquivocators_nodup before r),
        ← List.toFinset_card_of_nodup (archiveEquivocators_nodup after r)]
      apply Finset.card_le_card
      intro i hi
      exact List.mem_toFinset.mpr (archiveEquivocators_mono before after r hsub
        (List.mem_toFinset.mp hi))
    exact decide_eq_true (lt_of_lt_of_le (of_decide_eq_true hcount) hlen)

theorem capBroken_process (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (h : capBroken p st = true) : capBroken p (process p st o) = true :=
  capBroken_mono p st _ (process_archive_mono p st o) h

theorem capBroken_clock (p : Params) {n : Nat} (st : State n) (t : Time) :
    capBroken p (clock p st t) = capBroken p st := by
  simp only [capBroken, archiveEquivocators, clock_archive]
  rfl

/-- Equivocation proofs in the full raw archive count only faulty seats.
This holds before GST and without a path-resolution or delivery premise. -/
theorem archiveEquivocators_le_faults_of_authenticated {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hs : ScheduleWellFormed E rho) (st : State p.n)
    (hauth : ArchiveAuthenticated p E rho st) (r : Slot) :
    (archiveEquivocators st r).length ≤ (faulty rho).card := by
  rw [← List.toFinset_card_of_nodup (archiveEquivocators_nodup st r)]
  apply Finset.card_le_card_of_injOn (rho.seatOf r)
  · intro i hi
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hhonest
    have hi' := List.mem_toFinset.mp hi
    have hsize := (List.mem_filter.mp hi').2
    simp only [decide_eq_true_eq] at hsize
    let targets := (((st.receivedHeads.filter (fun o => headLabel? o == some r)).filter
      (fun o => headSeat? o == some i)).map (fun o => o.payload.target))
    have htwo : 1 < targets.toFinset.card := by
      rw [List.card_toFinset]
      exact hsize
    obtain ⟨a, ha, b, hb, hne⟩ := Finset.one_lt_card.mp htwo
    simp only [List.mem_toFinset, targets, List.mem_map, List.mem_filter,
      beq_iff_eq] at ha hb
    obtain ⟨oa, ⟨⟨homa, hlaba⟩, hseata⟩, hea⟩ := ha
    obtain ⟨ob, ⟨⟨homb, hlabb⟩, hseatb⟩, heb⟩ := hb
    have haa := head_auth_of_label_seat oa r i hlaba hseata
    have hab := head_auth_of_label_seat ob r i hlabb hseatb
    have he := authenticated_heads_equal p E rho hs st st hauth hauth r i oa.payload ob.payload
      (by simpa only [← haa] using homa) (by simpa only [← hab] using homb) hhonest
    exact hne (hea.symm.trans ((congrArg HeadData.target he).trans heb))
  · intro i _ j _ hij
    exact (rho.seatOf r).injective hij

theorem archiveEquivocators_le_faults {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (v : V) (t : Time) (r : Slot) :
    (archiveEquivocators (Run.readAt (sapc p) rho t v) r).length ≤ (faulty rho).card :=
  archiveEquivocators_le_faults_of_authenticated p E rho hx.toScheduleWellFormed _
    (archive_authenticated_at_read p E rho hx.toUnforgeableSignatures t v) r

/-- The cap test is false at every authenticated local input, not only
at completed public reads. -/
theorem capBroken_false_of_authenticated {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p)) (hs : ScheduleWellFormed E rho)
    (hcap : FaultBound (sapc p) (pcFaultCap p) rho) (st : State p.n)
    (hauth : ArchiveAuthenticated p E rho st) : capBroken p st = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨r, _, hr⟩ := List.any_eq_true.mp h
  have hle := (archiveEquivocators_le_faults_of_authenticated p E rho hs st hauth r).trans hcap
  have hgt : pcFaultCap p < (archiveEquivocators st r).length := by simpa using hr
  omega

/-- Under the cap the switch cannot fire, even in an arbitrary prefix
or throughout an outage of unbounded duration. -/
theorem capBroken_false_at_read {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hcap : FaultBound (sapc p) (pcFaultCap p) rho)
    (v : V) (t : Time) : capBroken p (Run.readAt (sapc p) rho t v) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨r, _, hr⟩ := List.any_eq_true.mp h
  have hle := (archiveEquivocators_le_faults p E rho hx v t r).trans hcap
  have hgt : pcFaultCap p <
      (archiveEquivocators (Run.readAt (sapc p) rho t v) r).length := by
    simpa using hr
  omega

theorem capBroken_false_before {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hcap : FaultBound (sapc p) (pcFaultCap p) rho)
    (v : V) (index : Nat) : capBroken p (Run.stateBefore (sapc p) rho index v) = false :=
  capBroken_false_of_authenticated p E rho hx.toScheduleWellFormed hcap _
    (archive_authenticated_before p E rho hx.toUnforgeableSignatures index v)

theorem capBroken_false_beforeTime {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (sapc p))
    (hx : ExecutionValid (sapc p) E rho) (hcap : FaultBound (sapc p) (pcFaultCap p) rho)
    (v : V) (t : Time) : capBroken p (Run.stateBeforeTime (sapc p) rho t v) = false :=
  capBroken_false_of_authenticated p E rho hx.toScheduleWellFormed hcap _
    (archive_authenticated_beforeTime p E rho hx.toUnforgeableSignatures t v)

end AvailableChain.SAPC
end
