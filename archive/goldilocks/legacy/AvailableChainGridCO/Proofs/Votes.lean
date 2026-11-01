module
public import AvailableChainGridCO.Proofs.RecordSlots

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

theorem admitVote_mem_origin (p : Params) {n : Nat} (st : State n)
    (parent o : Wire n) (ho : o ∈ (admitVote p st parent).votes) :
    o ∈ st.votes ∨ o = parent := by
  unfold admitVote at ho
  split at ho
  · dsimp only at ho
    split at ho
    · exact Or.inl ho
    · simpa only [List.mem_append, List.mem_singleton] using ho
  · exact Or.inl ho

private theorem fold_votes_origin (p : Params) {n : Nat} (xs : List (HeadWire n))
    (st : State n) (o : Wire n)
    (ho : o ∈ (xs.foldl (fun acc row => admitVote p acc (fromHead row)) st).votes) :
    o ∈ st.votes ∨ o ∈ xs.map fromHead := by
  induction xs generalizing st with
  | nil => exact Or.inl ho
  | cons x xs ih =>
      rcases ih _ ho with hfirst | hrest
      · rcases admitVote_mem_origin p st (fromHead x) o hfirst with hold | heq
        · exact Or.inl hold
        · exact Or.inr (List.mem_cons.mpr (Or.inl heq))
      · exact Or.inr (List.mem_cons_of_mem _ hrest)

/-- A handler can add only its own HEAD or a signed HEAD in its raw view. -/
theorem process_vote_origin (p : Params) {n : Nat} (st : State n)
    (parent o : Wire n) (ho : o ∈ (process p st parent).votes) :
    o ∈ st.votes ∨ parent = o ∨ carries parent o := by
  unfold process at ho
  split at ho
  · rcases admitVote_mem_origin p st parent o ho with hold | heq
    · exact Or.inl hold
    · exact Or.inr (Or.inl heq.symm)
  · rename_i auth payload s B raw support ha hp
    unfold admitProposal at ho
    dsimp only at ho
    split at ho <;> split at ho
    all_goals first
      | exact Or.inl ho
      | rcases fold_votes_origin p raw _ o ho with hold | hraw
        · exact Or.inl hold
        · exact Or.inr (Or.inr (by simp only [carries, hp]; exact Or.inl hraw))
  · exact Or.inl ho

private theorem fold_vote_origin {V : Type} [DecidableEq V] (p : Params)
    (events : List (Event V (gridCO p).Object)) (w : World V (gridCO p))
    (v : V) (o : Wire p.n) (ho : o ∈ ((events.foldl World.step w) v).votes) :
    o ∈ (w v).votes ∨ ∃ parent t, Event.deliver v parent t ∈ events ∧
      (parent = o ∨ carries parent o) := by
  set_option backward.isDefEq.respectTransparency false in
  induction events generalizing w with
  | nil => exact Or.inl ho
  | cons e events ih =>
      rcases ih _ ho with hfirst | ⟨parent, t, hm, hc⟩
      · cases e with
        | tick u t =>
            by_cases hv : v = u
            · subst v
              have hdata := clock_receiptData p (w u) t
              have heq : (clock p (w u) t).votes = (w u).votes :=
                congrArg (fun data => data.2.2.1) hdata
              exact Or.inl (by simpa [World.step, gridCO, heq] using hfirst)
            · exact Or.inl (by simpa [World.step, hv] using hfirst)
        | deliver u parent t =>
            by_cases hv : v = u
            · subst v
              have hmem : o ∈ (process p (w u) parent).votes := by
                simpa [World.step] using! hfirst
              rcases process_vote_origin p (w u) parent o hmem with hold | hc
              · exact Or.inl hold
              · exact Or.inr ⟨parent, t, by simp, hc⟩
            · exact Or.inl (by simpa [World.step, hv] using hfirst)
      · exact Or.inr ⟨parent, t, List.mem_cons_of_mem _ hm, hc⟩

/-- Every stored HEAD at a strict-time read has an earlier direct or
carried delivery. This includes HEADs admitted from a proposal view. -/
theorem stored_vote_origin {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (cut : Time) (v : V) (o : Wire p.n)
    (ho : o ∈ (Run.stateBeforeTime (gridCO p) rho cut v).votes) :
    ∃ parent t, t < cut ∧ Run.processes (gridCO p) rho v parent t ∧
      (parent = o ∨ carries parent o) := by
  rcases fold_vote_origin p _ World.init v o ho with hold | ⟨parent, t, hm, hc⟩
  · simp [World.init, gridCO, initial] at hold
  · obtain ⟨hevent, ht⟩ := List.mem_filter.mp hm
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hevent
    exact ⟨parent, t, of_decide_eq_true ht, ⟨i, hi⟩, hc⟩

/-- Authentication of a stored honest HEAD follows from the run's direct
and carried signature rules. Its emission is strictly before the read. -/
theorem stored_honest_vote_emitted {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p))
    (hsig : UnforgeableSignatures (gridCO p) E rho)
    (cut : Time) (reader holder : V) (o : Wire p.n)
    (ho : o ∈ (Run.stateBeforeTime (gridCO p) rho cut reader).votes)
    (hhonest : holder ∈ rho.honest)
    (hholder : Run.holder (gridCO p) rho o.auth = some holder) :
    ∃ t, t < cut ∧ Run.emits (gridCO p) E rho holder o t := by
  obtain ⟨parent, t, ht, hp, hc⟩ := stored_vote_origin p rho cut reader o ho
  rcases hc with rfl | hc
  · obtain ⟨t', ht', hem⟩ := hsig.unforgeable reader parent t hp holder hhonest hholder
    exact ⟨t', lt_of_le_of_lt ht' ht, hem⟩
  · obtain ⟨t', ht', hem⟩ := hsig.carried reader parent t hp o hc holder hhonest hholder
    exact ⟨t', lt_of_le_of_lt ht' ht, hem⟩

private theorem holder_eq_of_head {V : Type} (p : Params)
    (rho : Run V (gridCO p)) (o : Wire p.n) (r : Slot) (i : Fin p.n)
    (hr : headLabel? o = some r) (hi : headSeat? o = some i) :
    Run.holder (gridCO p) rho o.auth = some (rho.seatOf r i) := by
  rcases o with ⟨auth, payload⟩
  cases auth <;> cases payload <;> simp_all [headLabel?, headSeat?, Run.holder]

/-- Every emitted HEAD uses its label's unique duty and the clocked state. -/
theorem emitted_head_action {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (i : Nat) (v : V) (t : Time)
    (o : Wire p.n) (r : Slot) (target : Block)
    (ho : o ∈ Run.emittedAt (gridCO p) E rho i v t)
    (hr : headLabel? o = some r) (hb : headTarget? o = some target) :
    t = voteTime p r ∧
      act p (clock p (Run.stateBefore (gridCO p) rho i v) t) r = some (.head target) := by
  unfold Run.emittedAt at ho
  split at ho
  · change o ∈ (duties p t).filterMap (fun label =>
        (act p (clock p (Run.stateBefore (gridCO p) rho i v) t) label).map
          (fun msg => ⟨.seat label ((rho.seatOf label).symm v), msg⟩)) ++
      (slotsAt p t).filterMap (fun s => if rho.proposerOf s = v then
        (propose p (clock p (Run.stateBefore (gridCO p) rho i v) t) s).map
          (fun msg => ⟨.proposer s, msg⟩) else none) ++ [] at ho
    simp only [List.append_nil, List.mem_append] at ho
    rcases ho with hact | hproposal
    · obtain ⟨label, hlabel, hact⟩ := List.mem_filterMap.mp hact
      cases ha : act p (clock p (Run.stateBefore (gridCO p) rho i v) t) label with
      | none => simp [ha] at hact
      | some payload =>
          have heq : o = ⟨.seat label ((rho.seatOf label).symm v), payload⟩ := by
            simpa [ha] using hact.symm
          subst o
          cases payload with
          | head B =>
              have hlabel' : label = r := by simpa [headLabel?] using hr
              have hB : B = target := by simpa [headTarget?] using hb
              subst label; subst B
              exact ⟨((duties_spec p r t).mp hlabel).symm, ha⟩
          | proposal B raw support => simp [headLabel?] at hr
    · obtain ⟨s, _, hprop⟩ := List.mem_filterMap.mp hproposal
      split at hprop
      · cases hp : propose p (clock p (Run.stateBefore (gridCO p) rho i v) t) s with
        | none => simp [hp] at hprop
        | some payload =>
            have heq : o = ⟨.proposer s, payload⟩ := by simpa [hp] using hprop.symm
            subst o
            cases payload <;> simp [headLabel?] at hr
      · contradiction
  · contradiction

/-- If all honest label-r emissions are compatible with B, only faulty
seats can count against B at a reader. No delivery bound is needed. -/
theorem releaseCount_le_faults_of_emissions
    {V : Type} [DecidableEq V] [Fintype V] (p : Params) (E : Env V)
    (rho : Run V (gridCO p)) (hsig : UnforgeableSignatures (gridCO p) E rho)
    (cut : Time) (reader : V) (r : Slot) (B : Block)
    (hheads : ∀ u ∈ rho.honest, ∀ o t, t < cut →
      Run.emits (gridCO p) E rho u o t → headLabel? o = some r →
      ∀ target, headTarget? o = some target → Block.Compatible target B) :
    releaseCount p (Run.stateBeforeTime (gridCO p) rho cut reader) r B ≤
      (faulty rho).card := by
  set_option backward.isDefEq.respectTransparency false in
  rw [releaseCount_eq_card]
  apply Finset.card_le_card_of_injOn (rho.seatOf r)
  · intro i hi
    change i ∈ releaseConflictSeats p
      (Run.stateBeforeTime (gridCO p) rho cut reader) r B at hi
    change rho.seatOf r i ∈ faulty rho
    simp only [releaseConflictSeats, Finset.mem_filter, List.mem_toFinset] at hi
    obtain ⟨o, ho, hconf⟩ := List.any_eq_true.mp (Bool.and_eq_true_iff.mp hi.2).2
    have hseat : headSeat? o = some i := by simpa using (List.mem_filter.mp ho).2
    have hraw := (List.mem_filter.mp (List.mem_filter.mp ho).1).1
    have hlabel : headLabel? o = some r := by simpa using (List.mem_filter.mp hraw).2
    have hstored := (List.mem_filter.mp hraw).1
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hhonest
    obtain ⟨t, ht, hem⟩ := stored_honest_vote_emitted p E rho hsig cut reader
      (rho.seatOf r i) o hstored hhonest (holder_eq_of_head p rho o r i hlabel hseat)
    cases htarget : headTarget? o with
    | none => simp [htarget] at hconf
    | some target =>
        have hcompat := hheads _ hhonest o t ht hem hlabel target htarget
        simp [htarget, show Block.compatible target B = true from hcompat] at hconf
  · intro i _ j _ heq
    exact (rho.seatOf r).injective heq

/-- A stored honest seat belongs to the awake batch at its label's duty.
The conclusion also covers HEADs admitted from a proposal's raw view. -/
theorem stored_honest_seat_awake {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hsig : UnforgeableSignatures (gridCO p) E rho)
    (cut : Time) (reader : V) (o : Wire p.n) (r : Slot) (i : Fin p.n)
    (ho : o ∈ (Run.stateBeforeTime (gridCO p) rho cut reader).votes)
    (hl : headLabel? o = some r) (hi : headSeat? o = some i)
    (hh : rho.seatOf r i ∈ rho.honest) :
    rho.seatOf r i ∈ awakeAt E rho.honest (voteTime p r) := by
  set_option backward.isDefEq.respectTransparency false in
  obtain ⟨t, _, j, hj, hem⟩ := stored_honest_vote_emitted p E rho hsig cut reader
    (rho.seatOf r i) o ho hh (holder_eq_of_head p rho o r i hl hi)
  have hawake : E.awake (rho.seatOf r i) t = true := by
    by_contra hc
    simp [Run.emittedAt, hc] at hem
  have htarget : ∃ target, headTarget? o = some target := by
    rcases o with ⟨auth, payload⟩
    cases auth <;> cases payload <;> simp_all [headLabel?, headTarget?]
  obtain ⟨target, ht⟩ := htarget
  have htime := (emitted_head_action p E rho j _ t o r target hem hl ht).1
  exact Finset.mem_filter.mpr ⟨hh, htime ▸ hawake⟩

theorem head_wire_shape {n : Nat} (o : Wire n) (r : Slot) (i : Fin n)
    (hl : headLabel? o = some r) (hi : headSeat? o = some i) :
    ∃ B, o = ⟨.seat r i, .head B⟩ := by
  rcases o with ⟨auth, payload⟩
  cases auth <;> cases payload <;> simp_all [headLabel?, headSeat?]

/-- Honest stored HEADs for one seat and label are identical. Direct and
carried signatures both lead to the same unique clocked action. -/
theorem stored_honest_heads_equal {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hx : ExecutionValid (gridCO p) E rho) (cut : Time) (reader : V)
    (o q : Wire p.n) (r : Slot) (i : Fin p.n)
    (ho : o ∈ (Run.stateBeforeTime (gridCO p) rho cut reader).votes)
    (hq : q ∈ (Run.stateBeforeTime (gridCO p) rho cut reader).votes)
    (hol : headLabel? o = some r) (hql : headLabel? q = some r)
    (hoi : headSeat? o = some i) (hqi : headSeat? q = some i)
    (hh : rho.seatOf r i ∈ rho.honest) : o = q := by
  obtain ⟨t, _, j, hj, hem⟩ := stored_honest_vote_emitted p E rho hx.toUnforgeableSignatures
    cut reader (rho.seatOf r i) o ho hh (holder_eq_of_head p rho o r i hol hoi)
  obtain ⟨t', _, k, hk, hem'⟩ := stored_honest_vote_emitted p E rho hx.toUnforgeableSignatures
    cut reader (rho.seatOf r i) q hq hh (holder_eq_of_head p rho q r i hql hqi)
  obtain ⟨B, rfl⟩ := head_wire_shape o r i hol hoi
  obtain ⟨C, rfl⟩ := head_wire_shape q r i hql hqi
  obtain ⟨ht, ha⟩ := emitted_head_action p E rho j _ t _ r B hem rfl rfl
  obtain ⟨ht', ha'⟩ := emitted_head_action p E rho k _ t' _ r C hem' rfl rfl
  subst t; subst t'
  rw [stateBefore_tick_eq_stateBeforeTime hx.toScheduleWellFormed hj] at ha
  rw [stateBefore_tick_eq_stateBeforeTime hx.toScheduleWellFormed hk] at ha'
  have hBC : B = C := by simpa using (ha.symm.trans ha')
  rw [hBC]

/-- An early resolved honest HEAD survives the genuine late equivocation
filter. Faulty second copies cannot be attributed to its honest seat. -/
theorem honest_early_mem_cleanSupport {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hx : ExecutionValid (gridCO p) E rho) (cut : Time) (reader : V)
    (r : Slot) (o : Wire p.n) (i : Fin p.n)
    (ho : o ∈ earlyVotes p (Run.stateBeforeTime (gridCO p) rho cut reader) r)
    (hi : headSeat? o = some i) (hh : rho.seatOf r i ∈ rho.honest) :
    o ∈ cleanSupport p (Run.stateBeforeTime (gridCO p) rho cut reader) r := by
  apply List.mem_filter.mpr
  refine ⟨ho, ?_⟩
  simp only [Bool.not_eq_true']
  apply Bool.eq_false_iff.mpr
  intro hbad
  obtain ⟨q, hq, htest⟩ := List.any_eq_true.mp hbad
  obtain ⟨hsame, hne⟩ := Bool.and_eq_true_iff.mp htest
  have horaw := (List.mem_filter.mp ho).1
  have hqraw := (List.mem_filter.mp hq).1
  have hol : headLabel? o = some r := by simpa using (List.mem_filter.mp horaw).2
  have hql : headLabel? q = some r := by simpa using (List.mem_filter.mp hqraw).2
  have hqi : headSeat? q = some i := by
    obtain ⟨B, rfl⟩ := head_wire_shape o r i hol hi
    rcases q with ⟨auth, payload⟩
    cases auth <;> cases payload <;> simp_all [sameSeat, headSeat?, headLabel?]
  have heq := stored_honest_heads_equal p E rho hx cut reader q o r i
    (List.mem_filter.mp hqraw).1 (List.mem_filter.mp horaw).1 hql hol hqi hi hh
  simp [heq] at hne

/-- The late denominator contains only the awake honest batch and faulty
seats. This is an authentication result; it needs no delivery bound. -/
theorem late_voterCount_le_awake_add_faulty
    {V : Type} [DecidableEq V] [Fintype V] (p : Params) (E : Env V)
    (rho : Run V (gridCO p)) (hsig : UnforgeableSignatures (gridCO p) E rho)
    (cut : Time) (reader : V) (r : Slot) :
    voterCount (lateVotes p (Run.stateBeforeTime (gridCO p) rho cut reader) r) ≤
      (awakeAt E rho.honest (voteTime p r)).card + (faulty rho).card := by
  set_option backward.isDefEq.respectTransparency false in
  rw [← lateSeats_card]
  apply le_trans (b := (awakeAt E rho.honest (voteTime p r) ∪ faulty rho).card)
  · apply Finset.card_le_card_of_injOn (rho.seatOf r)
    · intro i hi
      obtain ⟨o, ho, hseat⟩ := List.mem_filterMap.mp
        (List.mem_dedup.mp (List.mem_toFinset.mp hi))
      have hraw := (List.mem_filter.mp ho).1
      have hlabel : headLabel? o = some r := by simpa using (List.mem_filter.mp hraw).2
      have hstored := (List.mem_filter.mp hraw).1
      by_cases hh : rho.seatOf r i ∈ rho.honest
      · exact Finset.mem_union_left _
          (stored_honest_seat_awake p E rho hsig cut reader o r i hstored hlabel hseat hh)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hh⟩)
    · intro i _ j _ he
      exact (rho.seatOf r).injective he
  · exact Finset.card_union_le _ _

/-- Event-prefix receipt also has a direct or carried signed origin.
This form can be used immediately after a delivery, before a time read. -/
theorem stored_honest_vote_emitted_at_event {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hsig : UnforgeableSignatures (gridCO p) E rho)
    (index : Nat) (reader holder : V) (o : Wire p.n)
    (ho : o ∈ (Run.stateBefore (gridCO p) rho index reader).votes)
    (hh : holder ∈ rho.honest)
    (hholder : Run.holder (gridCO p) rho o.auth = some holder) :
    ∃ t, Run.emits (gridCO p) E rho holder o t := by
  rcases fold_vote_origin p _ World.init reader o ho with hold | ⟨parent, t, hm, hc⟩
  · simp [World.init, gridCO, initial] at hold
  · have hp : Run.processes (gridCO p) rho reader parent t :=
      List.mem_iff_getElem?.mp (List.mem_of_mem_take hm)
    rcases hc with rfl | hc
    · obtain ⟨t', _, hem⟩ := hsig.unforgeable reader parent t hp holder hh hholder
      exact ⟨t', hem⟩
    · obtain ⟨t', _, hem⟩ := hsig.carried reader parent t hp o hc holder hh hholder
      exact ⟨t', hem⟩

/-- The same honest seat cannot supply two distinct stored HEADs at an
event prefix. The proof includes every call in an admitted proposal loop. -/
theorem stored_honest_heads_equal_at_event {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hx : ExecutionValid (gridCO p) E rho) (index : Nat) (reader : V)
    (o q : Wire p.n) (r : Slot) (i : Fin p.n)
    (ho : o ∈ (Run.stateBefore (gridCO p) rho index reader).votes)
    (hq : q ∈ (Run.stateBefore (gridCO p) rho index reader).votes)
    (hol : headLabel? o = some r) (hql : headLabel? q = some r)
    (hoi : headSeat? o = some i) (hqi : headSeat? q = some i)
    (hh : rho.seatOf r i ∈ rho.honest) : o = q := by
  obtain ⟨t, j, hj, hem⟩ := stored_honest_vote_emitted_at_event p E rho
    hx.toUnforgeableSignatures index reader (rho.seatOf r i) o ho hh
    (holder_eq_of_head p rho o r i hol hoi)
  obtain ⟨t', k, hk, hem'⟩ := stored_honest_vote_emitted_at_event p E rho
    hx.toUnforgeableSignatures index reader (rho.seatOf r i) q hq hh
    (holder_eq_of_head p rho q r i hql hqi)
  obtain ⟨B, rfl⟩ := head_wire_shape o r i hol hoi
  obtain ⟨C, rfl⟩ := head_wire_shape q r i hql hqi
  obtain ⟨ht, ha⟩ := emitted_head_action p E rho j _ t _ r B hem rfl rfl
  obtain ⟨ht', ha'⟩ := emitted_head_action p E rho k _ t' _ r C hem' rfl rfl
  subst t; subst t'
  rw [stateBefore_tick_eq_stateBeforeTime hx.toScheduleWellFormed hj] at ha
  rw [stateBefore_tick_eq_stateBeforeTime hx.toScheduleWellFormed hk] at ha'
  have hBC : B = C := by simpa using (ha.symm.trans ha')
  rw [hBC]

/-- A seat with at most one distinct object cannot trigger equivocation. -/
theorem equivocates_false_of_unique {n : Nat} (xs : List (Wire n)) (i : Fin n)
    (h : ∀ a ∈ seatVotes xs i, ∀ b ∈ seatVotes xs i, a = b) :
    equivocates xs i = false := by
  have hcard : (seatVotes xs i).toFinset.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact h a (List.mem_toFinset.mp ha) b (List.mem_toFinset.mp hb)
  have heq : (seatVotes xs i).eraseDups.toFinset = (seatVotes xs i).toFinset := by
    ext o; simp
  have hlen : (seatVotes xs i).eraseDups.length ≤ 1 := by
    rw [← List.toFinset_card_of_nodup (eraseDups_nodup _), heq]
    exact hcard
  change decide (2 ≤ (seatVotes xs i).eraseDups.length) = false
  exact decide_eq_false (by omega)

/-- An honest seat never hits the two-copy rejection condition in any
reachable event-prefix store. This uses authentication, not synchrony. -/
theorem honest_not_equivocating_at_event {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hx : ExecutionValid (gridCO p) E rho) (index : Nat) (reader : V)
    (r : Slot) (i : Fin p.n) (hh : rho.seatOf r i ∈ rho.honest) :
    equivocates (votesAt (Run.stateBefore (gridCO p) rho index reader) r) i = false := by
  apply equivocates_false_of_unique
  intro a ha b hb
  obtain ⟨ha, hai⟩ := List.mem_filter.mp ha
  obtain ⟨hb, hbi⟩ := List.mem_filter.mp hb
  obtain ⟨ha, hal⟩ := List.mem_filter.mp ha
  obtain ⟨hb, hbl⟩ := List.mem_filter.mp hb
  exact stored_honest_heads_equal_at_event p E rho hx index reader a b r i ha hb
    (by simpa using hal) (by simpa using hbl)
    (by simpa using hai) (by simpa using hbi) hh

end AvailableChain.GridCO
end
