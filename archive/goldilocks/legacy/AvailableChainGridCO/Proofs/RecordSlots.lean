module
public import AvailableChainGridCO.Proofs.StoreFacts
public import AvailableChainGridCO.Proofs.Stamps

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic AvailableChain.Statements.Generic

-- ROOT-DIGEST-2 option 3: keep the statement matcher in a private helper.
private theorem resolvedBefore_block_local {n : Nat} (st : State n) (o : Wire n)
    (cutoff : Time) :
    resolvedBefore st o cutoff = (match headTarget? o with
      | none => false
      | some B => blockKnown st B && B.slot ≤ (headLabel? o).getD 0 &&
          stampVote st o < cutoff && stampBlock st B < cutoff) :=
  resolvedBefore_block st o cutoff

-- ROOT-DIGEST-2 option 3: keep the statement matcher in a private helper.
private theorem goldfishScore_block_eq_local {n : Nat} (tree : List Block)
    (raw support : List (Wire n)) (B : Block) :
    goldfishScore tree raw support B =
      ((seats n raw).filter (fun i => equivocates raw i || (seatVotes support i).any
        (fun o => match headTarget? o with
          | some C => C ∈ tree && C.slot ≤ (headLabel? o).getD 0 && Block.preceq B C
          | none => false))).length :=
  goldfishScore_block_eq tree raw support B

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The executable first-copy filter has no duplicate objects. -/
theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α] (xs : List α) :
    xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons a xs =>
      rw [List.eraseDups_cons]
      apply List.nodup_cons.mpr
      constructor
      · simp
      · exact eraseDups_nodup (xs.filter (fun b => !b == a))
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Every early vote is also in the late pool. -/
theorem earlyVotes_subset_lateVotes (p : Params) {n : Nat} (st : State n) (r : Slot) :
    ∀ o ∈ earlyVotes p st r, o ∈ lateVotes p st r := by
  intro o ho
  obtain ⟨hraw, hres⟩ := List.mem_filter.mp ho
  refine List.mem_filter.mpr ⟨hraw, ?_⟩
  simp only [resolvedBefore_block_local] at hres
  split at hres
  · contradiction
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hres
    have ht := hres.1.2
    have he : earlyTime p r < gateTime p r := by
      dsimp [earlyTime, gateTime]; linarith [p.deltaPos]
    exact decide_eq_true (lt_trans ht he)

private theorem sameSeat_of_label_seat {n : Nat} (a b : Wire n) (r : Slot) (i : Fin n)
    (ha : headLabel? a = some r) (hb : headLabel? b = some r)
    (hia : headSeat? a = some i) (hib : headSeat? b = some i) :
    sameSeat a b = true := by
  rcases a with ⟨aa, ap⟩
  rcases b with ⟨ba, bp⟩
  cases aa <;> cases ap <;> cases ba <;> cases bp <;>
    simp_all [headLabel?, headSeat?, sameSeat]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Two surviving early votes from one seat are the same object. -/
theorem cleanSupport_seat_unique (p : Params) {n : Nat} (st : State n) (r : Slot)
    (i : Fin n) (a b : Wire n)
    (ha : a ∈ cleanSupport p st r) (hb : b ∈ cleanSupport p st r)
    (hia : headSeat? a = some i) (hib : headSeat? b = some i) : a = b := by
  obtain ⟨haearly, hclean⟩ := List.mem_filter.mp ha
  have hbearly := (List.mem_filter.mp hb).1
  have halabel : headLabel? a = some r := by
    simpa using (List.mem_filter.mp (List.mem_filter.mp haearly).1).2
  have hblabel : headLabel? b = some r := by
    simpa using (List.mem_filter.mp (List.mem_filter.mp hbearly).1).2
  by_contra hne
  have hany : (lateVotes p st r).any (fun u => sameSeat u a && u != a) = true := by
    apply List.any_eq_true.mpr
    exact ⟨b, earlyVotes_subset_lateVotes p st r b hbearly,
      by simp [sameSeat_of_label_seat b a r i hblabel halabel hib hia, Ne.symm hne]⟩
  simp [hany] at hclean

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Genuine support never uses the equivocation score shortcut. -/
theorem cleanSupport_no_equivocation (p : Params) {n : Nat} (st : State n)
    (r : Slot) (i : Fin n) : equivocates (cleanSupport p st r) i = false := by
  let xs := seatVotes (cleanSupport p st r) i
  have hcard : xs.toFinset.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ha' := List.mem_filter.mp (List.mem_toFinset.mp ha)
    have hb' := List.mem_filter.mp (List.mem_toFinset.mp hb)
    exact cleanSupport_seat_unique p st r i a b ha'.1 hb'.1
      (by simpa using ha'.2) (by simpa using hb'.2)
  have hlen : xs.eraseDups.length ≤ 1 := by
    have heq : xs.eraseDups.toFinset = xs.toFinset := by ext o; simp
    rw [← List.toFinset_card_of_nodup (eraseDups_nodup xs), heq]
    exact hcard
  change decide (2 ≤ xs.eraseDups.length) = false
  exact decide_eq_false (by omega)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Positive genuine support has an actual, slot-bounded target. -/
theorem prefixSupport_target (p : Params) {n : Nat} (st : State n) (r : Slot)
    (B : Block) (hpos : 0 < prefixSupport p st r B) :
    ∃ target ∈ st.blocks, target.slot ≤ r ∧ Block.Preceq B target := by
  simp only [prefixSupport_block_eq, goldfishScore_block_eq_local] at hpos
  obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ (List.length_pos_iff.mp hpos)
  have hscore := (List.mem_filter.mp hi).2
  rw [cleanSupport_no_equivocation, Bool.false_or] at hscore
  obtain ⟨o, ho, htarget⟩ := List.any_eq_true.mp hscore
  have hclean := (List.mem_filter.mp ho).1
  have hlabel : headLabel? o = some r := by
    simpa using (List.mem_filter.mp
      (List.mem_filter.mp (List.mem_filter.mp hclean).1).1).2
  cases ht : headTarget? o with
  | none => simp [ht] at htarget
  | some target =>
      simp only [ht, hlabel, Option.getD_some, Bool.and_eq_true, decide_eq_true_eq] at htarget
      exact ⟨target, htarget.1.1, htarget.1.2, htarget.2⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Slot order gives the slot bound for each prefix. -/
theorem slot_le_of_prefix (B C : Block) (hordered : SlotOrdered C)
    (hBC : Block.Preceq B C) : B.slot ≤ C.slot := by
  induction C with
  | genesis =>
      have : B = .genesis := by simpa [Block.Preceq, Block.preceq] using hBC
      subst B; rfl
  | node parent s r_s root ih =>
      obtain heq | hp : B = .node parent s r_s root ∨ Block.Preceq B parent := by
        simpa [Block.Preceq, Block.preceq, Bool.or_eq_true] using hBC
      · subst B; rfl
      · exact le_trans (ih hordered.2 hp) (Nat.le_of_lt hordered.1)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A genuine result cannot name a block from a later slot. -/
theorem confirmation_slot_le (p : Params) {n : Nat} (st : State n) (r : Slot)
    (B : Block) (hordered : ∀ b ∈ st.blocks, SlotOrdered b)
    (hresult : confirmation p st r = some B) : B.slot ≤ r := by
  have hmajority := confirmation_majority p st r B hresult
  obtain ⟨target, ht, hslot, hprefix⟩ := prefixSupport_target p st r B (by omega)
  exact le_trans (slot_le_of_prefix B target (hordered target ht) hprefix) hslot

theorem confirmation_mem (p : Params) {n : Nat} (st : State n) (r : Slot)
    (B : Block) (hc : confirmation p st r = some B) : B = .genesis ∨ B ∈ st.blocks :=
  confirmationFrom_mem p .genesis st r B hc

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Stored paths and the stable record have strictly increasing slots. -/
def RecordSlotOrdered {n : Nat} (st : State n) : Prop :=
  (∀ b ∈ st.blocks, SlotOrdered b) ∧ SlotOrdered st.stableRecord

private theorem admitVote_blocks_eq (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    (admitVote p st o).blocks = st.blocks := by
  unfold admitVote
  split
  · dsimp only; split <;> rfl
  · rfl

private theorem fold_votes_blocks (p : Params) {n : Nat} (xs : List (HeadWire n))
    (st : State n) :
    (xs.foldl (fun acc o => admitVote p acc (fromHead o)) st).blocks = st.blocks := by
  induction xs generalizing st with
  | nil => rfl
  | cons o xs ih => rw [List.foldl_cons, ih, admitVote_blocks_eq]

theorem admitProposal_blocks_ordered (p : Params) {n : Nat} (st : State n)
    (o : Wire n) (target : Block) (raw : List (HeadWire n))
    (h : ∀ b ∈ st.blocks, SlotOrdered b) :
    ∀ b ∈ (admitProposal p st o target raw).blocks, SlotOrdered b := by
  unfold admitProposal
  dsimp only
  split <;> split
  all_goals first
    | exact h
    | rename_i hgood
      rw [fold_votes_blocks]
      intro b hb
      rcases List.mem_append.mp hb with hold | hnew
      · exact h b hold
      · simp only [List.mem_singleton] at hnew
        subst b
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq,
          not_or, Bool.not_eq_false, decide_eq_false_iff_not] at hgood
        have hparent : blockKnown st target.parent = true := by tauto
        have hslot : target.parent.slot < target.slot := by tauto
        have ho := h _ (of_decide_eq_true hparent)
        cases target with
        | genesis => exact True.intro
        | node parent s r_s root => exact ⟨hslot, ho⟩

private theorem process_blocks_ordered (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (h : ∀ b ∈ st.blocks, SlotOrdered b) :
    ∀ b ∈ (process p st o).blocks, SlotOrdered b := by
  unfold process
  split
  · simpa only [admitVote_blocks_eq] using h
  · exact admitProposal_blocks_ordered p st o _ _ h
  · exact h

theorem process_recordSlotOrdered (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (h : RecordSlotOrdered st) : RecordSlotOrdered (process p st o) := by
  exact ⟨process_blocks_ordered p st o h.1, by rw [process_stable]; exact h.2⟩

private theorem clockPreGate_blocks_eq (p : Params) {n : Nat} (st : State n) (t : Time) :
    (clockPreGate p st t).blocks = st.blocks := by
  have h := clockPreGate_receiptData p st t
  exact congrArg Prod.fst h

theorem clock_recordSlotOrdered (p : Params) {n : Nat} (st : State n) (t : Time)
    (h : RecordSlotOrdered st) : RecordSlotOrdered (clock p st t) := by
  have hblocks : (clock p st t).blocks = st.blocks :=
    congrArg Prod.fst (clock_receiptData p st t)
  refine ⟨by simpa only [hblocks] using h.1, ?_⟩
  rw [clock_eq_gate_prestate]
  dsimp only
  split
  · rcases gate_stable_cases p (clockPreGate p st t) _ with he | ⟨B, hc, he⟩
    · rw [he, clockPreGate_stable]; exact h.2
    · rw [he]
      rcases confirmation_mem p _ _ B hc with rfl | hm
      · exact True.intro
      · rw [clockPreGate_blocks_eq] at hm
        exact h.1 B hm
  · rw [clockPreGate_stable]; exact h.2

private theorem fold_recordSlotOrdered {V : Type} [DecidableEq V] (p : Params)
    (events : List (Event V (gridCO p).Object)) (w : World V (gridCO p))
    (h : ∀ v, RecordSlotOrdered (w v)) :
    ∀ v, RecordSlotOrdered ((events.foldl World.step w) v) := by
  induction events generalizing w with
  | nil => exact h
  | cons e events ih =>
      apply ih
      intro v
      cases e with
      | tick u t =>
          by_cases hv : v = u
          · subst v; simpa [World.step] using! clock_recordSlotOrdered p (w u) t (h u)
          · simpa [World.step, hv] using h v
      | deliver u o t =>
          by_cases hv : v = u
          · subst v; simpa [World.step] using! process_recordSlotOrdered p (w u) o (h u)
          · simpa [World.step, hv] using h v

theorem run_time_recordSlotOrdered {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (t : Time) (v : V) :
    RecordSlotOrdered (Run.stateBeforeTime (gridCO p) rho t v) :=
  fold_recordSlotOrdered p _ World.init (by simp [RecordSlotOrdered, initial, World.init,
    gridCO, SlotOrdered]) v

private theorem clock_record_slot_le (p : Params) {n : Nat} (st : State n)
    (r : Slot) (t : Time) (ho : RecordSlotOrdered st)
    (hb : st.stableRecord.slot ≤ r) (ht : t ≤ gateTime p r) :
    (clock p st t).stableRecord.slot ≤ r := by
  rw [clock_eq_gate_prestate]
  dsimp only
  split
  · rename_i hg
    have he : t = gateTime p ((t - 6 * p.Δ) / (4 * p.Δ)).toNat := by
      simpa using (Bool.and_eq_true_iff.mp hg).2
    have hr := (gateTime_le_iff p _ r).mp (he ▸ ht)
    rcases gate_stable_cases p (clockPreGate p st t) _ with hold | ⟨B, hc, hB⟩
    · rw [hold, clockPreGate_stable]; exact hb
    · rw [hB]
      exact le_trans (confirmation_slot_le p _ _ B
        (by simpa only [clockPreGate_blocks_eq] using ho.1) hc) hr
  · rw [clockPreGate_stable]; exact hb

private theorem fold_record_slot_le {V : Type} [DecidableEq V] (p : Params)
    (events : List (Event V (gridCO p).Object)) (w : World V (gridCO p)) (r : Slot)
    (h : ∀ v, RecordSlotOrdered (w v) ∧ (w v).stableRecord.slot ≤ r)
    (ht : ∀ e ∈ events, e.time ≤ gateTime p r) :
    ∀ v, RecordSlotOrdered ((events.foldl World.step w) v) ∧
      ((events.foldl World.step w) v).stableRecord.slot ≤ r := by
  set_option backward.isDefEq.respectTransparency false in
  induction events generalizing w with
  | nil => exact h
  | cons e events ih =>
      apply ih
      · intro v
        cases e with
        | tick u t =>
            by_cases hv : v = u
            · subst v
              simpa [World.step] using!
                And.intro (clock_recordSlotOrdered p (w u) t (h u).1)
                  (clock_record_slot_le p (w u) r t (h u).1 (h u).2
                    (ht (.tick u t) (by simp)))
            · simpa [World.step, hv] using h v
        | deliver u o t =>
            by_cases hv : v = u
            · subst v
              simpa [World.step, gridCO, process_stable] using
                And.intro (process_recordSlotOrdered p (w u) o (h u).1) (h u).2
            · simpa [World.step, hv] using h v
      · intro e he; exact ht e (List.mem_cons_of_mem _ he)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
At and before gate `r`, the stable record has slot at most `r`.
This also holds for a reachable prefix with no synchrony or participation. -/
theorem read_stable_slot_le {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (r : Slot) (t : Time) (ht : t ≤ gateTime p r) (v : V) :
    (stable (Run.readAt (gridCO p) rho t v)).slot ≤ r := by
  exact (fold_record_slot_le p _ World.init r
    (by simp [RecordSlotOrdered, World.init, gridCO, initial, SlotOrdered, Block.slot])
    (by
      intro e he
      exact le_trans (of_decide_eq_true (List.mem_filter.mp he).2) ht) v).2

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The input to a positive-slot gate has a strictly older stable record. -/
theorem gate_input_slot_lt {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p)) (hs : ScheduleWellFormed E rho)
    (r : Slot) (hr : 0 < r) (v : V) : (stable (gateInput p rho r v)).slot < r := by
  rw [gate_input_record p E rho hs, ite_eq_right (Nat.ne_of_gt hr)]
  exact lt_of_le_of_lt (read_stable_slot_le p rho (r - 1) _ (le_refl _) v)
    (Nat.sub_lt hr (by decide))

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Before a gate, the clock can remove obligations but cannot add one. -/
theorem clockPreGate_obligations_subset (p : Params) {n : Nat} (st : State n) (t : Time) :
    ∀ row ∈ (clockPreGate p st t).obligations, row ∈ st.obligations := by
  unfold clockPreGate
  dsimp only
  split <;> split <;> split
  all_goals
    intro row hr
    repeat first | exact (List.mem_filter.mp hr).1
                 | replace hr := (List.mem_filter.mp hr).1

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The actual gate read repairs an older record once the fresh genuine
result passes the local guard. No bound on the old record is a premise. -/
theorem read_gate_repairs_fresh_slot {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hs : ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hr : 0 < r) (hh : gateTime p r ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (B : Block) (hslot : B.slot = r)
    (hc : confirmation p (gateInput p rho r v) r = some B)
    (hg : (gateInput p rho r v).obligations.any
      (fun (target, _, _) => !Block.compatible target B) = false) :
    stable (Run.readAt (gridCO p) rho (gateTime p r) v) = B := by
  set_option backward.isDefEq.respectTransparency false in
  have hpub : PublicTime E (gateTime p r) := by
    refine ⟨4 * r + 6, ?_⟩
    simp only [gateTime, proposalTime, hΔ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hn : 0 ≤ gateTime p r := by
    dsimp [gateTime, proposalTime]
    have := mul_nonneg (show 0 ≤ 4 * p.Δ by linarith [p.deltaPos]) (Int.natCast_nonneg r)
    linarith [p.deltaPos]
  rw [read_stable_eq_clock hs (hs.tick_total v hv _ hpub hn hh), clock_at_gate]
  apply gate_repairs_fresh_slot p _ r B
  · rw [confirmation_eq_of_receiptData p _ _
      (clockPreGate_receiptData p _ _) (run_time_receiptStamped p rho _ v)]
    exact hc
  · apply Bool.eq_false_iff.mpr
    intro hbad
    obtain ⟨row, hrow, hconf⟩ := List.any_eq_true.mp hbad
    have : (gateInput p rho r v).obligations.any
        (fun (target, _, _) => !Block.compatible target B) = true :=
      List.any_eq_true.mpr ⟨row, clockPreGate_obligations_subset p _ _ row hrow, hconf⟩
    simp [hg] at this
  · rw [clockPreGate_stable]
    exact (run_time_recordSlotOrdered p rho _ v).2
  · rw [clockPreGate_stable, hslot]
    exact gate_input_slot_lt p E rho hs r hr v

end AvailableChain.GridCO
end
