module
public import AvailableChainGridCO.Proofs.Walk
public import AvailableChainGridCO.Proofs.Votes

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
The actual non-equivocating seats counted for a genuine prefix. -/
def prefixSupportSeats (p : Params) {n : Nat} (st : State n) (r : Slot) (B : Block) :
    Finset (Fin n) :=
  (seats n (cleanSupport p st r)).toFinset.filter (fun i =>
    (seatVotes (cleanSupport p st r) i).any (fun o =>
      match headTarget? o with
      | some target => target ∈ st.blocks && target.slot ≤ (headLabel? o).getD 0 &&
          Block.preceq B target
      | none => false))

theorem prefixSupport_eq_card (p : Params) {n : Nat} (st : State n) (r : Slot) (B : Block) :
    prefixSupport p st r B = (prefixSupportSeats p st r B).card := by
  simp only [prefixSupport_block_eq, goldfishScore_block_eq_local, cleanSupport_no_equivocation,
    Bool.false_or,
    prefixSupportSeats]
  rw [← List.toFinset_filter]
  exact (List.toFinset_card_of_nodup
    (List.Nodup.filter _ (List.nodup_dedup _))).symm

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Each counted seat has a surviving HEAD whose target contains the prefix. -/
theorem prefixSupportSeats_witness (p : Params) {n : Nat} (st : State n) (r : Slot)
    (B : Block) (i : Fin n) (hi : i ∈ prefixSupportSeats p st r B) :
    ∃ o ∈ cleanSupport p st r, headSeat? o = some i ∧
      ∃ target, headTarget? o = some target ∧ Block.Preceq B target := by
  have hh := (Finset.mem_filter.mp hi).2
  obtain ⟨o, ho, ht⟩ := List.any_eq_true.mp hh
  obtain ⟨hm, hs⟩ := List.mem_filter.mp ho
  refine ⟨o, hm, by simpa using hs, ?_⟩
  cases he : headTarget? o with
  | none => simp [he] at ht
  | some target =>
      exact ⟨target, rfl, (Bool.and_eq_true_iff.mp (by simpa only [he] using ht)).2⟩

theorem prefixSupportSeats_subset_late (p : Params) {n : Nat} (st : State n)
    (r : Slot) (B : Block) : prefixSupportSeats p st r B ⊆ lateSeats p st r := by
  intro i hi
  obtain ⟨o, ho, hs, _⟩ := prefixSupportSeats_witness p st r B i hi
  have hl := earlyVotes_subset_lateVotes p st r o (List.mem_filter.mp ho).1
  apply List.mem_toFinset.mpr
  apply List.mem_dedup.mpr
  exact List.mem_filterMap.mpr ⟨o, hl, hs⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Conflicting prefixes have disjoint genuine support at the same reader. -/
theorem prefixSupportSeats_disjoint (p : Params) {n : Nat} (st : State n)
    (r : Slot) (B C : Block) (hc : Block.compatible B C = false) :
    Disjoint (prefixSupportSeats p st r B) (prefixSupportSeats p st r C) := by
  apply Finset.disjoint_left.mpr
  intro i hb hc'
  obtain ⟨o, ho, hs, target, ht, hbt⟩ := prefixSupportSeats_witness p st r B i hb
  obtain ⟨q, hq, hqs, target', hqt, hct⟩ := prefixSupportSeats_witness p st r C i hc'
  have he := cleanSupport_seat_unique p st r i o q ho hq hs hqs
  subst q
  have he' := Option.some.inj (ht.symm.trans hqt)
  subst target'
  have hh := ancestors_compatible B C target hbt hct
  change Block.compatible B C = true at hh
  rw [hc] at hh
  contradiction

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The support of conflicting prefixes fits in the late denominator. -/
theorem conflicting_support_sum_le_late (p : Params) {n : Nat} (st : State n)
    (r : Slot) (B C : Block) (hc : Block.compatible B C = false) :
    prefixSupport p st r B + prefixSupport p st r C ≤ voterCount (lateVotes p st r) := by
  rw [prefixSupport_eq_card, prefixSupport_eq_card, ← lateSeats_card,
    ← Finset.card_union_of_disjoint (prefixSupportSeats_disjoint p st r B C hc)]
  exact Finset.card_le_card (Finset.union_subset
    (prefixSupportSeats_subset_late p st r B) (prefixSupportSeats_subset_late p st r C))

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A majority prefix strictly outscores every conflicting prefix. -/
theorem majority_support_dominates_conflict (p : Params) {n : Nat} (st : State n)
    (r : Slot) (B C : Block)
    (hm : voterCount (lateVotes p st r) < 2 * prefixSupport p st r B)
    (hc : Block.compatible B C = false) :
    prefixSupport p st r C < prefixSupport p st r B := by
  have := conflicting_support_sum_le_late p st r B C hc
  omega

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The complete early resolved honest batch contributes its full count.
Authentication proves that all its seats survive the late filter. -/
theorem prefixSupport_ge_early_honest_batch
    {V : Type} [DecidableEq V] (p : Params) (E : Env V)
    (rho : Run V (gridCO p)) (hx : ExecutionValid (gridCO p) E rho)
    (cut : Time) (reader : V) (r : Slot) (B : Block)
    (hbatch : ∀ u ∈ awakeAt E rho.honest (voteTime p r), ∃ o,
      o ∈ earlyVotes p (Run.stateBeforeTime (gridCO p) rho cut reader) r ∧
      headSeat? o = some ((rho.seatOf r).symm u) ∧
      ∃ target, headTarget? o = some target ∧ Block.Preceq B target) :
    (awakeAt E rho.honest (voteTime p r)).card ≤
      prefixSupport p (Run.stateBeforeTime (gridCO p) rho cut reader) r B := by
  set_option backward.isDefEq.respectTransparency false in
  rw [prefixSupport_eq_card]
  apply Finset.card_le_card_of_injOn (rho.seatOf r).symm
  · intro u hu
    obtain ⟨o, ho, hseat, target, ht, hp⟩ := hbatch u hu
    have hhonest : rho.seatOf r ((rho.seatOf r).symm u) ∈ rho.honest := by
      simpa using (Finset.mem_filter.mp hu).1
    have hc := honest_early_mem_cleanSupport p E rho hx cut reader r o _ ho hseat hhonest
    apply Finset.mem_filter.mpr
    refine ⟨?_, List.any_eq_true.mpr ⟨o, List.mem_filter.mpr ⟨hc, by simp [hseat]⟩, ?_⟩⟩
    · exact List.mem_toFinset.mpr (List.mem_dedup.mpr
        (List.mem_filterMap.mpr ⟨o, hc, hseat⟩))
    · have hresolved := (List.mem_filter.mp ho).2
      simp only [resolvedBefore_block_local, ht, Bool.and_eq_true, decide_eq_true_eq] at hresolved
      simpa only [ht, Bool.and_eq_true, decide_eq_true_eq, blockKnown, Block.Preceq] using
        And.intro (And.intro hresolved.1.1.1 hresolved.1.1.2) hp
  · intro u _ v _ he
    exact (rho.seatOf r).symm.injective he

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A stored prefix with a strict genuine majority occurs in the genuine
result. This proves the confirmation step from the actual support count;
it requires no preselected result or extra GHOST assumption. -/
theorem confirmation_covers_majority (p : Params) {n : Nat} (st : State n)
    (r : Slot) (B : Block)
    (hpath : ∀ C, C ≠ .genesis → Block.Preceq C B → C ∈ st.blocks)
    (hm : voterCount (lateVotes p st r) < 2 * prefixSupport p st r B) :
    ∃ C, confirmation p st r = some C ∧ Block.Preceq B C := by
  let score := prefixSupport p st r
  let eligible := fun C => decide (2 * score C > voterCount (lateVotes p st r))
  let result := ghost .genesis st.blocks score eligible
  have hpre : Block.Preceq B result := by
    apply ghost_covers_of_path_dominance st.blocks score eligible .genesis B
      (Bool.or_eq_true_iff.mpr (Or.inl (genesis_prefix B))) hpath
    · intro C _ hp
      have hle := prefixSupport_mono p st r C B hp
      exact decide_eq_true (by dsimp [score]; omega)
    · intro C _ hp D _ hparent _ hne
      have hconf : Block.compatible D B = false :=
        conflict_mono_descendant C B D hp (siblings_incompatible D C hparent hne)
      have hrev : Block.compatible B D = false := by
        simpa [Block.compatible, Bool.or_comm] using hconf
      have hd := majority_support_dominates_conflict p st r B D hm hrev
      have hle := prefixSupport_mono p st r C B hp
      dsimp [score]
      omega
  have he : eligible result = true := by
    rcases ghostWalk_eligible st.blocks.eraseDups score eligible st.blocks.eraseDups.length
      .genesis with he | he
    · change result = .genesis at he
      rw [he] at hpre
      have hB : B = .genesis := by simpa [Block.Preceq, Block.preceq] using hpre
      rw [he]
      exact decide_eq_true (by simpa [hB] using hm)
    · exact he
  refine ⟨result, ?_, hpre⟩
  unfold confirmation
  dsimp only
  split
  · rfl
  · rename_i hbad
    exact (hbad (of_decide_eq_true he)).elim

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The preservation counting step needs only the complete early resolved
honest batch. The path and the strict GHOST majority then follow. -/
theorem confirmation_covers_early_honest_batch
    {V : Type} [DecidableEq V] [Fintype V] (p : Params) (E : Env V)
    (rho : Run V (gridCO p)) (hx : ExecutionValid (gridCO p) E rho)
    (cut : Time) (reader : V) (r : Slot) (B : Block)
    (hm : AwakeMajority E rho (voteTime p r))
    (hbatch : ∀ u ∈ awakeAt E rho.honest (voteTime p r), ∃ o,
      o ∈ earlyVotes p (Run.stateBeforeTime (gridCO p) rho cut reader) r ∧
      headSeat? o = some ((rho.seatOf r).symm u) ∧
      ∃ target, headTarget? o = some target ∧ Block.Preceq B target) :
    ∃ C, confirmation p (Run.stateBeforeTime (gridCO p) rho cut reader) r = some C ∧
      Block.Preceq B C := by
  have hsupport := prefixSupport_ge_early_honest_batch p E rho hx cut reader r B hbatch
  have hlate := late_voterCount_le_awake_add_faulty p E rho hx.toUnforgeableSignatures
    cut reader r
  change (faulty rho).card < (awakeAt E rho.honest (voteTime p r)).card at hm
  have hmajority : voterCount (lateVotes p (Run.stateBeforeTime (gridCO p) rho cut reader) r) <
      2 * prefixSupport p (Run.stateBeforeTime (gridCO p) rho cut reader) r B := by omega
  obtain ⟨target, ht, _, hbt⟩ := prefixSupport_target p
    (Run.stateBeforeTime (gridCO p) rho cut reader) r B (by omega)
  exact confirmation_covers_majority p _ r B
    (fun C hn hp => run_time_stored_prefix_closed p rho cut reader target ht C hn
      (prefix_trans C B target hp hbt)) hmajority

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A slot-ordered chain cannot have a different ancestor in the same slot. -/
theorem prefix_eq_of_slot_ge (B C : Block) (ho : SlotOrdered C)
    (hp : Block.Preceq B C) (hs : C.slot ≤ B.slot) : B = C := by
  cases C with
  | genesis => simpa [Block.Preceq, Block.preceq] using hp
  | node parent s r_s id =>
      obtain he | hpre : B = .node parent s r_s id ∨ Block.Preceq B parent := by
        simpa [Block.Preceq, Block.preceq, Bool.or_eq_true] using hp
      · exact he
      · have hle := slot_le_of_prefix B parent ho.2 hpre
        have hlt := ho.1
        change s ≤ B.slot at hs
        exact (Nat.not_lt_of_ge hs (lt_of_le_of_lt hle hlt)).elim

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A current-slot majority gives the exact fresh result used by repair. -/
theorem confirmation_eq_fresh_majority (p : Params) {n : Nat} (st : State n)
    (r : Slot) (B : Block) (hslot : B.slot = r)
    (hordered : ∀ C ∈ st.blocks, SlotOrdered C)
    (hpath : ∀ C, C ≠ .genesis → Block.Preceq C B → C ∈ st.blocks)
    (hm : voterCount (lateVotes p st r) < 2 * prefixSupport p st r B) :
    confirmation p st r = some B := by
  obtain ⟨C, hc, hp⟩ := confirmation_covers_majority p st r B hpath hm
  have hco : SlotOrdered C := by
    rcases confirmation_mem p st r C hc with he | hmem
    · subst C; trivial
    · exact hordered C hmem
  have hbound := confirmation_slot_le p st r C hordered hc
  have he := prefix_eq_of_slot_ge B C hco hp (hbound.trans_eq hslot.symm)
  simpa [he] using hc

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The public gate repairs the record from a fresh strict majority and
guard permission. Path closure and the old-record bound follow from the run. -/
theorem read_gate_repairs_majority {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hs : ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hr : 0 < r) (hh : gateTime p r ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (B : Block) (hslot : B.slot = r)
    (hm : voterCount (lateVotes p (gateInput p rho r v) r) <
      2 * prefixSupport p (gateInput p rho r v) r B)
    (hg : (gateInput p rho r v).obligations.any
      (fun (target, _, _) => !Block.compatible target B) = false) :
    stable (Run.readAt (gridCO p) rho (gateTime p r) v) = B := by
  apply read_gate_repairs_fresh_slot p E rho hs hΔ r hr hh v hv B hslot ?_ hg
  have hn : B ≠ .genesis := by
    intro he
    have ht : 0 < B.slot := hslot.symm ▸ hr
    simp [he, Block.slot] at ht
  obtain ⟨target, ht, _, hbt⟩ := prefixSupport_target p (gateInput p rho r v) r B (by omega)
  have hb := run_time_stored_prefix_closed p rho _ v target ht B hn hbt
  exact confirmation_eq_fresh_majority p _ r B hslot
    (run_time_recordSlotOrdered p rho _ v).1
    (fun C hn hp => run_time_stored_prefix_closed p rho _ v B hb C hn hp) hm

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
With an awake majority, complete honest support suffices for repair.
The late-pool bound, GHOST result, and record-slot bound come from the engine. -/
theorem read_gate_repairs_honest_support {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hx : ExecutionValid (gridCO p) E rho) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hr : 0 < r) (hh : gateTime p r ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (B : Block) (hslot : B.slot = r)
    (hm : AwakeMajority E rho (voteTime p r))
    (hsupport : (awakeAt E rho.honest (voteTime p r)).card ≤
      prefixSupport p (gateInput p rho r v) r B)
    (hg : (gateInput p rho r v).obligations.any
      (fun (target, _, _) => !Block.compatible target B) = false) :
    stable (Run.readAt (gridCO p) rho (gateTime p r) v) = B := by
  apply read_gate_repairs_majority p E rho hx.toScheduleWellFormed hΔ r hr hh v hv B hslot ?_ hg
  have hlate := late_voterCount_le_awake_add_faulty p E rho hx.toUnforgeableSignatures
    (gateTime p r) v r
  change (faulty rho).card < (awakeAt E rho.honest (voteTime p r)).card at hm
  change voterCount (lateVotes p (gateInput p rho r v) r) ≤ _ at hlate
  omega

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Repair from an early resolved honest batch and the local guard. All
support counting, equivocation exclusion, path fuel, and record replacement
are proved here; delivery of the batch and guard permission remain premises. -/
theorem read_gate_repairs_early_honest_batch {V : Type} [DecidableEq V] [Fintype V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hx : ExecutionValid (gridCO p) E rho) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hr : 0 < r) (hh : gateTime p r ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (B : Block) (hslot : B.slot = r)
    (hm : AwakeMajority E rho (voteTime p r))
    (hbatch : ∀ u ∈ awakeAt E rho.honest (voteTime p r), ∃ o,
      o ∈ earlyVotes p (gateInput p rho r v) r ∧
      headSeat? o = some ((rho.seatOf r).symm u) ∧
      ∃ target, headTarget? o = some target ∧ Block.Preceq B target)
    (hg : (gateInput p rho r v).obligations.any
      (fun (target, _, _) => !Block.compatible target B) = false) :
    stable (Run.readAt (gridCO p) rho (gateTime p r) v) = B := by
  exact read_gate_repairs_honest_support p E rho hx hΔ r hr hh v hv B hslot hm
    (prefixSupport_ge_early_honest_batch p E rho hx (gateTime p r) v r B hbatch) hg

end AvailableChain.GridCO
end
