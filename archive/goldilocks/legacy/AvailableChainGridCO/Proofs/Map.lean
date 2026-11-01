module
public import AvailableChainGridCO.Proofs.StoreFacts
public import AvailableChainGridCO.Model.StoreKeys
public import AvailableChainGridCO.Proofs.Relay

-- Find matcher bodies in the two definitions; do not depend on generated names.
local elab "hygieneEq% " lhs:term:max rhs:term:max : term => do
  let left ← Lean.Elab.Term.elabTerm lhs none
  let right ← Lean.Elab.Term.elabTerm rhs none
  let a ← Lean.getConstInfo left.getAppFn.constName!
  let b ← Lean.getConstInfo right.getAppFn.constName!
  for x in a.value!.getUsedConstants do
    unless (← Lean.Meta.getMatcherInfo? x).isSome do continue
    let ex ← Lean.Meta.mkConstWithFreshMVarLevels x
    for y in b.value!.getUsedConstants do
      unless (← Lean.Meta.getMatcherInfo? y).isSome do continue
      let ey ← Lean.Meta.mkConstWithFreshMVarLevels y
      if ← Lean.Meta.isDefEq (← Lean.Meta.inferType ex) (← Lean.Meta.inferType ey) then
        if ← Lean.Meta.isDefEq ex ey then
          return ← Lean.Meta.mkEq ex ey
  throwError "No equal matcher bodies in the supplied definitions"

namespace AvailableChain.GridCO

open AvailableChain.Generic

-- ROOT-DIGEST-2 option 3: use a private copy of the same matcher (BUILD B3).
private def hygiene_goldfishScoreOn {n : Nat} {mode : HeadMode} (domain tree : List Block)
    (raw support : List (Wire n mode)) (b : Block) : Nat :=
  ((seats n raw).filter (fun i =>
    equivocates raw i || (seatVotes support i).any (fun o =>
      match headTarget? o with
      | none => false
      | some target => match resolveTarget mode domain target with
        | none => false
        | some B => decide (B ∈ tree) && decide (B.slot ≤ (headLabel? o).getD 0) &&
            Block.preceq b B))).length

-- The generated matcher bodies are definitionally equal.
private theorem hygiene_goldfishScoreOn_match_1_eq :
    hygieneEq% (@goldfishScoreOn) (@hygiene_goldfishScoreOn) := rfl

end AvailableChain.GridCO

namespace AvailableChain.GridCO

open AvailableChain.Generic

-- ROOT-DIGEST-2 option 3: use a private copy of the same matcher (BUILD B3).
private def hygiene_resolvedBefore {n : Nat} {mode : HeadMode}
    (st : State n mode) (o : Wire n mode) (cutoff : Time) : Bool :=
  match resolvedHead? st o with
  | none => false
  | some B => decide (B.slot ≤ (headLabel? o).getD 0) &&
      decide (stampVote st o < cutoff) && decide (stampBlock st B < cutoff)

-- The generated matcher bodies are definitionally equal.
private theorem hygiene_resolvedBefore_match_1_eq :
    hygieneEq% (@resolvedBefore) (@hygiene_goldfishScoreOn) := rfl

end AvailableChain.GridCO

attribute [local simp]
  AvailableChain.GridCO.hygiene_goldfishScoreOn_match_1_eq
  AvailableChain.GridCO.hygiene_resolvedBefore_match_1_eq

local macro "hygiene_split" : tactic =>
  `(tactic| (
    try rw [AvailableChain.GridCO.hygiene_goldfishScoreOn_match_1_eq] at *;
    try rw [AvailableChain.GridCO.hygiene_resolvedBefore_match_1_eq] at *;
    all_goals split))

local macro "hygiene_split" "at" h:ident : tactic =>
  `(tactic| (
    try rw [AvailableChain.GridCO.hygiene_goldfishScoreOn_match_1_eq] at *;
    try rw [AvailableChain.GridCO.hygiene_resolvedBefore_match_1_eq] at *;
    all_goals split at $h:ident))

@[expose] public section

namespace AvailableChain.GridCO

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

open AvailableChain.Generic
open AvailableChain.Statements.Generic

private theorem event_time_le_of_key_le
    {V : Type} {n : Nat} {P : ProtocolSpec n}
    (e f : Event V P.Object) (h : e.key ≤ f.key) :
    e.time ≤ f.time := by
  have hk := (Prod.Lex.toLex_le_toLex.mp h)
  rcases hk with hlt | ⟨heq, _⟩
  · exact le_of_lt hlt
  · exact le_of_eq heq

private theorem block_preceq_trans (A B C : Block)
    (hAB : Block.preceq A B = true)
    (hBC : Block.preceq B C = true) :
    Block.preceq A C = true := by
  induction C with
  | genesis =>
      have h : B = .genesis := by simpa [Block.preceq] using hBC
      subst B
      exact hAB
  | node parent slot r_slot root ih =>
      have h : B = .node parent slot r_slot root ∨ Block.preceq B parent = true := by
        simpa [Block.preceq, Bool.or_eq_true] using hBC
      rcases h with h | h
      · subst B
        exact hAB
      · have hAC := ih h
        simp [Block.preceq, hAC]

private theorem block_ancestors_compatible (A B C : Block)
    (hAC : Block.preceq A C = true)
    (hBC : Block.preceq B C = true) :
    Block.compatible A B = true := by
  induction C with
  | genesis =>
      have hA : A = .genesis := by simpa [Block.preceq] using hAC
      have hB : B = .genesis := by simpa [Block.preceq] using hBC
      subst A
      subst B
      decide
  | node parent slot r_slot root ih =>
      have hA : A = .node parent slot r_slot root ∨ Block.preceq A parent = true := by
        simpa [Block.preceq, Bool.or_eq_true] using hAC
      have hB : B = .node parent slot r_slot root ∨ Block.preceq B parent = true := by
        simpa [Block.preceq, Bool.or_eq_true] using hBC
      rcases hA with hA | hA
      · subst A
        simp [Block.compatible, hBC]
      · rcases hB with hB | hB
        · subst B
          simp [Block.compatible, hAC]
        · exact ih hA hB

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A target that conflicts with an ancestor also conflicts with every
descendant. This is the tree fact behind release-count monotonicity. -/
theorem conflict_mono_descendant (B K target : Block)
    (hBK : Block.preceq B K = true)
    (hconflict : Block.compatible target B = false) :
    Block.compatible target K = false := by
  by_cases h : Block.compatible target K = true
  · have hcase : Block.preceq target K = true ∨
        Block.preceq K target = true := by
      simpa [Block.compatible, Bool.or_eq_true] using h
    have hcomp : Block.compatible target B = true := by
      rcases hcase with hTK | hKT
      · exact block_ancestors_compatible target B K hTK hBK
      · have hBT := block_preceq_trans B K target hBK hKT
        simp [Block.compatible, hBT]
    rw [hcomp] at hconflict
    cases hconflict
  · cases hbool : Block.compatible target K <;> simp_all

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Release conflicts increase along a branch: a HEAD that conflicts with
an ancestor also conflicts with its descendant. -/
theorem releaseConflictSeats_mono (p : Params) {n : Nat}
    (st : State n) (r : Slot) (B K : Block)
    (hBK : Block.preceq B K = true) :
    releaseConflictSeats p st r B ⊆ releaseConflictSeats p st r K := by
  intro i hi
  simp only [releaseConflictSeats, Finset.mem_filter, List.mem_toFinset] at hi ⊢
  refine ⟨hi.1, ?_⟩
  obtain ⟨hnot, hany⟩ := Bool.and_eq_true_iff.mp hi.2
  obtain ⟨o, ho, hconf⟩ := List.any_eq_true.mp hany
  cases htarget : headTarget? o with
  | none => simp [htarget] at hconf
  | some target =>
      have hconfB : Block.compatible target B = false := by
        simpa [htarget] using hconf
      have hconfK := conflict_mono_descendant B K target hBK hconfB
      apply Bool.and_eq_true_iff.mpr
      constructor
      · exact hnot
      · apply List.any_eq_true.mpr
        exact ⟨o, ho, by simp [htarget, hconfK]⟩

theorem releaseCount_mono (p : Params) {n : Nat}
    (st : State n) (r : Slot) (B K : Block)
    (hBK : Block.preceq B K = true) :
    releaseCount p st r B ≤ releaseCount p st r K := by
  rw [releaseCount_eq_card, releaseCount_eq_card]
  exact Finset.card_le_card (releaseConflictSeats_mono p st r B K hBK)

/-- [ROOT-DIGEST-2 W1; DC legacy HEAD]
A prefix receives at least the Goldfish score of its descendant. The
same equivocation seats count on both sides. -/
theorem goldfishScore_mono {n : Nat} (tree : List Block)
    (raw support : List (Wire n)) (B K : Block)
    (hBK : Block.preceq B K = true) :
    goldfishScore tree raw support K ≤ goldfishScore tree raw support B := by
  unfold goldfishScore goldfishScoreOn
  apply List.Sublist.length_le
  apply List.monotone_filter_right
  intro i hi
  rcases Bool.or_eq_true_iff.mp hi with he | hb
  · exact Bool.or_eq_true_iff.mpr (Or.inl he)
  · apply Bool.or_eq_true_iff.mpr
    right
    obtain ⟨o, ho, hv⟩ := List.any_eq_true.mp hb
    apply List.any_eq_true.mpr
    refine ⟨o, ho, ?_⟩
    hygiene_split at hv
    · contradiction
    · hygiene_split at hv
      · contradiction
      · rename_i C _
        simp only [Bool.and_eq_true] at hv ⊢
        exact ⟨hv.1, block_preceq_trans B K C hBK hv.2⟩

theorem prefixSupport_mono (p : Params) {n : Nat} (st : State n)
    (r : Slot) (B K : Block) (hBK : Block.preceq B K = true) :
    prefixSupport p st r K ≤ prefixSupport p st r B := by
  exact goldfishScore_mono st.blocks (cleanSupport p st r)
    (cleanSupport p st r) B K hBK

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The map key of an obligation is its block and grid level. -/
def obligationKey (row : Block × Nat × Time) : Block × Nat :=
  (row.1, row.2.1)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
At most one deadline is stored for each block and level. -/
def UniqueObligationKeys {n : Nat} (st : State n) : Prop :=
  ∀ x ∈ st.obligations, ∀ y ∈ st.obligations,
    obligationKey x = obligationKey y → x = y

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Every non-genesis prefix at the same level has a deadline at least as
late as its descendant's. This combines closure and deadline order. -/
def PrefixDeadlineOrder {n : Nat} (st : State n) : Prop :=
  ∀ K g deadline, (K, g, deadline) ∈ st.obligations →
    ∀ B, B ≠ .genesis → Block.preceq B K = true →
      ∃ ancestorDeadline,
        (B, g, ancestorDeadline) ∈ st.obligations ∧
        deadline ≤ ancestorDeadline

theorem initial_prefix_deadline_order (n : Nat) :
    PrefixDeadlineOrder (initial n) := by
  simp [PrefixDeadlineOrder, initial]

theorem expire_prefix_deadline_order {n : Nat} (st : State n) (t : Time)
    (hprefix : PrefixDeadlineOrder st) :
    PrefixDeadlineOrder (expire st t) := by
  intro K g deadline hrow B hB hBK
  have hrowOld := (List.mem_filter.mp hrow).1
  obtain ⟨ancestorDeadline, hancestor, horder⟩ :=
    hprefix K g deadline hrowOld B hB hBK
  refine ⟨ancestorDeadline, ?_, horder⟩
  apply List.mem_filter.mpr
  have hkeep : t < deadline := by
    simpa using (List.mem_filter.mp hrow).2
  exact ⟨hancestor, by simpa using lt_of_lt_of_le hkeep horder⟩

theorem release_prefix_deadline_order (p : Params) {n : Nat}
    (st : State n) (r : Slot) (hprefix : PrefixDeadlineOrder st) :
    PrefixDeadlineOrder (release p st r) := by
  intro K g deadline hrow B hB hBK
  have hrowOld := (List.mem_filter.mp hrow).1
  obtain ⟨ancestorDeadline, hancestor, horder⟩ :=
    hprefix K g deadline hrowOld B hB hBK
  refine ⟨ancestorDeadline, ?_, horder⟩
  apply List.mem_filter.mpr
  refine ⟨hancestor, ?_⟩
  have hkeep : releaseCount p st r K < g := by
    simpa using (List.mem_filter.mp hrow).2
  simpa using lt_of_le_of_lt (releaseCount_mono p st r B K hBK) hkeep

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
All old deadlines are no later than a new gate deadline. This holds for
reachable states whose writes are at or before the present gate. -/
def DeadlinesAtMost {n : Nat} (st : State n) (limit : Time) : Prop :=
  ∀ b g d, (b, g, d) ∈ st.obligations → d ≤ limit

def DeadlineHorizon (p : Params) {n : Nat} (st : State n) : Prop :=
  DeadlinesAtMost st (st.now + lifetime p)

def DeadlinesAligned (p : Params) {n : Nat} (st : State n) : Prop :=
  ∀ row ∈ st.obligations, ∃ s, row.2.2 = releaseTime p s

def LiveRows {n : Nat} (st : State n) : Prop :=
  ∀ row ∈ st.obligations, st.now < row.2.2

theorem initial_deadline_horizon (p : Params) :
    DeadlineHorizon p (initial p.n) := by
  simp [DeadlineHorizon, DeadlinesAtMost, initial]

theorem initial_deadlines_aligned (p : Params) :
    DeadlinesAligned p (initial p.n) := by
  simp [DeadlinesAligned, initial]

theorem initial_live_rows (n : Nat) : LiveRows (initial n) := by
  simp [LiveRows, initial]

private theorem deadlineOf_le {n : Nat} (st : State n) (b : Block)
    (g : Nat) (limit : Time) (hbound : DeadlinesAtMost st limit) :
    (deadlineOf st b g).getD limit ≤ limit := by
  unfold deadlineOf
  cases hfind : st.obligations.find? (fun (target, level, _) =>
      target == b && level == g) with
  | none => simp
  | some row =>
      have hmem : row ∈ st.obligations := List.mem_of_find?_eq_some hfind
      simpa [hfind] using hbound row.1 row.2.1 row.2.2 hmem

private theorem writeObligation_shape {n : Nat} (st : State n)
    (b : Block) (g : Nat) (limit : Time)
    (hbound : DeadlinesAtMost st limit) :
    (writeObligation st b g limit).obligations =
      st.obligations.filter (fun (target, level, _) =>
        !(target == b && level == g)) ++ [(b, g, limit)] := by
  unfold writeObligation
  simp only [max_eq_right (deadlineOf_le st b g limit hbound)]

private theorem writeObligation_bound {n : Nat} (st : State n)
    (b : Block) (g : Nat) (limit : Time)
    (hbound : DeadlinesAtMost st limit) :
    DeadlinesAtMost (writeObligation st b g limit) limit := by
  intro K level d hrow
  rw [writeObligation_shape st b g limit hbound] at hrow
  rcases List.mem_append.mp hrow with hold | hnew
  · exact hbound K level d (List.mem_filter.mp hold).1
  · have h : (K, level, d) = (b, g, limit) := by simpa using hnew
    cases h
    exact le_refl _

private theorem writeKeys_bound {n : Nat} (st : State n)
    (keys : List (Block × Nat)) (limit : Time)
    (hbound : DeadlinesAtMost st limit) :
    DeadlinesAtMost (writeKeys st keys limit) limit := by
  induction keys generalizing st with
  | nil => exact hbound
  | cons key keys ih =>
      exact ih (writeObligation st key.1 key.2 limit)
        (writeObligation_bound st key.1 key.2 limit hbound)

theorem writeKeys_now {n : Nat} (st : State n)
    (keys : List (Block × Nat)) (limit : Time) :
    (writeKeys st keys limit).now = st.now := by
  induction keys generalizing st with
  | nil => rfl
  | cons key keys ih =>
      simp only [writeKeys_def, List.foldl_cons]
      exact (ih (writeObligation st key.1 key.2 limit)).trans rfl

private theorem write_preserves_limit_row {n : Nat} (st : State n)
    (K : Block) (g : Nat) (limit : Time) (key : Block × Nat)
    (hbound : DeadlinesAtMost st limit)
    (hrow : (K, g, limit) ∈ st.obligations) :
    (K, g, limit) ∈ (writeObligation st key.1 key.2 limit).obligations := by
  rw [writeObligation_shape st key.1 key.2 limit hbound]
  apply List.mem_append.mpr
  by_cases hkey : (K, g) = key
  · apply Or.inr
    simp [← hkey]
  · apply Or.inl
    apply List.mem_filter.mpr
    refine ⟨hrow, ?_⟩
    have hne : K ≠ key.1 ∨ g ≠ key.2 := by
      rcases key with ⟨b, level⟩
      simp only [Prod.mk.injEq, not_and_or] at hkey
      exact hkey
    rcases hne with hne | hne
    · simp [hne]
    · simp [hne]

private theorem writeKeys_preserves_limit_row {n : Nat} (st : State n)
    (keys : List (Block × Nat)) (K : Block) (g : Nat) (limit : Time)
    (hbound : DeadlinesAtMost st limit)
    (hrow : (K, g, limit) ∈ st.obligations) :
    (K, g, limit) ∈ (writeKeys st keys limit).obligations := by
  induction keys generalizing st with
  | nil => exact hrow
  | cons key keys ih =>
      exact ih (writeObligation st key.1 key.2 limit)
        (writeObligation_bound st key.1 key.2 limit hbound)
        (write_preserves_limit_row st K g limit key hbound hrow)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A bounded gate write installs every selected key with the new deadline. -/
theorem writeKeys_mem_of_key {n : Nat} (st : State n)
    (keys : List (Block × Nat)) (K : Block) (g : Nat) (limit : Time)
    (hbound : DeadlinesAtMost st limit)
    (hkey : (K, g) ∈ keys) :
    (K, g, limit) ∈ (writeKeys st keys limit).obligations := by
  induction keys generalizing st with
  | nil => simp at hkey
  | cons key keys ih =>
      rcases List.mem_cons.mp hkey with hfirst | htail
      · subst key
        apply writeKeys_preserves_limit_row
          (writeObligation st K g limit) keys K g limit
          (writeObligation_bound st K g limit hbound)
        rw [writeObligation_shape st K g limit hbound]
        simp
      · exact ih (writeObligation st key.1 key.2 limit)
          (writeObligation_bound st key.1 key.2 limit hbound) htail

private theorem writeKeys_mem_origin {n : Nat} (st : State n)
    (keys : List (Block × Nat)) (K : Block) (g : Nat) (d limit : Time)
    (hbound : DeadlinesAtMost st limit)
    (hrow : (K, g, d) ∈ (writeKeys st keys limit).obligations) :
    (K, g, d) ∈ st.obligations ∨ ((K, g) ∈ keys ∧ d = limit) := by
  induction keys generalizing st with
  | nil => exact Or.inl hrow
  | cons key keys ih =>
      have hstepBound := writeObligation_bound st key.1 key.2 limit hbound
      rcases ih (writeObligation st key.1 key.2 limit) hstepBound hrow with
        hstep | ⟨hkey, hd⟩
      · rw [writeObligation_shape st key.1 key.2 limit hbound] at hstep
        rcases List.mem_append.mp hstep with hold | hnew
        · exact Or.inl (List.mem_filter.mp hold).1
        · have heq : (K, g, d) = (key.1, key.2, limit) := by simpa using hnew
          have hkey' : (K, g) = key := by
            rcases key with ⟨b, level⟩
            simpa using congrArg (fun row : Block × Nat × Time =>
              (row.1, row.2.1)) heq
          exact Or.inr ⟨List.mem_cons.mpr (Or.inl hkey'),
            by cases heq; rfl⟩
      · exact Or.inr ⟨List.mem_cons.mpr (Or.inr hkey), hd⟩

private theorem writeKeys_mem_old_of_unwritten {n : Nat} (st : State n)
    (keys : List (Block × Nat)) (K : Block) (g : Nat) (d limit : Time)
    (hbound : DeadlinesAtMost st limit)
    (hrow : (K, g, d) ∈ st.obligations)
    (hkey : (K, g) ∉ keys) :
    (K, g, d) ∈ (writeKeys st keys limit).obligations := by
  induction keys generalizing st with
  | nil => exact hrow
  | cons key keys ih =>
      have hne : (K, g) ≠ key := by
        intro heq
        exact hkey (List.mem_cons.mpr (Or.inl heq))
      have htail : (K, g) ∉ keys := by
        intro hm
        exact hkey (List.mem_cons.mpr (Or.inr hm))
      apply ih (writeObligation st key.1 key.2 limit)
        (writeObligation_bound st key.1 key.2 limit hbound) ?_ htail
      rw [writeObligation_shape st key.1 key.2 limit hbound]
      apply List.mem_append.mpr
      apply Or.inl
      apply List.mem_filter.mpr
      refine ⟨hrow, ?_⟩
      rcases key with ⟨b, level⟩
      by_cases hb : K = b
      · have hg : g ≠ level := by
          intro heq
          exact hne (by simp [hb, heq])
        simp [hg]
      · simp [hb]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A complete gate write preserves ancestor closure and deadline order.
The key list can have any order: every written key gets the same new
deadline, and its non-genesis ancestors must also occur in the list. -/
theorem writeKeys_prefix_deadline_order {n : Nat} (st : State n)
    (keys : List (Block × Nat)) (limit : Time)
    (hprefix : PrefixDeadlineOrder st)
    (hbound : DeadlinesAtMost st limit)
    (hclosed : ∀ K g, (K, g) ∈ keys → ∀ B,
      B ≠ .genesis → Block.preceq B K = true → (B, g) ∈ keys) :
    PrefixDeadlineOrder (writeKeys st keys limit) := by
  intro K g d hrow B hB hBK
  rcases writeKeys_mem_origin st keys K g d limit hbound hrow with
    hold | ⟨hkey, hd⟩
  · obtain ⟨ancestorDeadline, hancestor, horder⟩ :=
      hprefix K g d hold B hB hBK
    by_cases hBkey : (B, g) ∈ keys
    · refine ⟨limit, writeKeys_mem_of_key st keys B g limit hbound hBkey, ?_⟩
      exact hbound K g d hold
    · exact ⟨ancestorDeadline,
        writeKeys_mem_old_of_unwritten st keys B g ancestorDeadline limit
          hbound hancestor hBkey, horder⟩
  · subst d
    exact ⟨limit, writeKeys_mem_of_key st keys B g limit hbound
      (hclosed K g hkey B hB hBK), le_refl _⟩

theorem writeKeys_deadlines_aligned (p : Params) {n : Nat}
    (st : State n) (keys : List (Block × Nat)) (limit : Time)
    (hbound : DeadlinesAtMost st limit)
    (haligned : DeadlinesAligned p st)
    (hlimit : ∃ s, limit = releaseTime p s) :
    DeadlinesAligned p (writeKeys st keys limit) := by
  intro row hrow
  rcases row with ⟨K, g, d⟩
  rcases writeKeys_mem_origin st keys K g d limit hbound hrow with
    hold | ⟨_, hd⟩
  · exact haligned (K, g, d) hold
  · obtain ⟨s, hs⟩ := hlimit
    exact ⟨s, by simpa [hd] using hs⟩

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The stored block domain contains each non-genesis ancestor of a stored
block. Admission preserves this when it requires a known parent. -/
def StoredPrefixClosed {n : Nat} (st : State n) : Prop :=
  ∀ K ∈ st.blocks, ∀ B, B ≠ .genesis →
    Block.preceq B K = true → B ∈ st.blocks

theorem initial_stored_prefix_closed (n : Nat) :
    StoredPrefixClosed (initial n) := by
  intro K hK B hB hBK
  have hKgenesis : K = .genesis := by simpa [initial] using hK
  subst K
  have hBgenesis : B = .genesis := by simpa [Block.preceq] using hBK
  exact False.elim (hB hBgenesis)

private theorem stored_prefix_closed_of_same_blocks {n : Nat}
    (st st' : State n) (hblocks : st'.blocks = st.blocks)
    (hclosed : StoredPrefixClosed st) : StoredPrefixClosed st' := by
  intro K hK B hB hBK
  rw [hblocks] at hK ⊢
  exact hclosed K hK B hB hBK

theorem admitVote_now (p : Params) {n : Nat} (st : State n)
    (o : Wire n) : (admitVote p st o).now = st.now := by
  unfold admitVote
  hygiene_split <;> simp_all
  hygiene_split <;> rfl

theorem admitVote_stored_prefix_closed (p : Params) {n : Nat}
    (st : State n) (o : Wire n) (hclosed : StoredPrefixClosed st) :
    StoredPrefixClosed (admitVote p st o) :=
  stored_prefix_closed_of_same_blocks st (admitVote p st o)
    (admitVote_blocks p st o) hclosed

private theorem fold_admitVote_blocks (p : Params) {n : Nat}
    (raw : List (HeadWire n)) (st : State n) :
    (raw.foldl (fun acc row => admitVote p acc (fromHead row)) st).blocks =
      st.blocks := by
  induction raw generalizing st with
  | nil => rfl
  | cons row raw ih =>
      simpa only [List.foldl_cons] using
        (ih (admitVote p st (fromHead row))).trans (admitVote_blocks p st (fromHead row))

private theorem fold_admitVote_now (p : Params) {n : Nat}
    (raw : List (HeadWire n)) (st : State n) :
    (raw.foldl (fun acc row => admitVote p acc (fromHead row)) st).now =
      st.now := by
  induction raw generalizing st with
  | nil => rfl
  | cons row raw ih =>
      simpa only [List.foldl_cons] using
        (ih (admitVote p st (fromHead row))).trans (admitVote_now p st (fromHead row))

theorem admitProposal_now (p : Params) {n : Nat}
    (st : State n) (o : Wire n) (b : Block) (raw : List (HeadWire n)) :
    (admitProposal p st o b raw).now = st.now := by
  let bad : Bool :=
    b.slot > (st.now / (4 * p.Δ)).toNat || !blockKnown st b.parent ||
      b ∈ st.blocks || !(b.parent.slot < b.slot) ||
      !(match o.auth with
        | .proposer s => s == b.slot
        | _ => false)
  let st' : State n := { st with
    blocks := st.blocks ++ [b]
    blockStamp := st.blockStamp ++ [(b, st.now)]
    proposals := st.proposals ++ [o] }
  change (if bad then st else
    raw.foldl (fun acc row => admitVote p acc (fromHead row)) st').now = st.now
  hygiene_split
  · rfl
  · exact fold_admitVote_now p raw st'

theorem process_now (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    (process p st o).now = st.now := by
  cases o with
  | mk auth payload =>
      cases auth <;> cases payload <;> simp only [process]
      all_goals first
        | exact admitVote_now p st _
        | exact admitProposal_now p st _ _ _

theorem process_obligations (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    (process p st o).obligations = st.obligations := by
  cases o with
  | mk auth payload =>
      cases auth <;> cases payload <;> simp only [process]
      all_goals first
        | exact admitVote_obligations p st _
        | exact admitProposal_obligations p st _ _ _

theorem process_deadline_horizon (p : Params) {n : Nat}
    (st : State n) (o : Wire n) (horizon : DeadlineHorizon p st) :
    DeadlineHorizon p (process p st o) := by
  simpa [DeadlineHorizon, DeadlinesAtMost,
    process_now, process_obligations] using horizon

theorem process_deadlines_aligned (p : Params) {n : Nat}
    (st : State n) (o : Wire n) (haligned : DeadlinesAligned p st) :
    DeadlinesAligned p (process p st o) := by
  simpa [DeadlinesAligned, process_obligations] using haligned

theorem process_live_rows (p : Params) {n : Nat}
    (st : State n) (o : Wire n) (hlive : LiveRows st) :
    LiveRows (process p st o) := by
  simpa [LiveRows, process_now, process_obligations] using hlive

theorem admitProposal_stored_prefix_closed (p : Params) {n : Nat}
    (st : State n) (o : Wire n) (b : Block)
    (raw : List (HeadWire n)) (hclosed : StoredPrefixClosed st) :
    StoredPrefixClosed (admitProposal p st o b raw) := by
  by_cases hknown : blockKnown st b.parent = true
  · let bad : Bool :=
      b.slot > (st.now / (4 * p.Δ)).toNat || !blockKnown st b.parent ||
        b ∈ st.blocks || !(b.parent.slot < b.slot) ||
        !(match o.auth with
          | .proposer s => s == b.slot
          | _ => false)
    let st' : State n := { st with
      blocks := st.blocks ++ [b]
      blockStamp := st.blockStamp ++ [(b, st.now)]
      proposals := st.proposals ++ [o] }
    change StoredPrefixClosed
      (if bad then st else raw.foldl (fun acc row => admitVote p acc (fromHead row)) st')
    by_cases hbad : bad = true
    · simpa [hbad] using hclosed
    · have hfalse : bad = false := by cases h : bad <;> simp_all
      have hfold : StoredPrefixClosed
          (raw.foldl (fun acc row => admitVote p acc (fromHead row)) st') := by
        apply stored_prefix_closed_of_same_blocks st'
        · exact fold_admitVote_blocks p raw st'
        · intro K hK B hB hBK
          rcases List.mem_append.mp hK with hold | hnew
          · exact List.mem_append.mpr (Or.inl (hclosed K hold B hB hBK))
          · have hKeq : K = b := by simpa using hnew
            subst K
            have hcase : B = b ∨ Block.preceq B b.parent = true := by
              cases b with
              | genesis => exact False.elim (hB (by simpa [Block.preceq] using hBK))
              | node parent slot r_slot root =>
                  simpa [Block.preceq, Bool.or_eq_true] using! hBK
            rcases hcase with heq | hparent
            · exact List.mem_append.mpr (Or.inr (by simp [heq]))
            · have hparentKnown : b.parent ∈ st.blocks := by
                simpa [blockKnown] using hknown
              exact List.mem_append.mpr
                (Or.inl (hclosed b.parent hparentKnown B hB hparent))
      simpa [hfalse] using hfold
  · have hfalse : blockKnown st b.parent = false := by
      cases hbool : blockKnown st b.parent <;> simp_all
    simpa [admitProposal, hfalse] using hclosed

theorem process_stored_prefix_closed (p : Params) {n : Nat}
    (st : State n) (o : Wire n) (hclosed : StoredPrefixClosed st) :
    StoredPrefixClosed (process p st o) := by
  cases o with
  | mk auth payload =>
      cases auth <;> cases payload <;> simp only [process]
      all_goals first
        | exact admitVote_stored_prefix_closed p st _ hclosed
        | exact admitProposal_stored_prefix_closed p st _ _ _ hclosed
        | exact hclosed

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Slow admission is closed under containment of non-genesis prefixes. -/
theorem slowEligible_mono (p : Params) {n : Nat} (st : State n)
    (r : Slot) (B K : Block) (hBK : Block.preceq B K = true)
    (hK : slowEligible p st r K = true) : slowEligible p st r B = true := by
  obtain ⟨hlen, hall⟩ := Bool.and_eq_true_iff.mp hK
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hlen, List.all_eq_true.mpr ?_⟩
  intro j hj
  have h := List.all_eq_true.mp hall j hj
  cases hs : savedGenuine st (r - (j + 1)) with
  | none => simp [hs] at h
  | some result =>
    cases result with
    | none => simp [hs] at h
    | some C => exact block_preceq_trans B K C hBK (by simpa [hs] using h)

theorem admissionLevels_mono (p : Params) {n : Nat} (st : State n)
    (r : Slot) (B K : Block) (hBK : Block.preceq B K = true) :
    ∀ g ∈ admissionLevels p st r K, g ∈ admissionLevels p st r B := by
  intro g hg
  have hscore := prefixSupport_mono p st r B K hBK
  unfold admissionLevels at hg ⊢
  cases hmode : LeasePolicy.slowArming with
  | true =>
    simp only [hmode, ↓reduceIte] at hg ⊢
    hygiene_split at hg
    · rename_i ht
      have htest : (releaseThreshold p ≤ prefixSupport p st r B ||
          slowEligible p st r B) = true := by
        rcases Bool.or_eq_true_iff.mp ht with hf | hs
        · apply Bool.or_eq_true_iff.mpr; left
          exact decide_eq_true (le_trans (of_decide_eq_true hf) hscore)
        · exact Bool.or_eq_true_iff.mpr (Or.inr (slowEligible_mono p st r B K hBK hs))
      simpa [htest] using hg
    · simp at hg
  | false =>
    simp only [hmode, Bool.false_eq_true, ↓reduceIte] at hg ⊢
    obtain ⟨hrange, ht⟩ := List.mem_filter.mp hg
    obtain ⟨hgrid, hcount⟩ : g ∈ p.grid ∧ g ≤ prefixSupport p st r K := by simpa using ht
    exact List.mem_filter.mpr ⟨hrange, by simp [hgrid, le_trans hcount hscore]⟩

theorem gateWriteKeys_closed (p : Params) {n : Nat} (st : State n)
    (r : Slot) (C : Block) (hblocks : StoredPrefixClosed st) :
    ∀ K g, (K, g) ∈ gateWriteKeys p st r C → ∀ B,
      B ≠ .genesis → Block.preceq B K = true →
        (B, g) ∈ gateWriteKeys p st r C := by
  intro K g hkey B hB hBK
  obtain ⟨K', hK', hmap⟩ := List.mem_flatMap.mp hkey
  obtain ⟨g', hg', hpair⟩ := List.mem_map.mp hmap
  have ⟨hKeq, hgeq⟩ : K' = K ∧ g' = g := by
    simpa using hpair
  subst K'
  subst g'
  have hK : K ∈ st.blocks := (List.mem_filter.mp hK').1
  have hKC : Block.preceq K C = true := by
    have hp := (List.mem_filter.mp hK').2
    exact (Bool.and_eq_true_iff.mp hp).2
  have hBstored : B ∈ st.blocks := hblocks K hK B hB hBK
  have hBC : Block.preceq B C = true := block_preceq_trans B K C hBK hKC
  apply List.mem_flatMap.mpr
  refine ⟨B, List.mem_filter.mpr ⟨hBstored, by simp [hB, hBC]⟩, ?_⟩
  exact List.mem_map.mpr ⟨g, admissionLevels_mono p st r B K hBK g hg', rfl⟩

theorem gate_eq_writeKeys (p : Params) {n : Nat} (st : State n)
    (r : Slot) (C : Block)
    (hc : confirmation p st r = some C)
    (hguard : st.obligations.any (fun (target, _, _) =>
      !Block.compatible target C) = false) :
    gate p st r =
      writeKeys { st with
        goldfishRecord := advance st.goldfishRecord C
        genuine := recordGenuine st r (some C)
        stableRecord := advance st.stableRecord C }
        (gateWriteKeys p st r C) (gateTime p r + lifetime p) := by
  rw [gate_eq_from_genesis]
  exact gateFrom_eq_writeKeys p .genesis st r C hc hguard

theorem gate_deadlines_at_most (p : Params) {n : Nat}
    (st : State n) (r : Slot)
    (hbound : DeadlinesAtMost st (gateTime p r + lifetime p)) :
    DeadlinesAtMost (gate p st r) (gateTime p r + lifetime p) := by
  cases hc : confirmation p st r with
  | none => simpa [gate, hc] using! hbound
  | some C =>
      cases hguard : st.obligations.any (fun (target, _, _) =>
          !Block.compatible target C) with
      | true => simpa [gate, hc, hguard, DeadlinesAtMost] using hbound
      | false =>
          rw [gate_eq_writeKeys p st r C hc hguard]
          apply writeKeys_bound
          simpa [DeadlinesAtMost] using hbound

theorem gate_deadlines_aligned (p : Params) {n : Nat}
    (st : State n) (r : Slot)
    (hbound : DeadlinesAtMost st (gateTime p r + lifetime p))
    (haligned : DeadlinesAligned p st) :
    DeadlinesAligned p (gate p st r) := by
  cases hc : confirmation p st r with
  | none => simpa [gate, hc] using! haligned
  | some C =>
      cases hguard : st.obligations.any (fun (target, _, _) =>
          !Block.compatible target C) with
      | true => simpa [gate, hc, hguard, DeadlinesAligned] using haligned
      | false =>
          rw [gate_eq_writeKeys p st r C hc hguard]
          apply writeKeys_deadlines_aligned p
          · simpa [DeadlinesAtMost] using hbound
          · simpa [DeadlinesAligned] using haligned
          · exact ⟨r + p.m, deadline_eq_release p r⟩

theorem gate_live_rows (p : Params) {n : Nat}
    (st : State n) (r : Slot)
    (hnow : st.now = gateTime p r)
    (hbound : DeadlinesAtMost st (gateTime p r + lifetime p))
    (hlive : LiveRows st) :
    LiveRows (gate p st r) := by
  cases hc : confirmation p st r with
  | none => simpa [gate, hc] using! hlive
  | some C =>
      cases hguard : st.obligations.any (fun (target, _, _) =>
          !Block.compatible target C) with
      | true => simpa [gate, hc, hguard, LiveRows] using hlive
      | false =>
          rw [gate_eq_writeKeys p st r C hc hguard]
          intro row hrow
          rcases row with ⟨K, g, d⟩
          have hnow' :
              (writeKeys
                { st with
                  goldfishRecord := advance st.goldfishRecord C
                  genuine := recordGenuine st r (some C)
                  stableRecord := advance st.stableRecord C }
                (gateWriteKeys p st r C)
                (gateTime p r + lifetime p)).now = st.now := by
            exact writeKeys_now _ _ _
          rw [hnow', hnow]
          rcases writeKeys_mem_origin
            { st with
              goldfishRecord := advance st.goldfishRecord C
              genuine := recordGenuine st r (some C)
              stableRecord := advance st.stableRecord C }
            (gateWriteKeys p st r C) K g d
            (gateTime p r + lifetime p)
            (by simpa [DeadlinesAtMost] using hbound) hrow with
            hold | ⟨_, hd⟩
          · exact hnow ▸ hlive (K, g, d) hold
          · subst d
            linarith [lifetime_pos p]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The full gate write retains ancestor rows and their deadline order.
The input bound is the reachable-time fact that previous deadlines do not
exceed the deadline of this gate. -/
theorem gate_prefix_deadline_order (p : Params) {n : Nat}
    (st : State n) (r : Slot)
    (hprefix : PrefixDeadlineOrder st)
    (hblocks : StoredPrefixClosed st)
    (hbound : DeadlinesAtMost st (gateTime p r + lifetime p)) :
    PrefixDeadlineOrder (gate p st r) := by
  cases hc : confirmation p st r with
  | none => simpa [gate, hc] using! hprefix
  | some C =>
      cases hguard : st.obligations.any (fun (target, _, _) =>
          !Block.compatible target C) with
      | true => simpa [gate, hc, hguard, PrefixDeadlineOrder] using hprefix
      | false =>
          rw [gate_eq_writeKeys p st r C hc hguard]
          apply writeKeys_prefix_deadline_order
          · simpa [PrefixDeadlineOrder] using hprefix
          · simpa [DeadlinesAtMost] using hbound
          · exact gateWriteKeys_closed p st r C hblocks

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Every pair of stored obligation targets lies on one chain. -/
def ComparableTargets {n : Nat} (st : State n) : Prop :=
  ∀ K g d, (K, g, d) ∈ st.obligations →
    ∀ B level expiry, (B, level, expiry) ∈ st.obligations →
      Block.compatible K B = true

private theorem compatible_symm (A B : Block) :
    Block.compatible A B = Block.compatible B A := by
  simp [Block.compatible, Bool.or_comm]

private theorem compatible_with_prefix (A B C : Block)
    (hAC : Block.compatible A C = true)
    (hBC : Block.preceq B C = true) :
    Block.compatible A B = true := by
  rcases Bool.or_eq_true_iff.mp hAC with hA | hC
  · exact block_ancestors_compatible A B C hA hBC
  · have hBA := block_preceq_trans B C A hBC hC
    simp [Block.compatible, hBA]

private theorem writeKeys_comparable_targets {n : Nat} (st : State n)
    (keys : List (Block × Nat)) (limit : Time)
    (hbound : DeadlinesAtMost st limit)
    (hold : ComparableTargets st)
    (hcross : ∀ K g d, (K, g, d) ∈ st.obligations →
      ∀ key ∈ keys, Block.compatible K key.1 = true)
    (hnew : ∀ key ∈ keys, ∀ other ∈ keys,
      Block.compatible key.1 other.1 = true) :
    ComparableTargets (writeKeys st keys limit) := by
  intro K g d hK B level expiry hB
  rcases writeKeys_mem_origin st keys K g d limit hbound hK with
    hKold | ⟨hKnew, _⟩
  · rcases writeKeys_mem_origin st keys B level expiry limit hbound hB with
      hBold | ⟨hBnew, _⟩
    · exact hold K g d hKold B level expiry hBold
    · exact hcross K g d hKold (B, level) hBnew
  · rcases writeKeys_mem_origin st keys B level expiry limit hbound hB with
      hBold | ⟨hBnew, _⟩
    · rw [compatible_symm]
      exact hcross B level expiry hBold (K, g) hKnew
    · exact hnew (K, g) hKnew (B, level) hBnew

theorem initial_comparable_targets (n : Nat) :
    ComparableTargets (initial n) := by
  simp [ComparableTargets, initial]

theorem expire_comparable_targets {n : Nat} (st : State n) (t : Time)
    (h : ComparableTargets st) : ComparableTargets (expire st t) := by
  intro K g d hK B level expiry hB
  exact h K g d (List.mem_filter.mp hK).1
    B level expiry (List.mem_filter.mp hB).1

theorem release_comparable_targets (p : Params) {n : Nat}
    (st : State n) (r : Slot) (h : ComparableTargets st) :
    ComparableTargets (release p st r) := by
  intro K g d hK B level expiry hB
  exact h K g d (release_subset p st r (K, g, d) hK)
    B level expiry (release_subset p st r (B, level, expiry) hB)

theorem gate_comparable_targets (p : Params) {n : Nat}
    (st : State n) (r : Slot)
    (hold : ComparableTargets st)
    (hbound : DeadlinesAtMost st (gateTime p r + lifetime p)) :
    ComparableTargets (gate p st r) := by
  cases hc : confirmation p st r with
  | none => simpa [gate, hc] using! hold
  | some C =>
      cases hguard : st.obligations.any (fun (target, _, _) =>
          !Block.compatible target C) with
      | true => simpa [gate, hc, hguard, ComparableTargets] using hold
      | false =>
          rw [gate_eq_writeKeys p st r C hc hguard]
          apply writeKeys_comparable_targets
          · simpa [DeadlinesAtMost] using hbound
          · simpa [ComparableTargets] using hold
          · intro K g d hrow key hkey
            obtain ⟨b, hb, hmap⟩ := List.mem_flatMap.mp hkey
            obtain ⟨level, _, hpair⟩ := List.mem_map.mp hmap
            have ⟨hbeq, _⟩ : b = key.1 ∧ level = key.2 := by
              exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
            have hpre : Block.preceq key.1 C = true := by
              have hp := (List.mem_filter.mp hb).2
              exact hbeq ▸ (Bool.and_eq_true_iff.mp hp).2
            have hKC : Block.compatible K C = true := by
              have hall := List.any_eq_false.mp hguard (K, g, d) hrow
              simpa using hall
            exact compatible_with_prefix K key.1 C hKC hpre
          · intro key hkey other hother
            obtain ⟨b, hb, hmap⟩ := List.mem_flatMap.mp hkey
            obtain ⟨level, _, hpair⟩ := List.mem_map.mp hmap
            have hkeypre : Block.preceq key.1 C = true := by
              have ⟨hbeq, _⟩ : b = key.1 ∧ level = key.2 := by
                exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
              exact hbeq ▸ (Bool.and_eq_true_iff.mp (List.mem_filter.mp hb).2).2
            obtain ⟨b', hb', hmap'⟩ := List.mem_flatMap.mp hother
            obtain ⟨level', _, hpair'⟩ := List.mem_map.mp hmap'
            have hotherpre : Block.preceq other.1 C = true := by
              have ⟨hbeq, _⟩ : b' = other.1 ∧ level' = other.2 := by
                exact ⟨congrArg Prod.fst hpair', congrArg Prod.snd hpair'⟩
              exact hbeq ▸ (Bool.and_eq_true_iff.mp (List.mem_filter.mp hb').2).2
            exact block_ancestors_compatible key.1 other.1 C hkeypre hotherpre

private theorem foldl_now {n : Nat} {α : Type}
    (f : State n → α → State n) (xs : List α) (st : State n)
    (hf : ∀ acc x, (f acc x).now = acc.now) :
    (xs.foldl f st).now = st.now := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih, hf]

theorem gate_now (p : Params) {n : Nat} (st : State n) (r : Slot) :
    (gate p st r).now = st.now := by
  cases hc : confirmation p st r with
  | none => simp [gate, hc]
  | some C =>
      cases hguard : st.obligations.any (fun (target, _, _) =>
          !Block.compatible target C) with
      | true => simp [gate, hc, hguard]
      | false =>
          simp only [gate, hc, hguard]
          apply foldl_now
          intro acc b
          apply foldl_now
          intro acc g
          rfl

theorem gate_blocks (p : Params) {n : Nat} (st : State n) (r : Slot) :
    (gate p st r).blocks = st.blocks :=
  gateFrom_blocks p .genesis st r

theorem clock_blocks (p : Params) {n : Nat} (st : State n) (t : Time) :
    (clock p st t).blocks = st.blocks := by
  let s0 := expire { st with now := t } t
  let fSlot := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
  let s1 := if 0 ≤ t - 3 * p.Δ && t == freezeTime p fSlot then
    freeze p s0 fSlot else s0
  let eSlot := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
  let s2 := if 0 ≤ t - 2 * p.Δ && t == earlyTime p eSlot then
    { s1 with early := s1.early ++ [(eSlot, earlyVotes p s1 eSlot)] }
    else s1
  let qSlot := ((t - 5 * p.Δ) / (4 * p.Δ)).toNat
  let s3 := if 0 ≤ t - 5 * p.Δ && t == releaseTime p qSlot then
    release p s2 qSlot else s2
  let dSlot := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
  change (if 0 ≤ t - 6 * p.Δ && t == gateTime p dSlot then
    gate p s3 dSlot else s3).blocks = st.blocks
  have h0 : s0.blocks = st.blocks := rfl
  have h1 : s1.blocks = s0.blocks := by
    dsimp [s1]
    hygiene_split <;> rfl
  have h2 : s2.blocks = s1.blocks := by
    dsimp [s2]
    hygiene_split <;> rfl
  have h3 : s3.blocks = s2.blocks := by
    dsimp [s3]
    hygiene_split <;> rfl
  hygiene_split
  · exact (gate_blocks p s3 dSlot).trans (h3.trans (h2.trans (h1.trans h0)))
  · exact h3.trans (h2.trans (h1.trans h0))

theorem clock_deadline_horizon (p : Params) {n : Nat}
    (st : State n) (t : Time)
    (horizon : DeadlineHorizon p st) (htime : st.now ≤ t) :
    DeadlineHorizon p (clock p st t) := by
  let s0 := expire { st with now := t } t
  let fSlot := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
  let s1 := if 0 ≤ t - 3 * p.Δ && t == freezeTime p fSlot then
    freeze p s0 fSlot else s0
  let eSlot := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
  let s2 := if 0 ≤ t - 2 * p.Δ && t == earlyTime p eSlot then
    { s1 with early := s1.early ++ [(eSlot, earlyVotes p s1 eSlot)] }
    else s1
  let qSlot := ((t - 5 * p.Δ) / (4 * p.Δ)).toNat
  let s3 := if 0 ≤ t - 5 * p.Δ && t == releaseTime p qSlot then
    release p s2 qSlot else s2
  let dSlot := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
  change DeadlineHorizon p
    (if 0 ≤ t - 6 * p.Δ && t == gateTime p dSlot then
      gate p s3 dSlot else s3)
  have h0now : s0.now = t := rfl
  have h0bound : DeadlinesAtMost s0 (t + lifetime p) := by
    intro b g d hrow
    have hold : (b, g, d) ∈ st.obligations :=
      (List.mem_filter.mp hrow).1
    have hd := horizon b g d hold
    dsimp [DeadlineHorizon] at horizon
    linarith
  have h1now : s1.now = t := by
    dsimp [s1]
    hygiene_split <;> exact h0now
  have h1bound : DeadlinesAtMost s1 (t + lifetime p) := by
    dsimp [s1]
    hygiene_split
    · simpa [freeze, DeadlinesAtMost] using h0bound
    · exact h0bound
  have h2now : s2.now = t := by
    dsimp [s2]
    hygiene_split <;> exact h1now
  have h2bound : DeadlinesAtMost s2 (t + lifetime p) := by
    dsimp [s2]
    hygiene_split
    · simpa [DeadlinesAtMost] using h1bound
    · exact h1bound
  have h3now : s3.now = t := by
    dsimp [s3]
    hygiene_split <;> exact h2now
  have h3bound : DeadlinesAtMost s3 (t + lifetime p) := by
    dsimp [s3]
    hygiene_split
    · intro b g d hrow
      exact h2bound b g d (release_subset p s2 qSlot (b, g, d) hrow)
    · exact h2bound
  hygiene_split
  · rename_i hcond
    have ht : t = gateTime p dSlot := by
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp hcond).2
    have hgate := gate_deadlines_at_most p s3 dSlot
      (by simpa [ht] using h3bound)
    simpa [DeadlineHorizon, gate_now, h3now, ht] using hgate
  · simpa [DeadlineHorizon, h3now] using h3bound

theorem clock_now (p : Params) {n : Nat} (st : State n) (t : Time) :
    (clock p st t).now = t := by
  let s0 := expire { st with now := t } t
  let fSlot := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
  let s1 := if 0 ≤ t - 3 * p.Δ && t == freezeTime p fSlot then
    freeze p s0 fSlot else s0
  let eSlot := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
  let s2 := if 0 ≤ t - 2 * p.Δ && t == earlyTime p eSlot then
    { s1 with early := s1.early ++ [(eSlot, earlyVotes p s1 eSlot)] }
    else s1
  let qSlot := ((t - 5 * p.Δ) / (4 * p.Δ)).toNat
  let s3 := if 0 ≤ t - 5 * p.Δ && t == releaseTime p qSlot then
    release p s2 qSlot else s2
  let dSlot := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
  change (if 0 ≤ t - 6 * p.Δ && t == gateTime p dSlot then
    gate p s3 dSlot else s3).now = t
  have h0 : s0.now = t := rfl
  have h1 : s1.now = t := by dsimp [s1]; hygiene_split <;> exact h0
  have h2 : s2.now = t := by dsimp [s2]; hygiene_split <;> exact h1
  have h3 : s3.now = t := by dsimp [s3]; hygiene_split <;> exact h2
  hygiene_split
  · exact (gate_now p s3 dSlot).trans h3
  · exact h3

theorem clock_stored_prefix_closed (p : Params) {n : Nat}
    (st : State n) (t : Time) (hclosed : StoredPrefixClosed st) :
    StoredPrefixClosed (clock p st t) :=
  stored_prefix_closed_of_same_blocks st (clock p st t)
    (clock_blocks p st t) hclosed

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The clock state just before a possible gate at time `t`. -/
def clockPreGate (p : Params) {n : Nat} (st : State n) (t : Time) : State n :=
  let st := expire { st with now := t } t
  let fSlot := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 3 * p.Δ && t == freezeTime p fSlot then
    freeze p st fSlot else st
  let eSlot := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
  let st := if 0 ≤ t - 2 * p.Δ && t == earlyTime p eSlot then
    { st with early := st.early ++ [(eSlot, earlyVotes p st eSlot)] }
    else st
  let qSlot := ((t - 5 * p.Δ) / (4 * p.Δ)).toNat
  if 0 ≤ t - 5 * p.Δ && t == releaseTime p qSlot then
    release p st qSlot else st

theorem clock_eq_gate_prestate (p : Params) {n : Nat}
    (st : State n) (t : Time) :
    clock p st t =
      let dSlot := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
      if 0 ≤ t - 6 * p.Δ && t == gateTime p dSlot then
        gate p (clockPreGate p st t) dSlot
      else clockPreGate p st t := rfl

theorem clockPreGate_invariants (p : Params) {n : Nat}
    (st : State n) (t : Time)
    (hprefix : PrefixDeadlineOrder st)
    (hcomparable : ComparableTargets st)
    (hblocks : StoredPrefixClosed st)
    (hhorizon : DeadlineHorizon p st)
    (htime : st.now ≤ t) :
    PrefixDeadlineOrder (clockPreGate p st t) ∧
    ComparableTargets (clockPreGate p st t) ∧
    StoredPrefixClosed (clockPreGate p st t) ∧
    DeadlinesAtMost (clockPreGate p st t) (t + lifetime p) ∧
    (clockPreGate p st t).now = t := by
  let s0 := expire { st with now := t } t
  let fSlot := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
  let s1 := if 0 ≤ t - 3 * p.Δ && t == freezeTime p fSlot then
    freeze p s0 fSlot else s0
  let eSlot := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
  let s2 := if 0 ≤ t - 2 * p.Δ && t == earlyTime p eSlot then
    { s1 with early := s1.early ++ [(eSlot, earlyVotes p s1 eSlot)] }
    else s1
  let qSlot := ((t - 5 * p.Δ) / (4 * p.Δ)).toNat
  let s3 := if 0 ≤ t - 5 * p.Δ && t == releaseTime p qSlot then
    release p s2 qSlot else s2
  change PrefixDeadlineOrder s3 ∧ ComparableTargets s3 ∧
    StoredPrefixClosed s3 ∧ DeadlinesAtMost s3 (t + lifetime p) ∧ s3.now = t
  have h0prefix : PrefixDeadlineOrder s0 := by
    exact expire_prefix_deadline_order _ t
      (by simpa [PrefixDeadlineOrder] using hprefix)
  have h0comp : ComparableTargets s0 := by
    exact expire_comparable_targets _ t
      (by simpa [ComparableTargets] using hcomparable)
  have h0blocks : StoredPrefixClosed s0 := by
    apply stored_prefix_closed_of_same_blocks st s0 rfl hblocks
  have h0bound : DeadlinesAtMost s0 (t + lifetime p) := by
    intro b g d hrow
    have hold : (b, g, d) ∈ st.obligations :=
      (List.mem_filter.mp hrow).1
    have hd := hhorizon b g d hold
    dsimp [DeadlineHorizon] at hhorizon
    linarith
  have h0now : s0.now = t := rfl
  have h1prefix : PrefixDeadlineOrder s1 := by
    dsimp [s1]
    hygiene_split
    · simpa [freeze, PrefixDeadlineOrder] using h0prefix
    · exact h0prefix
  have h1comp : ComparableTargets s1 := by
    dsimp [s1]
    hygiene_split
    · simpa [freeze, ComparableTargets] using h0comp
    · exact h0comp
  have h1blocks : StoredPrefixClosed s1 := by
    dsimp [s1]
    hygiene_split
    · simpa [freeze, StoredPrefixClosed] using h0blocks
    · exact h0blocks
  have h1bound : DeadlinesAtMost s1 (t + lifetime p) := by
    dsimp [s1]
    hygiene_split
    · simpa [freeze, DeadlinesAtMost] using h0bound
    · exact h0bound
  have h1now : s1.now = t := by dsimp [s1]; hygiene_split <;> exact h0now
  have h2prefix : PrefixDeadlineOrder s2 := by
    dsimp [s2]
    hygiene_split
    · simpa [PrefixDeadlineOrder] using h1prefix
    · exact h1prefix
  have h2comp : ComparableTargets s2 := by
    dsimp [s2]
    hygiene_split
    · simpa [ComparableTargets] using h1comp
    · exact h1comp
  have h2blocks : StoredPrefixClosed s2 := by
    dsimp [s2]
    hygiene_split
    · simpa [StoredPrefixClosed] using h1blocks
    · exact h1blocks
  have h2bound : DeadlinesAtMost s2 (t + lifetime p) := by
    dsimp [s2]
    hygiene_split
    · simpa [DeadlinesAtMost] using h1bound
    · exact h1bound
  have h2now : s2.now = t := by dsimp [s2]; hygiene_split <;> exact h1now
  have h3prefix : PrefixDeadlineOrder s3 := by
    dsimp [s3]
    hygiene_split
    · exact release_prefix_deadline_order p s2 qSlot h2prefix
    · exact h2prefix
  have h3comp : ComparableTargets s3 := by
    dsimp [s3]
    hygiene_split
    · exact release_comparable_targets p s2 qSlot h2comp
    · exact h2comp
  have h3blocks : StoredPrefixClosed s3 := by
    dsimp [s3]
    hygiene_split
    · simpa [release, StoredPrefixClosed] using h2blocks
    · exact h2blocks
  have h3bound : DeadlinesAtMost s3 (t + lifetime p) := by
    dsimp [s3]
    hygiene_split
    · intro b g d hrow
      exact h2bound b g d (release_subset p s2 qSlot (b, g, d) hrow)
    · exact h2bound
  have h3now : s3.now = t := by dsimp [s3]; hygiene_split <;> exact h2now
  exact ⟨h3prefix, h3comp, h3blocks, h3bound, h3now⟩

theorem clockPreGate_deadlines_aligned (p : Params) {n : Nat}
    (st : State n) (t : Time)
    (haligned : DeadlinesAligned p st) :
    DeadlinesAligned p (clockPreGate p st t) := by
  let s0 := expire { st with now := t } t
  let fSlot := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
  let s1 := if 0 ≤ t - 3 * p.Δ && t == freezeTime p fSlot then
    freeze p s0 fSlot else s0
  let eSlot := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
  let s2 := if 0 ≤ t - 2 * p.Δ && t == earlyTime p eSlot then
    { s1 with early := s1.early ++ [(eSlot, earlyVotes p s1 eSlot)] }
    else s1
  let qSlot := ((t - 5 * p.Δ) / (4 * p.Δ)).toNat
  let s3 := if 0 ≤ t - 5 * p.Δ && t == releaseTime p qSlot then
    release p s2 qSlot else s2
  change DeadlinesAligned p s3
  have h0 : DeadlinesAligned p s0 := by
    intro row hrow
    exact haligned row (List.mem_filter.mp hrow).1
  have h1 : DeadlinesAligned p s1 := by
    dsimp [s1]
    hygiene_split
    · simpa [freeze, DeadlinesAligned] using h0
    · exact h0
  have h2 : DeadlinesAligned p s2 := by
    dsimp [s2]
    hygiene_split
    · simpa [DeadlinesAligned] using h1
    · exact h1
  have h3 : DeadlinesAligned p s3 := by
    dsimp [s3]
    hygiene_split
    · intro row hrow
      exact h2 row (release_subset p s2 qSlot row hrow)
    · exact h2
  exact h3

theorem clockPreGate_live_rows (p : Params) {n : Nat}
    (st : State n) (t : Time) :
    LiveRows (clockPreGate p st t) := by
  let s0 := expire { st with now := t } t
  let fSlot := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
  let s1 := if 0 ≤ t - 3 * p.Δ && t == freezeTime p fSlot then
    freeze p s0 fSlot else s0
  let eSlot := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
  let s2 := if 0 ≤ t - 2 * p.Δ && t == earlyTime p eSlot then
    { s1 with early := s1.early ++ [(eSlot, earlyVotes p s1 eSlot)] }
    else s1
  let qSlot := ((t - 5 * p.Δ) / (4 * p.Δ)).toNat
  let s3 := if 0 ≤ t - 5 * p.Δ && t == releaseTime p qSlot then
    release p s2 qSlot else s2
  change LiveRows s3
  have h0 : LiveRows s0 := by
    intro row hrow
    simpa [s0] using! (List.mem_filter.mp hrow).2
  have h1 : LiveRows s1 := by
    dsimp [s1]
    hygiene_split
    · simpa [freeze, LiveRows] using h0
    · exact h0
  have h2 : LiveRows s2 := by
    dsimp [s2]
    hygiene_split
    · simpa [LiveRows] using h1
    · exact h1
  have h3 : LiveRows s3 := by
    dsimp [s3]
    hygiene_split
    · intro row hrow
      exact h2 row (release_subset p s2 qSlot row hrow)
    · exact h2
  exact h3

theorem clock_map_invariants (p : Params) {n : Nat}
    (st : State n) (t : Time)
    (hprefix : PrefixDeadlineOrder st)
    (hcomparable : ComparableTargets st)
    (hblocks : StoredPrefixClosed st)
    (hhorizon : DeadlineHorizon p st)
    (htime : st.now ≤ t) :
    PrefixDeadlineOrder (clock p st t) ∧
    ComparableTargets (clock p st t) := by
  let pre := clockPreGate p st t
  let dSlot := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
  change
    PrefixDeadlineOrder
      (if 0 ≤ t - 6 * p.Δ && t == gateTime p dSlot then
        gate p pre dSlot else pre) ∧
    ComparableTargets
      (if 0 ≤ t - 6 * p.Δ && t == gateTime p dSlot then
        gate p pre dSlot else pre)
  obtain ⟨hpre, hcomp, hblocks', hbound, _⟩ :=
    clockPreGate_invariants p st t hprefix hcomparable hblocks hhorizon htime
  hygiene_split
  · rename_i hcond
    have ht : t = gateTime p dSlot :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp hcond).2
    have hgateBound : DeadlinesAtMost pre (gateTime p dSlot + lifetime p) := by
      rw [← ht]
      exact hbound
    exact ⟨gate_prefix_deadline_order p pre dSlot hpre hblocks' hgateBound,
      gate_comparable_targets p pre dSlot hcomp hgateBound⟩
  · exact ⟨hpre, hcomp⟩

theorem clock_deadlines_aligned (p : Params) {n : Nat}
    (st : State n) (t : Time)
    (hprefix : PrefixDeadlineOrder st)
    (hcomparable : ComparableTargets st)
    (hblocks : StoredPrefixClosed st)
    (hhorizon : DeadlineHorizon p st)
    (haligned : DeadlinesAligned p st)
    (htime : st.now ≤ t) :
    DeadlinesAligned p (clock p st t) := by
  let pre := clockPreGate p st t
  let dSlot := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
  change DeadlinesAligned p
    (if 0 ≤ t - 6 * p.Δ && t == gateTime p dSlot then
      gate p pre dSlot else pre)
  have hpreAligned := clockPreGate_deadlines_aligned p st t haligned
  have hpreBound := (clockPreGate_invariants p st t
    hprefix hcomparable hblocks hhorizon htime).2.2.2.1
  hygiene_split
  · rename_i hcond
    have ht : t = gateTime p dSlot :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp hcond).2
    apply gate_deadlines_aligned p pre dSlot
    · rw [← ht]
      exact hpreBound
    · exact hpreAligned
  · exact hpreAligned

theorem clock_live_rows (p : Params) {n : Nat}
    (st : State n) (t : Time)
    (hprefix : PrefixDeadlineOrder st)
    (hcomparable : ComparableTargets st)
    (hblocks : StoredPrefixClosed st)
    (hhorizon : DeadlineHorizon p st)
    (htime : st.now ≤ t) :
    LiveRows (clock p st t) := by
  let pre := clockPreGate p st t
  let dSlot := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
  change LiveRows
    (if 0 ≤ t - 6 * p.Δ && t == gateTime p dSlot then
      gate p pre dSlot else pre)
  have hpreLive := clockPreGate_live_rows p st t
  have hpreInv := clockPreGate_invariants p st t
    hprefix hcomparable hblocks hhorizon htime
  have hpreBound := hpreInv.2.2.2.1
  have hpreNow := hpreInv.2.2.2.2
  hygiene_split
  · rename_i hcond
    have ht : t = gateTime p dSlot :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp hcond).2
    apply gate_live_rows p pre dSlot
    · exact hpreNow.trans ht
    · rw [← ht]
      exact hpreBound
    · exact hpreLive
  · exact hpreLive

structure MapReachable (p : Params) (st : State p.n) : Prop where
  prefixOrder : PrefixDeadlineOrder st
  comparable : ComparableTargets st
  blocks : StoredPrefixClosed st
  horizon : DeadlineHorizon p st
  aligned : DeadlinesAligned p st
  liveRows : LiveRows st

theorem initial_map_reachable (p : Params) :
    MapReachable p (initial p.n) :=
  ⟨initial_prefix_deadline_order p.n,
    initial_comparable_targets p.n,
    initial_stored_prefix_closed p.n,
    initial_deadline_horizon p,
    initial_deadlines_aligned p,
    initial_live_rows p.n⟩

theorem process_map_reachable (p : Params)
    (st : State p.n) (o : Wire p.n)
    (h : MapReachable p st) : MapReachable p (process p st o) := by
  refine ⟨?_, ?_, process_stored_prefix_closed p st o h.blocks,
    process_deadline_horizon p st o h.horizon,
    process_deadlines_aligned p st o h.aligned,
    process_live_rows p st o h.liveRows⟩
  · simpa [PrefixDeadlineOrder, process_obligations] using h.prefixOrder
  · simpa [ComparableTargets, process_obligations] using h.comparable

theorem clock_map_reachable (p : Params)
    (st : State p.n) (t : Time)
    (h : MapReachable p st) (htime : st.now ≤ t) :
    MapReachable p (clock p st t) := by
  obtain ⟨hp, hc⟩ := clock_map_invariants p st t
    h.prefixOrder h.comparable h.blocks h.horizon htime
  exact ⟨hp, hc, clock_stored_prefix_closed p st t h.blocks,
    clock_deadline_horizon p st t h.horizon htime,
    clock_deadlines_aligned p st t h.prefixOrder h.comparable h.blocks
      h.horizon h.aligned htime,
    clock_live_rows p st t h.prefixOrder h.comparable h.blocks
      h.horizon htime⟩

private theorem world_step_map_reachable
    {V : Type} [DecidableEq V] (p : Params)
    (w : World V (gridCO p)) (e : Event V (gridCO p).Object)
    (bound : Time)
    (hinv : ∀ v, (w v).now ≤ bound ∧ MapReachable p (w v))
    (hbound : bound ≤ e.time) :
    ∀ v, (World.step w e v).now ≤ e.time ∧
      MapReachable p (World.step w e v) := by
  cases e with
  | tick u t =>
      intro v
      by_cases h : v = u
      · subst v
        have ht := le_trans (hinv u).1 hbound
        simpa [World.step] using!
          (show (clock p (w u) t).now ≤ t ∧
            MapReachable p (clock p (w u) t) from
            ⟨(clock_now p (w u) t).le, clock_map_reachable p (w u) t (hinv u).2 ht⟩)
      · simpa [World.step, h] using!
          (show (w v).now ≤ t ∧ MapReachable p (w v) from
            ⟨le_trans (hinv v).1 hbound, (hinv v).2⟩)
  | deliver u o t =>
      intro v
      by_cases h : v = u
      · subst v
        simpa [World.step] using!
          (show (process p (w u) o).now ≤ t ∧
            MapReachable p (process p (w u) o) from
            ⟨(process_now p (w u) o).le.trans ((hinv u).1.trans hbound),
              process_map_reachable p (w u) o (hinv u).2⟩)
      · simpa [World.step, h] using!
          (show (w v).now ≤ t ∧ MapReachable p (w v) from
            ⟨le_trans (hinv v).1 hbound, (hinv v).2⟩)

private theorem fold_world_map_reachable
    {V : Type} [DecidableEq V] (p : Params)
    (events : List (Event V (gridCO p).Object))
    (w : World V (gridCO p)) (bound : Time)
    (hordered : events.Pairwise (fun e f => e.time ≤ f.time))
    (hfuture : ∀ e ∈ events, bound ≤ e.time)
    (hinv : ∀ v, (w v).now ≤ bound ∧ MapReachable p (w v)) :
    ∀ v, MapReachable p ((events.foldl World.step w) v) := by
  induction events generalizing w bound with
  | nil => exact fun v => (hinv v).2
  | cons e events ih =>
      have he : bound ≤ e.time := hfuture e (by simp)
      have htail : events.Pairwise (fun a b => a.time ≤ b.time) :=
        List.Pairwise.tail hordered
      have hfuture' : ∀ x ∈ events, e.time ≤ x.time := by
        intro x hx
        exact (List.pairwise_cons.mp hordered).1 x hx
      exact ih (World.step w e) e.time htail hfuture'
        (world_step_map_reachable p w e bound hinv he)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Every state reached by a well-formed schedule has ordered map rows,
comparable targets, prefix-closed blocks, and a deadline horizon. -/
theorem run_map_reachable
    {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p))
    (hschedule : ScheduleWellFormed E rho)
    (i : Nat) (v : V) :
    MapReachable p (Run.stateBefore (gridCO p) rho i v) := by
  have htime : rho.events.Pairwise (fun e f => e.time ≤ f.time) :=
    hschedule.sorted.imp (fun h => event_time_le_of_key_le _ _ h)
  have htimeTake : (rho.events.take i).Pairwise
      (fun e f => e.time ≤ f.time) := htime.take
  have hnonneg : ∀ e ∈ rho.events.take i, 0 ≤ e.time := by
    intro e he
    exact (hschedule.in_horizon e (List.mem_of_mem_take he)).1
  exact fold_world_map_reachable p (rho.events.take i) World.init 0
    htimeTake hnonneg
    (fun u => ⟨by rfl, initial_map_reachable p⟩) v

theorem run_time_map_reachable
    {V : Type} [DecidableEq V] (p : Params)
    (E : Env V) (rho : Run V (gridCO p))
    (hschedule : ScheduleWellFormed E rho)
    (t : Time) (v : V) :
    MapReachable p (Run.stateBeforeTime (gridCO p) rho t v) := by
  have htime : rho.events.Pairwise (fun e f => e.time ≤ f.time) :=
    hschedule.sorted.imp (fun h => event_time_le_of_key_le _ _ h)
  have htimeFilter : (rho.events.filter (fun e => decide (e.time < t))).Pairwise
      (fun e f => e.time ≤ f.time) := htime.filter _
  have hnonneg : ∀ e ∈ rho.events.filter (fun e => decide (e.time < t)),
      0 ≤ e.time := by
    intro e he
    exact (hschedule.in_horizon e (List.mem_filter.mp he).1).1
  exact fold_world_map_reachable p
    (rho.events.filter (fun e => decide (e.time < t))) World.init 0
    htimeFilter hnonneg
    (fun u => ⟨by rfl, initial_map_reachable p⟩) v

private theorem world_step_stored_prefix_closed
    {V : Type} [DecidableEq V] (p : Params)
    (w : World V (gridCO p)) (e : Event V (gridCO p).Object)
    (hclosed : ∀ v, StoredPrefixClosed (w v)) :
    ∀ v, StoredPrefixClosed (World.step w e v) := by
  cases e with
  | tick u t =>
      intro v
      by_cases h : v = u
      · subst v
        simpa [World.step] using! clock_stored_prefix_closed p (w u) t (hclosed u)
      · simpa [World.step, h] using hclosed v
  | deliver u o t =>
      intro v
      by_cases h : v = u
      · subst v
        simpa [World.step] using! process_stored_prefix_closed p (w u) o (hclosed u)
      · simpa [World.step, h] using hclosed v

private theorem fold_world_stored_prefix_closed
    {V : Type} [DecidableEq V] (p : Params)
    (events : List (Event V (gridCO p).Object))
    (w : World V (gridCO p))
    (hclosed : ∀ v, StoredPrefixClosed (w v)) :
    ∀ v, StoredPrefixClosed ((events.foldl World.step w) v) := by
  induction events generalizing w with
  | nil => exact hclosed
  | cons e events ih =>
      exact ih (World.step w e)
        (world_step_stored_prefix_closed p w e hclosed)

theorem run_time_stored_prefix_closed
    {V : Type} [DecidableEq V] (p : Params)
    (rho : Run V (gridCO p)) (t : Time) (v : V) :
    StoredPrefixClosed (Run.stateBeforeTime (gridCO p) rho t v) := by
  exact fold_world_stored_prefix_closed p
    (rho.events.filter (fun e => decide (e.time < t))) World.init
    (fun u => initial_stored_prefix_closed p.n) v

def liveTargets {n : Nat} (st : State n) : List Block :=
  st.obligations.filterMap (fun (b, _, expiry) =>
    if st.now < expiry then some b else none)

def deeper (best b : Block) : Block :=
  if best.depth < b.depth ||
     (best.depth == b.depth && best.root < b.root) then b else best

theorem liveRoot_eq_fold {n : Nat} (st : State n) :
    liveRoot st = (liveTargets st).foldl deeper .genesis := rfl

private theorem deeper_depth (best b : Block) :
    best.depth ≤ (deeper best b).depth ∧
    b.depth ≤ (deeper best b).depth := by
  unfold deeper
  hygiene_split
  · rename_i h
    have hle : best.depth ≤ b.depth := by
      rcases Bool.or_eq_true_iff.mp h with hlt | htie
      · exact Nat.le_of_lt (of_decide_eq_true hlt)
      · exact le_of_eq (of_decide_eq_true (Bool.and_eq_true_iff.mp htie).1)
    exact ⟨hle, le_refl _⟩
  · rename_i h
    have hnot : ¬ best.depth < b.depth := by
      intro hlt
      exact h (by simp [hlt])
    have hle : b.depth ≤ best.depth := Nat.le_of_not_gt hnot
    exact ⟨le_refl _, hle⟩

theorem fold_deeper_depth (xs : List Block) (start : Block) :
    start.depth ≤ (xs.foldl deeper start).depth ∧
    ∀ b ∈ xs, b.depth ≤ (xs.foldl deeper start).depth := by
  induction xs generalizing start with
  | nil => exact ⟨le_refl _, by simp⟩
  | cons x xs ih =>
      have hstep := deeper_depth start x
      have htail := ih (deeper start x)
      constructor
      · exact le_trans hstep.1 htail.1
      · intro b hb
        rcases List.mem_cons.mp hb with heq | hmem
        · subst b
          exact le_trans hstep.2 htail.1
        · exact htail.2 b hmem

theorem fold_deeper_origin (xs : List Block) (start : Block) :
    xs.foldl deeper start = start ∨
      xs.foldl deeper start ∈ xs := by
  induction xs generalizing start with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rcases ih (deeper start x) with h | h
      · rw [h]
        unfold deeper
        hygiene_split
        · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
        · exact Or.inl rfl
      · exact Or.inr (List.mem_cons.mpr (Or.inr h))

theorem liveRoot_is_deepest {n : Nat} (st : State n) :
    (liveRoot st = .genesis ∨ liveRoot st ∈ liveTargets st) ∧
    ∀ K ∈ liveTargets st, K.depth ≤ (liveRoot st).depth := by
  rw [liveRoot_eq_fold]
  exact ⟨fold_deeper_origin (liveTargets st) .genesis,
    (fold_deeper_depth (liveTargets st) .genesis).2⟩

private theorem preceq_depth_le (B C : Block)
    (hBC : Block.preceq B C = true) : B.depth ≤ C.depth := by
  induction C with
  | genesis =>
      have h : B = .genesis := by simpa [Block.preceq] using hBC
      subst B
      exact le_refl _
  | node parent slot r_slot root ih =>
      have h : B = .node parent slot r_slot root ∨ Block.preceq B parent = true := by
        simpa [Block.preceq, Bool.or_eq_true] using hBC
      rcases h with h | h
      · subst B
        exact le_refl _
      · exact Nat.le_trans (ih h) (by simp [Block.depth])

private theorem preceq_eq_of_depth_ge (B C : Block)
    (hBC : Block.preceq B C = true)
    (hdepth : C.depth ≤ B.depth) : B = C := by
  induction C with
  | genesis =>
      simpa [Block.preceq] using hBC
  | node parent slot r_slot root ih =>
      have h : B = .node parent slot r_slot root ∨ Block.preceq B parent = true := by
        simpa [Block.preceq, Bool.or_eq_true] using hBC
      rcases h with h | h
      · exact h
      · have hle := preceq_depth_le B parent h
        simp [Block.depth] at hdepth
        omega

theorem preceq_of_compatible_depth_le (B C : Block)
    (hcompatible : Block.compatible B C = true)
    (hdepth : B.depth ≤ C.depth) : Block.preceq B C = true := by
  rcases Bool.or_eq_true_iff.mp hcompatible with hBC | hCB
  · exact hBC
  · have heq := preceq_eq_of_depth_ge C B hCB hdepth
    subst C
    exact block_preceq_self B

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
With comparable live targets, the executable deepest-choice root is
their deepest target. Every live target is its ancestor. -/
theorem liveTarget_preceq_liveRoot {n : Nat} (st : State n)
    (hcomparable : ComparableTargets st)
    (g : Nat) (b : Block) (deadline : Time)
    (hrow : (b, g, deadline) ∈ st.obligations)
    (hlive : st.now < deadline) :
    Block.preceq b (liveRoot st) = true := by
  have hb : b ∈ liveTargets st := by
    apply List.mem_filterMap.mpr
    exact ⟨(b, g, deadline), hrow, by simp [hlive]⟩
  obtain ⟨horigin, hdeep⟩ := liveRoot_is_deepest st
  have hdepth := hdeep b hb
  rcases horigin with hgenesis | hmem
  · rw [hgenesis] at hdepth ⊢
    cases b with
    | genesis => decide
    | node parent slot r_slot root => simp [Block.depth] at hdepth
  · obtain ⟨row, hrow', htarget⟩ := List.mem_filterMap.mp hmem
    rcases row with ⟨K', level, expiry⟩
    by_cases htime : st.now < expiry
    · simp [htime] at htarget
      have hKeq : K' = liveRoot st := htarget
      have hcomp := hcomparable b g deadline hrow K' level expiry hrow'
      exact preceq_of_compatible_depth_le b (liveRoot st)
        (hKeq ▸ hcomp) hdepth
    · simp [htime] at htarget

theorem initial_unique_keys (n : Nat) :
    UniqueObligationKeys (initial n) := by
  simp [UniqueObligationKeys, initial]

theorem write_unique_keys {n : Nat} (st : State n) (b : Block)
    (g : Nat) (deadline : Time) (hunique : UniqueObligationKeys st) :
    UniqueObligationKeys (writeObligation st b g deadline) := by
  intro x hx y hy hkey
  simp only [writeObligation, List.mem_append, List.mem_singleton] at hx hy
  rcases hx with hx | hx
  · rcases hy with hy | hy
    · exact hunique x (List.mem_filter.mp hx).1
        y (List.mem_filter.mp hy).1 hkey
    · subst y
      have hneq := (List.mem_filter.mp hx).2
      have heq : x.1 = b ∧ x.2.1 = g := by
        simpa [obligationKey] using hkey
      simp [heq.1, heq.2] at hneq
  · subst x
    rcases hy with hy | hy
    · have hneq := (List.mem_filter.mp hy).2
      have heq : y.1 = b ∧ y.2.1 = g := by
        have hs := hkey.symm
        simpa [obligationKey] using hs
      simp [heq.1, heq.2] at hneq
    · subst y
      rfl

theorem foldl_unique_keys {n : Nat} {α : Type}
    (f : State n → α → State n) (xs : List α) (st : State n)
    (hstep : ∀ acc x, UniqueObligationKeys acc →
      UniqueObligationKeys (f acc x))
    (hstart : UniqueObligationKeys st) :
    UniqueObligationKeys (xs.foldl f st) := by
  induction xs generalizing st with
  | nil => exact hstart
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact ih (f st x) (hstep st x hstart)

theorem gate_unique_keys (p : Params) {n : Nat} (st : State n)
    (r : Slot) (hunique : UniqueObligationKeys st) :
    UniqueObligationKeys (gate p st r) := by
  cases hc : confirmation p st r with
  | none => simpa [gate, hc] using! hunique
  | some B =>
      by_cases hv : st.obligations.any (fun (target, _, _) =>
          !Block.compatible target B) = true
      · simpa [gate, hc, hv, UniqueObligationKeys] using hunique
      · have hvf : st.obligations.any (fun (target, _, _) =>
            !Block.compatible target B) = false := by
          cases hbool : st.obligations.any (fun (target, _, _) =>
              !Block.compatible target B) <;> simp_all
        simp only [gate, hc, hvf]
        apply foldl_unique_keys
        · intro acc b hacc
          apply foldl_unique_keys
          · intro acc g hg
            exact write_unique_keys acc b g (gateTime p r + lifetime p) hg
          · exact hacc
        · simpa [UniqueObligationKeys] using hunique

end AvailableChain.GridCO
end
