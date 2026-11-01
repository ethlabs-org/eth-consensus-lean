module
public import AvailableChainGridCO.Proofs.Execution

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
private def hygiene_proposerSupportView
    {n : Nat} {mode : HeadMode} (st : State n mode) (s : Slot) : List
    (Wire n mode) :=
  (proposerView st s).filter (fun o =>
    match resolvedHead? st o with
    | some b => b.slot ≤ s - 1
    | none => false)

-- The generated matcher bodies are definitionally equal.
private theorem hygiene_proposerSupportView_match_1_eq :
    hygieneEq% (@proposerSupportView) (@hygiene_proposerSupportView) := rfl

end AvailableChain.GridCO

-- Rewrite before simp can generate equations for the public matcher.
attribute [local simp↓]
  AvailableChain.GridCO.hygiene_proposerSupportView_match_1_eq

local macro "hygiene_split" : tactic =>
  `(tactic| (
    try rw [AvailableChain.GridCO.hygiene_proposerSupportView_match_1_eq] at *;
    all_goals split))

local macro "hygiene_split" "at" h:ident : tactic =>
  `(tactic| (
    try rw [AvailableChain.GridCO.hygiene_proposerSupportView_match_1_eq] at *;
    all_goals split at $h:ident))

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

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Every stored object has a receipt stamp. -/
def ReceiptStamped {n : Nat} (st : State n) : Prop :=
  (∀ b ∈ st.blocks, ∃ t, (b, t) ∈ st.blockStamp) ∧
  (∀ o ∈ st.votes, ∃ t, (o, t) ∈ st.voteStamp)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The fields read by confirmation, apart from the fallback clock. -/
def receiptData {n : Nat} (st : State n) :=
  (st.blocks, st.blockStamp, st.votes, st.voteStamp)

theorem stamped_of_data_eq {n : Nat} {a b : State n}
    (heq : receiptData a = receiptData b) (hb : ReceiptStamped b) : ReceiptStamped a := by
  have ⟨h1, h2, h3, h4⟩ : a.blocks = b.blocks ∧ a.blockStamp = b.blockStamp ∧
      a.votes = b.votes ∧ a.voteStamp = b.voteStamp := by simpa [receiptData] using heq
  simpa only [ReceiptStamped, h1, h2, h3, h4] using hb

private theorem fold_data {n : Nat} {α : Type} (xs : List α)
    (f : State n → α → State n) (hf : ∀ st x, receiptData (f st x) = receiptData st)
    (st : State n) : receiptData (xs.foldl f st) = receiptData st := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, hf]

theorem gate_receiptData (p : Params) {n : Nat} (st : State n) (r : Slot) :
    receiptData (gate p st r) = receiptData st := by
  unfold gate
  hygiene_split
  · rfl
  · dsimp only
    hygiene_split
    · rfl
    · apply fold_data
      intro acc b
      apply fold_data
      intro acc g
      rfl

theorem clockPreGate_receiptData (p : Params) {n : Nat} (st : State n) (t : Time) :
    receiptData (clockPreGate p st t) = receiptData st := by
  unfold clockPreGate
  dsimp only
  hygiene_split <;> hygiene_split <;> hygiene_split <;> rfl

theorem clock_receiptData (p : Params) {n : Nat} (st : State n) (t : Time) :
    receiptData (clock p st t) = receiptData st := by
  rw [clock_eq_gate_prestate]
  dsimp only
  hygiene_split
  · rw [gate_receiptData, clockPreGate_receiptData]
  · exact clockPreGate_receiptData p st t

theorem initial_stamped (n : Nat) : ReceiptStamped (initial n) := by
  simp [ReceiptStamped, initial]

theorem admitVote_stamped (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (h : ReceiptStamped st) : ReceiptStamped (admitVote p st o) := by
  unfold admitVote
  hygiene_split
  · dsimp only
    hygiene_split
    · exact h
    · refine ⟨h.1, ?_⟩
      intro u hu
      obtain hu | hu : u ∈ st.votes ∨ u = o := by simpa using hu
      · obtain ⟨t, ht⟩ := h.2 u hu
        exact ⟨t, List.mem_append_left _ ht⟩
      · subst u; exact ⟨st.now, by simp⟩
  · exact h

private theorem fold_admitVote_stamped (p : Params) {n : Nat}
    (xs : List (HeadWire n)) (st : State n) (h : ReceiptStamped st) :
    ReceiptStamped (xs.foldl (fun acc row => admitVote p acc (fromHead row)) st) := by
  induction xs generalizing st with
  | nil => exact h
  | cons x xs ih => exact ih _ (admitVote_stamped p st (fromHead x) h)

theorem admitProposal_stamped (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (b : Block) (raw : List (HeadWire n)) (h : ReceiptStamped st) :
    ReceiptStamped (admitProposal p st o b raw) := by
  unfold admitProposal
  dsimp only
  split_ifs
  · exact h
  · apply fold_admitVote_stamped
    refine ⟨?_, h.2⟩
    intro b hb
    simp only [List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · obtain ⟨t, ht⟩ := h.1 b hb
      exact ⟨t, List.mem_append_left _ ht⟩
    · exact ⟨st.now, by simp⟩

private theorem process_stamped (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (h : ReceiptStamped st) : ReceiptStamped (process p st o) := by
  unfold process
  hygiene_split
  · exact admitVote_stamped p st o h
  · exact admitProposal_stamped p st o _ _ h
  · exact h

private theorem fold_stamped {V : Type} [DecidableEq V] (p : Params)
    (xs : List (Event V (gridCO p).Object)) (w : World V (gridCO p))
    (h : ∀ v, ReceiptStamped (w v)) :
    ∀ v, ReceiptStamped ((xs.foldl World.step w) v) := by
  induction xs generalizing w with
  | nil => exact h
  | cons e xs ih =>
      apply ih
      intro v
      cases e with
      | tick u t =>
          by_cases hv : v = u
          · subst v
            simpa [World.step] using! stamped_of_data_eq (clock_receiptData p (w u) t) (h u)
          · simpa [World.step, hv] using h v
      | deliver u o t =>
          by_cases hv : v = u
          · subst v; simpa [World.step] using! process_stamped p (w u) o (h u)
          · simpa [World.step, hv] using h v

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Stored votes and blocks have stamps at every time-filtered run state. -/
theorem run_receiptStamped {V : Type} [DecidableEq V]
    (p : Params) (rho : Run V (gridCO p)) (i : Nat) (v : V) :
    ReceiptStamped (Run.stateBefore (gridCO p) rho i v) :=
  fold_stamped p _ World.init (fun _ => initial_stamped p.n) v

theorem run_time_receiptStamped {V : Type} [DecidableEq V]
    (p : Params) (rho : Run V (gridCO p)) (t : Time) (v : V) :
    ReceiptStamped (Run.stateBeforeTime (gridCO p) rho t v) :=
  fold_stamped p _ World.init (fun _ => initial_stamped p.n) v

private theorem stamp_eq_of_data {α : Type} [BEq α] [LawfulBEq α]
    (xs : List (α × Time)) (x : α) (a b : Time) (h : ∃ t, (x, t) ∈ xs) :
    ((xs.find? (fun row => row.1 == x)).map Prod.snd).getD a =
      ((xs.find? (fun row => row.1 == x)).map Prod.snd).getD b := by
  obtain ⟨t, ht⟩ := h
  cases hf : xs.find? (fun row => row.1 == x) with
  | none =>
      have hh := List.find?_eq_none.mp hf (x, t) ht
      simp at hh
  | some row => rfl

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
A clock change does not change resolution of a stored, stamped HEAD. -/
theorem resolvedBefore_eq_of_receiptData {n : Nat} (a b : State n)
    (heq : receiptData a = receiptData b) (hb : ReceiptStamped b)
    (o : Wire n) (ho : o ∈ b.votes) (cut : Time) :
    resolvedBefore a o cut = resolvedBefore b o cut := by
  have ⟨h1, h2, h3, h4⟩ : a.blocks = b.blocks ∧ a.blockStamp = b.blockStamp ∧
      a.votes = b.votes ∧ a.voteStamp = b.voteStamp := by simpa [receiptData] using heq
  have hv : stampVote a o = stampVote b o := by
    simp only [stampVote, h4]
    exact stamp_eq_of_data _ _ _ _ (hb.2 o ho)
  simp only [resolvedBefore_block_local]
  hygiene_split
  · rfl
  · rename_i target ht
    by_cases hknown : target ∈ b.blocks
    · have ht : stampBlock a target = stampBlock b target := by
        simp only [stampBlock, h2]
        exact stamp_eq_of_data _ _ _ _ (hb.1 target hknown)
      simp only [blockKnown, h1, ht, hv]
    · simp [blockKnown, h1, hknown]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Expiry, freeze, and clock stamping leave the release count unchanged. -/
theorem releaseCount_eq_of_receiptData (p : Params) {n : Nat} (a b : State n)
    (heq : receiptData a = receiptData b) (hb : ReceiptStamped b) (r : Slot) (B : Block) :
    releaseCount p a r B = releaseCount p b r B := by
  have hv : a.votes = b.votes := congrArg (fun data => data.2.2.1) heq
  have hraw : votesAt a r = votesAt b r := by simp only [votesAt, hv]
  have hresolved : (votesAt b r).filter (fun o => resolvedBefore a o (releaseTime p r)) =
      (votesAt b r).filter (fun o => resolvedBefore b o (releaseTime p r)) := by
    apply List.filter_congr
    intro o ho
    exact resolvedBefore_eq_of_receiptData a b heq hb o (List.mem_filter.mp ho).1 _
  simp only [
      ↓AvailableChain.GridCO.hygiene_proposerSupportView_match_1_eq,
      releaseCount, hraw, hresolved]
  have hblocks : a.blocks = b.blocks := congrArg Prod.fst heq
  simp only [resolvedHead?, resolutionTree, hblocks]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
Restamping the local clock cannot change a genuine result once all
stored votes and blocks have their own receipt stamps. -/
theorem confirmation_eq_of_receiptData (p : Params) {n : Nat}
    (a b : State n) (heq : receiptData a = receiptData b) (hb : ReceiptStamped b)
    (r : Slot) : confirmation p a r = confirmation p b r := by
  have ⟨h1, h2, h3, h4⟩ : a.blocks = b.blocks ∧ a.blockStamp = b.blockStamp ∧
      a.votes = b.votes ∧ a.voteStamp = b.voteStamp := by simpa [receiptData] using heq
  have hv : ∀ o ∈ b.votes, stampVote a o = stampVote b o := by
    intro o ho
    simp only [stampVote, h4]
    exact stamp_eq_of_data _ _ _ _ (hb.2 o ho)
  have hres : ∀ o ∈ b.votes, resolvedBefore a o (earlyTime p r) =
      resolvedBefore b o (earlyTime p r) := by
    intro o ho
    simp only [resolvedBefore_block_local]
    hygiene_split
    · rfl
    · rename_i target ht
      by_cases hknown : target ∈ b.blocks
      · have ht : stampBlock a target = stampBlock b target := by
          simp only [stampBlock, h2]
          exact stamp_eq_of_data _ _ _ _ (hb.1 target hknown)
        simp only [blockKnown, h1, ht, hv o ho]
      · simp [blockKnown, h1, hknown]
  have hvotes : votesAt a r = votesAt b r := by simp [votesAt, h3]
  have hearly : earlyVotes p a r = earlyVotes p b r := by
    simp only [earlyVotes, hvotes]
    apply List.filter_congr
    intro o ho
    exact hres o (List.mem_filter.mp ho).1
  have hlate : lateVotes p a r = lateVotes p b r := by
    simp only [lateVotes, hvotes]
    apply List.filter_congr
    intro o ho
    rw [hv o (List.mem_filter.mp ho).1]
  have hclean : cleanSupport p a r = cleanSupport p b r := by
    simp only [cleanSupport, hearly, hlate]
  simp only [confirmation, hclean, hlate, resolutionTree, h1]
  rfl

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The gate branch runs at its advertised time and label. -/
theorem clock_at_gate (p : Params) {n : Nat} (st : State n) (r : Slot) :
    clock p st (gateTime p r) = gate p (clockPreGate p st (gateTime p r)) r := by
  have hd : 4 * p.Δ ≠ 0 := ne_of_gt (by linarith [p.deltaPos])
  have ht : gateTime p r - 6 * p.Δ = 4 * p.Δ * (r : Time) := by
    simp [gateTime, proposalTime]
  have hslot : ((gateTime p r - 6 * p.Δ) / (4 * p.Δ)).toNat = r := by
    simp [ht, hd]
  have hn : 0 ≤ gateTime p r - 6 * p.Δ := by
    rw [ht]
    exact mul_nonneg (by linarith [p.deltaPos]) (Int.natCast_nonneg r)
  rw [clock_eq_gate_prestate]
  simp only [hslot, hn, decide_true, beq_self_eq_true, Bool.and_self, ↓reduceIte]

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
In integer time, the strict-time read is the preceding integer read. -/
theorem stateBeforeTime_eq_readAt_pred {V : Type} [DecidableEq V]
    (p : Params) (rho : Run V (gridCO p)) (t : Time) :
    Run.stateBeforeTime (gridCO p) rho t = Run.readAt (gridCO p) rho (t - 1) := by
  unfold Run.stateBeforeTime Run.readAt
  congr 2
  funext e
  simp only [decide_eq_decide]
  exact Int.le_sub_one_iff.symm

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
The record before gate zero is genesis; later gates read the preceding
completed gate's record. -/
theorem gate_input_record {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hs : ScheduleWellFormed E rho) (r : Slot) (v : V) :
    stable (gateInput p rho r v) =
      if r = 0 then .genesis
      else stable (Run.readAt (gridCO p) rho (gateTime p (r - 1)) v) := by
  unfold gateInput
  rw [stateBeforeTime_eq_readAt_pred]
  by_cases hz : r = 0
  · subst r
    simp only [↓reduceIte]
    exact read_stable_before_first_gate p rho (gateTime p 0 - 1) (sub_lt_self _ (by norm_num)) v
  · rw [ite_eq_right hz]
    apply read_stable_eq_latest_gate p E rho hs (r - 1) (gateTime p r - 1)
    · have hslot : ((r - 1 : Nat) : Time) = r - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hz), Nat.cast_one]
      simp only [gateTime, proposalTime, hslot]
      have hd : 1 ≤ p.Δ := Int.add_one_le_iff.mpr p.deltaPos
      nlinarith
    · have hr : r - 1 + 1 = r := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hz)
      rw [hr]
      exact sub_lt_self _ (by norm_num)

/-- [ROOT-DIGEST-2 W1; DC shared named and HEAD interfaces]
An honest gate read either retains the preceding record or contains
that reader's genuine result, computed from the strict gate input. -/
theorem read_gate_record_cases {V : Type} [DecidableEq V]
    (p : Params) (E : Env V) (rho : Run V (gridCO p))
    (hs : ScheduleWellFormed E rho) (hΔ : E.Δ = p.Δ)
    (r : Slot) (hh : gateTime p r ≤ rho.horizon) (v : V) (hv : v ∈ rho.honest) :
    stable (Run.readAt (gridCO p) rho (gateTime p r) v) =
        stable (gateInput p rho r v) ∨
      confirmation p (gateInput p rho r v) r =
        some (stable (Run.readAt (gridCO p) rho (gateTime p r) v)) := by
  set_option backward.isDefEq.respectTransparency false in
  have hpub : PublicTime E (gateTime p r) := by
    refine ⟨4 * r + 6, ?_⟩
    simp only [gateTime, proposalTime, hΔ, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hnonneg : 0 ≤ gateTime p r := by
    dsimp [gateTime, proposalTime]
    have := mul_nonneg (show 0 ≤ 4 * p.Δ by linarith [p.deltaPos])
      (Int.natCast_nonneg r)
    linarith [p.deltaPos]
  have hread := read_stable_eq_clock hs (hs.tick_total v hv _ hpub hnonneg hh)
  rw [hread, clock_at_gate]
  rcases gate_stable_cases p
      (clockPreGate p (gateInput p rho r v) (gateTime p r)) r with h | ⟨B, hc, he⟩
  · exact Or.inl (h.trans (clockPreGate_stable p _ _))
  · right
    change confirmation p (gateInput p rho r v) r =
      some (gate p (clockPreGate p (gateInput p rho r v) (gateTime p r)) r).stableRecord
    rw [he]
    exact (confirmation_eq_of_receiptData p _ _
      (clockPreGate_receiptData p (gateInput p rho r v) (gateTime p r))
      (run_time_receiptStamped p rho (gateTime p r) v) r).symm.trans hc

end AvailableChain.GridCO
end
