module
public import AvailableChainGridCO.Proofs.ClockBounds
public import AvailableChainKit.Engine.Stable

@[expose] public section

/-! E4 hook facts for Grid CO (design §2 E4). Each run-level fact has the
statement of the matching `HooksSound` field with `P := gridCO p`; the
Registry assembles them. This library does not import the framework. -/

namespace AvailableChain.GridCO

open AvailableChain.Generic AvailableChain.Statements.Generic
open AvailableChain.Engine (stateBefore_stable stateBefore_stable_clock)

/-- A proposal is never excluded. -/
theorem excludes_proposal (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (B : Block) (raw support : List (HeadWire n))
    (hp : o.payload = .proposal B raw support) : excludes p st o = false := by
  obtain ⟨auth, payload⟩ := o
  subst hp
  cases auth <;> rfl

/-- A HEAD that is not processed is excluded iff `admitVote` refuses it
permanently: the old-label test or the equivocation test holds. -/
theorem excludes_head_iff (p : Params) {n : Nat} (st : State n) (r : Slot)
    (i : Fin n) (x : Block) :
    excludes p st ⟨.seat r i, .head x⟩ = true ↔
      (⟨.seat r i, .head x⟩ : Wire n) ∉ st.votes ∧
        (r + 1 < (st.now / (4 * p.Δ)).toNat ∨ equivocates (votesAt st r) i = true) := by
  simp [excludes]

/-- Only a HEAD can be excluded. -/
private theorem excludes_head {n : Nat} (p : Params) (st : State n) (o : Wire n)
    (h : excludes p st o = true) :
    ∃ r i x, o = (⟨.seat r i, .head x⟩ : Wire n) := by
  obtain ⟨auth, payload⟩ := o
  cases auth with
  | seat r i =>
      cases payload with
      | head x => exact ⟨r, i, x, rfl⟩
      | proposal b raw support => simp [excludes] at h
  | proposer s => cases payload <;> simp [excludes] at h
  | none => cases payload <;> simp [excludes] at h

/-- `processed` and `excludes` are disjoint. -/
theorem excludes_not_processed (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (h : excludes p st o = true) : processed st o = false := by
  obtain ⟨r, i, x, rfl⟩ := excludes_head p st o h
  simpa [processed] using ((excludes_head_iff p st r i x).mp h).1

/-- An exclusion survives a state change that keeps the clock, keeps the
stored HEADs, and does not store the excluded HEAD. -/
private theorem excludes_of_votes (p : Params) {n : Nat} (st st' : State n) (o : Wire n)
    (hnow : st'.now = st.now) (hsub : st.votes ⊆ st'.votes) (hm : o ∉ st'.votes)
    (h : excludes p st o = true) : excludes p st' o = true := by
  obtain ⟨r, i, x, rfl⟩ := excludes_head p st o h
  rw [excludes_head_iff] at h ⊢
  refine ⟨hm, ?_⟩
  rw [hnow]
  exact h.2.imp id (equivocates_mono _ _ i (votesAt_subset _ _ r hsub))

/-- One HEAD call keeps an exclusion: `admitVote` refuses the excluded HEAD
on the same tests. -/
private theorem admitVote_keeps_excludes (p : Params) {n : Nat} (st : State n)
    (o o' : Wire n) (h : excludes p st o = true) :
    excludes p (admitVote p st o') o = true := by
  apply excludes_of_votes p st _ o (admitVote_now p st o') (admitVote_votes_subset p st o') _ h
  obtain ⟨r, i, x, rfl⟩ := excludes_head p st o h
  obtain ⟨hm, hc⟩ := (excludes_head_iff p st r i x).mp h
  unfold admitVote
  split
  · rename_i r' i' x' hauth hpay
    dsimp only
    split
    · exact hm
    · rename_i hguard
      simp only [List.mem_append, List.mem_singleton, not_or]
      refine ⟨hm, fun heq => hguard ?_⟩
      have ho : o' = ⟨.seat r i, .head x⟩ := heq.symm
      subst ho
      simp only [Auth.seat.injEq, Msg.head.injEq] at hauth hpay
      obtain ⟨rfl, rfl⟩ := hauth
      rcases hc with hc | hc
      · simp [Nat.lt_sub_of_add_lt hc]
      · simp [hc]
  · exact hm

private theorem fold_keeps_excludes (p : Params) {n : Nat} (raw : List (HeadWire n))
    (st : State n) (o : Wire n) (h : excludes p st o = true) :
    excludes p (raw.foldl (fun acc row => admitVote p acc (fromHead row)) st) o = true := by
  induction raw generalizing st with
  | nil => exact h
  | cons row raw ih => exact ih _ (admitVote_keeps_excludes p st o (fromHead row) h)

/-- A handler call keeps an exclusion. -/
theorem excludes_process (p : Params) {n : Nat} (st : State n) (o o' : Wire n)
    (h : excludes p st o = true) : excludes p (process p st o') o = true := by
  obtain ⟨auth, payload⟩ := o'
  cases auth <;> cases payload <;> simp only [process]
  all_goals first
    | exact h
    | exact admitVote_keeps_excludes p st o _ h
    | skip
  rename_i s b raw support
  unfold admitProposal
  dsimp only
  split
  · exact h
  · exact fold_keeps_excludes p raw _ o h

private theorem fold_votes_subset (p : Params) {n : Nat} (raw : List (HeadWire n))
    (st : State n) : st.votes ⊆
      (raw.foldl (fun acc row => admitVote p acc (fromHead row)) st).votes := by
  induction raw generalizing st with
  | nil => exact List.Subset.refl _
  | cons row raw ih => exact List.Subset.trans (admitVote_votes_subset p st (fromHead row)) (ih _)

/-- A handler call never removes a stored HEAD. -/
theorem process_votes_subset (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    st.votes ⊆ (process p st o).votes := by
  obtain ⟨auth, payload⟩ := o
  cases auth <;> cases payload <;> simp only [process]
  all_goals first
    | exact List.Subset.refl _
    | exact admitVote_votes_subset p st _
    | skip
  rename_i s b raw support
  unfold admitProposal
  dsimp only
  split
  · exact List.Subset.refl _
  · refine List.Subset.trans ?_ (fold_votes_subset p raw _)
    exact List.Subset.refl _

private theorem fold_blocks {n : Nat} (p : Params) (raw : List (HeadWire n))
    (st : State n) :
    (raw.foldl (fun acc row => admitVote p acc (fromHead row)) st).blocks = st.blocks := by
  induction raw generalizing st with
  | nil => rfl
  | cons row raw ih =>
      simp only [List.foldl_cons]
      rw [ih, admitVote_blocks]

/-- A handler call never removes a stored block. -/
theorem process_blocks_subset (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    st.blocks ⊆ (process p st o).blocks := by
  obtain ⟨auth, payload⟩ := o
  cases auth <;> cases payload <;> simp only [process]
  all_goals first
    | exact List.Subset.refl _
    | exact (admitVote_blocks p st _).symm ▸ List.Subset.refl _
    | skip
  rename_i s b raw support
  unfold admitProposal
  dsimp only
  split
  · exact List.Subset.refl _
  · rw [fold_blocks]
    exact List.subset_append_left _ _

-- Keep one shared proof interface for both lease policies.
set_option linter.unusedSectionVars false

variable [LeasePolicy]

private theorem foldl_votes {n : Nat} {α : Type}
    (f : State n → α → State n) (xs : List α) (st : State n)
    (hf : ∀ acc x, (f acc x).votes = acc.votes) :
    (xs.foldl f st).votes = st.votes := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih, hf]

theorem gate_votes (p : Params) {n : Nat} (st : State n) (r : Slot) :
    (gate p st r).votes = st.votes := by
  cases hc : confirmation p st r with
  | none => simp [gate, hc]
  | some C =>
      cases hguard : st.obligations.any (fun (target, _, _) =>
          !Block.compatible target C) with
      | true => simp [gate, hc, hguard]
      | false =>
          simp only [gate, hc, hguard]
          apply foldl_votes
          intro acc b
          apply foldl_votes
          intro acc g
          rfl

/-- No clock evaluation (`expire`, `freeze`, the early save, `release`,
`gate`) changes the stored HEADs. -/
theorem clock_votes (p : Params) {n : Nat} (st : State n) (t : Time) :
    (clock p st t).votes = st.votes := by
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
    gate p s3 dSlot else s3).votes = st.votes
  have h0 : s0.votes = st.votes := rfl
  have h1 : s1.votes = s0.votes := by
    dsimp [s1]
    split <;> rfl
  have h2 : s2.votes = s1.votes := by
    dsimp [s2]
    split <;> rfl
  have h3 : s3.votes = s2.votes := by
    dsimp [s3]
    split <;> rfl
  split
  · exact (gate_votes p s3 dSlot).trans (h3.trans (h2.trans (h1.trans h0)))
  · exact h3.trans (h2.trans (h1.trans h0))

/-- A clock tick that does not move backwards keeps an exclusion: the stored
HEADs do not change, and the label of the clock does not decrease. -/
theorem excludes_clock (p : Params) {n : Nat} (st : State n) (o : Wire n) (t : Time)
    (ht : st.now ≤ t) (h : excludes p st o = true) : excludes p (clock p st t) o = true := by
  obtain ⟨r, i, x, rfl⟩ := excludes_head p st o h
  rw [excludes_head_iff] at h ⊢
  have hv : votesAt (clock p st t) r = votesAt st r := by simp only [votesAt, clock_votes]
  rw [clock_votes, clock_now, hv]
  refine ⟨h.1, h.2.imp (fun hl => lt_of_lt_of_le hl ?_) id⟩
  have hd : 0 < 4 * p.Δ := by linarith [p.deltaPos]
  exact Int.toNat_le_toNat (Int.ediv_le_ediv hd ht)

theorem excludes_inert (p : Params) :
    ∀ st o, (gridCO p).excludes st o = true → (gridCO p).process st o = st := by
  set_option backward.isDefEq.respectTransparency false in
  intro st o h
  rw [gridCO_excludes] at h
  obtain ⟨r, i, x, rfl⟩ := excludes_head p st o h
  obtain ⟨_, hc⟩ := (excludes_head_iff p st r i x).mp h
  change process p st ⟨.seat r i, .head x⟩ = st
  simp only [process, admitVote]
  rw [ite_eq_left]
  rcases hc with hc | hc
  · simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl (Or.inl (Or.inl (Nat.lt_sub_of_add_lt hc)))
  · simp [hc]

-- The run-level facts keep the `HooksSound` field shape, `[Fintype V]` included.
set_option linter.unusedFintypeInType false in
/-- Exclusion is stable along a valid run. The old-label test needs the
clock not to move backwards, which only a valid schedule gives. -/
theorem excludes_stable (p : Params) :
    ∀ {V : Type} [DecidableEq V] [Fintype V] (E : Env V)
      (rho : Run V (gridCO p)), ScheduleWellFormed E rho → ∀ v o i j, i ≤ j →
        (gridCO p).excludes (Run.stateBefore (gridCO p) rho i v) o = true →
        (gridCO p).excludes (Run.stateBefore (gridCO p) rho j v) o = true := by
  intro V _ _ E rho hs v o i j hij h
  exact stateBefore_stable_clock (engineClock p) E rho hs
    (fun st => (gridCO p).excludes st o = true)
    (fun st t ht hq => excludes_clock p st o t ht hq)
    (fun st o' hq => excludes_process p st o o' hq) hij v h

set_option linter.unusedFintypeInType false in
theorem processed_stable (p : Params) :
    ∀ {V : Type} [DecidableEq V] [Fintype V] (E : Env V)
      (rho : Run V (gridCO p)), ScheduleWellFormed E rho → ∀ v o i j, i ≤ j →
        (gridCO p).processed (Run.stateBefore (gridCO p) rho i v) o = true →
        (gridCO p).processed (Run.stateBefore (gridCO p) rho j v) o = true := by
  set_option backward.isDefEq.respectTransparency false in
  intro V _ _ E rho _ v o i j hij h
  exact stateBefore_stable (P := gridCO p) (fun st => processed st o = true)
    (fun st t hq => by
      change processed (clock p st t) o = true
      obtain ⟨auth, payload⟩ := o
      cases payload with
      | head x =>
          simpa [processed, clock_votes] using! hq
      | proposal b raw support =>
          simpa [processed, blockKnown, clock_blocks] using! hq)
    (fun st o' hq => by
      change processed (process p st o') o = true
      obtain ⟨auth, payload⟩ := o
      cases payload with
      | head x =>
          simp only [processed, decide_eq_true_eq] at hq ⊢
          exact process_votes_subset p st o' hq
      | proposal b raw support =>
          simp only [processed, blockKnown, decide_eq_true_eq] at hq ⊢
          exact process_blocks_subset p st o' hq)
    rho hij v h

set_option linter.unusedFintypeInType false in
theorem deps_stable (p : Params) :
    ∀ {V : Type} [DecidableEq V] [Fintype V] (E : Env V)
      (rho : Run V (gridCO p)), ScheduleWellFormed E rho → ∀ v o i j, i ≤ j →
        (gridCO p).depsPresent (Run.stateBefore (gridCO p) rho i v) o = true →
        (gridCO p).depsPresent (Run.stateBefore (gridCO p) rho j v) o = true := by
  set_option backward.isDefEq.respectTransparency false in
  intro V _ _ E rho _ v o i j hij h
  exact stateBefore_stable (P := gridCO p) (fun st => depsPresent st o = true)
    (fun st t hq => by
      change depsPresent (clock p st t) o = true
      obtain ⟨auth, payload⟩ := o
      cases payload with
      | head x => rfl
      | proposal b raw support =>
          simpa [depsPresent, blockKnown, clock_blocks] using! hq)
    (fun st o' hq => by
      change depsPresent (process p st o') o = true
      obtain ⟨auth, payload⟩ := o
      cases payload with
      | head x => rfl
      | proposal b raw support =>
          simp only [depsPresent, blockKnown, decide_eq_true_eq] at hq ⊢
          exact process_blocks_subset p st o' hq)
    rho hij v h

theorem handles_carries (p : Params) :
    ∀ st o o', (gridCO p).handles st o o' → o = o' ∨ (gridCO p).carries o o' := by
  intro st o o' h
  change handles p st o o' at h
  change o = o' ∨ carries o o'
  rcases h with h | h
  · exact Or.inl h
  · right
    unfold carries
    cases hp : o.payload with
    | head x => simp [hp] at h
    | proposal b raw support =>
        simp only [hp] at h
        exact Or.inl h.2.2

end AvailableChain.GridCO
end
