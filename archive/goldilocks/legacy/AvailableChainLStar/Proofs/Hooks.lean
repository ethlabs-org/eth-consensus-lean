module
public import AvailableChainLStar.Model.Protocol
public import AvailableChainKit.Engine.Stable

@[expose] public section

/-! E4 hook facts for L* (design §2 E4). Each run-level fact has the
statement of the matching `HooksSound` field with `P := lstar p n`; the
Registry assembles them. This library does not import the framework or
Grid CO. -/

namespace AvailableChain.LStar

open AvailableChain.Generic AvailableChain.Statements.Generic
open AvailableChain.Engine (stateBefore_stable)

/-- The instance field is the model's `excludes`. -/
theorem lstar_excludes (p : Params) (n : Nat) (st : State n) (o : Wire n) :
    (lstar p n).excludes st o = excludes st o := rfl

/-- A HEAD that is not processed is excluded iff its seat already
equivocates at its label: `admitVote` then refuses it permanently. -/
theorem excludes_head_iff {n : Nat} (st : State n) (r : Slot) (i : Fin n) (x : Block) :
    excludes st ⟨.seat r i, .head x⟩ = true ↔
      (⟨.seat r i, .head x⟩ : Wire n) ∉ st.votes ∧ equivocates (votesAt st r) i = true := by
  simp [excludes]

/-- A proposal wire that is not processed is excluded iff its block is
already stored: `admitProposal` then refuses it permanently. -/
theorem excludes_proposal_iff {n : Nat} (st : State n) (s : Slot) (b : Block)
    (raw support : List (HeadWire n)) :
    excludes st ⟨.proposer s, .proposal b raw support⟩ = true ↔
      (⟨.proposer s, .proposal b raw support⟩ : Wire n) ∉ st.proposals ∧ b ∈ st.blocks := by
  simp [excludes]

/-- A proposal wire whose block is not stored is not excluded, whatever its
authentication. With proposer authentication, `admitProposal` can still
accept it later. -/
theorem excludes_proposal_not_stored {n : Nat} (st : State n) (o : Wire n) (b : Block)
    (raw support : List (HeadWire n)) (hp : o.payload = .proposal b raw support)
    (hb : b ∉ st.blocks) : excludes st o = false := by
  obtain ⟨auth, payload⟩ := o
  subst hp
  cases auth <;> simp [excludes, hb]

/-- The shape of an excluded object: one of the two clauses holds. -/
private theorem excludes_cases {n : Nat} (st : State n) (o : Wire n)
    (h : excludes st o = true) :
    (∃ r i x, o = (⟨.seat r i, .head x⟩ : Wire n) ∧
        o ∉ st.votes ∧ equivocates (votesAt st r) i = true) ∨
      (∃ s b raw support, o = (⟨.proposer s, .proposal b raw support⟩ : Wire n) ∧
        o ∉ st.proposals ∧ b ∈ st.blocks) := by
  obtain ⟨auth, payload⟩ := o
  cases auth with
  | seat r i =>
      cases payload with
      | head x => exact Or.inl ⟨r, i, x, rfl, (excludes_head_iff st r i x).mp h⟩
      | proposal b raw support => simp [excludes] at h
  | proposer s =>
      cases payload with
      | head x => simp [excludes] at h
      | proposal b raw support =>
          exact Or.inr ⟨s, b, raw, support, rfl, (excludes_proposal_iff st s b raw support).mp h⟩
  | none => cases payload <;> simp [excludes] at h

/-- `processed` and `excludes` are disjoint. -/
theorem excludes_not_processed {n : Nat} (st : State n) (o : Wire n)
    (h : excludes st o = true) : processed st o = false := by
  rcases excludes_cases st o h with ⟨r, i, x, rfl, hm, _⟩ | ⟨s, b, raw, support, rfl, hm, _⟩
  · simpa [processed] using hm
  · simpa [processed] using hm

/-- The executable first-copy filter has no duplicate objects. -/
private theorem eraseDups_nodup {α : Type} [BEq α] [LawfulBEq α] (xs : List α) :
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

/-- Adding stored HEADs cannot remove evidence of equivocation. -/
theorem equivocates_mono {n : Nat} (xs ys : List (Wire n)) (i : Fin n)
    (hsub : xs ⊆ ys) (he : equivocates xs i = true) : equivocates ys i = true := by
  have hlen : (seatVotes xs i).eraseDups.length ≤ (seatVotes ys i).eraseDups.length := by
    rw [← List.toFinset_card_of_nodup (eraseDups_nodup (seatVotes xs i)),
      ← List.toFinset_card_of_nodup (eraseDups_nodup (seatVotes ys i))]
    apply Finset.card_le_card
    intro o ho
    obtain ⟨hm, hi⟩ := List.mem_filter.mp (List.mem_eraseDups.mp (List.mem_toFinset.mp ho))
    exact List.mem_toFinset.mpr (List.mem_eraseDups.mpr (List.mem_filter.mpr ⟨hsub hm, hi⟩))
  simp only [equivocates, decide_eq_true_eq] at he ⊢
  omega

private theorem votesAt_subset {n : Nat} (a b : State n) (r : Slot)
    (hsub : a.votes ⊆ b.votes) : votesAt a r ⊆ votesAt b r := by
  intro o ho
  obtain ⟨hm, hl⟩ := List.mem_filter.mp ho
  exact List.mem_filter.mpr ⟨hsub hm, hl⟩

/-- An exclusion survives a state change that keeps the stored HEADs and
blocks and does not process the excluded object. -/
private theorem excludes_mono {n : Nat} (st st' : State n) (o : Wire n)
    (hv : st.votes ⊆ st'.votes) (hb : st.blocks ⊆ st'.blocks)
    (hp : processed st' o = false) (h : excludes st o = true) : excludes st' o = true := by
  rcases excludes_cases st o h with ⟨r, i, x, rfl, _, he⟩ | ⟨s, b, raw, support, rfl, _, hbm⟩
  · rw [excludes_head_iff]
    exact ⟨by simpa [processed] using hp, equivocates_mono _ _ i (votesAt_subset _ _ r hv) he⟩
  · rw [excludes_proposal_iff]
    exact ⟨by simpa [processed] using hp, hb hbm⟩

/-- `excludes` reads only the stored HEADs, blocks, and proposal wires. -/
private theorem excludes_congr {n : Nat} (st st' : State n) (o : Wire n)
    (hv : st'.votes = st.votes) (hb : st'.blocks = st.blocks)
    (hp : st'.proposals = st.proposals) : excludes st' o = excludes st o := by
  simp only [excludes, votesAt, hv, hb, hp]

/-! Monotonicity of the stores under `process` and `clock`. -/

theorem admitVote_votes_subset (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    st.votes ⊆ (admitVote p st o).votes := by
  unfold admitVote
  split
  · dsimp only
    split
    · exact List.Subset.refl _
    · exact List.subset_append_left _ _
  · exact List.Subset.refl _

theorem admitVote_blocks (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    (admitVote p st o).blocks = st.blocks := by
  unfold admitVote
  split
  · dsimp only
    split <;> rfl
  · rfl

theorem admitVote_proposals (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    (admitVote p st o).proposals = st.proposals := by
  unfold admitVote
  split
  · dsimp only
    split <;> rfl
  · rfl

private theorem fold_votes_subset (p : Params) {n : Nat} (raw : List (HeadWire n))
    (st : State n) : st.votes ⊆
      (raw.foldl (fun acc row => admitVote p acc (fromHead row)) st).votes := by
  induction raw generalizing st with
  | nil => exact List.Subset.refl _
  | cons row raw ih => exact List.Subset.trans (admitVote_votes_subset p st (fromHead row)) (ih _)

private theorem fold_blocks (p : Params) {n : Nat} (raw : List (HeadWire n)) (st : State n) :
    (raw.foldl (fun acc row => admitVote p acc (fromHead row)) st).blocks = st.blocks := by
  induction raw generalizing st with
  | nil => rfl
  | cons row raw ih =>
      simp only [List.foldl_cons]
      rw [ih, admitVote_blocks]

private theorem fold_proposals (p : Params) {n : Nat} (raw : List (HeadWire n))
    (st : State n) :
    (raw.foldl (fun acc row => admitVote p acc (fromHead row)) st).proposals =
      st.proposals := by
  induction raw generalizing st with
  | nil => rfl
  | cons row raw ih =>
      simp only [List.foldl_cons]
      rw [ih, admitVote_proposals]

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

/-- A handler call never removes a stored proposal wire. -/
theorem process_proposals_subset (p : Params) {n : Nat} (st : State n) (o : Wire n) :
    st.proposals ⊆ (process p st o).proposals := by
  obtain ⟨auth, payload⟩ := o
  cases auth <;> cases payload <;> simp only [process]
  all_goals first
    | exact List.Subset.refl _
    | exact (admitVote_proposals p st _).symm ▸ List.Subset.refl _
    | skip
  rename_i s b raw support
  unfold admitProposal
  dsimp only
  split
  · exact List.Subset.refl _
  · rw [fold_proposals]
    exact List.subset_append_left _ _

/-- The gate changes only the records and the lock. -/
private theorem gate_stores (p : Params) {n : Nat} (st : State n) (r : Slot) :
    (gate p st r).votes = st.votes ∧ (gate p st r).blocks = st.blocks ∧
      (gate p st r).proposals = st.proposals := by
  unfold gate
  split
  · exact ⟨rfl, rfl, rfl⟩
  · simp only []
    repeat' split
    all_goals exact ⟨rfl, rfl, rfl⟩

/-- No clock evaluation (expiry, `freeze`, the early save, `gate`) changes
the stored HEADs, blocks, or proposal wires. -/
theorem clock_stores (p : Params) {n : Nat} (st : State n) (t : Time) :
    (clock p st t).votes = st.votes ∧ (clock p st t).blocks = st.blocks ∧
      (clock p st t).proposals = st.proposals := by
  let newLock := st.lock.bind (fun pair => if t < pair.2 then some pair else none)
  let s0 : State n := { st with now := t, lock := newLock }
  let fSlot := ((t - 3 * p.Δ) / (4 * p.Δ)).toNat
  let s1 := if 0 ≤ t - 3 * p.Δ && t == freezeTime p fSlot then freeze p s0 fSlot else s0
  let eSlot := ((t - 2 * p.Δ) / (4 * p.Δ)).toNat
  let s2 := if 0 ≤ t - 2 * p.Δ && t == earlyTime p eSlot then
    { s1 with early := s1.early ++ [(eSlot, earlyVotes p s1 eSlot)] } else s1
  let dSlot := ((t - 6 * p.Δ) / (4 * p.Δ)).toNat
  change (if 0 ≤ t - 6 * p.Δ && t == gateTime p dSlot then gate p s2 dSlot else s2).votes =
      st.votes ∧
    (if 0 ≤ t - 6 * p.Δ && t == gateTime p dSlot then gate p s2 dSlot else s2).blocks =
      st.blocks ∧
    (if 0 ≤ t - 6 * p.Δ && t == gateTime p dSlot then gate p s2 dSlot else s2).proposals =
      st.proposals
  have h1 : s1.votes = st.votes ∧ s1.blocks = st.blocks ∧ s1.proposals = st.proposals := by
    dsimp [s1]
    split <;> exact ⟨rfl, rfl, rfl⟩
  have h2 : s2.votes = st.votes ∧ s2.blocks = st.blocks ∧ s2.proposals = st.proposals := by
    dsimp [s2]
    split
    · exact h1
    · exact h1
  split
  · obtain ⟨hv, hb, hp⟩ := gate_stores p s2 dSlot
    exact ⟨hv.trans h2.1, hb.trans h2.2.1, hp.trans h2.2.2⟩
  · exact h2

/-! Permanence of both clauses: one handler call or one clock tick keeps an
exclusion. -/

/-- One HEAD call keeps an exclusion. A call for the excluded HEAD itself
meets the same equivocation test; a HEAD call does not store a proposal
wire. -/
private theorem admitVote_keeps_excludes (p : Params) {n : Nat} (st : State n)
    (o o' : Wire n) (h : excludes st o = true) :
    excludes (admitVote p st o') o = true := by
  refine excludes_mono st _ o (admitVote_votes_subset p st o')
    (by rw [admitVote_blocks]) ?_ h
  rcases excludes_cases st o h with
    ⟨r, i, x, rfl, hm, he⟩ | ⟨s, b, raw, support, rfl, hm, _⟩
  · simp only [processed, decide_eq_false_iff_not]
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
        simp [he]
    · exact hm
  · simpa [processed, admitVote_proposals] using hm

private theorem fold_keeps_excludes (p : Params) {n : Nat} (raw : List (HeadWire n))
    (st : State n) (o : Wire n) (h : excludes st o = true) :
    excludes (raw.foldl (fun acc row => admitVote p acc (fromHead row)) st) o = true := by
  induction raw generalizing st with
  | nil => exact h
  | cons row raw ih => exact ih _ (admitVote_keeps_excludes p st o (fromHead row) h)

/-- A handler call keeps an exclusion. An accepted proposal wire has a block
that was not stored, so it is not an excluded wire. -/
theorem excludes_process (p : Params) {n : Nat} (st : State n) (o o' : Wire n)
    (h : excludes st o = true) : excludes (process p st o') o = true := by
  obtain ⟨auth, payload⟩ := o'
  cases auth <;> cases payload <;> simp only [process]
  all_goals first
    | exact h
    | exact admitVote_keeps_excludes p st o _ h
    | skip
  rename_i s b' raw' support'
  unfold admitProposal
  dsimp only
  split
  · exact h
  · rename_i hguard
    apply fold_keeps_excludes
    refine excludes_mono st _ o (List.Subset.refl _) (List.subset_append_left _ _) ?_ h
    rcases excludes_cases st o h with
      ⟨r, i, x, rfl, hm, _⟩ | ⟨s₀, b, raw, support, rfl, hm, hb⟩
    · simpa [processed] using hm
    · simp only [processed, List.mem_append, List.mem_singleton, decide_eq_false_iff_not,
        not_or]
      refine ⟨hm, fun heq => hguard ?_⟩
      simp only [Signed.mk.injEq, Msg.proposal.injEq] at heq
      obtain ⟨_, rfl, _, _⟩ := heq
      simp [hb]

/-- A clock tick keeps an exclusion: it changes none of the stores that
`excludes` reads. The L* clauses do not read the clock. -/
theorem excludes_clock (p : Params) {n : Nat} (st : State n) (o : Wire n) (t : Time) :
    excludes (clock p st t) o = excludes st o := by
  obtain ⟨hv, hb, hp⟩ := clock_stores p st t
  exact excludes_congr st _ o hv hb hp

/-- An excluded object does not change the state. -/
theorem excludes_inert (p : Params) {n : Nat} :
    ∀ st o, (lstar p n).excludes st o = true → (lstar p n).process st o = st := by
  intro (st : State n) (o : Wire n) h
  change excludes st o = true at h
  change process p st o = st
  rcases excludes_cases st o h with
    ⟨r, i, x, rfl, _, he⟩ | ⟨s, b, raw, support, rfl, _, hb⟩
  · simp only [process, admitVote]
    rw [ite_eq_left]
    simp [he]
  · simp only [process, admitProposal]
    rw [ite_eq_left]
    simp [hb]

set_option linter.unusedFintypeInType false in
/-- Exclusion is stable along a run. The L* clauses do not read the clock,
so the schedule premise is not used. -/
theorem excludes_stable (p : Params) {n : Nat} :
    ∀ {V : Type} [DecidableEq V] [Fintype V] (E : Env V)
      (rho : Run V (lstar p n)), ScheduleWellFormed E rho → ∀ v o i j, i ≤ j →
        (lstar p n).excludes (Run.stateBefore (lstar p n) rho i v) o = true →
        (lstar p n).excludes (Run.stateBefore (lstar p n) rho j v) o = true := by
  intro V _ _ E rho _ v o i j hij h
  exact stateBefore_stable (P := lstar p n) (fun st => excludes st o = true)
    (fun st t hq => (excludes_clock p st o t).trans hq)
    (fun st o' hq => excludes_process p st o o' hq) rho hij v h

set_option linter.unusedFintypeInType false in
theorem processed_stable (p : Params) {n : Nat} :
    ∀ {V : Type} [DecidableEq V] [Fintype V] (E : Env V)
      (rho : Run V (lstar p n)), ScheduleWellFormed E rho → ∀ v o i j, i ≤ j →
        (lstar p n).processed (Run.stateBefore (lstar p n) rho i v) o = true →
        (lstar p n).processed (Run.stateBefore (lstar p n) rho j v) o = true := by
  intro V _ _ E rho _ v o i j hij h
  exact stateBefore_stable (P := lstar p n) (fun st => processed st o = true)
    (fun st t hq => by
      change processed (clock p st t) o = true
      obtain ⟨hv, _, hp⟩ := clock_stores p st t
      obtain ⟨auth, payload⟩ := o
      cases payload with
      | head x => simpa [processed, hv] using hq
      | proposal b raw support => simpa [processed, hp] using hq)
    (fun st o' hq => by
      change processed (process p st o') o = true
      obtain ⟨auth, payload⟩ := o
      cases payload with
      | head x =>
          simp only [processed, decide_eq_true_eq] at hq ⊢
          exact process_votes_subset p st o' hq
      | proposal b raw support =>
          simp only [processed, decide_eq_true_eq] at hq ⊢
          exact process_proposals_subset p st o' hq)
    rho hij v h

set_option linter.unusedFintypeInType false in
theorem deps_stable (p : Params) {n : Nat} :
    ∀ {V : Type} [DecidableEq V] [Fintype V] (E : Env V)
      (rho : Run V (lstar p n)), ScheduleWellFormed E rho → ∀ v o i j, i ≤ j →
        (lstar p n).depsPresent (Run.stateBefore (lstar p n) rho i v) o = true →
        (lstar p n).depsPresent (Run.stateBefore (lstar p n) rho j v) o = true := by
  intro V _ _ E rho _ v o i j hij h
  exact stateBefore_stable (P := lstar p n) (fun st => depsPresent st o = true)
    (fun st t hq => by
      change depsPresent (clock p st t) o = true
      obtain ⟨_, hb, _⟩ := clock_stores p st t
      obtain ⟨auth, payload⟩ := o
      cases payload with
      | head x => rfl
      | proposal b raw support => simpa [depsPresent, blockKnown, hb] using hq)
    (fun st o' hq => by
      change depsPresent (process p st o') o = true
      obtain ⟨auth, payload⟩ := o
      cases payload with
      | head x => rfl
      | proposal b raw support =>
          simp only [depsPresent, blockKnown, decide_eq_true_eq] at hq ⊢
          exact process_blocks_subset p st o' hq)
    rho hij v h

theorem handles_carries (p : Params) {n : Nat} :
    ∀ st o o', (lstar p n).handles st o o' → o = o' ∨ (lstar p n).carries o o' := by
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

/-! The second-wire test at run level: a stored proposal wire has its block
stored, so another wire with the same block is excluded. -/

/-- Every stored proposal wire has its block stored. -/
def ProposalBlocksStored {n : Nat} (st : State n) : Prop :=
  ∀ o ∈ st.proposals, ∀ b raw support, o.payload = .proposal b raw support → b ∈ st.blocks

private theorem proposalBlocksStored_process (p : Params) {n : Nat} (st : State n)
    (o' : Wire n) (h : ProposalBlocksStored st) : ProposalBlocksStored (process p st o') := by
  obtain ⟨auth, payload⟩ := o'
  cases auth <;> cases payload <;> simp only [process]
  all_goals first
    | exact h
    | skip
  · intro o ho b raw support hp
    rw [admitVote_proposals] at ho
    rw [admitVote_blocks]
    exact h o ho b raw support hp
  rename_i s b' raw' support'
  unfold admitProposal
  dsimp only
  split
  · exact h
  · intro o ho b raw support hp
    rw [fold_proposals] at ho
    rw [fold_blocks]
    simp only [List.mem_append, List.mem_singleton] at ho ⊢
    rcases ho with ho | rfl
    · exact Or.inl (h o ho b raw support hp)
    · simp only [Msg.proposal.injEq] at hp
      exact Or.inr hp.1.symm

/-- In every state of a run, every stored proposal wire has its block
stored. -/
theorem proposalBlocksStored_run (p : Params) {n : Nat} {V : Type} [DecidableEq V]
    (rho : Run V (lstar p n)) (i : Nat) (v : V) :
    ProposalBlocksStored (Run.stateBefore (lstar p n) rho i v) := by
  refine stateBefore_stable (P := lstar p n) ProposalBlocksStored
    (fun st t hq => ?_) (fun st o' hq => proposalBlocksStored_process p st o' hq)
    rho (Nat.zero_le i) v ?_
  · change ProposalBlocksStored (clock p st t)
    obtain ⟨_, hb, hp⟩ := clock_stores p st t
    intro o ho b raw support hpay
    rw [hp] at ho
    rw [hb]
    exact hq o ho b raw support hpay
  · intro o ho
    simp [Run.stateBefore, World.init, lstar, initial] at ho

/-- A second well-formed wire for a stored block is excluded in every
state of a run: a faulty proposer signed two wires with the same block, and
the store refuses the one that it did not process. -/
theorem excludes_second_wire (p : Params) {n : Nat} {V : Type} [DecidableEq V]
    (rho : Run V (lstar p n)) (i : Nat) (v : V) (o₁ : Wire n) (s : Slot) (b : Block)
    (raw₁ support₁ raw₂ support₂ : List (HeadWire n))
    (h₁ : o₁ ∈ (Run.stateBefore (lstar p n) rho i v).proposals)
    (hp₁ : o₁.payload = .proposal b raw₁ support₁)
    (h₂ : (⟨.proposer s, .proposal b raw₂ support₂⟩ : Wire n) ∉
      (Run.stateBefore (lstar p n) rho i v).proposals) :
    (lstar p n).excludes (Run.stateBefore (lstar p n) rho i v)
      ⟨.proposer s, .proposal b raw₂ support₂⟩ = true :=
  (excludes_proposal_iff _ s b raw₂ support₂).mpr
    ⟨h₂, proposalBlocksStored_run p rho i v o₁ h₁ b raw₁ support₁ hp₁⟩

/-- The store dependency lookup with the `wellFormed` parent-slot test: the
parent is stored with a slot below `s` iff a stored block has the parent's root
and a slot below `s`. `wellFormed` itself reads no store. -/
theorem blockKnown_parent_slot_iff_root {n : Nat} (st : State n) (b : Block) (s : Slot)
    (hr : ∀ q ∈ st.blocks, q.root = b.parent.root → q = b.parent) :
    (blockKnown st b.parent = true ∧ b.parent.slot < s) ↔
      ∃ q ∈ st.blocks, q.root = b.parent.root ∧ q.slot < s := by
  simpa [blockKnown] using parent_mem_and_iff_root b st.blocks (fun q => q.slot < s) hr

/-- A proposal with an unknown parent is a missing dependency: admission
returns the state before it stores the block or admits carried HEADs. The
handler does not repeat the parent-slot test of `wellFormed`. -/
theorem admitProposal_missingParent (p : Params) {n : Nat} (st : State n) (o : Wire n)
    (b : Block) (raw : List (HeadWire n)) (h : ¬ blockKnown st b.parent) :
    admitProposal p st o b raw = st := by
  simp [admitProposal, h]

end AvailableChain.LStar
end
