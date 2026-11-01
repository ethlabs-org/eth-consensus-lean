module
public import AvailableChainFGSA.Proofs.StoreInv
public import AvailableChainFGSA.Proofs.Reconcile
public import AvailableChainFGSA.Proofs.Metadata
public import AvailableChainFGSA.Proofs.NamedStore
public import AvailableChainFGSARun.Statements.Excludes
public import AvailableChainFGSARun.Proofs.Protocol
public import AvailableChainEngineV2.Conditions.Duty.Schedule

-- ROOT-DIGEST-2: private matcher copy; equality is checked by the kernel (BUILD B3).
namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

private def hygiene_invalidForParent (p : Params) (st : State p.n)
    (N : NamedProposal p.n) : Bool :=
  if !namedParentHeld st N then false else
  match parentFG st N.erase with
  | none => false
  | some P => !rowsValidForParent p P N.slot N.rows

private theorem hygiene_invalidForParent_eq :
    @invalidForParent = @hygiene_invalidForParent := rfl

private theorem hygiene_namedParentHeld_eq {n : Nat} (st : State n)
    (N : NamedProposal n) : namedParentHeld st N = decide (N.parent ∈ st.namedBodies) := rfl

end AvailableChain.FGSA.Run

public section

/-! `excludes_inert` for FG-SA on engine v2 (plan
`docs/plans/2026-09-29-fgsa-composition-t7-t1.md` r11, T7.2; lead input,
2026-09-29).

* One state (`excludesS_inert`, `excludes_inert`): at EVERY store state, the
  delivery of an excluded object does not change the state. This is the
  one-state field of the frozen `V2.D.HooksSound`.
* One epoch (`excludes_inert_epoch`): an exclusion holds, and its delivery
  is a no-op, at every later state of the same restart epoch with a clock
  that does not go back (`Epoch p true`). The clock-free exclusions
  (`excludesFixed`) need no clock condition (`excludesFixed_inert_epoch`).
  `restartFree` is not a premise: the epoch is a sequence of store steps.
* Runs (`excludes_stable_epoch`): on a restart-free interval of a run whose
  ticks of the node do not move its store clock back, the exclusion is kept
  and the delivery is a no-op. This is the stability field of
  `V2.D.HooksSound` with the clock premise explicit.

The Grid CO vote facts are proved here from the model: T7 imports no Grid CO
proof module (plan §3.1). They and the other general-purpose helpers (clock
arithmetic, store folds) are in the namespace `Internal`; they are not
private, so that the used-constant check sees them. -/

namespace AvailableChain.FGSA.Run

open AvailableChain.SimplexFG

/-! ### Grid CO vote facts (local, from `GridCO/Model/Protocol.lean`) -/

namespace Internal

section Grid

variable {q : GridCO.Params} {n : Nat}

theorem eraseDups_nodup' {α : Type} [BEq α] [LawfulBEq α] (xs : List α) :
    xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons a xs =>
      rw [List.eraseDups_cons]
      apply List.nodup_cons.mpr
      constructor
      · simp
      · exact eraseDups_nodup' (xs.filter (fun b => !b == a))
termination_by xs.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] Equivocation is kept when the vote list grows.
-/
theorem grid_equivocates_mono (xs ys : List (GridCO.Wire n .root)) (i : Fin n) (hsub : xs ⊆ ys)
    (he : GridCO.equivocates xs i = true) : GridCO.equivocates ys i = true := by
  have hlen : (GridCO.seatVotes xs i).eraseDups.length ≤
      (GridCO.seatVotes ys i).eraseDups.length := by
    rw [← List.toFinset_card_of_nodup (eraseDups_nodup' (GridCO.seatVotes xs i)),
      ← List.toFinset_card_of_nodup (eraseDups_nodup' (GridCO.seatVotes ys i))]
    apply Finset.card_le_card
    intro o ho
    obtain ⟨hm, hi⟩ := List.mem_filter.mp (List.mem_eraseDups.mp (List.mem_toFinset.mp ho))
    exact List.mem_toFinset.mpr (List.mem_eraseDups.mpr (List.mem_filter.mpr ⟨hsub hm, hi⟩))
  simp only [GridCO.equivocates, decide_eq_true_eq] at he ⊢
  omega

theorem grid_votesAt_subset (a b : GridCO.State n .root) (r : Slot) (hsub : a.votes ⊆ b.votes) :
    GridCO.votesAt a r ⊆ GridCO.votesAt b r := by
  intro o ho
  obtain ⟨hm, hl⟩ := List.mem_filter.mp ho
  exact List.mem_filter.mpr ⟨hsub hm, hl⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] (i) The old-label tests of `GridCO.excludes`
and `GridCO.admitVote` agree:
`r < cur − 1 ↔ r + 1 < cur` on `Nat`. -/
theorem lt_sub_one_iff_add_one_lt (r cur : Nat) : r < cur - 1 ↔ r + 1 < cur := by omega

theorem grid_excludes_head_iff (st : GridCO.State n .root) (r : Slot) (i : Fin n) (x : BlockId) :
    GridCO.excludes q st ⟨.seat r i, .head x⟩ = true ↔
      (⟨.seat r i, .head x⟩ : GridCO.Wire n .root) ∉ st.votes ∧
        (r + 1 < (st.now / (4 * q.Δ)).toNat ∨
          GridCO.equivocates (GridCO.votesAt st r) i = true) := by
  simp [GridCO.excludes]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] Only a HEAD can be excluded by Grid CO. -/
theorem grid_excludes_head (st : GridCO.State n .root) (o : GridCO.Wire n .root)
    (h : GridCO.excludes q st o = true) : ∃ r i x,
      o = (⟨.seat r i, .head x⟩ : GridCO.Wire n .root) := by
  obtain ⟨auth, payload⟩ := o
  cases auth with
  | seat r i =>
      cases payload with
      | head x => exact ⟨r, i, x, rfl⟩
      | proposal b raw support => simp [GridCO.excludes] at h
  | proposer s => cases payload <;> simp [GridCO.excludes] at h
  | none => cases payload <;> simp [GridCO.excludes] at h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] `GridCO.excludes` reads only the stored votes
and the clock. -/
theorem grid_excludes_congr {st st' : GridCO.State n .root} (hv : st'.votes = st.votes)
    (hn : st'.now = st.now) (o : GridCO.Wire n .root) :
    GridCO.excludes q st' o = GridCO.excludes q st o := by
  unfold GridCO.excludes GridCO.votesAt
  rw [hv, hn]

theorem grid_admitVote_now (st : GridCO.State n .root) (o : GridCO.Wire n .root) :
    (GridCO.admitVote q st o).now = st.now := by
  obtain ⟨auth, payload⟩ := o
  cases auth <;> cases payload <;> simp only [GridCO.admitVote]
  split <;> rfl

theorem grid_admitVote_votes_subset (st : GridCO.State n .root) (o : GridCO.Wire n .root) :
    st.votes ⊆ (GridCO.admitVote q st o).votes := by
  obtain ⟨auth, payload⟩ := o
  cases auth <;> cases payload <;> simp only [GridCO.admitVote] <;>
    first
    | exact List.Subset.refl _
    | split
      · exact List.Subset.refl _
      · exact List.subset_append_left _ _

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] An excluded HEAD is refused: `admitVote`
returns the state. -/
theorem grid_admitVote_of_excludes (st : GridCO.State n .root) (o : GridCO.Wire n .root)
    (h : GridCO.excludes q st o = true) : GridCO.admitVote q st o = st := by
  obtain ⟨r, i, x, rfl⟩ := grid_excludes_head st o h
  obtain ⟨hm, hc⟩ := (grid_excludes_head_iff st r i x).mp h
  unfold GridCO.admitVote
  dsimp only
  rw [ite_eq_left]
  rcases hc with hc | hc
  · simp [(lt_sub_one_iff_add_one_lt r _).mpr hc]
  · simp [hc]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] An exclusion survives a state change that keeps
the clock, keeps the
stored votes, and does not store the excluded HEAD. -/
theorem grid_excludes_of_votes (st st' : GridCO.State n .root) (o : GridCO.Wire n .root)
    (hnow : st'.now = st.now) (hsub : st.votes ⊆ st'.votes) (hm : o ∉ st'.votes)
    (h : GridCO.excludes q st o = true) : GridCO.excludes q st' o = true := by
  obtain ⟨r, i, x, rfl⟩ := grid_excludes_head st o h
  rw [grid_excludes_head_iff] at h ⊢
  refine ⟨hm, ?_⟩
  rw [hnow]
  exact h.2.imp id (grid_equivocates_mono _ _ i (grid_votesAt_subset _ _ r hsub))

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] One vote call keeps an exclusion. -/
theorem grid_admitVote_keeps (st : GridCO.State n .root) (o o' : GridCO.Wire n .root)
    (h : GridCO.excludes q st o = true) :
    GridCO.excludes q (GridCO.admitVote q st o') o = true := by
  by_cases ho : o' = o
  · subst ho; rw [grid_admitVote_of_excludes st o' h]; exact h
  apply grid_excludes_of_votes st _ o (grid_admitVote_now st o') (grid_admitVote_votes_subset st o')
    _ h
  obtain ⟨r, i, x, rfl⟩ := grid_excludes_head st o h
  have hm := ((grid_excludes_head_iff (q := q) st r i x).mp h).1
  obtain ⟨auth, payload⟩ := o'
  cases auth <;> cases payload <;> simp only [GridCO.admitVote] <;>
    first
    | exact hm
    | split
      · exact hm
      · simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨hm, fun e => ho e.symm⟩

theorem grid_fold_keeps (raw : List (GridCO.HeadWire n .root)) (st : GridCO.State n .root) (o :
    GridCO.Wire n .root)
    (h : GridCO.excludes q st o = true) :
    GridCO.excludes q (raw.foldl (fun acc row => GridCO.admitVote q acc (GridCO.fromHead row)) st) o
      = true := by
  induction raw generalizing st with
  | nil => exact h
  | cons row raw ih => exact ih _ (grid_admitVote_keeps st o _ h)

theorem grid_fold_now (raw : List (GridCO.HeadWire n .root)) (st : GridCO.State n .root) :
    (raw.foldl (fun acc row => GridCO.admitVote q acc (GridCO.fromHead row)) st).now = st.now := by
  induction raw generalizing st with
  | nil => rfl
  | cons row raw ih => rw [List.foldl_cons, ih, grid_admitVote_now]

theorem grid_fold_votes_subset (raw : List (GridCO.HeadWire n .root)) (st : GridCO.State n .root) :
    st.votes ⊆
      (raw.foldl (fun acc row => GridCO.admitVote q acc (GridCO.fromHead row)) st).votes := by
  induction raw generalizing st with
  | nil => exact List.Subset.refl _
  | cons row raw ih => exact List.Subset.trans (grid_admitVote_votes_subset st _) (ih _)

theorem grid_admitProposal_now (st : GridCO.State n .root) (o : GridCO.Wire n .root) (b : Block)
    (raw : List (GridCO.HeadWire n .root)) : (GridCO.admitProposal q st o b raw).now = st.now := by
  unfold GridCO.admitProposal
  dsimp only
  split_ifs
  · rfl
  · exact grid_fold_now raw _

theorem grid_admitProposal_votes_subset (st : GridCO.State n .root) (o : GridCO.Wire n .root)
    (b : Block)
    (raw : List (GridCO.HeadWire n .root)) : st.votes ⊆ (GridCO.admitProposal q st o b
        raw).votes := by
  unfold GridCO.admitProposal
  dsimp only
  split_ifs
  · exact List.Subset.refl _
  · refine List.Subset.trans ?_ (grid_fold_votes_subset raw _)
    exact List.Subset.refl _

theorem grid_admitProposal_keeps (st : GridCO.State n .root) (o : GridCO.Wire n .root) (b : Block)
    (raw : List (GridCO.HeadWire n .root)) (o' : GridCO.Wire n .root) (h : GridCO.excludes q st
        o' = true) :
    GridCO.excludes q (GridCO.admitProposal q st o b raw) o' = true := by
  unfold GridCO.admitProposal
  dsimp only
  split_ifs
  · exact h
  · apply grid_fold_keeps
    rw [grid_excludes_congr rfl rfl]
    exact h

end Grid

end Internal

open Internal

variable {p : Params}

/-! ### The hooks at a decoded object -/

theorem excludesS_of_vote (st : State p.n) {o : Obj p} {s : Slot} {i : Fin p.n} {b : BlockId}
    (hd : (toWire p o).decode = some (.vote s i b)) :
    excludesS p st o = GridCO.excludes p.toParams.engine st.base ⟨.seat s i, .head b⟩ := by
  unfold excludesS; rw [hd]; rfl

theorem excludesS_of_row (st : State p.n) {o : Obj p} {i : Fin p.n} {body : RowPayload}
    (hd : (toWire p o).decode = some (.row i body)) :
    excludesS p st o = false := by
  unfold excludesS; rw [hd]

theorem excludesS_of_block (st : State p.n) {o : Obj p} {s : Slot} {N : NamedProposal p.n}
    (hd : (toWire p o).decode = some (.block s N)) :
    excludesS p st o = (blockExcluded st N.erase || invalidForParent p st N) := by
  unfold excludesS; rw [hd]

theorem excludesS_of_none (st : State p.n) {o : Obj p} (hd : (toWire p o).decode = none) :
    excludesS p st o = false := by
  unfold excludesS; rw [hd]

/-! ### One state: an excluded delivery is a no-op -/

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] (ii) The decode round trip of a row: the row
wire that `excludesS` rebuilds
from the decode is the row wire that `FGSA.process` gives to `admitRow`. -/
theorem row_wire_roundtrip {o : Obj p} {i : Fin p.n} {body : RowPayload}
    (hd : (toWire p o).decode = some (.row i body)) :
    (⟨(toWire p o).auth, body⟩ : RowWire p.n) = ⟨.seat .fg i, body⟩ := by
  rw [decode_eq_row.mp hd]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] (iii) A proposal whose block is not compatible
with F is refused:
`admitBlock` returns the state. If the FG parent is not stored, `admitBlock`
refuses at once; else the FG acceptance test `F ⪯ fgBlock P b rows` fails,
because under the other tests the erasure of `fgBlock P b rows` is `b`
(`eraseFG_fgBlock`), so F would be compatible with `b`. -/
theorem admitBlock_of_blockExcluded (st : State p.n) (s : Slot) (N : NamedProposal p.n)
    (h : blockExcluded st N.erase = true) : admitBlock p st s N = st := by
  unfold admitBlock
  split
  · rfl
  · split
    · rfl
    · rename_i P hP
      rw [ite_eq_right]
      intro hacc
      have hc := blockAccepted_contentOk hacc
      simp only [blockAccepted, Bool.and_eq_true] at hacc
      obtain ⟨⟨⟨⟨⟨⟨⟨hgen, -⟩, -⟩, hF⟩, -⟩, -⟩, -⟩, _⟩ := hacc
      have hb : N.erase ≠ .genesis := by simpa using hgen
      have hpar : eraseFG P = N.erase.parent := by
        simpa using (pickPair_some_spec _ _ hP).2
      have he := eraseFG_fgBlock hb hpar N.rows (contentOk_rowsOk hc)
      have hpre : Block.Preceq (eraseFG st.fg.F) N.erase := he ▸ eraseFG_preceq hF
      have hcompat : Block.compatible N.erase (eraseFG st.fg.F) = true := by
        rw [block_compatible_comm]
        exact block_compatible_of_preceq hpre
      simp [blockExcluded, activeCompatible, hcompat] at h

/-- [ROOT-DIGEST-2 W2; DC NamedStore] Invalidity persists when both parent stores grow. -/
theorem invalidForParent_mono (st st' : State p.n) (hsub : st.fg.TF ⊆ st'.fg.TF)
    (hn : st.namedBodies ⊆ st'.namedBodies) (N : NamedProposal p.n)
    (h : invalidForParent p st N = true) : invalidForParent p st' N = true := by
  have hp : namedParentHeld st N = true := by
    rw [hygiene_invalidForParent_eq] at h
    unfold hygiene_invalidForParent at h
    split at h
    · cases h
    · simpa using ‹¬ (!namedParentHeld st N) = true›
  have hp' : namedParentHeld st' N = true := by
    exact decide_eq_true (hn (of_decide_eq_true hp))
  rw [hygiene_invalidForParent_eq] at h ⊢
  unfold hygiene_invalidForParent at h ⊢
  simp only [hp, hp', Bool.not_true, Bool.false_eq_true, ite_false] at h ⊢
  cases hP : parentFG st N.erase with
  | none => simp only [hP, Bool.false_eq_true] at h
  | some P =>
    obtain ⟨hm, he⟩ := (parentFG_spec st N.erase P).mp hP
    have hP' := (parentFG_spec st' N.erase P).mpr ⟨hsub hm, he⟩
    simpa only [hP, hP'] using h

/-- [ROOT-DIGEST-2 W2; DC NamedStore] A clock keeps both parent lookup domains. -/
theorem invalidForParent_clock (st : State p.n) (t : Time) (N : NamedProposal p.n) :
    invalidForParent p (FGSA.clock p st t) N = invalidForParent p st N := by
  have hP : parentFG (FGSA.clock p st t) N.erase = parentFG st N.erase := by
    change pickPair (FGSA.clock p st t).fg.TF _ = pickPair st.fg.TF _
    rw [clock_fg]
  rw [hygiene_invalidForParent_eq]
  dsimp only [hygiene_invalidForParent]
  simp only [hygiene_namedParentHeld_eq, clock_namedBodies, hP]
  rfl

/-- [ROOT-DIGEST-2 W2; DC NamedStore] Invalidity causes refusal without writes. -/
theorem admitBlock_of_invalidForParent (st : State p.n) (s : Slot) (N : NamedProposal p.n)
    (h : invalidForParent p st N = true) : admitBlock p st s N = st := by
  rw [hygiene_invalidForParent_eq] at h
  unfold hygiene_invalidForParent at h
  split at h
  · cases h
  · cases hP : parentFG st N.erase with
    | none => simp only [hP, Bool.false_eq_true] at h
    | some P =>
      have hv : rowsValidForParent p P N.slot N.rows = false := by
        simpa only [hP, Bool.not_eq_true'] using h
      exact admitBlock_invalid_rows p st s N P hP hv

/-- [ROOT-DIGEST-2 W2; DC NamedReceiptCalls] Invalid proposals cannot call carried handlers. -/
theorem invalidForParent_no_carried (st : State p.n) (s : Slot) (N : NamedProposal p.n)
    (h : invalidForParent p st N = true) :
    ¬ ∃ P, parentFG st N.erase = some P ∧ blockAccepted p st s N P = true := by
  rintro ⟨P, hP, ha⟩
  have hv := blockAccepted_rowsValid ha
  rw [named_erase_slot] at hv
  rw [hygiene_invalidForParent_eq] at h
  unfold hygiene_invalidForParent at h
  split at h
  · cases h
  · simp only [hP, hv, Bool.not_true, Bool.false_eq_true] at h

/-- [ROOT-DIGEST-2 W2; DC NamedStore] Delivery retains all exact named bodies. -/
theorem process_namedBodies_subset (st : State p.n) (w : Wire p.n) :
    st.namedBodies ⊆ (FGSA.process p st w).namedBodies := by
  intro N hN
  rcases (mem_namedBodies _ N).mp hN with rfl | ⟨s, hs⟩
  · exact (mem_namedBodies _ _).mpr (Or.inl rfl)
  · exact (mem_namedBodies _ N).mpr (Or.inr
      ⟨s, (process_cumulative p st w).2.2.2.2.1.subset hs⟩)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] The delivery of an excluded object does not
change the store, at every
store state. -/
theorem excludesS_inert (st : State p.n) (o : Obj p) (h : excludesS p st o = true) :
    FGSA.process p st (toWire p o) = st := by
  unfold FGSA.process
  split
  · rename_i s i b hd
    rw [excludesS_of_vote st hd] at h
    unfold admitHead
    rw [grid_admitVote_of_excludes _ _ h]
  · rename_i i body hd
    simp only [excludesS_of_row st hd, Bool.false_eq_true] at h
  · rename_i s N hd
    rw [excludesS_of_block st hd] at h
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · exact admitBlock_of_blockExcluded st s N h
    · exact admitBlock_of_invalidForParent st s N h
  · rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] [HooksSound `excludes_inert`] The one-state
field of `V2.D.HooksSound` for
`fgsa p c`: at EVERY state, the delivery of an excluded object does not change
the state. No run, schedule or restart premise. -/
theorem excludes_inert {In : Type} (c : AppCodec In) :
    ∀ nd o, (fgsa p c).excludes nd o = true → (fgsa p c).process nd o = nd := by
  intro nd o h
  change Node.mk (FGSA.process p nd.st (toWire p o)) nd.record = nd
  rw [excludesS_inert nd.st o h]
  rfl

/-! ### Store fields along a delivery and a tick -/

namespace Internal

theorem admitRow_base (st : State p.n) (a : RowWire p.n) : (admitRow p st a).base = st.base := by
  unfold admitRow
  split
  · split <;> rfl
  · rfl

theorem foldl_admitRow_base (rows : List (RowWire p.n)) (st : State p.n) :
    (rows.foldl (admitRow p) st).base = st.base := by
  induction rows generalizing st with
  | nil => rfl
  | cons a rows ih => rw [List.foldl_cons, ih, admitRow_base]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] The state after the block admission of
`admitBlock`, with `reconcile` if F
moved, has the votes, the clock and the row pool of the state before
`reconcile`. -/
theorem ite_reconcile (st1 st : State p.n) :
    (if st1.fg.F = st.fg.F then st1 else reconcile st1).base.votes = st1.base.votes ∧
      (if st1.fg.F = st.fg.F then st1 else reconcile st1).base.now = st1.base.now ∧
      (if st1.fg.F = st.fg.F then st1 else reconcile st1).rowPool = st1.rowPool := by
  split
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨(reconcile_frame _).2.2.2.2.2.1, (reconcile_frame _).2.2.2.2.2.2.2.2.1,
      (reconcile_frame _).2.2.1⟩

end Internal

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] A delivery keeps the store clock. -/
theorem process_base_now (st : State p.n) (w : Wire p.n) :
    (FGSA.process p st w).base.now = st.base.now := by
  unfold FGSA.process
  split
  · exact grid_admitVote_now _ _
  · rw [admitRow_base]
  · unfold admitBlock
    split
    · rfl
    · split
      · rfl
      · split_ifs
        · rw [foldl_admitRow_base, (ite_reconcile _ _).2.1]
          exact grid_admitProposal_now _ _ _ _
        · rfl
  · rfl

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] A delivery keeps a Grid CO HEAD exclusion of
the base. -/
theorem process_keeps_grid (st : State p.n) (w : Wire p.n) (v : GridCO.Wire p.n .root)
    (h : GridCO.excludes p.toParams.engine st.base v = true) :
    GridCO.excludes p.toParams.engine (FGSA.process p st w).base v = true := by
  unfold FGSA.process
  split
  · exact grid_admitVote_keeps _ _ _ h
  · rw [admitRow_base]; exact h
  · unfold admitBlock
    split
    · exact h
    · split
      · exact h
      · split_ifs
        · rw [foldl_admitRow_base, grid_excludes_congr (ite_reconcile _ _).1
            (ite_reconcile _ _).2.1]
          exact grid_admitProposal_keeps _ _ _ _ _ h
        · exact h
  · exact h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] A delivery keeps a block exclusion: F moves
only to a descendant. -/
theorem process_keeps_block (st : State p.n) (w : Wire p.n) (b : Block)
    (h : blockExcluded st b = true) : blockExcluded (FGSA.process p st w) b = true :=
  blockExcluded_stable st (process_F_mono p st w) b h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] A delivery keeps every exclusion. -/
theorem excludesS_process (st : State p.n) (w : Wire p.n) (o : Obj p)
    (h : excludesS p st o = true) : excludesS p (FGSA.process p st w) o = true := by
  cases hd : (toWire p o).decode with
  | none => rw [excludesS_of_none st hd] at h; exact absurd h (by simp)
  | some x =>
      cases x with
      | vote s i b =>
          rw [excludesS_of_vote _ hd] at h ⊢; exact process_keeps_grid st w _ h
      | row i body =>
          simp only [excludesS_of_row _ hd, Bool.false_eq_true] at h
      | block s N =>
          rw [excludesS_of_block _ hd, Bool.or_eq_true] at h ⊢
          exact h.imp (process_keeps_block st w N.erase)
            (invalidForParent_mono st _ (process_cumulative p st w).1
              (process_namedBodies_subset st w) N)

namespace Internal

theorem foldl_vn {n : Nat} {α : Type} (f : GridCO.State n .root → α → GridCO.State n .root)
    (xs : List α) (st : GridCO.State n .root)
    (hf : ∀ acc x, (f acc x).votes = acc.votes ∧ (f acc x).now = acc.now) :
    (xs.foldl f st).votes = st.votes ∧ (xs.foldl f st).now = st.now := by
  induction xs generalizing st with
  | nil => exact ⟨rfl, rfl⟩
  | cons x xs ih =>
      rw [List.foldl_cons]
      obtain ⟨h1, h2⟩ := ih (f st x)
      exact ⟨h1.trans (hf st x).1, h2.trans (hf st x).2⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] The SA gate (Grid CO gate at the slow policy)
keeps the votes and the clock. -/
theorem saGateFrom_vn {n : Nat} (q : SA.Params) (a : Block) (v : GridCO.State n .root) (r : Slot) :
    (SA.Root.gateFrom q a v r).votes = v.votes ∧ (SA.Root.gateFrom q a v r).now = v.now := by
  unfold SA.Root.gateFrom GridCO.gateFrom
  split
  · exact ⟨rfl, rfl⟩
  · dsimp only
    split_ifs
    · exact ⟨rfl, rfl⟩
    · exact foldl_vn _ _ _ (fun acc _ => foldl_vn _ _ _ (fun acc _ => ⟨rfl, rfl⟩))

theorem clockPre_vn (st : State p.n) (t : Time) :
    (clockPre p st t).base.votes = st.base.votes ∧ (clockPre p st t).base.now = t := by
  unfold clockPre
  dsimp only
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem gateStep_vn (st : State p.n) (s : Slot) :
    (gateStep p st s).base.votes = st.base.votes ∧ (gateStep p st s).base.now = st.base.now := by
  unfold gateStep normalizeS
  dsimp only
  split_ifs <;> first
    | exact ⟨rfl, rfl⟩
    | exact saGateFrom_vn _ _ _ _

end Internal

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] A tick keeps the stored votes and sets the
store clock to its time. -/
theorem clock_vn (st : State p.n) (t : Time) :
    (FGSA.clock p st t).base.votes = st.base.votes ∧ (FGSA.clock p st t).base.now = t := by
  unfold FGSA.clock
  dsimp only
  split
  · obtain ⟨h1, h2⟩ := gateStep_vn (clockPre p st t) (((t - 6 * p.Δ) / (4 * p.Δ)).toNat)
    exact ⟨h1.trans (clockPre_vn st t).1, h2.trans (clockPre_vn st t).2⟩
  · exact clockPre_vn st t

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] A delivery never removes a stored vote. -/
theorem process_votes_subset (st : State p.n) (w : Wire p.n) :
    st.base.votes ⊆ (FGSA.process p st w).base.votes := by
  unfold FGSA.process
  split
  · exact grid_admitVote_votes_subset _ _
  · rw [admitRow_base]
  · unfold admitBlock
    split
    · exact List.Subset.refl _
    · split
      · exact List.Subset.refl _
      · split_ifs
        · rw [foldl_admitRow_base, (ite_reconcile _ _).1]
          exact grid_admitProposal_votes_subset _ _ _ _
        · exact List.Subset.refl _
  · exact List.Subset.refl _

namespace Internal

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] The slot of the store clock does not decrease
when the clock goes forward. -/
theorem slotOf_mono {t t' : Time} (ht : t ≤ t') : p.slotOf t ≤ p.slotOf t' := by
  have hd : (0 : Int) < 4 * p.Δ := by have : (0 : Int) < p.Δ := p.deltaPos; omega
  exact Int.toNat_le_toNat (Int.ediv_le_ediv hd ht)

end Internal

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] A tick that does not move the store clock back
keeps every exclusion. -/
theorem excludesS_clock (st : State p.n) (t : Time) (ht : st.base.now ≤ t) (o : Obj p)
    (h : excludesS p st o = true) : excludesS p (FGSA.clock p st t) o = true := by
  obtain ⟨hv, hn⟩ := clock_vn st t
  cases hd : (toWire p o).decode with
  | none => rw [excludesS_of_none st hd] at h; exact absurd h (by simp)
  | some x =>
      cases x with
      | vote s i b =>
          rw [excludesS_of_vote _ hd] at h ⊢
          rw [grid_excludes_head_iff] at h ⊢
          have hva : GridCO.votesAt (FGSA.clock p st t).base s = GridCO.votesAt st.base s := by
            simp only [GridCO.votesAt, hv]
          rw [hv, hn, hva]
          refine ⟨h.1, h.2.imp (fun hl => lt_of_lt_of_le hl ?_) id⟩
          exact slotOf_mono (p := p) ht
      | row i body => simp only [excludesS_of_row _ hd, Bool.false_eq_true] at h
      | block s N =>
          rw [excludesS_of_block _ hd] at h ⊢
          simpa only [blockExcluded, activeCompatible, clock_F_eq, invalidForParent_clock] using h

/-! ### Clock-free exclusions -/

theorem excludesFixed_of_vote (st : State p.n) {o : Obj p} {s : Slot} {i : Fin p.n} {b : BlockId}
    (hd : (toWire p o).decode = some (.vote s i b)) :
    excludesFixed p st o = (!decide ((⟨.seat s i, .head b⟩ : GridCO.Wire p.n .root) ∈
        st.base.votes) &&
      GridCO.equivocates (GridCO.votesAt st.base s) i) := by
  dsimp only [excludesFixed]; rw [hd]; rfl

theorem excludesFixed_of_row (st : State p.n) {o : Obj p} {i : Fin p.n}
    {body : RowPayload} (hd : (toWire p o).decode = some (.row i body)) :
    excludesFixed p st o = false := by
  dsimp only [excludesFixed]; rw [hd]

theorem excludesFixed_of_block (st : State p.n) {o : Obj p} {s : Slot} {N : NamedProposal p.n}
    (hd : (toWire p o).decode = some (.block s N)) :
    excludesFixed p st o = (blockExcluded st N.erase || invalidForParent p st N) := by
  dsimp only [excludesFixed]; rw [hd]

theorem excludesFixed_of_none (st : State p.n) {o : Obj p} (hd : (toWire p o).decode = none) :
    excludesFixed p st o = false := by
  dsimp only [excludesFixed]; rw [hd]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] A clock-free exclusion is an exclusion. -/
theorem excludesFixed_excludesS (st : State p.n) (o : Obj p) (h : excludesFixed p st o = true) :
    excludesS p st o = true := by
  cases hd : (toWire p o).decode with
  | none => rw [excludesFixed_of_none st hd] at h; exact absurd h (by simp)
  | some x =>
      cases x with
      | vote s i b =>
          rw [excludesFixed_of_vote _ hd] at h; rw [excludesS_of_vote _ hd]
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
          exact (grid_excludes_head_iff st.base s i b).mpr ⟨h.1, Or.inr h.2⟩
      | row i body => simp only [excludesFixed_of_row _ hd, Bool.false_eq_true] at h
      | block s N =>
          rw [excludesFixed_of_block _ hd] at h; rw [excludesS_of_block _ hd]; exact h

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] A delivery keeps a clock-free exclusion. -/
theorem excludesFixed_process (st : State p.n) (w : Wire p.n) (o : Obj p)
    (h : excludesFixed p st o = true) : excludesFixed p (FGSA.process p st w) o = true := by
  have hx := excludesS_process st w o (excludesFixed_excludesS st o h)
  cases hd : (toWire p o).decode with
  | none => rw [excludesFixed_of_none st hd] at h; exact absurd h (by simp)
  | some x =>
      cases x with
      | vote s i b =>
          rw [excludesFixed_of_vote _ hd] at h ⊢
          rw [excludesS_of_vote _ hd, grid_excludes_head_iff] at hx
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h ⊢
          exact ⟨hx.1, grid_equivocates_mono _ _ i
            (grid_votesAt_subset _ _ s (process_votes_subset st w)) h.2⟩
      | row i body => simp only [excludesFixed_of_row _ hd, Bool.false_eq_true] at h
      | block s N =>
          rw [excludesFixed_of_block _ hd, Bool.or_eq_true] at h ⊢
          exact h.imp (process_keeps_block st w N.erase)
            (invalidForParent_mono st _ (process_cumulative p st w).1
              (process_namedBodies_subset st w) N)

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] A tick, at any time, keeps a clock-free
exclusion: it keeps the votes, the
row pool and F. -/
theorem excludesFixed_clock (st : State p.n) (t : Time) (o : Obj p) :
    excludesFixed p (FGSA.clock p st t) o = excludesFixed p st o := by
  dsimp only [excludesFixed]
  simp only [GridCO.votesAt, (clock_vn st t).1,
    blockExcluded, activeCompatible, clock_F_eq, invalidForParent_clock]

/-! ### One epoch -/

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] [`excludes_inert`, epoch form] Inside one
restart epoch of the store, with a
store clock that does not go back, an exclusion holds at every later state,
and the delivery of the excluded object is a no-op there. No run and no
`restartFree` premise: the epoch is the sequence of store steps. -/
theorem excludes_inert_epoch {st st' : State p.n} (hE : Epoch p true st st') {o : Obj p}
    (h : excludesS p st o = true) :
    excludesS p st' o = true ∧ FGSA.process p st' (toWire p o) = st' := by
  have hx : excludesS p st' o = true := by
    induction hE with
    | refl => exact h
    | tail _ hs ih =>
        cases hs with
        | deliver w => exact excludesS_process _ w o ih
        | clock t ht => exact excludesS_clock _ t (ht rfl) o ih
  exact ⟨hx, excludesS_inert st' o hx⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] [`excludes_inert`, clock-free form] The
clock-free exclusions (a proposal
that conflicts with F or fails R6, or an equivocating HEAD) hold, and their
delivery is a no-op, at every later state of the epoch, with any ticks: only
the old-label exclusions need a clock that does not go back. -/
theorem excludesFixed_inert_epoch {mono : Bool} {st st' : State p.n} (hE : Epoch p mono st st')
    {o : Obj p}
    (h : excludesFixed p st o = true) :
    excludesFixed p st' o = true ∧ FGSA.process p st' (toWire p o) = st' := by
  have hx : excludesFixed p st' o = true := by
    induction hE with
    | refl => exact h
    | tail _ hs ih =>
        cases hs with
        | deliver w => exact excludesFixed_process _ w o ih
        | clock t _ => rw [excludesFixed_clock]; exact ih
  exact ⟨hx, excludesS_inert st' o (excludesFixed_excludesS st' o hx)⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] An epoch with a monotone clock is an epoch:
`Epoch p false` asks nothing of
the ticks. -/
theorem Epoch.weaken {mono : Bool} {st st' : State p.n} (hE : Epoch p mono st st') :
    Epoch p false st st' :=
  Relation.ReflTransGen.mono (fun _ _ hs => by
    cases hs with
    | deliver w => exact EpochStep.deliver _ w
    | clock t _ => exact EpochStep.clock _ t (fun h => absurd h (by simp))) _ _ hE

/-! ### Runs: restart-free intervals -/

section RunLevel

variable {In : Type} {c : AppCodec In} {V : Type} [DecidableEq V]

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] The store of `v` from `stateBefore i` to
`stateBefore j` is an epoch when
`v` does not restart in `[i, j)`; with `mono = true`, the ticks of `v` in that
interval must not move its store clock back. A tick changes the store by
`FGSA.clock` (`tick_st`), a delivery by `FGSA.process`, and an event of another
node does not change it. -/
theorem epoch_of_restartFree (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (v : V)
    (mono : Bool) {i j : Nat} (hij : i ≤ j) (hrf : V2.D.restartFree rho v i j)
    (hmono : mono = true → ∀ k t, i ≤ k → k < j → rho.events[k]? = some (.tick v t) →
      (V2.D.Run.stateBefore E rho k v).st.base.now ≤ t) :
    Epoch p mono (V2.D.Run.stateBefore E rho i v).st (V2.D.Run.stateBefore E rho j v).st := by
  -- v4.34.1: without it `rw [tick_st]` finds no pattern after `Function.update_self`.
  set_option backward.isDefEq.respectTransparency false in
  induction j, hij using Nat.le_induction with
  | base => exact Relation.ReflTransGen.refl
  | succ j hij ih =>
      have ih' := ih (fun k t h1 h2 => hrf k t h1 (by omega))
        (fun hm k t h1 h2 he => hmono hm k t h1 (by omega) he)
      cases he : rho.events[j]? with
      | none =>
          have hl : rho.events.length ≤ j := List.getElem?_eq_none_iff.mp he
          have hs : V2.D.Run.stateBefore E rho (j + 1) = V2.D.Run.stateBefore E rho j := by
            unfold V2.D.Run.stateBefore
            rw [List.take_of_length_le (by omega), List.take_of_length_le hl]
          rw [hs]; exact ih'
      | some e =>
          rw [V2.D.Run.stateBefore_succ E rho he]
          cases e with
          | restart w t =>
              by_cases hw : w = v
              · subst hw; exact absurd he (hrf j t hij (by omega))
              · simp only [V2.D.World.step, Function.update_of_ne (Ne.symm hw)]; exact ih'
          | tick w t =>
              by_cases hw : w = v
              · subst hw
                simp only [V2.D.World.step, Function.update_self]
                rw [tick_st]
                exact ih'.tail (EpochStep.clock _ t (fun hm => hmono hm j t hij (by omega) he))
              · simp only [V2.D.World.step, Function.update_of_ne (Ne.symm hw)]; exact ih'
          | deliver w o t =>
              by_cases hw : w = v
              · subst hw
                simp only [V2.D.World.step, Function.update_self]
                exact ih'.tail (EpochStep.deliver _ (toWire p o))
              · simp only [V2.D.World.step, Function.update_of_ne (Ne.symm hw)]; exact ih'

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] [HooksSound `excludes_stable`, with the clock
premise explicit] On a
restart-free interval of a run whose ticks of `v` do not move the store clock of
`v` back, an exclusion is kept, and the delivery of the excluded object is a
no-op, at the end of the interval. -/
theorem excludes_stable_epoch (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (v : V)
    (o : (fgsa p c).Object) {i j : Nat} (hij : i ≤ j) (hrf : V2.D.restartFree rho v i j)
    (hmono : ∀ k t, i ≤ k → k < j → rho.events[k]? = some (.tick v t) →
      (V2.D.Run.stateBefore E rho k v).st.base.now ≤ t)
    (h : (fgsa p c).excludes (V2.D.Run.stateBefore E rho i v) o = true) :
    (fgsa p c).excludes (V2.D.Run.stateBefore E rho j v) o = true ∧
      (fgsa p c).process (V2.D.Run.stateBefore E rho j v) o = V2.D.Run.stateBefore E rho j v := by
  have h' := excludes_inert_epoch (epoch_of_restartFree E rho v true hij hrf (fun _ => hmono)) h
  exact ⟨h'.1, excludes_inert c _ o h'.1⟩

/-- [ROOT-DIGEST-2 W2; DC named and HEAD interfaces] The clock-free exclusions are kept on every
restart-free interval of every
run, with no clock premise. -/
theorem excludesFixed_stable_epoch (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (v : V)
    (o : (fgsa p c).Object) {i j : Nat} (hij : i ≤ j) (hrf : V2.D.restartFree rho v i j)
    (h : excludesFixed p (V2.D.Run.stateBefore E rho i v).st o = true) :
    excludesFixed p (V2.D.Run.stateBefore E rho j v).st o = true ∧
      (fgsa p c).process (V2.D.Run.stateBefore E rho j v) o = V2.D.Run.stateBefore E rho j v := by
  have h' := excludesFixed_inert_epoch
    (epoch_of_restartFree E rho v false hij hrf (fun hm => absurd hm (by simp))) h
  exact ⟨h'.1, excludes_inert c _ o (excludesFixed_excludesS _ o h'.1)⟩

end RunLevel

end AvailableChain.FGSA.Run

end
