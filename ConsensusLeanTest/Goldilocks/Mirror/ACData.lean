module
public import ConsensusLeanTest.Goldilocks.Mirror.FG
@[expose] public section

/-! # A computable mirror of the Goldilocks node: AC data, views and counts

The AC state of the mirror (`Goldilocks/Mirror/Setup`) as lists: `ACD` holds the accepted
votes with their stamps in the order of acceptance (`adm`, the pools and vote stamps), the block
stamps (`bs`, newest first), the saved confirmations (`saved`, newest first), the locks as a list,
and the scalar fields. `ACD.interp` is the `SAState`.

Over the frame `frameOf M` of the fragment, the module computes the AC's reads by lists and proves
them equal to the trusted definitions: admission (`admitVote_interp`), the block receipt
(`blockReceipt_interp`), joining (`joined_interp`), resolution times
(`resolutionTime_interp`), vote views and the merged view (`voteViewList_interp`,
`mergedVoteView_interp`), equivocators, voters, supporters, the Goldfish score and the opponents
as lists of validators whose distinct members the sets count (`equivocators_eq`, `voters_eq`,
`supporters_eq`, `goldfishScore_eq`, `opponents_eq`), the confirmation score and result
(`confirmationScore_eq`, `getConfirmation_eq`), the optimistic voters (`optimisticVoters_eq`),
and the voter block tree and vote domain (`voterBlockTree_eq`, `voteDomain_eq`). -/

namespace Consensus.Goldilocks.Test.HalfCommittee

open SA

namespace Fix

variable (X : Fix)

/-- The votes of the node. -/
abbrev V := Vote X.sp.n

/-- The AC data. -/
structure ACD where
  /-- The accepted votes with their stamps, in the order of acceptance. -/
  adm : List (X.V × Int)
  /-- The block stamps, newest first. -/
  bs : List (Nat × Int)
  /-- The saved confirmations, newest first. -/
  saved : List (Int × Option Nat)
  /-- The locks. -/
  locks : List Lock
  /-- `latest_confirmed`. -/
  lc : Nat
  /-- `fg_reported`. -/
  rep : Nat
  /-- `voted_slot`. -/
  voted : Int
  /-- `restart_time`, `none` for `−∞`. -/
  rst : Option Int

/-- The initial AC data. -/
def ACD.init : X.ACD := ⟨[], [], [], [], X.g, X.g, -1, none⟩

variable {X}

/-- `max` on the extended time line, by its `<`. -/
def maxE (x y : ETime) : ETime := if x < y then y else x

theorem maxE_eq (x y : ETime) : maxE x y = max x y := (max_def_lt x y).symm

/-- The slot-`s` pool. -/
def ACD.pool (a : X.ACD) (s : Nat) : List X.V :=
  (a.adm.filter (fun p => decide (p.1.slot = s))).map Prod.fst

/-- The pool of an integer slot. -/
def ACD.poolAt (a : X.ACD) (s : Int) : List X.V := if s < 0 then [] else a.pool s.toNat

/-- The stamp of a vote. -/
def ACD.stampV (a : X.ACD) (v : X.V) : ETime :=
  match a.adm.find? (fun p => decide (p.1 = v)) with
  | some p => ETime.of p.2
  | none => ⊤

/-- The stamp of a block. -/
def ACD.stampB (a : X.ACD) (r : Nat) : ETime :=
  match a.bs.find? (fun p => decide (p.1 = r)) with
  | some p => ETime.of p.2
  | none => if r = X.g then ⊥ else ⊤

/-- The saved confirmation of a slot. -/
def ACD.savedAt (a : X.ACD) (j : Int) : Option Nat :=
  match a.saved.find? (fun p => decide (p.1 = j)) with
  | some p => p.2
  | none => none

/-- `restart_time` on the extended line. -/
def rstE : Option Int → WithBot Time
  | none => ⊥
  | some t => (t : WithBot Time)

/-- The AC state of the data. -/
def ACD.interp (a : X.ACD) : SAState X.sp.n where
  pool := a.pool
  voteStamp := a.stampV
  blockStamp := a.stampB
  saved := a.savedAt
  locks := {l | l ∈ a.locks}
  latestConfirmed := a.lc
  fgReported := a.rep
  votedSlot := a.voted
  restartTime := rstE a.rst

/-- Joined at `t`. -/
def ACD.joinedB (a : X.ACD) (t : Int) : Bool :=
  match a.rst with
  | none => true
  | some r => decide (r ≤ 4 * ((slotT t : Int) - 1))

/-- `on_goldfish_vote`. -/
def ACD.addVote (a : X.ACD) (t : Int) (v : X.V) : X.ACD :=
  if (v.slot : Int) < (slotT t : Int) - 1 ∨ slotT t < v.slot ∨ v ∈ a.pool v.slot then a
  else if 2 ≤ ((a.pool v.slot).filter (fun x => x.val = v.val)).dedup.length then a
  else { a with adm := a.adm ++ [(v, t)] }

/-- The stamp of a received block (its AC payload holds no vote). -/
def ACD.stamp (a : X.ACD) (r : Nat) (t : Int) : X.ACD := { a with bs := (r, t) :: a.bs }

/-- The resolution time of a vote in the frame of `M`. -/
def ACD.res (a : X.ACD) (M : List Nat) (v : X.V) : ETime :=
  if v.head ∈ M then (if v.slot < X.slotR v.head then ⊤ else maxE (a.stampV v) (a.stampB v.head))
  else ⊤

/-- `vote_view` as lists. -/
def ACD.view (a : X.ACD) (M : List Nat) (s : Int) (c : ETime) : List X.V × List X.V :=
  let votes := (a.poolAt s).filter (fun v => decide (a.stampV v < c))
  (votes, votes.filter (fun v => decide (a.res M v < c)))

/-- The vote freeze `t_{s−1} + 3`. -/
def freezeD (s : Nat) : Int := 4 * ((s : Int) - 1) + 3

/-- The equivocators of a vote list (with repeats). -/
def eqv (L : List X.V) : List (Fin X.sp.n) :=
  (L.filter (fun x => L.any (fun y => decide (y ≠ x ∧ y.val = x.val)))).map Vote.val

/-- The supporters of the root `b` among the slot-`s` support votes `L2`, with the equivocators
of `L1` removed (with repeats). -/
def supp (M : List Nat) (L1 L2 : List X.V) (s : Int) (b : Nat) : List (Fin X.sp.n) :=
  ((L2.filter (fun x => decide ((x.slot : Int) = s ∧ x.head ∈ M ∧ b ∈ X.chain x.head))).map
    Vote.val).filter (fun i => decide (i ∉ eqv L1))

/-- The Goldfish score of `b` in the view `p`. -/
def score (M : List Nat) (p : List X.V × List X.V) (s : Int) (b : Nat) : Nat :=
  (eqv p.1).dedup.length + (supp M p.1 p.2 s b).dedup.length

/-- The opponents of `b` in the view `p` (with repeats). -/
def opp (M : List Nat) (p : List X.V × List X.V) (s : Int) (b : Nat) : List (Fin X.sp.n) :=
  eqv p.1 ++ (p.2.filter (fun x => decide ((x.slot : Int) = s ∧ x.head ∈ M ∧
    ¬ (x.head ∈ X.chain b ∨ b ∈ X.chain x.head)))).map Vote.val

/-- The slot-`s` votes resolved before `t_s + 2`. -/
def ACD.early (a : X.ACD) (M : List Nat) (s : Nat) : List X.V :=
  (a.pool s).filter (fun v => decide (a.res M v < ETime.of (4 * (s : Int) + 2)))

/-- The confirmation score of `b` in slot `s`. -/
def ACD.confScore (a : X.ACD) (M : List Nat) (s b : Nat) : Nat :=
  (supp M (a.pool s) (a.early M s) s b).dedup.length

/-- `get_confirmation` as a root. -/
def ACD.getConf (a : X.ACD) (M : List Nat) (s : Nat) : Option Nat :=
  X.deep (M.filter (fun b => decide
    (((a.pool s).map Vote.val).dedup.length < 2 * a.confScore M s b)))

/-- The optimistic voters of `b` in slot `s` (with repeats). -/
def ACD.optVoters (a : X.ACD) (M : List Nat) (s b : Nat) : List (Fin X.sp.n) :=
  ((a.pool s).filter (fun x => decide (x.head ∈ M ∧ b ∈ X.chain x.head))).map Vote.val

/-- The voter block tree of slot `s`, as roots. -/
def ACD.vbt (a : X.ACD) (M : List Nat) (s : Nat) : List Nat :=
  M.filter (fun r => decide (a.stampB r < ETime.of (freezeD s) ∨
    ∃ p ∈ M, X.slotR p = s ∧ r ∈ X.chain p))

/-- The vote domain of slot `s`, as roots. -/
def ACD.dom (a : X.ACD) (M : List Nat) (s : Nat) : List Nat :=
  if a.vbt M s = [] then M else a.vbt M s

/-! ## The state -/

section State

variable (a : X.ACD)

@[simp] theorem interp_pool : a.interp.pool = a.pool := rfl
@[simp] theorem interp_voteStamp : a.interp.voteStamp = a.stampV := rfl
@[simp] theorem interp_blockStamp : a.interp.blockStamp = a.stampB := rfl
@[simp] theorem interp_saved : a.interp.saved = a.savedAt := rfl
@[simp] theorem interp_locks : a.interp.locks = {l | l ∈ a.locks} := rfl
@[simp] theorem interp_latestConfirmed : a.interp.latestConfirmed = a.lc := rfl
@[simp] theorem interp_fgReported : a.interp.fgReported = a.rep := rfl
@[simp] theorem interp_votedSlot : a.interp.votedSlot = a.voted := rfl
@[simp] theorem interp_restartTime : a.interp.restartTime = rstE a.rst := rfl
@[simp] theorem interp_poolAt (s : Int) : a.interp.poolAt s = a.poolAt s := rfl

end State

theorem sastate_ext {A B : SAState X.sp.n} (h1 : A.pool = B.pool)
    (h2 : A.voteStamp = B.voteStamp) (h3 : A.blockStamp = B.blockStamp) (h4 : A.saved = B.saved)
    (h5 : A.locks = B.locks) (h6 : A.latestConfirmed = B.latestConfirmed)
    (h7 : A.fgReported = B.fgReported) (h8 : A.votedSlot = B.votedSlot)
    (h9 : A.restartTime = B.restartTime) : A = B := by
  cases A; cases B; simp only at *; subst_vars; rfl

theorem ACD.interp_init : (ACD.init X).interp = SAState.initial X.g := by
  refine sastate_ext ?_ ?_ ?_ ?_ ?_ rfl rfl rfl rfl
  · funext s; simp [ACD.interp, ACD.init, ACD.pool, SAState.initial]
  · funext v; simp [ACD.interp, ACD.init, ACD.stampV, SAState.initial]
  · funext r; simp [ACD.interp, ACD.init, ACD.stampB, SAState.initial]
  · funext j; simp [ACD.interp, ACD.init, ACD.savedAt, SAState.initial]
  · ext l; simp [ACD.interp, ACD.init, SAState.initial]

theorem joined_interp (a : X.ACD) (t : Int) : joined X.sp a.interp t ↔ a.joinedB t = true := by
  unfold joined
  rw [slot_eq, ts_eq]
  rcases a with ⟨_, _, _, _, _, _, _, _ | r⟩
  · simp [ACD.joinedB, ACD.interp, rstE]
  · simp only [ACD.joinedB, ACD.interp, rstE, decide_eq_true_eq]; exact WithBot.coe_le_coe

theorem mem_pool_iff {a : X.ACD} {v : X.V} : v ∈ a.pool v.slot ↔ ∃ t, (v, t) ∈ a.adm := by
  simp [ACD.pool]

theorem admitVote_interp (a : X.ACD) (t : Int) (v : X.V) :
    admitVote X.sp a.interp t v = (a.addVote t v).interp := by
  unfold admitVote ACD.addVote
  rw [slot_eq]
  simp only [interp_pool]
  by_cases h1 : (v.slot : Int) < (slotT t : Int) - 1 ∨ slotT t < v.slot ∨ v ∈ a.pool v.slot
  · simp only [h1, ↓reduceIte]
  by_cases h2 : 2 ≤ ((a.pool v.slot).filter (fun x => x.val = v.val)).dedup.length
  · simp only [h1, h2, ↓reduceIte]
  simp only [h1, h2, ↓reduceIte]
  have hn : ∀ p ∈ a.adm, p.1 ≠ v := by
    rintro ⟨w, s⟩ hp rfl
    exact h1 (Or.inr (Or.inr (mem_pool_iff.2 ⟨s, hp⟩)))
  refine sastate_ext ?_ ?_ rfl rfl rfl rfl rfl rfl rfl
  · funext s
    by_cases hs : s = v.slot
    · subst hs; simp [ACD.interp, ACD.pool]
    · simp [ACD.interp, ACD.pool, Function.update_of_ne hs, Ne.symm hs]
  · funext w
    by_cases hw : w = v
    · subst hw
      have : a.adm.find? (fun p => decide (p.1 = w)) = none := by
        simpa using fun x y h => hn (x, y) h
      simp [ACD.interp, ACD.stampV, List.find?_append, this]
    · simp only [ACD.interp, ACD.stampV, Function.update_of_ne hw, List.find?_append]
      cases a.adm.find? (fun p => decide (p.1 = w)) <;> simp [Ne.symm hw]

theorem blockReceipt_interp (a : X.ACD) (t : Int) {r : Nat} (hr : X.Valid r) :
    blockReceipt X.sp a.interp t (X.blk r) = (a.stamp r t).interp := by
  unfold blockReceipt
  simp only [blockVotes, blk_acPayload, List.foldl_nil, blk_root hr]
  refine sastate_ext rfl rfl ?_ rfl rfl rfl rfl rfl rfl
  funext q
  by_cases hq : q = r
  · subst hq; simp [ACD.interp, ACD.stamp, ACD.stampB]
  · simp [ACD.interp, ACD.stamp, ACD.stampB, Function.update_of_ne hq, Ne.symm hq]

/-! ## Views -/

variable {M : List Nat}

theorem resolutionTime_interp (hM : X.Closed M) (a : X.ACD) (v : X.V) :
    resolutionTime a.interp (X.frameOf M) v = a.res M v := by
  unfold resolutionTime ACD.res
  rw [lookup_frameOf hM]
  by_cases h : v.head ∈ M <;> simp [h, blk_slot, maxE_eq]

theorem voteViewList_interp (hM : X.Closed M) (a : X.ACD) (s : Int) (c : ETime) :
    voteViewList a.interp (X.frameOf M) s c = a.view M s c := by
  simp only [voteViewList, ACD.view, interp_poolAt, interp_voteStamp,
    resolutionTime_interp hM]
  rfl

theorem freeze_eq (s : Nat) : freeze X.sp s = freezeD s := by
  simp only [freeze, freezeD, ts_eq, X.hΔ]; ring

theorem blockVotes_T {B : X.Blk} (hB : B ∈ X.T M) : blockVotes B = [] := by
  obtain ⟨r, -, rfl⟩ := hB; simp [blockVotes, blk_acPayload]

theorem blockSupport_T {B : X.Blk} (hB : B ∈ X.T M) : blockSupport B = [] := by
  obtain ⟨r, -, rfl⟩ := hB; simp [blockSupport, blk_acPayload]

theorem mergedVoteView_interp (hM : X.Closed M) (a : X.ACD) (s : Nat) :
    mergedVoteView X.sp a.interp (X.frameOf M) s =
      View.ofLists (a.view M ((s : Int) - 1) (ETime.of (freezeD s))) := by
  unfold mergedVoteView voteView
  rw [freeze_eq, voteViewList_interp hM]
  have h1 : {v | ∃ B ∈ (X.frameOf M).tree, B.slot = s ∧ v ∈ blockVotes B} = ∅ := by
    ext v; simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨B, hB, -, hv⟩; rw [blockVotes_T hB] at hv; simp at hv
  have h2 : {v | ∃ B ∈ (X.frameOf M).tree, B.slot = s ∧ v ∈ blockSupport B ∧ v.slot + 1 = s ∧
      ∃ H ∈ (X.frameOf M).tree, H.root = v.head ∧ H.slot + 1 ≤ s} = ∅ := by
    ext v; simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨B, hB, -, hv, -⟩; rw [blockSupport_T hB] at hv; simp at hv
  simp only [h1, h2, Set.union_empty]

/-! ## Counts -/

theorem equivocators_eq (L : List X.V) : equivocators {v | v ∈ L} = {i | i ∈ eqv L} := by
  ext i
  simp only [equivocators, eqv, Set.mem_ofPred_eq, List.mem_map, List.mem_filter, List.any_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨x, hx, y, hy, hxy, rfl, hyi⟩
    exact ⟨x, ⟨hx, y, hy, Ne.symm hxy, hyi⟩, rfl⟩
  · rintro ⟨x, ⟨hx, y, hy, hyx, hyv⟩, rfl⟩
    exact ⟨x, hx, y, hy, Ne.symm hyx, rfl, hyv⟩

theorem voters_eq (L : List X.V) : voters {v | v ∈ L} = {i | i ∈ L.map Vote.val} := by
  ext i; simp [voters]

theorem supporters_eq (hX : X.OK) (hM : X.Closed M) (L1 L2 : List X.V) (s : Int) {b : Nat}
    (hb : X.Valid b) :
    supporters (X.frameOf M) (View.ofLists (L1, L2)) s (X.blk b) = {i | i ∈ supp M L1 L2 s b} := by
  ext i
  simp only [supporters, View.ofLists, equivocators_eq, supp, Set.mem_ofPred_eq, List.mem_filter,
    List.mem_map, decide_eq_true_eq, ancR_frameOf hX hM hb]
  constructor
  · rintro ⟨hi, x, hx, rfl, hs, hm, hc⟩
    exact ⟨⟨x, ⟨hx, hs, hm, hc⟩, rfl⟩, hi⟩
  · rintro ⟨⟨x, ⟨hx, hs, hm, hc⟩, rfl⟩, hi⟩
    exact ⟨hi, x, hx, rfl, hs, hm, hc⟩

theorem goldfishScore_eq (hX : X.OK) (hM : X.Closed M) (p : List X.V × List X.V) (s : Int)
    {b : Nat} (hb : X.Valid b) :
    goldfishScore X.sp (X.frameOf M) (View.ofLists p) s (X.blk b) = score M p s b := by
  obtain ⟨L1, L2⟩ := p
  unfold goldfishScore score
  rw [supporters_eq hX hM L1 L2 s hb]
  simp only [View.ofLists, equivocators_eq, ncard_mem]

theorem opponents_eq (hX : X.OK) (hM : X.Closed M) (p : List X.V × List X.V) (s : Int)
    {b : Nat} (hb : b ∈ M) :
    opponents X.sp (X.frameOf M) (View.ofLists p) s (X.blk b) = {i | i ∈ opp M p s b} := by
  obtain ⟨L1, L2⟩ := p
  ext i
  simp only [opponents, View.ofLists, equivocators_eq, opp, Set.mem_union, Set.mem_ofPred_eq,
    List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq]
  refine or_congr_right ⟨?_, ?_⟩
  · rintro ⟨x, hx, rfl, hs, H, hH, hr, hc⟩
    obtain ⟨hm, e⟩ := root_mem_of_T hM hH
    rw [hr] at e hm
    rw [e, compatible_frameOf hX hM hm hb] at hc
    exact ⟨x, ⟨hx, hs, hm, hc⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hs, hm, hc⟩, rfl⟩
    refine ⟨x, hx, rfl, hs, X.blk x.head, blk_mem_T hm, blk_root (hM.valid _ hm), ?_⟩
    rwa [compatible_frameOf hX hM hm hb]

theorem early_eq (hM : X.Closed M) (a : X.ACD) (s : Nat) :
    {v | v ∈ a.interp.pool s ∧
      resolutionTime a.interp (X.frameOf M) v < ETime.of (X.sp.ts s + 2 * X.sp.Δ)} =
      {v | v ∈ a.early M s} := by
  ext v
  simp [ACD.early, resolutionTime_interp hM, ts_eq, X.hΔ]

theorem confirmationScore_eq (hX : X.OK) (hM : X.Closed M) (a : X.ACD) (s : Nat) {b : Nat}
    (hb : X.Valid b) :
    confirmationScore X.sp a.interp (X.frameOf M) s (X.blk b) = a.confScore M s b := by
  unfold confirmationScore ACD.confScore
  dsimp only
  rw [early_eq hM]
  have e : (⟨{v | v ∈ a.interp.pool s}, {v | v ∈ a.early M s}⟩ : View X.sp.n) =
    View.ofLists (a.pool s, a.early M s) := rfl
  rw [e, supporters_eq hX hM _ _ _ hb, ncard_mem]

theorem getConfirmation_eq (hX : X.OK) (hM : X.Closed M) (a : X.ACD) (s : Nat) :
    getConfirmation X.sp a.interp (X.frameOf M) s = (a.getConf M s).map X.blk := by
  unfold getConfirmation ACD.getConf
  refine deepest_eq hX hM (fun r hr => (List.mem_filter.1 hr).1) fun B => ?_
  simp only [Set.mem_ofPred_eq, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hB, -, h⟩
    obtain ⟨hm, e⟩ := root_mem_of_T hM hB
    rw [e, voters_eq, ncard_mem, confirmationScore_eq hX hM a s (hM.valid _ hm)] at h
    exact ⟨B.root, ⟨hm, h⟩, e⟩
  · rintro ⟨r, ⟨hm, h⟩, rfl⟩
    refine ⟨blk_mem_T hm, gBlk_anc hX hM (blk_mem_T hm), ?_⟩
    rwa [voters_eq, ncard_mem, confirmationScore_eq hX hM a s (hM.valid _ hm)]

theorem optimisticVoters_eq (hX : X.OK) (hM : X.Closed M) (a : X.ACD) (s : Nat) {b : Nat}
    (hb : X.Valid b) :
    optimisticVoters X.sp a.interp (X.frameOf M) s (X.blk b) = {i | i ∈ a.optVoters M s b} := by
  ext i
  simp only [optimisticVoters, ACD.optVoters, interp_pool, ancR_frameOf hX hM hb,
    Set.mem_ofPred_eq, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨x, hx, rfl, h⟩; exact ⟨x, ⟨hx, h⟩, rfl⟩
  · rintro ⟨x, ⟨hx, h⟩, rfl⟩; exact ⟨x, hx, rfl, h⟩

/-! ## The voter block tree and the vote domain -/

theorem T_sub {L : List Nat} (h : ∀ r ∈ L, r ∈ M) : X.T L ⊆ X.T M := by
  rintro B ⟨r, hr, rfl⟩; exact blk_mem_T (h r hr)

theorem vbt_sub (a : X.ACD) (s : Nat) : ∀ r ∈ a.vbt M s, r ∈ M :=
  fun _ hr => (List.mem_filter.1 hr).1

theorem dom_sub (a : X.ACD) (s : Nat) : ∀ r ∈ a.dom M s, r ∈ M := by
  unfold ACD.dom; split_ifs
  · exact fun _ h => h
  · exact vbt_sub a s

theorem voterBlockTree_eq (hX : X.OK) (hM : X.Closed M) (a : X.ACD) (s : Nat) :
    voterBlockTree X.sp a.interp (X.frameOf M) s = X.T (a.vbt M s) := by
  ext B
  simp only [voterBlockTree, ACD.vbt, freeze_eq, interp_blockStamp, Set.mem_ofPred_eq, T,
    List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hB, h⟩
    obtain ⟨hm, e⟩ := root_mem_of_T hM hB
    refine ⟨B.root, ⟨hm, ?_⟩, e⟩
    rcases h with h | ⟨P, hP, hs, hPa⟩
    · exact Or.inl h
    · obtain ⟨hp, e'⟩ := root_mem_of_T hM hP
      rw [e', blk_slot] at hs
      rw [e, e', anc_frameOf hX hM (hM.valid _ hm) hp] at hPa
      exact Or.inr ⟨P.root, hp, hs, hPa⟩
  · rintro ⟨r, ⟨hm, h⟩, rfl⟩
    refine ⟨blk_mem_T hm, ?_⟩
    rw [blk_root (hM.valid r hm)]
    rcases h with h | ⟨p, hp, hs, hc⟩
    · exact Or.inl h
    · exact Or.inr ⟨X.blk p, blk_mem_T hp, by rw [blk_slot]; exact hs,
        (anc_frameOf hX hM (hM.valid r hm) hp).2 hc⟩

theorem T_nonempty {L : List Nat} : (X.T L).Nonempty ↔ L ≠ [] := by
  constructor
  · rintro ⟨B, r, hr, -⟩ rfl; simp at hr
  · intro h
    obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil L h
    exact ⟨_, blk_mem_T hr⟩

theorem voteDomain_eq (hX : X.OK) (hM : X.Closed M) (a : X.ACD) (s : Nat) :
    voteDomain X.sp a.interp (X.frameOf M) s = X.T (a.dom M s) := by
  rw [voteDomain, voterBlockTree_eq hX hM, viableTree_frameOf hX hM (T_sub (vbt_sub a s)),
    T_nonempty]
  unfold ACD.dom
  by_cases h : a.vbt M s = []
  · ext B; simp [h]; rfl
  · ext B; simp [h]

end Fix

end Consensus.Goldilocks.Test.HalfCommittee

end
