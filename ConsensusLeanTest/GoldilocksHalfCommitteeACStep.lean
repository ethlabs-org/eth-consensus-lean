module
public import ConsensusLeanTest.GoldilocksHalfCommitteeACLocks
@[expose] public section

/-! # A computable mirror of the Goldilocks node: the AC calls

The AC calls of the SA (`Spec/SA/Confirmation`, `Spec/SA/Actions`) over the frame `frameOf M` of
the mirror (`GoldilocksHalfCommitteeSetup`), computed on the AC data `ACD` and proved equal to
the trusted definitions:

* `update_latest_confirmed`, the optimistic check and confirmation (`updateLatestConfirmed_eq`,
  `optimisticSelect_eq`, `optimisticConfirmation_eq`);
* the confirmation update of a slot: the result saved also when `⊥`, the veto stopping only the
  record, the fast and the slow lock on the unvetoed path (`updateConfirmation_eq`);
* `try_vote` with its emission (vote, read point, head, anchor, vote domain), the receipts of a
  message and a block, the tick, and `ac_to_fg` (`tryVote_eq`, `acOnMessage_eq`, `acOnBlock_eq`,
  `acOnTick_eq`, `acToFG_eq`);
* an unjoined `ac_on_block` only stamps the block (`acOnBlock_unjoined`), which the restart's
  replay uses. -/

namespace Consensus.Goldilocks.Test.HalfCommittee

open SA

namespace Fix

variable (X : Fix)

/-- An emission of the mirror: the vote, the AC data at its read point, and the roots of its head
and anchor and of its vote domain. -/
structure EmD where
  /-- The vote. -/
  vote : X.V
  /-- The AC data at the read point. -/
  rp : X.ACD
  /-- The head. -/
  head : Nat
  /-- The anchor. -/
  anchor : Nat
  /-- The vote domain. -/
  dom : List Nat

/-- Whether the tree of `M` holds a block of slot `s`. -/
def readyD (M : List Nat) (s : Nat) : Bool := M.any (fun p => decide (X.slotR p = s))

variable {X}

/-- The emission of the mirror's emission. -/
def EmD.interp (e : X.EmD) : SA.Em X.sp (List (FG.Att X.sp.n)) :=
  ⟨e.vote, e.rp.interp, some ⟨X.blk e.head, X.blk e.anchor, X.T e.dom⟩⟩

/-- `update_latest_confirmed`. -/
def ACD.updLC (a : X.ACD) (M : List Nat) (c : Nat) : X.ACD :=
  if a.lc ∈ M ∧ c ∈ X.chain a.lc then a else { a with lc := c }

/-- The block of the optimistic check. -/
def ACD.optSel (a : X.ACD) (M : List Nat) (t : Int) : Option Nat :=
  if a.joinedB t = false ∨ slotT t = 0 ∨ 4 * (slotT t : Int) + 2 ≤ t then none
  else X.deep (M.filter (fun b => decide
    (3 * X.sp.n ≤ 4 * (a.optVoters M (slotT t) b).dedup.length ∧
      X.conflictsD a.locks M t b = false)))

/-- `optimistic_confirmation`. -/
def ACD.optConf (a : X.ACD) (M : List Nat) (t : Int) : X.ACD :=
  match a.optSel M t with
  | none => a
  | some b =>
    let N : List (Nat × Bool × Nat) := [(b, true, X.fastExpD a.locks M t (slotT t))]
    ({ a with locks := addLocksD a.locks M t (slotT t) N } : X.ACD).updLC M b

/-- The slow test of the update of slot `s` for the root `b`: the saved results of the slots in
`(s − k, s)` are blocks of the tree that extend `b`. -/
def ACD.slowD (a : X.ACD) (M : List Nat) (s b : Nat) : Bool :=
  (List.range (X.sp.k - 1)).all (fun i =>
    match a.savedAt ((s : Int) - X.sp.k + 1 + i) with
    | some r => decide (r ∈ M ∧ b ∈ X.chain r)
    | none => false)

/-- `update_confirmation` of slot `s`. -/
def ACD.updConf (a : X.ACD) (M : List Nat) (t : Int) (s : Nat) : X.ACD :=
  let a₁ : X.ACD := { a with saved := ((s : Int), a.getConf M s) :: a.saved }
  match a.getConf M s with
  | none => a₁
  | some c =>
    let a₂ := if X.conflictsD a₁.locks M t c = true then a₁ else a₁.updLC M c
    let path := (X.chain c).filter (fun b => decide (b ≠ X.g ∧ X.conflictsD a₁.locks M t b = false))
    let D := X.deep (path.filter (fun b => decide (X.sp.n ≤ 2 * a.confScore M s b)))
    let Y := X.deep (path.filter (fun b => a₁.slowD M s b))
    let N := (D.map (fun b => (b, true, X.fastExpD a₂.locks M t s))).toList ++
      (Y.map (fun b => (b, false, s + X.sp.k))).toList
    { a₂ with locks := addLocksD a₂.locks M t s N }

/-- `try_vote` of validator `self`. -/
def ACD.tryVote (a : X.ACD) (self : Fin X.sp.n) (M : List Nat) (t : Int) :
    X.ACD × List X.EmD :=
  if a.joinedB t = false ∨ a.voted = (slotT t : Int) ∨ 4 * (slotT t : Int) + 1 < t then (a, [])
  else if t < 4 * (slotT t : Int) + 1 ∧ (slotT t = 0 ∨ X.readyD M (slotT t) = false) then (a, [])
  else
    let s := slotT t
    let p := a.view M ((s : Int) - 1) (ETime.of (freezeD s))
    let a₁ := if 0 < s then { a with locks := X.unlockD a.locks M t ((s : Int) - 1) p } else a
    let dom := a₁.dom M s
    let h := X.headD a₁ M t dom p ((s : Int) - 1)
    let a₂ : X.ACD := { a₁ with voted := (s : Int) }
    let v : X.V := ⟨self, s, h⟩
    ((a₂.addVote t v).optConf M t, [⟨v, a₂, h, X.anchorD a₁.locks M t, dom⟩])

/-- `ac_on_message`. -/
def ACD.onMsg (a : X.ACD) (self : Fin X.sp.n) (M : List Nat) (t : Int) (v : X.V) :
    X.ACD × List X.EmD :=
  ((a.addVote t v).optConf M t).tryVote self M t

/-- `ac_on_block` of the root `r`. -/
def ACD.onBlk (a : X.ACD) (self : Fin X.sp.n) (M : List Nat) (t : Int) (r : Nat) :
    X.ACD × List X.EmD :=
  ((a.stamp r t).optConf M t).tryVote self M t

/-- `ac_on_tick`. -/
def ACD.onTick (a : X.ACD) (self : Fin X.sp.n) (M : List Nat) (t : Int) : X.ACD × List X.EmD :=
  if a.joinedB t = false then (a, [])
  else
    let r := if t = 4 * (slotT t : Int) + 1 then a.tryVote self M t else (a, [])
    ((if t = 4 * (slotT t : Int) + 2 ∧ 0 < slotT t then r.1.updConf M t (slotT t - 1) else r.1),
      r.2)

/-- The candidates of `ac_to_fg`, as roots. -/
def ACD.candD (a : X.ACD) (M : List Nat) (t : Int) : List Nat :=
  ((liveD a.locks M t).filter (fun l => l.fast && decide (slotT t ≤ l.slot + 2))).map Lock.block

/-- `ac_to_fg`. -/
def ACD.toFG (a : X.ACD) (M : List Nat) (t : Int) : X.ACD × Option Nat :=
  if a.joinedB t = false then (a, none)
  else
    match X.deep (a.candD M t) with
    | none => (a, none)
    | some c => if a.rep ∈ M ∧ c ∈ X.chain a.rep then (a, none) else ({ a with rep := c }, some c)

variable {M : List Nat}

theorem interp_setLocks (a : X.ACD) (L : List Lock) :
    ({ a.interp with locks := {l | l ∈ L} } : SAState X.sp.n) =
      ({ a with locks := L } : X.ACD).interp :=
  rfl

/-! ## Confirmation -/

theorem updateLatestConfirmed_eq (hX : X.OK) (hM : X.Closed M) (a : X.ACD) {c : Nat}
    (hc : X.Valid c) :
    updateLatestConfirmed X.sp a.interp (X.frameOf M) (X.blk c) = (a.updLC M c).interp := by
  unfold updateLatestConfirmed ACD.updLC
  rw [interp_latestConfirmed, ancR_frameOf hX hM hc]
  by_cases h : a.lc ∈ M ∧ c ∈ X.chain a.lc
  · simp only [h, and_self, ↓reduceIte]
  · simp only [h, ↓reduceIte, blk_root hc]; rfl

theorem deep_filter_mem {L : List Nat} {p : Nat → Bool} {c : Nat}
    (h : X.deep (L.filter p) = some c) : c ∈ L ∧ p c = true :=
  List.mem_filter.1 (bestBy_spec h).1

theorem optimisticSelect_eq (hX : X.OK) (hM : X.Closed M) (a : X.ACD) (t : Int) :
    optimisticSelect X.sp a.interp (X.frameOf M) t = (a.optSel M t).map X.blk := by
  unfold optimisticSelect ACD.optSel
  simp only [joined_interp, slot_eq, ts_eq, X.hΔ, mul_one, Bool.not_eq_true]
  by_cases h : a.joinedB t = false ∨ slotT t = 0 ∨ 4 * (slotT t : Int) + 2 ≤ t
  · simp only [h, ↓reduceIte, Option.map_none]
  simp only [h, ↓reduceIte]
  refine deepest_eq hX hM (fun r hr => (List.mem_filter.1 hr).1) fun B => ?_
  simp only [Set.mem_ofPred_eq, List.mem_filter, decide_eq_true_eq, interp_locks]
  constructor
  · rintro ⟨hB, h1, h2⟩
    obtain ⟨hm, e⟩ := root_mem_of_T hM hB
    rw [e, optimisticVoters_eq hX hM a _ (hM.valid _ hm), ncard_mem] at h1
    rw [e, conflictsWithLock_eq hX hM _ _ hm] at h2
    exact ⟨B.root, ⟨hm, h1, by simpa using h2⟩, e⟩
  · rintro ⟨r, ⟨hm, h1, h2⟩, rfl⟩
    refine ⟨blk_mem_T hm, ?_, ?_⟩
    · rwa [optimisticVoters_eq hX hM a _ (hM.valid _ hm), ncard_mem]
    · rw [conflictsWithLock_eq hX hM _ _ hm]; simpa using h2

theorem optSel_mem {a : X.ACD} {t : Int} {b : Nat} (h : a.optSel M t = some b) : b ∈ M := by
  unfold ACD.optSel at h
  split_ifs at h
  exact (deep_filter_mem h).1

theorem optimisticConfirmation_eq (hX : X.OK) (hM : X.Closed M) (a : X.ACD) (t : Int) :
    optimisticConfirmation X.sp a.interp (X.frameOf M) t = (a.optConf M t).interp := by
  unfold optimisticConfirmation ACD.optConf
  rw [optimisticSelect_eq hX hM]
  cases h : a.optSel M t with
  | none => rfl
  | some b =>
    have hb := optSel_mem h
    have e : ({(b, true, X.fastExpD a.locks M t (slotT t))} : Set (Nat × Bool × Nat)) =
        {p | p ∈ [(b, true, X.fastExpD a.locks M t (slotT t))]} := by ext; simp
    simp only [Option.map_some, blk_root (hM.valid b hb), slot_eq, interp_locks,
      fastExpiry_eq hX hM, e, addLocks_eq hX hM, interp_setLocks]
    exact updateLatestConfirmed_eq hX hM _ (hM.valid b hb)

theorem getConf_mem {a : X.ACD} {s c : Nat} (h : a.getConf M s = some c) : c ∈ M :=
  (deep_filter_mem h).1

theorem slow_eq (hX : X.OK) (hM : X.Closed M) (a : X.ACD) (s : Nat) {b : Nat} (hb : X.Valid b) :
    (∀ j : Int, (s : Int) - X.sp.k < j → j < s →
      ∃ S ∈ (X.frameOf M).tree, a.interp.saved j = some S.root ∧ (X.frameOf M).Anc (X.blk b) S) ↔
      a.slowD M s b = true := by
  have key : ∀ j : Int, (∃ S ∈ (X.frameOf M).tree, a.interp.saved j = some S.root ∧
      (X.frameOf M).Anc (X.blk b) S) ↔
      (match a.savedAt j with
        | some r => decide (r ∈ M ∧ b ∈ X.chain r)
        | none => false) = true := by
    intro j
    rw [interp_saved]
    cases a.savedAt j with
    | none => simp
    | some r =>
      simp only [Option.some.injEq, decide_eq_true_eq]
      constructor
      · rintro ⟨S, hS, rfl, hA⟩
        obtain ⟨hm, e⟩ := root_mem_of_T hM hS
        rw [e, anc_frameOf hX hM hb hm] at hA
        exact ⟨hm, hA⟩
      · rintro ⟨hm, hA⟩
        exact ⟨X.blk r, blk_mem_T hm, (blk_root (hM.valid r hm)).symm,
          (anc_frameOf hX hM hb hm).2 hA⟩
  unfold ACD.slowD
  simp only [List.all_eq_true, List.mem_range, key]
  have hk := X.sp.two_le_k
  constructor
  · intro h i hi
    exact h _ (by omega) (by omega)
  · intro h j h1 h2
    have := h (j - ((s : Int) - X.sp.k + 1)).toNat (by omega)
    rwa [show (s : Int) - X.sp.k + 1 + ((j - ((s : Int) - X.sp.k + 1)).toNat : Int) = j by omega]
      at this

theorem update_saved (a : X.ACD) (s : Nat) (o : Option Nat) :
    Function.update a.interp.saved (s : Int) o =
      ({ a with saved := ((s : Int), o) :: a.saved } : X.ACD).interp.saved := by
  funext j
  by_cases hj : j = s
  · subst hj; simp [ACD.interp, ACD.savedAt]
  · have hj' : (s : Int) ≠ j := Ne.symm hj
    simp [ACD.interp, ACD.savedAt, Function.update_of_ne hj, hj']

theorem path_mem (hX : X.OK) (hM : X.Closed M) {c : Nat} (hcM : c ∈ M) (L : List Lock) (t : Int)
    (B : X.Blk) :
    (B ∈ confirmationPath X.sp (X.frameOf M) (X.blk c) ∧
      ¬ conflictsWithLock X.sp {l | l ∈ L} (X.frameOf M) t B) ↔
      ∃ r ∈ (X.chain c).filter (fun b => decide (b ≠ X.g ∧ X.conflictsD L M t b = false)),
        B = X.blk r := by
  have hsub := chain_sub hX hM hcM
  simp only [confirmationPath, Set.mem_ofPred_eq, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨-, hg, hA⟩, hn⟩
    obtain ⟨r, hr, rfl⟩ := (anc_T hX hM hcM).1 hA
    rw [blk_root (hM.valid r (hsub r hr))] at hg
    rw [conflictsWithLock_eq hX hM _ _ (hsub r hr)] at hn
    exact ⟨r, ⟨hr, hg, by simpa using hn⟩, rfl⟩
  · rintro ⟨r, ⟨hr, hg, hn⟩, rfl⟩
    refine ⟨⟨blk_mem_T (hsub r hr), by rwa [blk_root (hM.valid r (hsub r hr))],
      (anc_T hX hM hcM).2 ⟨r, hr, rfl⟩⟩, ?_⟩
    rw [conflictsWithLock_eq hX hM _ _ (hsub r hr)]; simp [hn]

theorem updateConfirmation_eq (hX : X.OK) (hM : X.Closed M) (a : X.ACD) (t : Int) (s : Nat) :
    updateConfirmation X.sp a.interp (X.frameOf M) t s = (a.updConf M t s).interp := by
  cases hc : a.getConf M s with
  | none =>
    unfold updateConfirmation ACD.updConf
    simp only [getConfirmation_eq hX hM, hc, Option.map_none, update_saved]
    rfl
  | some c =>
    have hcM := getConf_mem hc
    have hcv := hM.valid c hcM
    unfold updateConfirmation ACD.updConf
    simp only [getConfirmation_eq hX hM, hc, Option.map_some, blk_root hcv, update_saved]
    have hA₁ : (SAState.mk a.interp.pool a.interp.voteStamp a.interp.blockStamp
        ({ a with saved := ((s : Int), some c) :: a.saved } : X.ACD).interp.saved a.interp.locks
        a.interp.latestConfirmed a.interp.fgReported a.interp.votedSlot a.interp.restartTime) =
        ({ a with saved := ((s : Int), some c) :: a.saved } : X.ACD).interp := rfl
    rw [hA₁]
    set a₁ : X.ACD := { a with saved := ((s : Int), some c) :: a.saved } with ha₁
    have hl : a.interp.locks = {l | l ∈ a₁.locks} := rfl
    rw [hl, conflictsWithLock_eq hX hM _ _ hcM]
    set a₂ := if X.conflictsD a₁.locks M t c = true then a₁ else a₁.updLC M c with ha₂
    have hA₂ : ∀ {_ : Decidable (X.conflictsD a₁.locks M t c = true)},
        (if X.conflictsD a₁.locks M t c = true then a₁.interp
          else updateLatestConfirmed X.sp a₁.interp (X.frameOf M) (X.blk c)) = a₂.interp := by
      intro _
      rw [ha₂]
      by_cases h : X.conflictsD a₁.locks M t c = true
      · rw [ite_eq_left h, ite_eq_left h]
      · rw [ite_eq_right h, ite_eq_right h]; exact updateLatestConfirmed_eq hX hM _ hcv
    rw [hA₂, interp_locks, fastExpiry_eq hX hM]
    have hch := chain_sub hX hM hcM
    have hsub : ∀ r ∈ (X.chain c).filter
        (fun b => decide (b ≠ X.g ∧ X.conflictsD a₁.locks M t b = false)), r ∈ M :=
      fun r hr => hch r (List.mem_filter.1 hr).1
    have hD : deepest (X.frameOf M) {B | B ∈ {B |
        B ∈ confirmationPath X.sp (X.frameOf M) (X.blk c) ∧
        ¬conflictsWithLock X.sp {l | l ∈ a₁.locks} (X.frameOf M) t B} ∧
        FastTest X.sp a.interp (X.frameOf M) s B} =
        (X.deep (((X.chain c).filter
          (fun b => decide (b ≠ X.g ∧ X.conflictsD a₁.locks M t b = false))).filter
          (fun b => decide (X.sp.n ≤ 2 * a.confScore M s b)))).map X.blk := by
      refine deepest_eq hX hM (fun r hr => hsub r (List.mem_filter.1 hr).1) fun B => ?_
      simp only [Set.mem_ofPred_eq, path_mem hX hM hcM, List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨r, hr, rfl⟩, hf⟩
        rw [FastTest, confirmationScore_eq hX hM a s (hM.valid r (hch r hr.1))] at hf
        exact ⟨r, ⟨hr, hf⟩, rfl⟩
      · rintro ⟨r, ⟨hr, hf⟩, rfl⟩
        refine ⟨⟨r, hr, rfl⟩, ?_⟩
        rwa [FastTest, confirmationScore_eq hX hM a s (hM.valid r (hch r hr.1))]
    have hY : deepest (X.frameOf M) {B | B ∈ {B |
        B ∈ confirmationPath X.sp (X.frameOf M) (X.blk c) ∧
        ¬conflictsWithLock X.sp {l | l ∈ a₁.locks} (X.frameOf M) t B} ∧
        ∀ j : Int, (s : Int) - X.sp.k < j → j < s →
          ∃ S ∈ (X.frameOf M).tree, a₁.interp.saved j = some S.root ∧ (X.frameOf M).Anc B S} =
        (X.deep (((X.chain c).filter
          (fun b => decide (b ≠ X.g ∧ X.conflictsD a₁.locks M t b = false))).filter
          (fun b => a₁.slowD M s b))).map X.blk := by
      refine deepest_eq hX hM (fun r hr => hsub r (List.mem_filter.1 hr).1) fun B => ?_
      simp only [Set.mem_ofPred_eq, path_mem hX hM hcM, List.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ⟨⟨r, hr, rfl⟩, hf⟩
        exact ⟨r, ⟨hr, (slow_eq hX hM a₁ s (hM.valid r (hch r hr.1))).1 hf⟩, rfl⟩
      · rintro ⟨r, ⟨hr, hf⟩, rfl⟩
        exact ⟨⟨r, hr, rfl⟩, (slow_eq hX hM a₁ s (hM.valid r (hch r hr.1))).2 hf⟩
    rw [hD, hY, show a₁.locks = a.locks from rfl]
    have hval : ∀ L : List Nat, (∀ r ∈ L, r ∈ X.chain c) → ∀ d, X.deep L = some d → X.Valid d :=
      fun L hL d hd => hM.valid d (hch d (hL d (bestBy_spec hd).1))
    have hf : ∀ (q : Nat → Bool), ∀ r ∈ ((X.chain c).filter
        (fun b => decide (b ≠ X.g ∧ X.conflictsD a.locks M t b = false))).filter q, r ∈ X.chain c :=
      fun q r hr => (List.mem_filter.1 (List.mem_filter.1 hr).1).1
    have hDv := hval _ (hf (fun b => decide (X.sp.n ≤ 2 * a.confScore M s b)))
    have hYv := hval _ (hf (fun b => a₁.slowD M s b))
    generalize X.deep (((X.chain c).filter
      (fun b => decide (b ≠ X.g ∧ X.conflictsD a.locks M t b = false))).filter
        (fun b => decide (X.sp.n ≤ 2 * a.confScore M s b))) = Dr at hDv ⊢
    generalize X.deep (((X.chain c).filter
      (fun b => decide (b ≠ X.g ∧ X.conflictsD a.locks M t b = false))).filter
        (fun b => a₁.slowD M s b)) = Yr at hYv ⊢
    have hN : {p | (∃ B, Dr.map X.blk = some B ∧ p = (B.root, true, X.fastExpD a₂.locks M t s)) ∨
        ∃ B, Yr.map X.blk = some B ∧ p = (B.root, false, s + X.sp.k)} =
        {p | p ∈ (Dr.map (fun b => (b, true, X.fastExpD a₂.locks M t s))).toList ++
          (Yr.map (fun b => (b, false, s + X.sp.k))).toList} := by
      ext p
      cases Dr with
      | none =>
        cases Yr with
        | none => simp
        | some y => simp [blk_root (hYv y rfl), eq_comm]
      | some d =>
        cases Yr with
        | none => simp [blk_root (hDv d rfl), eq_comm]
        | some y => simp [blk_root (hDv d rfl), blk_root (hYv y rfl), eq_comm]
    rw [hN, addLocks_eq hX hM]
    rfl


/-- The interpretation of a call's result. -/
def resI (r : X.ACD × List X.EmD) : SAState X.sp.n × List (SA.Em X.sp (List (FG.Att X.sp.n))) :=
  (r.1.interp, r.2.map EmD.interp)

theorem voteReady_eq (hM : X.Closed M) (s : Nat) :
    voteReady X.sp (X.frameOf M) s ↔ X.readyD M s = true := by
  unfold voteReady readyD
  simp only [List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨P, hP, hs, -⟩
    obtain ⟨hm, e⟩ := root_mem_of_T hM hP
    exact ⟨P.root, hm, by rw [← blk_slot, ← e]; exact hs⟩
  · rintro ⟨r, hm, hs⟩
    refine ⟨X.blk r, blk_mem_T hm, by rw [blk_slot]; exact hs, fun x hx => ?_⟩
    rw [blockSupport_T (blk_mem_T hm)] at hx; simp at hx

theorem ghostD_valid {dom : List Nat} (hdom : ∀ r ∈ dom, X.Valid r) (key : Nat → Nat)
    (elig : Nat → Bool) : ∀ fuel h, X.Valid h → X.Valid (X.ghostD dom key elig fuel h) := by
  intro fuel
  induction fuel with
  | zero => intro h hh; exact hh
  | succ f ih =>
    intro h hh
    simp only [ghostD]
    split
    · rename_i c hc; exact ih c (hdom c (List.mem_filter.1 (bestBy_spec hc).1).1)
    · exact hh

theorem headD_valid (hM : X.Closed M) (a : X.ACD) (t : Int) {dom : List Nat}
    (hdom : ∀ r ∈ dom, r ∈ M) (p : List X.V × List X.V) (s : Int) :
    X.Valid (X.headD a M t dom p s) :=
  ghostD_valid (fun r hr => hM.valid r (hdom r hr)) _ _ _ _ (hM.valid _ (anchorD_mem hM _ t))

theorem tryVote_eq (hX : X.OK) (hM : X.Closed M) (hnd : M.Nodup) (a : X.ACD) (self : Fin X.sp.n)
    (t : Int) : tryVote X.sp self a.interp (X.frameOf M) t = resI (a.tryVote self M t) := by
  unfold tryVote ACD.tryVote
  simp only [joined_interp, slot_eq, ts_eq, X.hΔ, Bool.not_eq_true, voteReady_eq hM,
    interp_votedSlot]
  by_cases h1 : a.joinedB t = false ∨ a.voted = (slotT t : Int) ∨ 4 * (slotT t : Int) + 1 < t
  · simp only [h1, ↓reduceIte, resI]; rfl
  by_cases h2 : t < 4 * (slotT t : Int) + 1 ∧ (slotT t = 0 ∨ X.readyD M (slotT t) = false)
  · simp only [h1, h2, ↓reduceIte, resI]; rfl
  simp only [h1, h2, ↓reduceIte, mergedVoteView_interp hM]
  set p := a.view M ((slotT t : Int) - 1) (ETime.of (freezeD (slotT t)))
  set a₁ : X.ACD := if 0 < slotT t then
    { a with locks := X.unlockD a.locks M t ((slotT t : Int) - 1) p }
    else a with ha₁
  have hA₁ : ∀ {_ : Decidable (0 < slotT t)}, (if 0 < slotT t then
      SAState.mk a.interp.pool a.interp.voteStamp a.interp.blockStamp a.interp.saved
        (unlock X.sp a.interp.locks (X.frameOf M) t ((slotT t : Int) - 1) (View.ofLists p))
        a.interp.latestConfirmed a.interp.fgReported a.voted a.interp.restartTime
      else a.interp) = a₁.interp := by
    intro _
    rw [ha₁]
    by_cases h3 : 0 < slotT t
    · rw [ite_eq_left h3, ite_eq_left h3, interp_locks, unlock_eq hX hM]; rfl
    · rw [ite_eq_right h3, ite_eq_right h3]
  rw [hA₁, voteDomain_eq hX hM, viableTree_frameOf hX hM (T_sub (dom_sub a₁ _)),
    getHead_eq hX hM hnd a₁ t (dom_sub a₁ _), getAnchor_eq hX hM,
    blk_root (headD_valid hM a₁ t (dom_sub a₁ _) p _)]
  have hA₂ : (SAState.mk a₁.interp.pool a₁.interp.voteStamp a₁.interp.blockStamp a₁.interp.saved
      a₁.interp.locks a₁.interp.latestConfirmed a₁.interp.fgReported (slotT t : Int)
      a₁.interp.restartTime) = ({ a₁ with voted := (slotT t : Int) } : X.ACD).interp := rfl
  rw [hA₂, admitVote_interp, optimisticConfirmation_eq hX hM]
  rfl

theorem acOnMessage_eq (hX : X.OK) (hM : X.Closed M) (hnd : M.Nodup) (a : X.ACD)
    (self : Fin X.sp.n) (t : Int) (v : X.V) :
    acOnMessage X.sp self a.interp (X.frameOf M) t v = resI (a.onMsg self M t v) := by
  unfold acOnMessage ACD.onMsg
  rw [admitVote_interp, optimisticConfirmation_eq hX hM, tryVote_eq hX hM hnd]

theorem acOnBlock_eq (hX : X.OK) (hM : X.Closed M) (hnd : M.Nodup) (a : X.ACD)
    (self : Fin X.sp.n) (t : Int) {r : Nat} (hr : X.Valid r) :
    acOnBlock X.sp self a.interp (X.frameOf M) t (X.blk r) = resI (a.onBlk self M t r) := by
  unfold acOnBlock ACD.onBlk
  rw [blockReceipt_interp a t hr, optimisticConfirmation_eq hX hM, tryVote_eq hX hM hnd]

/-- An unjoined `ac_on_block` only stamps the block. -/
theorem onBlk_unjoined {a : X.ACD} {t : Int} (h : a.joinedB t = false) (self : Fin X.sp.n)
    (r : Nat) : a.onBlk self M t r = (a.stamp r t, []) := by
  have h' : (a.stamp r t).joinedB t = false := h
  unfold ACD.onBlk ACD.optConf ACD.optSel ACD.tryVote
  simp [h']

theorem acOnTick_eq (hX : X.OK) (hM : X.Closed M) (hnd : M.Nodup) (a : X.ACD)
    (self : Fin X.sp.n) (t : Int) :
    acOnTick X.sp self a.interp (X.frameOf M) t = resI (a.onTick self M t) := by
  unfold acOnTick ACD.onTick
  simp only [joined_interp, slot_eq, ts_eq, X.hΔ, Bool.not_eq_true, mul_one]
  by_cases h1 : a.joinedB t = false
  · simp only [h1, ↓reduceIte, resI, List.map_nil]
  simp only [h1, Bool.true_eq_false, ↓reduceIte]
  by_cases h2 : t = 4 * (slotT t : Int) + 1
  · simp only [ite_eq_left_of_eq_true _ _ (eq_true h2), tryVote_eq hX hM hnd]
    by_cases h3 : t = 4 * (slotT t : Int) + 2 ∧ 0 < slotT t
    · simp only [ite_eq_left_of_eq_true _ _ (eq_true h3), resI, updateConfirmation_eq hX hM]
    · simp only [ite_eq_right_of_eq_false _ _ (eq_false h3), resI]
  · simp only [ite_eq_right_of_eq_false _ _ (eq_false h2)]
    by_cases h3 : t = 4 * (slotT t : Int) + 2 ∧ 0 < slotT t
    · simp only [ite_eq_left_of_eq_true _ _ (eq_true h3), resI, updateConfirmation_eq hX hM,
        List.map_nil]
    · simp only [ite_eq_right_of_eq_false _ _ (eq_false h3), resI, List.map_nil]

/-- The interpretation of `ac_to_fg`'s result. -/
def resF (r : X.ACD × Option Nat) : SAState X.sp.n × Option X.Blk := (r.1.interp, r.2.map X.blk)

theorem acToFG_eq (hX : X.OK) (hM : X.Closed M) (a : X.ACD) (t : Int) :
    acToFG X.sp a.interp (X.frameOf M) t = resF (a.toFG M t) := by
  unfold acToFG ACD.toFG
  simp only [joined_interp, Bool.not_eq_true]
  by_cases h1 : a.joinedB t = false
  · simp only [h1, ↓reduceIte, resF, Option.map_none]
  simp only [h1, Bool.true_eq_false, ↓reduceIte]
  have hv : (X.frameOf M).viableTree (X.frameOf M).tree = X.T M := viableTree_frameOf hX hM le_rfl
  have hc : ∀ r ∈ a.candD M t, r ∈ M := by
    intro r hr
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hr
    exact liveD_sub l (List.mem_filter.1 hl).1
  have hD : deepest (X.frameOf M) (toFGCandidates X.sp a.interp (X.frameOf M) t) =
      (X.deep (a.candD M t)).map X.blk := by
    refine deepest_eq hX hM hc fun B => ?_
    simp only [toFGCandidates, hv, interp_locks, liveLocks_eq hX hM,
      slot_eq, Set.mem_ofPred_eq, ACD.candD, List.mem_map, List.mem_filter, Bool.and_eq_true,
      decide_eq_true_eq]
    constructor
    · rintro ⟨hB, l, hl, hb, hf, hs⟩
      obtain ⟨-, e⟩ := root_mem_of_T hM hB
      exact ⟨l.block, ⟨l, ⟨hl, hf, hs⟩, rfl⟩, hb ▸ e⟩
    · rintro ⟨r, ⟨l, ⟨hl, hf, hs⟩, rfl⟩, rfl⟩
      have hm := liveD_sub l hl
      exact ⟨blk_mem_T hm, l, hl, (blk_root (hM.valid _ hm)).symm, hf, hs⟩
  rw [hD]
  cases hd : X.deep (a.candD M t) with
  | none => rfl
  | some c =>
    have hcM := hc c (bestBy_spec hd).1
    simp only [Option.map_some, interp_fgReported, ancR_frameOf hX hM (hM.valid c hcM)]
    by_cases h2 : a.rep ∈ M ∧ c ∈ X.chain a.rep
    · simp only [h2, and_self, ↓reduceIte, resF, Option.map_none]
    · simp only [h2, ↓reduceIte, resF, Option.map_some, blk_root (hM.valid c hcM)]; rfl

end Fix

end Consensus.Goldilocks.Test.HalfCommittee

end
