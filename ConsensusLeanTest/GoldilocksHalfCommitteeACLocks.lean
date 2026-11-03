module
public import ConsensusLeanTest.GoldilocksHalfCommitteeACData
@[expose] public section

/-! # A computable mirror of the Goldilocks node: locks and the head walk

The lock rules and the head walk of the SA over the frame `frameOf M` of the mirror
(`GoldilocksHalfCommitteeSetup`), computed on lists of locks and roots and proved equal to the
trusted definitions (`Spec/SA/Locks`, `Spec/SA/ForkChoice`):

* every block of `frameOf M` is its own viable ancestor, so `liveLocks` keeps the unexpired locks
  on blocks of the tree, with their slot, fast bit and expiry (`liveLocks_eq`, expiry inclusive);
* `fastExpiry` through the greatest live fast expiry of an earlier slot (`fastExpiry_eq`);
* the live lock blocks, the lock veto, the anchor, `add_locks` (`liveLockBlocks_eq`,
  `conflictsWithLock_eq`, `getAnchor_eq`, `addLocks_eq`);
* `unlockTarget` (the deepest ancestor with `2 · |opponents| < n`, else genesis) and `unlock`,
  which keeps slot, fast bit and expiry (`unlockTarget_eq`, `unlock_eq`);
* the walk `ghost` through `bestBy` on the children (`ghost_eq`) and `getHead` (`getHead_eq`). -/

namespace Consensus.Goldilocks.Test.HalfCommittee

open SA

/-- The live locks: unexpired at `t` (expiry inclusive) on a block of `M`. -/
def liveD (L : List Lock) (M : List Nat) (t : Int) : List Lock :=
  L.filter (fun l => decide (l.block ∈ M ∧ slotT t ≤ l.expiry))

/-- The blocks of the live locks. -/
def lockBlocksD (L : List Lock) (M : List Nat) (t : Int) : List Nat :=
  (liveD L M t).map Lock.block

/-- `add_locks` with the new locks `(B, s, f, e)` for `(B, f, e) ∈ N`. -/
def addLocksD (L : List Lock) (M : List Nat) (t : Int) (s : Nat) (N : List (Nat × Bool × Nat)) :
    List Lock :=
  liveD (L ++ N.map (fun p => (⟨p.1, s, p.2.1, p.2.2⟩ : Lock))) M t

theorem foldr_max_mem : ∀ {es : List Nat}, es ≠ [] → es.foldr max 0 ∈ es
  | [], h => absurd rfl h
  | [x], _ => by simp
  | x :: y :: es, _ => by
    have ih := foldr_max_mem (es := y :: es) (by simp)
    rw [List.foldr_cons]
    rcases max_choice x ((y :: es).foldr max 0) with h | h <;> rw [h]
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ ih

theorem le_foldr_max : ∀ {es : List Nat}, ∀ e ∈ es, e ≤ es.foldr max 0
  | [], _, h => by simp at h
  | x :: es, e, h => by
    rw [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (le_foldr_max e h) (le_max_right _ _)

theorem sSup_list {es : List Nat} (h : es ≠ []) : sSup {e | e ∈ es} = es.foldr max 0 :=
  IsGreatest.csSup_eq ⟨foldr_max_mem h, fun _ he => le_foldr_max _ he⟩

namespace Fix

variable (X : Fix)

/-- `fastExpiry`: the greatest live fast expiry of an earlier slot plus `c`, between `s + 2`
and `s + k`. -/
def fastExpD (L : List Lock) (M : List Nat) (t : Int) (s : Nat) : Nat :=
  let es := ((liveD L M t).filter (fun l => l.fast && decide (l.slot < s))).map Lock.expiry
  min (s + X.sp.k) (if es = [] then s + 2 else max (s + 2) (es.foldr max 0 + X.sp.c))

/-- The lock veto of the root `c`. -/
def conflictsD (L : List Lock) (M : List Nat) (t : Int) (c : Nat) : Bool :=
  (lockBlocksD L M t).any (fun b => decide (¬ (c ∈ X.chain b ∨ b ∈ X.chain c)))

/-- The anchor. -/
def anchorD (L : List Lock) (M : List Nat) (t : Int) : Nat :=
  (X.deep (X.g :: lockBlocksD L M t)).getD X.g

/-- The unlock target of the root `b` against the slot-`s` votes of `p`. -/
def unlockTargetD (M : List Nat) (p : List X.V × List X.V) (s : Int) (b : Nat) : Nat :=
  (X.deep ((X.chain b).filter (fun b' => decide (2 * (opp M p s b').dedup.length < X.sp.n)))).getD
    X.g

/-- `unlock`. -/
def unlockD (L : List Lock) (M : List Nat) (t : Int) (s : Int) (p : List X.V × List X.V) :
    List Lock :=
  (liveD L M t).map (fun l =>
    if (l.slot : Int) < s then { l with block := X.unlockTargetD M p s l.block } else l)

/-- The eligibility of a child `c` in the walk. -/
def eligD (M : List Nat) (t : Int) (p : List X.V × List X.V) (s : Int) (c : Nat) : Bool :=
  decide (X.slotR c = slotT t) || decide ((p.1.map Vote.val).dedup.length < 2 * score M p s c)

/-- The walk over the roots `dom` with key `key` and eligibility `elig`, with fuel. -/
def ghostD (dom : List Nat) (key : Nat → Nat) (elig : Nat → Bool) : Nat → Nat → Nat
  | 0, h => h
  | f + 1, h =>
    match bestBy key (dom.filter (fun c => decide (c ≠ X.g ∧ X.par c = h) && elig c)) with
    | some c => ghostD dom key elig f c
    | none => h

/-- `get_head` over the roots `dom` with the view `p` of slot `s`. -/
def headD (a : X.ACD) (M : List Nat) (t : Int) (dom : List Nat) (p : List X.V × List X.V)
    (s : Int) : Nat :=
  X.ghostD dom (score M p s) (X.eligD M t p s) M.length (X.anchorD a.locks M t)

variable {X} {M : List Nat}

theorem liveD_sub {L : List Lock} {t : Int} : ∀ l ∈ liveD L M t, l.block ∈ M :=
  fun _ h => (List.mem_filter.1 h).2 |> of_decide_eq_true |>.1

theorem lockBlocksD_sub {L : List Lock} {t : Int} : ∀ b ∈ lockBlocksD L M t, b ∈ M := by
  intro b hb
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hb
  exact liveD_sub l hl

theorem liveLocks_eq (hX : X.OK) (hM : X.Closed M) (L : List Lock) (t : Int) :
    liveLocks X.sp {l | l ∈ L} (X.frameOf M) t = {l | l ∈ liveD L M t} := by
  ext l'
  simp only [liveLocks, Lock.LiveAt, slot_eq, Set.mem_ofPred_eq, liveD, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ⟨l, hl, B, hB, hr, hlive, rfl⟩
    rw [viableAncestor_frameOf hX hM hB, hr]
    obtain ⟨hm, -⟩ := root_mem_of_T hM hB
    exact ⟨hl, hr ▸ hm, hlive⟩
  · rintro ⟨hl, hm, hlive⟩
    refine ⟨l', hl, X.blk l'.block, blk_mem_T hm, blk_root (hM.valid _ hm), hlive, ?_⟩
    rw [viableAncestor_frameOf hX hM (blk_mem_T hm), blk_root (hM.valid _ hm)]

theorem fastExpiry_eq (hX : X.OK) (hM : X.Closed M) (L : List Lock) (t : Int) (s : Nat) :
    fastExpiry X.sp {l | l ∈ L} (X.frameOf M) t s = X.fastExpD L M t s := by
  unfold fastExpiry fastExpD
  rw [liveLocks_eq hX hM]
  set es := ((liveD L M t).filter (fun l => l.fast && decide (l.slot < s))).map Lock.expiry
  have hE : {e | ∃ l ∈ {l | l ∈ liveD L M t}, l.fast = true ∧ l.slot < s ∧ e = l.expiry} =
      {e | e ∈ es} := by
    ext e
    simp only [Set.mem_ofPred_eq, es, List.mem_map, List.mem_filter, Bool.and_eq_true,
      decide_eq_true_eq]
    constructor
    · rintro ⟨l, hl, hf, hs, rfl⟩; exact ⟨l, ⟨hl, hf, hs⟩, rfl⟩
    · rintro ⟨l, ⟨hl, hf, hs⟩, rfl⟩; exact ⟨l, hl, hf, hs, rfl⟩
  dsimp only
  rw [hE]
  by_cases h : es = []
  · have : ¬ ({e | e ∈ es} : Set Nat).Nonempty := by rw [h]; simp
    simp only [this, ↓reduceIte]
    simp only [h, ↓reduceIte]
  · have : ({e | e ∈ es} : Set Nat).Nonempty := by
      obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil es h; exact ⟨e, he⟩
    simp only [this, h, ↓reduceIte, sSup_list h]

theorem liveLockBlocks_eq (hX : X.OK) (hM : X.Closed M) (L : List Lock) (t : Int) :
    liveLockBlocks X.sp {l | l ∈ L} (X.frameOf M) t = X.T (lockBlocksD L M t) := by
  ext B
  simp only [liveLockBlocks, liveLocks_eq hX hM, T, lockBlocksD, Set.mem_ofPred_eq,
    List.mem_map]
  constructor
  · rintro ⟨hB, l, hl, hlb⟩
    obtain ⟨-, e⟩ := root_mem_of_T hM hB
    exact ⟨l.block, ⟨l, hl, rfl⟩, hlb ▸ e⟩
  · rintro ⟨r, ⟨l, hl, rfl⟩, rfl⟩
    have hm := liveD_sub l hl
    exact ⟨blk_mem_T hm, l, hl, (blk_root (hM.valid _ hm)).symm⟩

theorem conflictsWithLock_eq (hX : X.OK) (hM : X.Closed M) (L : List Lock) (t : Int) {c : Nat}
    (hc : c ∈ M) :
    conflictsWithLock X.sp {l | l ∈ L} (X.frameOf M) t (X.blk c) ↔ X.conflictsD L M t c = true := by
  unfold conflictsWithLock conflictsD
  rw [liveLockBlocks_eq hX hM]
  simp only [T, Set.mem_ofPred_eq, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨B, ⟨r, hr, rfl⟩, hn⟩
    rw [compatible_frameOf hX hM hc (lockBlocksD_sub r hr)] at hn
    exact ⟨r, hr, hn⟩
  · rintro ⟨r, hr, hn⟩
    exact ⟨X.blk r, ⟨r, hr, rfl⟩, by rwa [compatible_frameOf hX hM hc (lockBlocksD_sub r hr)]⟩

theorem anchorD_mem (hM : X.Closed M) (L : List Lock) (t : Int) : X.anchorD L M t ∈ M := by
  unfold anchorD
  cases h : X.deep (X.g :: lockBlocksD L M t) with
  | none => exact hM.g_mem
  | some d =>
    rcases List.mem_cons.1 (bestBy_spec h).1 with rfl | hd
    · exact hM.g_mem
    · exact lockBlocksD_sub d hd

theorem getAnchor_eq (hX : X.OK) (hM : X.Closed M) (a : X.ACD) (t : Int) :
    getAnchor X.sp a.interp (X.frameOf M) t = X.blk (X.anchorD a.locks M t) := by
  unfold getAnchor anchorD
  rw [interp_locks, liveLockBlocks_eq hX hM,
    deepest_eq hX hM (L := X.g :: lockBlocksD a.locks M t)]
  · cases X.deep (X.g :: lockBlocksD a.locks M t) <;> simp [frameOf, blk_g hX]
  · intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact hM.g_mem
    · exact lockBlocksD_sub r hr
  · intro B
    simp only [frameOf, Set.mem_union, Set.mem_singleton_iff, T, Set.mem_ofPred_eq,
      List.mem_cons, exists_eq_or_imp, blk_g hX]
    exact or_comm

theorem addLocks_eq (hX : X.OK) (hM : X.Closed M) (L : List Lock) (t : Int) (s : Nat)
    (N : List (Nat × Bool × Nat)) :
    addLocks X.sp {l | l ∈ L} (X.frameOf M) t s {p | p ∈ N} = {l | l ∈ addLocksD L M t s N} := by
  unfold addLocks addLocksD
  have e : {l | l ∈ L} ∪ {l | ∃ p ∈ {p | p ∈ N}, l = (⟨p.1, s, p.2.1, p.2.2⟩ : Lock)} =
      {l | l ∈ L ++ N.map (fun p => (⟨p.1, s, p.2.1, p.2.2⟩ : Lock))} := by
    ext l; simp [eq_comm]
  rw [e, liveLocks_eq hX hM]

theorem unlockTarget_eq (hX : X.OK) (hM : X.Closed M) (p : List X.V × List X.V) (s : Int)
    {b : Nat} (hb : b ∈ M) :
    unlockTarget X.sp (X.frameOf M) (View.ofLists p) s (X.blk b) =
      X.blk (X.unlockTargetD M p s b) := by
  unfold unlockTarget unlockTargetD
  have hsub := chain_sub hX hM hb
  rw [deepest_eq hX hM (fun r hr => hsub r (List.mem_filter.1 hr).1)]
  · cases X.deep _ <;> simp [frameOf, blk_g hX]
  · intro B
    simp only [Set.mem_ofPred_eq, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨hB, hA, hc⟩
      obtain ⟨r, hr, rfl⟩ := (anc_T hX hM hb).1 hA
      rw [opponents_eq hX hM p s (hsub r hr), ncard_mem] at hc
      exact ⟨r, ⟨hr, hc⟩, rfl⟩
    · rintro ⟨r, ⟨hr, hc⟩, rfl⟩
      refine ⟨blk_mem_T (hsub r hr), (anc_T hX hM hb).2 ⟨r, hr, rfl⟩, ?_⟩
      rwa [opponents_eq hX hM p s (hsub r hr), ncard_mem]

theorem unlock_eq (hX : X.OK) (hM : X.Closed M) (L : List Lock) (t : Int) (s : Int)
    (p : List X.V × List X.V) :
    unlock X.sp {l | l ∈ L} (X.frameOf M) t s (View.ofLists p) = {l | l ∈ X.unlockD L M t s p} := by
  ext l'
  simp only [unlock, liveLocks_eq hX hM, unlockD, Set.mem_ofPred_eq, List.mem_map]
  constructor
  · rintro ⟨l, hl, B, hB, hr, rfl⟩
    obtain ⟨-, e⟩ := root_mem_of_T hM hB
    rw [hr] at e; subst e
    refine ⟨l, hl, ?_⟩
    have hm := liveD_sub l hl
    split_ifs
    · rw [unlockTarget_eq hX hM p s hm, blk_root (hM.valid _ (chain_sub hX hM hm _ ?_))]
      unfold unlockTargetD
      cases h : X.deep _ with
      | none => exact g_mem_chain hX (hM.valid _ hm)
      | some d => exact (List.mem_filter.1 (bestBy_spec h).1).1
    · rfl
  · rintro ⟨l, hl, rfl⟩
    have hm := liveD_sub l hl
    refine ⟨l, hl, X.blk l.block, blk_mem_T hm, blk_root (hM.valid _ hm), ?_⟩
    split_ifs
    · rw [unlockTarget_eq hX hM p s hm, blk_root]
      unfold unlockTargetD
      cases h : X.deep _ with
      | none => exact valid_g
      | some d => exact hM.valid _ (chain_sub hX hM hm _ (List.mem_filter.1 (bestBy_spec h).1).1)
    · rfl

/-! ## The walk -/

theorem goldfishEligible_eq (hX : X.OK) (hM : X.Closed M) (t : Int) (p : List X.V × List X.V)
    (s : Int) {c : Nat} (hc : c ∈ M) (hcg : c ≠ X.g) :
    goldfishEligible X.sp (X.frameOf M) t (View.ofLists p) s (X.blk c) ↔
      X.eligD M t p s c = true := by
  have hcm := mem_roots_of_valid (hM.valid c hc) hcg
  have hpar : ∃ W ∈ (X.frameOf M).viableHeads, (X.blk c).parent = some W.root :=
    ⟨X.blk (X.par c), blk_mem_T (hM.par_mem c hc hcg),
      by rw [blk_parent_of_mem hcm, blk_root (valid_par hX hcm)]⟩
  unfold goldfishEligible eligD
  rw [goldfishScore_eq hX hM p s (hM.valid c hc), blk_slot, slot_eq]
  simp only [hpar, not_true_eq_false, false_or, Bool.or_eq_true, decide_eq_true_eq]
  obtain ⟨L1, L2⟩ := p
  simp only [View.ofLists, voters_eq, ncard_mem]

theorem ghost_eq (hX : X.OK) {dom : List Nat} (hdom : ∀ r ∈ dom, X.Valid r)
    (sc : X.Blk → Nat) (el : X.Blk → Prop) (key : Nat → Nat) (elB : Nat → Bool)
    (hkey : ∀ c ∈ dom, sc (X.blk c) = key c)
    (hel : ∀ c ∈ dom, c ≠ X.g → (el (X.blk c) ↔ elB c = true)) :
    ∀ fuel h, X.Valid h → ghost X.sp (X.T dom) sc el fuel (X.blk h) =
      X.blk (X.ghostD dom key elB fuel h) := by
  intro fuel
  induction fuel with
  | zero => intro h _; rfl
  | succ f ih =>
    intro h hh
    set cs := dom.filter (fun c => decide (c ≠ X.g ∧ X.par c = h) && elB c) with hcs
    have hcsv : ∀ r ∈ cs, X.Valid r := fun r hr => hdom r (List.mem_filter.1 hr).1
    have hS : ∀ B, B ∈ {B | B ∈ X.T dom ∧ B.parent = some (X.blk h).root ∧ el B} ↔
        ∃ r ∈ cs, B = X.blk r := by
      intro B
      simp only [Set.mem_ofPred_eq, hcs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
        blk_root hh]
      constructor
      · rintro ⟨⟨c, hc, rfl⟩, hp, he⟩
        have hcg : c ≠ X.g := by rintro rfl; rw [blk_parent_g hX] at hp; cases hp
        rw [blk_parent_of_mem (mem_roots_of_valid (hdom c hc) hcg)] at hp
        exact ⟨c, ⟨hc, ⟨hcg, Option.some_injective _ hp⟩, (hel c hc hcg).1 he⟩, rfl⟩
      · rintro ⟨c, ⟨hc, ⟨hcg, hp⟩, he⟩, rfl⟩
        refine ⟨⟨c, hc, rfl⟩, ?_, (hel c hc hcg).2 he⟩
        rw [blk_parent_of_mem (mem_roots_of_valid (hdom c hc) hcg), hp]
    have hb := best_blk hcsv hS sc key (fun r hr => hkey r (List.mem_filter.1 hr).1)
    simp only [ghost]
    refine (pick_eq (P := IsBest X.sp sc _) hb.1 hb.2 _ _).trans ?_
    simp only [ghostD, ← hcs]
    cases ho : bestBy key cs with
    | none => rfl
    | some c => exact ih c (hcsv c (bestBy_spec ho).1)

theorem getHead_eq (hX : X.OK) (hM : X.Closed M) (hnd : M.Nodup) (a : X.ACD) (t : Int)
    {dom : List Nat} (hdom : ∀ r ∈ dom, r ∈ M) (p : List X.V × List X.V) (s : Int) :
    getHead X.sp a.interp (X.frameOf M) t (X.T dom) (View.ofLists p) s =
      X.blk (X.headD a M t dom p s) := by
  unfold getHead headD
  rw [getAnchor_eq hX hM, show (X.frameOf M).tree = X.T M from rfl, ncard_T hM hnd]
  exact ghost_eq hX (fun r hr => hM.valid r (hdom r hr)) _ _ _ _
    (fun c hc => goldfishScore_eq hX hM p s (hM.valid c (hdom c hc)))
    (fun c hc hcg => goldfishEligible_eq hX hM t p s (hdom c hc) hcg) _ _
    (hM.valid _ (anchorD_mem hM _ t))

end Fix

end Consensus.Goldilocks.Test.HalfCommittee

end
