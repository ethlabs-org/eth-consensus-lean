module
public import ConsensusLean.Instances.Goldilocks.Spec.WeightedLocks.Store
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Locks
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.UnlockTargetSelf

public section

/-! # Lock rules: the laws and the step properties

The operational part of a lock rule (a stored lock type `LockStore`, an unlock stage
`UnlockStage`, `LockStore.unlockWith` and `LockStore.addLocksWith`) is in the Spec
(`Spec/WeightedLocks/Store`). This module states its laws and proves the step properties the
parent's routes read of the unlock:

* `LockStore.Lawful`: a move changes only the block of the forgotten lock, the second of two
  moves wins, and a move to a lock's own block is no move;
* `UnlockStage.Lawful E K`, for a keep premise `K`: the stage's target is an ancestor in the tree,
  it keeps a lock at or above `Y` under `K`, and it reads a stored lock only up to its block;
* `UnlockStage.Fixes E G`: the stage fixes its own choice for the stored locks satisfying `G` in
  the frame (every lock for evidence-release; a composite of stages may need a condition on the
  lock, such as a weight antitone along the chain).

For a lawful store and stage:

* (B) `unlockWith_backward`: every lock of `unlockWith` is a stored lock moved to an ancestor of
  the parent's lock (the parent's `unlock` of the forgotten set), in the tree;
* no removal: `unlockWith_image` (every live stored lock has an image) and `unlockWith_covers`
  (every lock of the parent's unlock is the image of one);
* (S) `unlockWith_slot_ge`: a live lock of a slot at or above `s` keeps its place;
* (K) `unlockWith_keeps`: a live stored lock whose parent target is at or above `Y` stays at or
  above `Y` under `K`;
* A0.4 (c) `unlockWith_movesBack`, of the forgotten locks, the parent's statement `MovesBack`;
* A0.4 (d) `unlockWith_idempotent`, for stored locks satisfying `G`;
* A0.4 (e) reads only `opponents`, which a stage does not change;
* the write: `lock_image_addLocksWith` (the forgotten `addLocksWith` is `add_locks`).

**The parent is an instance**: `lockStore_lawful`, `UnlockStage.id_lawful` (premise `True`),
`unlockWith_id_eq_unlock` (`unlockWith` of the stage that adds nothing is `unlock`) and
`addLocksWith_lockStore` (`addLocksWith` is `addLocks`). -/

namespace Consensus.Goldilocks.SA

/-- The laws of a lock store: a move changes only the block of the forgotten lock, the second of
two moves wins, and a move to the lock's own block is no move. -/
structure LockStore.Lawful (S : LockStore) : Prop where
  /-- A move changes only the block of the forgotten lock. -/
  lock_withBlock : ∀ w r, S.lock (S.withBlock w r) = { S.lock w with block := r }
  /-- The second of two moves wins. -/
  withBlock_withBlock : ∀ w r r', S.withBlock (S.withBlock w r) r' = S.withBlock w r'
  /-- A move to the lock's own block is no move. -/
  withBlock_self : ∀ w, S.withBlock w (S.lock w).block = w

/-- A keep premise for a stage: when it holds of a stored lock at `Y`, the stage keeps the lock at
or above `Y`. -/
abbrev UnlockStage.Keep (sp : SAParams) (S : LockStore) (σ : Type) : Type 1 :=
  ∀ {FGP : Type}, σ → Frm sp.n FGP → View sp.n → Int → S.Lk → Blk sp.n FGP → Prop

/-- A lawful stage with keep premise `K`: it moves to an ancestor in the tree, keeps under `K`,
and reads a stored lock only up to its block. That it fixes its own choice is `Fixes`. -/
structure UnlockStage.Lawful {sp : SAParams} {S : LockStore} {σ : Type}
    (E : UnlockStage sp S σ) (K : UnlockStage.Keep sp S σ) : Prop where
  /-- The target does not read the lock's block. -/
  target_withBlock : ∀ {FGP : Type} (c : σ) (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int)
    (w : S.Lk) (r : Nat) (T : Blk sp.n FGP),
    E.target c Φ V s (S.withBlock w r) T = E.target c Φ V s w T
  /-- The target is in the tree, at or below `T`. -/
  target_anc : ∀ {FGP : Type} (c : σ) {Φ : Frm sp.n FGP} (V : View sp.n) (s : Int) (w : S.Lk)
    {T : Blk sp.n FGP}, FrameOK Φ → T ∈ Φ.tree →
    E.target c Φ V s w T ∈ Φ.tree ∧ Φ.Anc (E.target c Φ V s w T) T
  /-- Under `K`, a block of the tree at or below `T` stays at or below the target. -/
  keeps : ∀ {FGP : Type} (c : σ) {Φ : Frm sp.n FGP} (V : View sp.n) (s : Int) (w : S.Lk)
    {T Y : Blk sp.n FGP}, FrameOK Φ → Y ∈ Φ.tree → Φ.Anc Y T → K c Φ V s w Y →
    Φ.Anc Y (E.target c Φ V s w T)

/-- A predicate on stored locks in a frame (for the fixed-point law: the locks it holds for). -/
abbrev UnlockStage.Pred (sp : SAParams) (S : LockStore) : Type 1 :=
  ∀ {FGP : Type}, Frm sp.n FGP → S.Lk → Prop

/-- The stage fixes its own choice for the stored locks that satisfy `G` in the frame. -/
structure UnlockStage.Fixes {sp : SAParams} {S : LockStore} {σ : Type}
    (E : UnlockStage sp S σ) (G : UnlockStage.Pred sp S) : Prop where
  /-- The stage fixes its own choice. -/
  target_target : ∀ {FGP : Type} (c : σ) {Φ : Frm sp.n FGP} (V : View sp.n) (s : Int)
    (w : S.Lk) {T : Blk sp.n FGP}, FrameOK Φ → T ∈ Φ.tree → G Φ w →
    E.target c Φ V s w (E.target c Φ V s w T) = E.target c Φ V s w T

/-! ### Parent facts the idempotence uses -/

section ParentFacts

variable {sp : SAParams} {FGP : Type}

/-- A block below a candidate of `viable_ancestor` is a candidate. -/
theorem ancestorCandidate_of_anc {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {X B : Blk sp.n FGP}
    (hXB : Φ.Anc X B) (hB : Φ.AncestorCandidate B) : Φ.AncestorCandidate X := by
  rcases hB with hB | ⟨hBt, hfB, W, hW, hWv, hBW⟩
  · exact Or.inl (hXB.trans hB)
  · rcases anc_total hΦ.coherent hXB hfB with h | h
    · exact Or.inl h
    · exact Or.inr ⟨mem_of_anc hXB hBt, h, W, hW, hWv, hXB.trans hBW⟩

/-- An opponent of a block is an opponent of every descendant: a head incompatible with `Y` is
incompatible with every `D ⪰ Y`. -/
theorem opponents_anc {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (V : View sp.n) (s : Int)
    {Y D : Blk sp.n FGP} (hYD : Φ.Anc Y D) : opponents sp Φ V s Y ⊆ opponents sp Φ V s D := by
  rintro i (hi | ⟨x, hx, hxi, hs, H, hH, hHr, hc⟩)
  · exact Or.inl hi
  · refine Or.inr ⟨x, hx, hxi, hs, H, hH, hHr, fun hHD => hc ?_⟩
    rcases hHD with h | h
    · exact anc_total hΦ.coherent h hYD
    · exact Or.inr (hYD.trans h)

/-- The parent's unlock target of a block of the tree at or below the unlock target of `B` is
that block itself: the blocks with few opponents below `B` are closed downwards
(`opponents_anc`), and below `Φ.F` there is only `Φ.F`. -/
theorem unlockTarget_eq_self_of_anc_unlockTarget {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (V : View sp.n) (s : Int) {B Y : Blk sp.n FGP} (hB : B ∈ Φ.tree) (hY : Y ∈ Φ.tree)
    (hYT : Φ.Anc Y (unlockTarget sp Φ V s B)) : unlockTarget sp Φ V s Y = Y := by
  have hsub : ∀ {X}, Φ.Anc X B →
      {B' | B' ∈ Φ.tree ∧ Φ.Anc B' X ∧ 2 * (opponents sp Φ V s B').ncard < sp.n} ⊆
      {B' | B' ∈ Φ.tree ∧ Φ.Anc B' B ∧ 2 * (opponents sp Φ V s B').ncard < sp.n} :=
    fun hXB B' hB' => ⟨hB'.1, hB'.2.1.trans hXB, hB'.2.2⟩
  unfold unlockTarget at hYT
  rcases hd : deepest Φ {B' | B' ∈ Φ.tree ∧ Φ.Anc B' B ∧ 2 * (opponents sp Φ V s B').ncard < sp.n}
    with _ | D
  · rw [hd, Option.getD_none] at hYT
    obtain rfl : Y = Φ.F := Anc.antisymm hΦ.coherent hYT (hΦ.rooted.2 Y hY)
    have hempty :
        {B' | B' ∈ Φ.tree ∧ Φ.Anc B' B ∧ 2 * (opponents sp Φ V s B').ncard < sp.n} = ∅ := by
      by_contra hne
      obtain ⟨D, hD⟩ := exists_deepest hΦ (fun X hX => hX.1) (Set.nonempty_iff_ne_empty.2 hne)
      rw [hd] at hD
      cases hD
    unfold unlockTarget
    rcases hd' : deepest Φ
        {B' | B' ∈ Φ.tree ∧ Φ.Anc B' Φ.F ∧ 2 * (opponents sp Φ V s B').ncard < sp.n} with _ | D'
    · rfl
    · have := hsub (hΦ.rooted.2 B hB) (deepest_mem hd').1
      rw [hempty] at this
      exact absurd this (Set.notMem_empty _)
  · rw [hd, Option.getD_some] at hYT
    obtain ⟨⟨-, -, hDf⟩, -⟩ := deepest_mem hd
    refine unlockTarget_eq_self hΦ V s hY (lt_of_le_of_lt ?_ hDf)
    exact Nat.mul_le_mul_left 2 (Set.ncard_le_ncard (opponents_anc hΦ V s hYT) (Set.toFinite _))

end ParentFacts

namespace LockStore

variable (S : LockStore) (sp : SAParams) {FGP : Type}

variable {S sp}

theorem mem_liveLocks {L : Set S.Lk} {Φ : Frm sp.n FGP} {t : Time} {w' : S.Lk} :
    w' ∈ S.liveLocks sp L Φ t ↔ ∃ w ∈ L, ∃ B ∈ Φ.tree, B.root = (S.lock w).block ∧
      (S.lock w).LiveAt sp t ∧ w' = S.withBlock w (Φ.viableAncestor B).root :=
  Iff.rfl

theorem addLocksWith_eq (L N : Set S.Lk) (Φ : Frm sp.n FGP) (t : Time) :
    S.addLocksWith sp L N Φ t = S.liveLocks sp (L ∪ N) Φ t := by
  rfl

theorem mem_unlockWith {σ : Type} {E : UnlockStage sp S σ} {c : σ} {L : Set S.Lk}
    {Φ : Frm sp.n FGP} {t : Time} {s : Int} {V : View sp.n} {w' : S.Lk} :
    w' ∈ S.unlockWith sp E c L Φ t s V ↔ ∃ w ∈ S.liveLocks sp L Φ t, ∃ B ∈ Φ.tree,
      B.root = (S.lock w).block ∧ w' = if ((S.lock w).slot : Int) < s then
        S.withBlock w (E.target c Φ V s w (unlockTarget sp Φ V s B)).root else w :=
  Iff.rfl

/-- The fields of a moved lock: the block is the new one, the rest is the stored lock's. -/
theorem lock_withBlock_fields (hS : S.Lawful) (w : S.Lk) (r : Nat) :
    (S.lock (S.withBlock w r)).block = r ∧ (S.lock (S.withBlock w r)).slot = (S.lock w).slot ∧
      (S.lock (S.withBlock w r)).fast = (S.lock w).fast ∧
      (S.lock (S.withBlock w r)).expiry = (S.lock w).expiry := by
  rw [hS.lock_withBlock]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The forgotten live stored locks are the parent's live locks of the forgotten set. -/
theorem lock_image_liveLocks (hS : S.Lawful) (L : Set S.Lk) (Φ : Frm sp.n FGP) (t : Time) :
    S.lock '' S.liveLocks sp L Φ t = SA.liveLocks sp (S.lock '' L) Φ t := by
  ext l
  constructor
  · rintro ⟨_, ⟨w, hw, B, hB, hr, hlive, rfl⟩, rfl⟩
    exact ⟨S.lock w, ⟨w, hw, rfl⟩, B, hB, hr, hlive, hS.lock_withBlock _ _⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, B, hB, hr, hlive, rfl⟩
    exact ⟨_, ⟨w, hw, B, hB, hr, hlive, rfl⟩, hS.lock_withBlock _ _⟩

/-- **The write.** If the new stored locks forget to the parent's new locks of slot `s`, the
forgotten `addLocksWith` is the parent's `add_locks`. -/
theorem lock_image_addLocksWith (hS : S.Lawful) (L N : Set S.Lk) (Φ : Frm sp.n FGP) (t : Time)
    (s : Nat)
    {N' : Set (Nat × Bool × Nat)}
    (hN : S.lock '' N = {l | ∃ p ∈ N', l = ⟨p.1, s, p.2.1, p.2.2⟩}) :
    S.lock '' S.addLocksWith sp L N Φ t = addLocks sp (S.lock '' L) Φ t s N' := by
  rw [addLocksWith_eq, lock_image_liveLocks hS, Set.image_union, hN]
  rfl

/-- A lock of `unlockWith` written out from the stored lock it comes from. -/
theorem mem_unlockWith_stored {σ : Type} (hS : S.Lawful) {E : UnlockStage sp S σ}
    {K : UnlockStage.Keep sp S σ}
    (hE : E.Lawful K) {c : σ}
    {L : Set S.Lk} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} {s : Int} {V : View sp.n}
    {w' : S.Lk} (hw' : w' ∈ S.unlockWith sp E c L Φ t s V) :
    ∃ w ∈ L, ∃ B ∈ Φ.tree, B.root = (S.lock w).block ∧ (S.lock w).LiveAt sp t ∧
      w' = if ((S.lock w).slot : Int) < s then
        S.withBlock w (E.target c Φ V s w (unlockTarget sp Φ V s (Φ.viableAncestor B))).root
      else S.withBlock w (Φ.viableAncestor B).root := by
  obtain ⟨_, ⟨w, hw, B₀, hB₀, hr₀, hlive, rfl⟩, B, hB, hBr, rfl⟩ := hw'
  obtain ⟨hvt, -⟩ := viableAncestor_anc hΦ hB₀
  obtain rfl : B = Φ.viableAncestor B₀ :=
    hΦ.coherent.1 hB hvt (hBr.trans (lock_withBlock_fields hS w _).1)
  refine ⟨w, hw, B₀, hB₀, hr₀, hlive, ?_⟩
  simp only [(lock_withBlock_fields hS w _).2.1, hS.withBlock_withBlock, hE.target_withBlock]

/-- **(B), backward.** Every lock of `unlockWith` is a stored lock moved to an ancestor (in the
tree) of the block of a lock of the parent's `unlock` of the forgotten set, with that lock's
slot, fast bit and expiry. -/
theorem unlockWith_backward {σ : Type} (hS : S.Lawful) {E : UnlockStage sp S σ}
    {K : UnlockStage.Keep sp S σ}
    (hE : E.Lawful K) (c : σ)
    {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (L : Set S.Lk) (t : Time) (s : Int) (V : View sp.n) :
    ∀ w' ∈ S.unlockWith sp E c L Φ t s V, ∃ w ∈ L, (∃ r, w' = S.withBlock w r) ∧
      ∃ l ∈ unlock sp (S.lock '' L) Φ t s V, l.slot = (S.lock w).slot ∧
        l.fast = (S.lock w).fast ∧ l.expiry = (S.lock w).expiry ∧
        ∃ T ∈ Φ.tree, T.root = l.block ∧ ∃ Y ∈ Φ.tree, Y.root = (S.lock w').block ∧
          Φ.Anc Y T := by
  intro w' hw'
  obtain ⟨w, hw, B₀, hB₀, hr₀, hlive, rfl⟩ := mem_unlockWith_stored hS hE hΦ hw'
  obtain ⟨hvt, hvB⟩ := viableAncestor_anc hΦ hB₀
  have hl : (⟨(Φ.viableAncestor B₀).root, (S.lock w).slot, (S.lock w).fast,
      (S.lock w).expiry⟩ : Lock) ∈ SA.liveLocks sp (S.lock '' L) Φ t :=
    ⟨S.lock w, ⟨w, hw, rfl⟩, B₀, hB₀, hr₀, hlive, rfl⟩
  have hu : ∀ l', l' = (if ((S.lock w).slot : Int) < s then
      (⟨(unlockTarget sp Φ V s (Φ.viableAncestor B₀)).root, (S.lock w).slot, (S.lock w).fast,
        (S.lock w).expiry⟩ : Lock) else
      ⟨(Φ.viableAncestor B₀).root, (S.lock w).slot, (S.lock w).fast, (S.lock w).expiry⟩) →
      l' ∈ unlock sp (S.lock '' L) Φ t s V :=
    fun l' hl' => ⟨_, hl, _, hvt, rfl, hl'⟩
  by_cases hlt : ((S.lock w).slot : Int) < s
  · obtain ⟨hTt, -⟩ := unlockTarget_anc sp hΦ V s hvt
    obtain ⟨hEt, hET⟩ := hE.target_anc c V s w hΦ hTt
    refine ⟨w, hw, ⟨_, ite_eq_left hlt⟩, _, hu _ (ite_eq_left hlt).symm, rfl, rfl, rfl, _, hTt,
      rfl, _, hEt, ?_, hET⟩
    rw [ite_eq_left hlt, (lock_withBlock_fields hS w _).1]
  · refine ⟨w, hw, ⟨_, ite_eq_right hlt⟩, _, hu _ (ite_eq_right hlt).symm, rfl, rfl, rfl, _, hvt,
      rfl, _, hvt, ?_, .refl⟩
    rw [ite_eq_right hlt, (lock_withBlock_fields hS w _).1]

/-- **No removal.** Every live stored lock has an image in `unlockWith`: the stored lock moved to
an ancestor of its block in the tree. -/
theorem unlockWith_image {σ : Type} (hS : S.Lawful) {E : UnlockStage sp S σ}
    {K : UnlockStage.Keep sp S σ}
    (hE : E.Lawful K) (c : σ)
    {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {L : Set S.Lk} {t : Time} (s : Int) (V : View sp.n)
    {w : S.Lk} (hw : w ∈ L) {B : Blk sp.n FGP} (hB : B ∈ Φ.tree)
    (hBr : B.root = (S.lock w).block) (hlive : (S.lock w).LiveAt sp t) :
    ∃ Y ∈ Φ.tree, Φ.Anc Y B ∧ S.withBlock w Y.root ∈ S.unlockWith sp E c L Φ t s V := by
  obtain ⟨hvt, hvB⟩ := viableAncestor_anc hΦ hB
  have hlw : S.withBlock w (Φ.viableAncestor B).root ∈ S.liveLocks sp L Φ t :=
    ⟨w, hw, B, hB, hBr, hlive, rfl⟩
  have hmem := (mem_unlockWith (E := E) (c := c) (s := s) (V := V)).2
    ⟨_, hlw, _, hvt, (lock_withBlock_fields hS w _).1.symm, rfl⟩
  rw [(lock_withBlock_fields hS w _).2.1, hS.withBlock_withBlock, hE.target_withBlock] at hmem
  by_cases hlt : ((S.lock w).slot : Int) < s
  · rw [ite_eq_left hlt] at hmem
    obtain ⟨hTt, hTB⟩ := unlockTarget_anc sp hΦ V s hvt
    obtain ⟨hEt, hET⟩ := hE.target_anc c V s w hΦ hTt
    exact ⟨_, hEt, hET.trans (hTB.trans hvB), hmem⟩
  · rw [ite_eq_right hlt] at hmem
    exact ⟨_, hvt, hvB, hmem⟩

/-- **No removal**, against the parent: every lock of the parent's `unlock` of the forgotten set
is, up to its block, the forgotten image of a lock of `unlockWith`. -/
theorem unlockWith_covers {σ : Type} (hS : S.Lawful) {E : UnlockStage sp S σ}
    {K : UnlockStage.Keep sp S σ}
    (hE : E.Lawful K) (c : σ)
    {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (L : Set S.Lk) (t : Time) (s : Int) (V : View sp.n) :
    ∀ l ∈ unlock sp (S.lock '' L) Φ t s V, ∃ w' ∈ S.unlockWith sp E c L Φ t s V,
      (S.lock w').slot = l.slot ∧ (S.lock w').fast = l.fast ∧
        (S.lock w').expiry = l.expiry := by
  rintro _ ⟨_, ⟨_, ⟨w, hw, rfl⟩, B₀, hB₀, hr₀, hlive, rfl⟩, B, hB, hBr, rfl⟩
  obtain ⟨Y, -, -, hY⟩ := unlockWith_image hS hE c hΦ s V hw hB₀ hr₀ hlive
  obtain ⟨-, h1, h2, h3⟩ := lock_withBlock_fields hS w Y.root
  refine ⟨_, hY, ?_⟩
  split_ifs <;> exact ⟨h1, h2, h3⟩

/-- **(S), the slot exemption.** A live stored lock of a slot at or above `s` keeps its place. -/
theorem unlockWith_slot_ge {σ : Type} {E : UnlockStage sp S σ} {c : σ} {L : Set S.Lk}
    {Φ : Frm sp.n FGP} {t : Time} {s : Int} {V : View sp.n} {w : S.Lk}
    (hw : w ∈ S.liveLocks sp L Φ t) (hs : s ≤ ((S.lock w).slot : Int)) {B : Blk sp.n FGP}
    (hB : B ∈ Φ.tree) (hBr : B.root = (S.lock w).block) :
    w ∈ S.unlockWith sp E c L Φ t s V :=
  ⟨w, hw, B, hB, hBr, by rw [ite_eq_right (not_lt.2 hs)]⟩

/-- **(K), the keep.** A live stored lock on `B` whose parent unlock target (from its viable
ancestor) is at or above `Y` in the tree stays at or above `Y` in `unlockWith` when the stage's
premise holds at `Y`. -/
theorem unlockWith_keeps {σ : Type} (hS : S.Lawful) {E : UnlockStage sp S σ}
    {K : UnlockStage.Keep sp S σ}
    (hE : E.Lawful K) (c : σ)
    {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {L : Set S.Lk} {t : Time} {s : Int} {V : View sp.n}
    {w : S.Lk} (hw : w ∈ L) {B : Blk sp.n FGP} (hB : B ∈ Φ.tree)
    (hBr : B.root = (S.lock w).block) (hlive : (S.lock w).LiveAt sp t) {Y : Blk sp.n FGP}
    (hY : Y ∈ Φ.tree) (hpar : Φ.Anc Y (unlockTarget sp Φ V s (Φ.viableAncestor B)))
    (hk : K c Φ V s w Y) :
    ∃ Z ∈ Φ.tree, Φ.Anc Y Z ∧ S.withBlock w Z.root ∈ S.unlockWith sp E c L Φ t s V := by
  obtain ⟨hvt, -⟩ := viableAncestor_anc hΦ hB
  have hlw : S.withBlock w (Φ.viableAncestor B).root ∈ S.liveLocks sp L Φ t :=
    ⟨w, hw, B, hB, hBr, hlive, rfl⟩
  have hmem := (mem_unlockWith (E := E) (c := c) (s := s) (V := V)).2
    ⟨_, hlw, _, hvt, (lock_withBlock_fields hS w _).1.symm, rfl⟩
  rw [(lock_withBlock_fields hS w _).2.1, hS.withBlock_withBlock, hE.target_withBlock] at hmem
  obtain ⟨hTt, -⟩ := unlockTarget_anc sp hΦ V s hvt
  by_cases hlt : ((S.lock w).slot : Int) < s
  · rw [ite_eq_left hlt] at hmem
    exact ⟨_, (hE.target_anc c V s w hΦ hTt).1, hE.keeps c V s w hΦ hY hpar hk, hmem⟩
  · rw [ite_eq_right hlt] at hmem
    exact ⟨_, hvt, hpar.trans (unlockTarget_anc sp hΦ V s hvt).2, hmem⟩

/-- **A0.4 (c) for `unlockWith`**: the forgotten locks only move back, in the parent's sense
`MovesBack`. -/
theorem unlockWith_movesBack {σ : Type} (hS : S.Lawful) {E : UnlockStage sp S σ}
    {K : UnlockStage.Keep sp S σ}
    (hE : E.Lawful K) (c : σ)
    {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (L : Set S.Lk) (t : Time) (s : Int) (V : View sp.n) :
    MovesBack sp Φ (S.lock '' L) (S.lock '' S.unlockWith sp E c L Φ t s V) := by
  rintro _ ⟨w', hw', rfl⟩
  obtain ⟨w, -, ⟨r, rfl⟩, l, hl, hs₁, hf₁, he₁, T, hT, hTr, Y, hY, hYr, hYT⟩ :=
    unlockWith_backward hS hE c hΦ L t s V _ hw'
  obtain ⟨l₀, hl₀, hs, hf, he, B₀, hB₀, hr₀, B₁, hB₁, hr₁, hB₁B₀⟩ :=
    (locks_move_back sp FGP Φ (S.lock '' L) t hΦ).2.2 s V l hl
  obtain rfl : T = B₁ := hΦ.coherent.1 hT hB₁ (hTr.trans hr₁.symm)
  obtain ⟨-, h1, h2, h3⟩ := lock_withBlock_fields hS w r
  exact ⟨l₀, hl₀, by rw [h1, ← hs₁, hs], by rw [h2, ← hf₁, hf], by rw [h3, ← he₁, he], B₀, hB₀,
    hr₀, Y, hY, hYr, hYT.trans hB₁B₀⟩

/-- Every lock of `unlockWith` is live, on a block that is its own viable ancestor and, for a slot
below `s`, fixed by the parent's unlock and by the stage. -/
private theorem unlockWith_fixed {σ : Type} (hS : S.Lawful) {E : UnlockStage sp S σ}
    {K : UnlockStage.Keep sp S σ} {G : UnlockStage.Pred sp S}
    (hE : E.Lawful K) (hF : E.Fixes G) (c : σ)
    {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {L : Set S.Lk} (hG : ∀ w ∈ L, G Φ w) (t : Time) (s : Int)
    (V : View sp.n) :
    ∀ w ∈ S.unlockWith sp E c L Φ t s V, ∃ Y ∈ Φ.tree, Y.root = (S.lock w).block ∧
      (S.lock w).LiveAt sp t ∧ Φ.viableAncestor Y = Y ∧ (((S.lock w).slot : Int) < s →
        E.target c Φ V s w (unlockTarget sp Φ V s Y) = Y) := by
  intro w' hw'
  obtain ⟨w, hw, B₀, hB₀, -, hlive, rfl⟩ := mem_unlockWith_stored hS hE hΦ hw'
  obtain ⟨hvt, -⟩ := viableAncestor_anc hΦ hB₀
  have hcand := (viableAncestor_spec hΦ hB₀).2.1
  by_cases hlt : ((S.lock w).slot : Int) < s
  · rw [ite_eq_left hlt]
    obtain ⟨-, h1, -, h3⟩ := lock_withBlock_fields hS w
      (E.target c Φ V s w (unlockTarget sp Φ V s (Φ.viableAncestor B₀))).root
    obtain ⟨hTt, hTB⟩ := unlockTarget_anc sp hΦ V s hvt
    obtain ⟨hYt, hYT⟩ := hE.target_anc c V s w hΦ hTt
    refine ⟨_, hYt, (lock_withBlock_fields hS w _).1.symm, (by rw [Lock.LiveAt, h3]; exact hlive),
      viableAncestor_self hΦ hYt (ancestorCandidate_of_anc hΦ (hYT.trans hTB) hcand).symm,
      fun _ => ?_⟩
    rw [unlockTarget_eq_self_of_anc_unlockTarget hΦ V s hvt hYt hYT, hE.target_withBlock,
      hF.target_target c V s w hΦ hTt (hG w hw)]
  · rw [ite_eq_right hlt]
    obtain ⟨-, h1, -, h3⟩ := lock_withBlock_fields hS w (Φ.viableAncestor B₀).root
    exact ⟨_, hvt, (lock_withBlock_fields hS w _).1.symm, (by rw [Lock.LiveAt, h3]; exact hlive),
      viableAncestor_self hΦ hvt hcand.symm, fun h => absurd (h1 ▸ h) hlt⟩

/-- **A0.4 (d) for `unlockWith`**: for a lawful stage that fixes its own choice for the stored
locks, unlocking is idempotent for a fixed context, frame, slot, view and time. -/
theorem unlockWith_idempotent {σ : Type} (hS : S.Lawful) {E : UnlockStage sp S σ}
    {K : UnlockStage.Keep sp S σ} {G : UnlockStage.Pred sp S}
    (hE : E.Lawful K) (hF : E.Fixes G) (c : σ)
    {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {L : Set S.Lk} (hG : ∀ w ∈ L, G Φ w) (t : Time) (s : Int)
    (V : View sp.n) :
    S.unlockWith sp E c (S.unlockWith sp E c L Φ t s V) Φ t s V =
      S.unlockWith sp E c L Φ t s V := by
  have hfix := unlockWith_fixed hS hE hF c hΦ hG t s V
  -- the second pass returns each lock of the first unchanged
  have hid : ∀ w ∈ S.unlockWith sp E c L Φ t s V, ∀ B ∈ Φ.tree, B.root = (S.lock w).block →
      (if ((S.lock w).slot : Int) < s then
        S.withBlock w (E.target c Φ V s w (unlockTarget sp Φ V s B)).root else w) = w := by
    intro w hw B hB hBr
    obtain ⟨Y, hY, hYr, -, -, hT⟩ := hfix w hw
    obtain rfl : B = Y := hΦ.coherent.1 hB hY (hBr.trans hYr.symm)
    by_cases h : ((S.lock w).slot : Int) < s
    · rw [ite_eq_left h, hT h, hBr, hS.withBlock_self]
    · rw [ite_eq_right h]
  have hlive : ∀ w ∈ S.unlockWith sp E c L Φ t s V, ∃ Y ∈ Φ.tree, Y.root = (S.lock w).block ∧
      (S.lock w).LiveAt sp t ∧ w = S.withBlock w (Φ.viableAncestor Y).root := by
    intro w hw
    obtain ⟨Y, hY, hYr, hk, hva, -⟩ := hfix w hw
    exact ⟨Y, hY, hYr, hk, by rw [hva, hYr, hS.withBlock_self]⟩
  ext w
  constructor
  · intro hw2
    obtain ⟨w', hw', B, hB, hBr, rfl⟩ := mem_unlockWith.1 hw2
    obtain ⟨w₁, hw₁, Y₁, hY₁, hY₁r, -, rfl⟩ := mem_liveLocks.1 hw'
    obtain ⟨Y₂, hY₂, hY₂r, -, hva, -⟩ := hfix w₁ hw₁
    obtain rfl : Y₁ = Y₂ := hΦ.coherent.1 hY₁ hY₂ (hY₁r.trans hY₂r.symm)
    have he : S.withBlock w₁ (Φ.viableAncestor Y₁).root = w₁ := by
      rw [hva, hY₁r, hS.withBlock_self]
    rw [he] at hBr ⊢
    rw [hid w₁ hw₁ B hB hBr]
    exact hw₁
  · intro hw
    obtain ⟨Y, hY, hYr, hk, he⟩ := hlive w hw
    exact mem_unlockWith.2 ⟨w, mem_liveLocks.2 ⟨w, hw, Y, hY, hYr, hk, he⟩, Y, hY, hYr,
      (hid w hw Y hY hYr).symm⟩

end LockStore

/-! ### The parent as an instance -/

theorem lockStore_lock (l : lockStore.Lk) : lockStore.lock l = l := by
  rfl

theorem lockStore_withBlock (l : lockStore.Lk) (r : Nat) :
    lockStore.withBlock l r = ({ (l : Lock) with block := r } : Lock) := by
  rfl

/-- The parent's lock store is lawful. -/
theorem lockStore_lawful : lockStore.Lawful where
  lock_withBlock _ _ := rfl
  withBlock_withBlock _ _ _ := rfl
  withBlock_self _ := rfl

theorem UnlockStage.id_target {sp : SAParams} {S : LockStore} {σ : Type} {FGP : Type} (c : σ)
    (Φ : Frm sp.n FGP) (V : View sp.n) (s : Int) (w : S.Lk) (T : Blk sp.n FGP) :
    (UnlockStage.id sp S σ).target c Φ V s w T = T := by
  rfl

/-- The stage that adds nothing is lawful, with the premise that always holds. -/
theorem UnlockStage.id_lawful (sp : SAParams) (S : LockStore) (σ : Type) :
    (UnlockStage.id sp S σ).Lawful fun _ _ _ _ _ _ => True where
  target_withBlock _ _ _ _ _ _ _ := rfl
  target_anc := by intros; exact ⟨‹_›, .refl⟩
  keeps := by intros; assumption

/-- The stage that adds nothing fixes its own choice for every lock. -/
theorem UnlockStage.id_fixes (sp : SAParams) (S : LockStore) (σ : Type) :
    (UnlockStage.id sp S σ).Fixes fun _ _ => True where
  target_target := by intros; rfl

variable {sp : SAParams} {FGP : Type}

/-- **The parent's unlock is an instance**: the parent's lock store with the stage that adds
nothing gives `unlock` exactly. -/
theorem unlockWith_id_eq_unlock {σ : Type} (c : σ) (L : Set Lock) (Φ : Frm sp.n FGP) (t : Time)
    (s : Int) (V : View sp.n) :
    lockStore.unlockWith sp (UnlockStage.id sp lockStore σ) c L Φ t s V = unlock sp L Φ t s V := by
  rfl

/-- **The parent's write is an instance**: `addLocksWith` of the parent's new locks of slot `s`
is `add_locks`. -/
theorem addLocksWith_lockStore (L : Set Lock) (Φ : Frm sp.n FGP) (t : Time) (s : Nat)
    (N : Set (Nat × Bool × Nat)) :
    lockStore.addLocksWith sp L {l | ∃ p ∈ N, l = ⟨p.1, s, p.2.1, p.2.2⟩} Φ t =
      addLocks sp L Φ t s N := by
  rfl

end Consensus.Goldilocks.SA

end
