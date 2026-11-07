module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockRule

public section

/-! # Lock rules: one unlock stage after another

`UnlockStage.comp E₁ E₂` moves a lock first to `E₁`'s target and from there to `E₂`'s target, with
the pair of their contexts. It is lawful with the conjunction of the keep premises
(`UnlockStage.comp_lawful`): its target is an ancestor of `E₁`'s, which is an ancestor of the
parent's, and a block that both stages keep stays.

It fixes its own choice (`UnlockStage.comp_fixes`) when `E₂` fixes its own choice and `E₁` fixes
every block of the tree at or below its own choice (`UnlockStage.FixesBelow`): then `E₂`'s choice,
which lies at or below `E₁`'s, is left in place by `E₁`, and then by `E₂`. The parent's unlock
target has that property (`unlockTarget_eq_self_of_anc_unlockTarget`), and evidence-release's
stage has it for locks whose weight is antitone along the chain (`Candidates/LateCertificate`). -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {S : LockStore}

/-- `E₂` after `E₁`, reading the pair of their contexts. -/
def UnlockStage.comp {σ₁ σ₂ : Type} (E₁ : UnlockStage sp S σ₁) (E₂ : UnlockStage sp S σ₂) :
    UnlockStage sp S (σ₁ × σ₂) where
  target c Φ V s w T := E₂.target c.2 Φ V s w (E₁.target c.1 Φ V s w T)

theorem UnlockStage.comp_target {σ₁ σ₂ : Type} (E₁ : UnlockStage sp S σ₁)
    (E₂ : UnlockStage sp S σ₂) {FGP : Type} (c : σ₁ × σ₂) (Φ : Frm sp.n FGP) (V : View sp.n)
    (s : Int) (w : S.Lk) (T : Blk sp.n FGP) :
    (E₁.comp E₂).target c Φ V s w T = E₂.target c.2 Φ V s w (E₁.target c.1 Φ V s w T) := by
  rfl

/-- The keep premise of a composite: both stages' premises. -/
def UnlockStage.Keep.and {σ₁ σ₂ : Type} (K₁ : UnlockStage.Keep sp S σ₁)
    (K₂ : UnlockStage.Keep sp S σ₂) : UnlockStage.Keep sp S (σ₁ × σ₂) :=
  fun c Φ V s w Y => K₁ c.1 Φ V s w Y ∧ K₂ c.2 Φ V s w Y

theorem UnlockStage.Keep.and_iff {σ₁ σ₂ : Type} (K₁ : UnlockStage.Keep sp S σ₁)
    (K₂ : UnlockStage.Keep sp S σ₂) {FGP : Type} (c : σ₁ × σ₂) (Φ : Frm sp.n FGP)
    (V : View sp.n) (s : Int) (w : S.Lk) (Y : Blk sp.n FGP) :
    K₁.and K₂ c Φ V s w Y ↔ K₁ c.1 Φ V s w Y ∧ K₂ c.2 Φ V s w Y :=
  Iff.rfl

/-- **The composite is lawful**, with both keep premises. -/
theorem UnlockStage.comp_lawful {σ₁ σ₂ : Type} {E₁ : UnlockStage sp S σ₁}
    {E₂ : UnlockStage sp S σ₂} {K₁ : UnlockStage.Keep sp S σ₁} {K₂ : UnlockStage.Keep sp S σ₂}
    (h₁ : E₁.Lawful K₁) (h₂ : E₂.Lawful K₂) : (E₁.comp E₂).Lawful (K₁.and K₂) where
  target_withBlock c Φ V s w r T := by
    rw [UnlockStage.comp_target, UnlockStage.comp_target, h₁.target_withBlock,
      h₂.target_withBlock]
  target_anc := by
    intro _ c Φ V s w T hΦ hT
    rw [UnlockStage.comp_target]
    obtain ⟨h1t, h1a⟩ := h₁.target_anc c.1 V s w hΦ hT
    obtain ⟨h2t, h2a⟩ := h₂.target_anc c.2 V s w hΦ h1t
    exact ⟨h2t, h2a.trans h1a⟩
  keeps := by
    intro _ c Φ V s w T Y hΦ hY hYT hk
    rw [UnlockStage.comp_target]
    exact h₂.keeps c.2 V s w hΦ hY (h₁.keeps c.1 V s w hΦ hY hYT hk.1) hk.2

/-- The stage fixes every block of the tree at or below its own choice, for the stored locks that
satisfy `G` in the frame. -/
structure UnlockStage.FixesBelow {σ : Type} (E : UnlockStage sp S σ) (G : UnlockStage.Pred sp S) :
    Prop where
  /-- A block at or below the stage's choice is its own target. -/
  target_of_anc : ∀ {FGP : Type} (c : σ) {Φ : Frm sp.n FGP} (V : View sp.n) (s : Int)
    (w : S.Lk) {T Y : Blk sp.n FGP}, FrameOK Φ → T ∈ Φ.tree → Y ∈ Φ.tree → G Φ w →
    Φ.Anc Y (E.target c Φ V s w T) → E.target c Φ V s w Y = Y

/-- A stage that fixes every block at or below its choice fixes its choice. -/
theorem UnlockStage.FixesBelow.fixes {σ : Type} {E : UnlockStage sp S σ}
    {G : UnlockStage.Pred sp S} {K : UnlockStage.Keep sp S σ} (hE : E.Lawful K)
    (h : E.FixesBelow G) : E.Fixes G where
  target_target := by
    intro _ c Φ V s w T hΦ hT hG
    exact h.target_of_anc c V s w hΦ hT (hE.target_anc c V s w hΦ hT).1 hG .refl

/-- The predicate of a composite: both stages' predicates. -/
def UnlockStage.Pred.and (G₁ G₂ : UnlockStage.Pred sp S) : UnlockStage.Pred sp S :=
  fun Φ w => G₁ Φ w ∧ G₂ Φ w

theorem UnlockStage.Pred.and_iff (G₁ G₂ : UnlockStage.Pred sp S) {FGP : Type}
    (Φ : Frm sp.n FGP) (w : S.Lk) : G₁.and G₂ Φ w ↔ G₁ Φ w ∧ G₂ Φ w :=
  Iff.rfl

/-- **The composite fixes its own choice** when `E₁` fixes every block at or below its choice and
`E₂` fixes its choice. -/
theorem UnlockStage.comp_fixes {σ₁ σ₂ : Type} {E₁ : UnlockStage sp S σ₁}
    {E₂ : UnlockStage sp S σ₂} {K₁ : UnlockStage.Keep sp S σ₁} {K₂ : UnlockStage.Keep sp S σ₂}
    {G₁ G₂ : UnlockStage.Pred sp S} (h₁ : E₁.Lawful K₁) (h₂ : E₂.Lawful K₂)
    (hb : E₁.FixesBelow G₁) (hf : E₂.Fixes G₂) : (E₁.comp E₂).Fixes (G₁.and G₂) where
  target_target := by
    intro _ c Φ V s w T hΦ hT hG
    simp only [UnlockStage.comp_target]
    obtain ⟨h1t, -⟩ := h₁.target_anc c.1 V s w hΦ hT
    obtain ⟨h2t, h2a⟩ := h₂.target_anc c.2 V s w hΦ h1t
    rw [hb.target_of_anc c.1 V s w hΦ hT h2t hG.1 h2a, hf.target_target c.2 V s w hΦ h1t hG.2]

/-- **(B) against the first stage.** Every lock of the composite's unlock is a lock of the first
stage's unlock moved to an ancestor of its block, in the tree. -/
theorem LockStore.unlockWith_comp_backward {σ₁ σ₂ : Type} (hS : S.Lawful)
    {E₁ : UnlockStage sp S σ₁} {E₂ : UnlockStage sp S σ₂} {K₁ : UnlockStage.Keep sp S σ₁}
    {K₂ : UnlockStage.Keep sp S σ₂} (h₁ : E₁.Lawful K₁) (h₂ : E₂.Lawful K₂) (c : σ₁ × σ₂)
    {FGP : Type} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (L : Set S.Lk) (t : Time) (s : Int)
    (V : View sp.n) :
    ∀ w' ∈ S.unlockWith sp (E₁.comp E₂) c L Φ t s V, ∃ w'' ∈ S.unlockWith sp E₁ c.1 L Φ t s V,
      ∃ r, w' = S.withBlock w'' r ∧ ∃ Y ∈ Φ.tree, Y.root = r ∧ ∃ Z ∈ Φ.tree,
        Z.root = (S.lock w'').block ∧ Φ.Anc Y Z := by
  intro w' hw'
  obtain ⟨w, hw, B₀, hB₀, hr₀, hlive, rfl⟩ :=
    LockStore.mem_unlockWith_stored hS (UnlockStage.comp_lawful h₁ h₂) hΦ hw'
  obtain ⟨hvt, -⟩ := viableAncestor_anc hΦ hB₀
  have hlw : S.withBlock w (Φ.viableAncestor B₀).root ∈ S.liveLocks sp L Φ t :=
    ⟨w, hw, B₀, hB₀, hr₀, hlive, rfl⟩
  have hmem := (LockStore.mem_unlockWith (E := E₁) (c := c.1) (s := s) (V := V)).2
    ⟨_, hlw, _, hvt, (LockStore.lock_withBlock_fields hS w _).1.symm, rfl⟩
  rw [(LockStore.lock_withBlock_fields hS w _).2.1, hS.withBlock_withBlock,
    h₁.target_withBlock] at hmem
  obtain ⟨hTt, -⟩ := unlockTarget_anc sp hΦ V s hvt
  obtain ⟨h1t, -⟩ := h₁.target_anc c.1 V s w hΦ hTt
  by_cases hlt : ((S.lock w).slot : Int) < s
  · rw [ite_eq_left hlt] at hmem ⊢
    obtain ⟨h2t, h2a⟩ := h₂.target_anc c.2 V s w hΦ h1t
    refine ⟨_, hmem, _, by rw [hS.withBlock_withBlock, UnlockStage.comp_target], _, h2t, rfl, _,
      h1t, (LockStore.lock_withBlock_fields hS w _).1.symm, h2a⟩
  · rw [ite_eq_right hlt] at hmem ⊢
    exact ⟨_, hmem, _, (hS.withBlock_withBlock w _ _).symm, _, hvt, rfl, _, hvt,
      (LockStore.lock_withBlock_fields hS w _).1.symm, .refl⟩

/-! ### Maps of lock stores

A map of stored locks that commutes with the forgetful map and with moves carries `live_locks`,
`add_locks` and the unlock of one store to those of the other, when the two stages agree through
the map on blocks of the tree (`LockStore.Hom.image_unlockWith`). It forgets data the stages do
not read, such as a lock's first formation slot. -/

/-- A map of stored locks that keeps the forgotten lock and commutes with moves. -/
structure LockStore.Hom (S S' : LockStore) where
  /-- The map. -/
  toFun : S.Lk → S'.Lk
  /-- The forgotten lock is kept. -/
  lock_map : ∀ w, S'.lock (toFun w) = S.lock w
  /-- The map commutes with moves. -/
  map_withBlock : ∀ w r, toFun (S.withBlock w r) = S'.withBlock (toFun w) r

namespace LockStore.Hom

variable {S' : LockStore} {FGP : Type}

/-- The image of `live_locks` is `live_locks` of the image. -/
theorem image_liveLocks (f : LockStore.Hom S S') (L : Set S.Lk) (Φ : Frm sp.n FGP) (t : Time) :
    f.toFun '' S.liveLocks sp L Φ t = S'.liveLocks sp (f.toFun '' L) Φ t := by
  ext w'
  constructor
  · rintro ⟨_, ⟨w, hw, B, hB, hr, hlive, rfl⟩, rfl⟩
    exact ⟨f.toFun w, ⟨w, hw, rfl⟩, B, hB, by rw [f.lock_map]; exact hr,
      by rw [f.lock_map]; exact hlive, f.map_withBlock w _⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, B, hB, hr, hlive, rfl⟩
    rw [f.lock_map] at hr hlive
    exact ⟨_, ⟨w, hw, B, hB, hr, hlive, rfl⟩, f.map_withBlock w _⟩

/-- The image of `add_locks` is `add_locks` of the images. -/
theorem image_addLocksWith (f : LockStore.Hom S S') (L N : Set S.Lk) (Φ : Frm sp.n FGP)
    (t : Time) :
    f.toFun '' S.addLocksWith sp L N Φ t =
      S'.addLocksWith sp (f.toFun '' L) (f.toFun '' N) Φ t := by
  rw [LockStore.addLocksWith_eq, LockStore.addLocksWith_eq, image_liveLocks, Set.image_union]

/-- **The image of the unlock** is the unlock of the image, when the stages agree through the map
on the blocks of the tree. -/
theorem image_unlockWith (f : LockStore.Hom S S') {σ σ' : Type} {E : UnlockStage sp S σ}
    {E' : UnlockStage sp S' σ'} (c : σ) (c' : σ') {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hE : ∀ (V : View sp.n) (s : Int) (w : S.Lk) (T : Blk sp.n FGP),
      T ∈ Φ.tree → E'.target c' Φ V s (f.toFun w) T = E.target c Φ V s w T)
    (L : Set S.Lk) (t : Time) (s : Int) (V : View sp.n) :
    f.toFun '' S.unlockWith sp E c L Φ t s V = S'.unlockWith sp E' c' (f.toFun '' L) Φ t s V := by
  ext w'
  rw [Set.mem_image, LockStore.mem_unlockWith, ← image_liveLocks]
  constructor
  · rintro ⟨_, ⟨w, hw, B, hB, hBr, rfl⟩, rfl⟩
    refine ⟨f.toFun w, ⟨w, hw, rfl⟩, B, hB, by rw [f.lock_map]; exact hBr, ?_⟩
    rw [f.lock_map]
    split_ifs
    · rw [f.map_withBlock, hE V s w _ (unlockTarget_anc sp hΦ V s hB).1]
    · rfl
  · rintro ⟨_, ⟨w, hw, rfl⟩, B, hB, hBr, rfl⟩
    rw [f.lock_map] at hBr ⊢
    refine ⟨_, ⟨w, hw, B, hB, hBr, rfl⟩, ?_⟩
    split_ifs
    · rw [f.map_withBlock, hE V s w _ (unlockTarget_anc sp hΦ V s hB).1]
    · rfl

end LockStore.Hom

end Consensus.Goldilocks.SA

end
