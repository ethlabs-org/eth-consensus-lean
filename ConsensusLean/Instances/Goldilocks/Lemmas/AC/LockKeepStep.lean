module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Restart
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance

public section

/-! # Goldilocks SA: a lock that every lock function keeps in place

The "keep" half of the AC lock step (consensus-lean#135, WI-15/16). Take a lock `l` held before
a call at time `t` with frame `Φ`, on a block `B` of the tree, with these conditions:

* `l` does not expire at `t`: `slot(t) ≤ l.slot + k` (`live_locks`);
* `B` is its own viable ancestor in `Φ` (`live_locks` moves it to `B`);
* `unlock` does not move it: `slot(t) − 1 ≤ l.slot`, or `unlockTarget(Φ, V, slot(t) − 1, B) = B`
  for every view `V` (`unlock` moves only locks of a slot below `slot(t) − 1`, to their
  `unlockTarget`).

Then `l` itself is held after the call (`mem_step_locks_of_keep`). Each lock function keeps it:
`live_locks`, `add_locks`, `unlock`, the optimistic confirmation, the confirmation update,
`try_vote`, and so every AC call (the restart keeps all locks, A0.7). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {Φ : Frm sp.n FGP} {t : Time} {l : Lock}
  {B : Blk sp.n FGP}

/-- `live_locks` keeps a lock that does not expire and whose block is its own viable ancestor. -/
theorem mem_liveLocks_of_keep {L : Set Lock} (hl : l ∈ L) (hk : sp.slot t ≤ l.slot + sp.k)
    (hB : B ∈ Φ.tree) (hBr : B.root = l.block) (hva : Φ.viableAncestor B = B) :
    l ∈ liveLocks sp L Φ t :=
  ⟨l, hl, B, hB, hBr, hk, by rw [hva, hBr]⟩

/-- `add_locks` keeps such a lock. -/
theorem mem_addLocks_of_keep {L : Set Lock} {s : Nat} {N : Set (Nat × Bool)} (hl : l ∈ L)
    (hk : sp.slot t ≤ l.slot + sp.k) (hB : B ∈ Φ.tree) (hBr : B.root = l.block)
    (hva : Φ.viableAncestor B = B) : l ∈ addLocks sp L Φ t s N :=
  mem_liveLocks_of_keep (Set.mem_union_left _ hl) hk hB hBr hva

/-- `unlock` against the slot-`s` votes of `V` keeps such a lock when its slot is `s` or later
or its `unlockTarget` is its block. -/
theorem mem_unlock_of_keep {L : Set Lock} {s : Int} {V : View sp.n} (hl : l ∈ L)
    (hk : sp.slot t ≤ l.slot + sp.k) (hB : B ∈ Φ.tree) (hBr : B.root = l.block)
    (hva : Φ.viableAncestor B = B) (hu : s ≤ l.slot ∨ unlockTarget sp Φ V s B = B) :
    l ∈ unlock sp L Φ t s V := by
  refine ⟨l, mem_liveLocks_of_keep hl hk hB hBr hva, B, hB, hBr, ?_⟩
  split_ifs with h
  · rcases hu with hu | hu
    · exact absurd h (not_lt.2 hu)
    · rw [hu, hBr]
  · rfl

/-- The optimistic confirmation keeps such a lock. -/
theorem mem_optimisticConfirmation_of_keep {A : SAState sp.n} (hl : l ∈ A.locks)
    (hk : sp.slot t ≤ l.slot + sp.k) (hB : B ∈ Φ.tree) (hBr : B.root = l.block)
    (hva : Φ.viableAncestor B = B) : l ∈ (optimisticConfirmation sp A Φ t).locks := by
  unfold optimisticConfirmation
  split
  · exact hl
  · rw [updateLatestConfirmed_locks_eq]
    exact mem_addLocks_of_keep hl hk hB hBr hva

/-- The confirmation update keeps such a lock. -/
theorem mem_updateConfirmation_of_keep {A : SAState sp.n} {s : Nat} (hl : l ∈ A.locks)
    (hk : sp.slot t ≤ l.slot + sp.k) (hB : B ∈ Φ.tree) (hBr : B.root = l.block)
    (hva : Φ.viableAncestor B = B) : l ∈ (updateConfirmation sp A Φ t s).locks := by
  unfold updateConfirmation
  dsimp only
  split
  · exact hl
  · split_ifs
    · exact hl
    · rw [updateLatestConfirmed_locks_eq]
      exact mem_addLocks_of_keep hl hk hB hBr hva

/-- `try_vote` keeps such a lock that `unlock` does not move. -/
theorem mem_tryVote_of_keep (self : Fin sp.n) {A : SAState sp.n} (hl : l ∈ A.locks)
    (hk : sp.slot t ≤ l.slot + sp.k) (hB : B ∈ Φ.tree) (hBr : B.root = l.block)
    (hva : Φ.viableAncestor B = B)
    (hu : (sp.slot t : Int) - 1 ≤ l.slot ∨
      ∀ V, unlockTarget sp Φ V ((sp.slot t : Int) - 1) B = B) :
    l ∈ (tryVote sp self A Φ t).1.locks := by
  unfold tryVote
  dsimp only
  split_ifs with h₁ h₂ h₃
  · exact hl
  · exact hl
  · refine mem_optimisticConfirmation_of_keep ?_ hk hB hBr hva
    rw [admitVote_locks_eq]
    exact mem_unlock_of_keep hl hk hB hBr hva (hu.imp_right fun h => h _)
  · refine mem_optimisticConfirmation_of_keep ?_ hk hB hBr hva
    rw [admitVote_locks_eq]
    exact hl

/-- `ac_on_message` keeps such a lock. -/
theorem mem_acOnMessage_of_keep (self : Fin sp.n) {A : SAState sp.n} (v : Vote sp.n)
    (hl : l ∈ A.locks) (hk : sp.slot t ≤ l.slot + sp.k) (hB : B ∈ Φ.tree)
    (hBr : B.root = l.block) (hva : Φ.viableAncestor B = B)
    (hu : (sp.slot t : Int) - 1 ≤ l.slot ∨
      ∀ V, unlockTarget sp Φ V ((sp.slot t : Int) - 1) B = B) :
    l ∈ (acOnMessage sp self A Φ t v).1.locks := by
  refine mem_tryVote_of_keep self ?_ hk hB hBr hva hu
  refine mem_optimisticConfirmation_of_keep ?_ hk hB hBr hva
  rw [admitVote_locks_eq]
  exact hl

/-- `ac_on_block` keeps such a lock. -/
theorem mem_acOnBlock_of_keep (self : Fin sp.n) {A : SAState sp.n} (C : Blk sp.n FGP)
    (hl : l ∈ A.locks) (hk : sp.slot t ≤ l.slot + sp.k) (hB : B ∈ Φ.tree)
    (hBr : B.root = l.block) (hva : Φ.viableAncestor B = B)
    (hu : (sp.slot t : Int) - 1 ≤ l.slot ∨
      ∀ V, unlockTarget sp Φ V ((sp.slot t : Int) - 1) B = B) :
    l ∈ (acOnBlock sp self A Φ t C).1.locks := by
  refine mem_tryVote_of_keep self ?_ hk hB hBr hva hu
  refine mem_optimisticConfirmation_of_keep ?_ hk hB hBr hva
  rw [blockReceipt_locks]
  exact hl

/-- `ac_on_tick` keeps such a lock. -/
theorem mem_acOnTick_of_keep (self : Fin sp.n) {A : SAState sp.n} (hl : l ∈ A.locks)
    (hk : sp.slot t ≤ l.slot + sp.k) (hB : B ∈ Φ.tree) (hBr : B.root = l.block)
    (hva : Φ.viableAncestor B = B)
    (hu : (sp.slot t : Int) - 1 ≤ l.slot ∨
      ∀ V, unlockTarget sp Φ V ((sp.slot t : Int) - 1) B = B) :
    l ∈ (acOnTick sp self A Φ t).1.locks := by
  have hv := mem_tryVote_of_keep self hl hk hB hBr hva hu
  unfold acOnTick
  dsimp only
  split_ifs <;>
    first
    | exact hl
    | exact hv
    | exact mem_updateConfirmation_of_keep hl hk hB hBr hva
    | exact mem_updateConfirmation_of_keep hv hk hB hBr hva

/-- `ac_proposal` keeps such a lock. -/
theorem mem_acProposal_of_keep {A : SAState sp.n} (hl : l ∈ A.locks)
    (hk : sp.slot t ≤ l.slot + sp.k) (hB : B ∈ Φ.tree) (hBr : B.root = l.block)
    (hva : Φ.viableAncestor B = B)
    (hu : (sp.slot t : Int) - 1 ≤ l.slot ∨
      ∀ V, unlockTarget sp Φ V ((sp.slot t : Int) - 1) B = B) :
    l ∈ (acProposal sp A Φ t).1.locks := by
  unfold acProposal
  dsimp only
  split_ifs <;>
    first
    | exact hl
    | exact mem_unlock_of_keep hl hk hB hBr hva (hu.imp_right fun h => h _)

/-- `ac_to_fg` keeps the locks. -/
theorem acToFG_locks_eq (A : SAState sp.n) : (acToFG sp A Φ t).1.locks = A.locks := by
  unfold acToFG
  split_ifs
  · split
    · rfl
    · split_ifs <;> rfl
  · rfl

/-- **The keep lemma of an AC call.** A call of the SA at time `t ≥ 0` with a well-formed frame
`Φ` keeps a lock `l` on a block `B` of the tree when `l` does not expire at `t`, `B` is its own
viable ancestor, and `unlock` does not move it. -/
theorem mem_step_locks_of_keep {ro : ReplayOrder sp FGP} (self : Fin sp.n) {A : SAState sp.n}
    (c : (goldilocksSA sp FGP ro).Call) (hΦ : FrameOK Φ) (ht : 0 ≤ t) (hl : l ∈ A.locks)
    (hk : sp.slot t ≤ l.slot + sp.k) (hB : B ∈ Φ.tree) (hBr : B.root = l.block)
    (hva : Φ.viableAncestor B = B)
    (hu : (sp.slot t : Int) - 1 ≤ l.slot ∨
      ∀ V, unlockTarget sp Φ V ((sp.slot t : Int) - 1) B = B) :
    l ∈ ((goldilocksSA sp FGP ro).step self A Φ t c).1.locks := by
  cases c with
  | tick => exact mem_acOnTick_of_keep self hl hk hB hBr hva hu
  | proposal => exact mem_acProposal_of_keep hl hk hB hBr hva hu
  | toFG =>
    change l ∈ (acToFG sp A Φ t).1.locks
    rw [acToFG_locks_eq]
    exact hl
  | message v => exact mem_acOnMessage_of_keep self v hl hk hB hBr hva hu
  | block C => exact mem_acOnBlock_of_keep self C hl hk hB hBr hva hu
  | restart =>
    change l ∈ (acRestart sp ro self A Φ t).1.locks
    rw [((restart_state sp) FGP ro self A Φ t hΦ ht).2.1]
    exact hl

/-! ## The keep lemma with the view that `unlock` reads

`opponents` contains the equivocators of the view, so the premise `∀ V, unlockTarget … B = B`
above holds in general only for `B = Φ.F` (`unlockTarget_F`). The lemmas below name the view
that the call passes to `unlock` (`unlockView`): the merged vote view of the state that
`try_vote` receives, and the slot-`(slot(t) − 1)` pool view in `ac_proposal`. A bound on its
opponents (`unlockTarget_eq_self_of_subset`) then discharges the premise. -/

/-- `try_vote` keeps such a lock when `unlock` does not move it against the merged vote view
that `try_vote` reads. -/
theorem mem_tryVote_of_keep_view (self : Fin sp.n) {A : SAState sp.n} (hl : l ∈ A.locks)
    (hk : sp.slot t ≤ l.slot + sp.k) (hB : B ∈ Φ.tree) (hBr : B.root = l.block)
    (hva : Φ.viableAncestor B = B)
    (hu : (sp.slot t : Int) - 1 ≤ l.slot ∨
      unlockTarget sp Φ (mergedVoteView sp A Φ (sp.slot t)) ((sp.slot t : Int) - 1) B = B) :
    l ∈ (tryVote sp self A Φ t).1.locks := by
  unfold tryVote
  dsimp only
  split_ifs with h₁ h₂ h₃
  · exact hl
  · exact hl
  · refine mem_optimisticConfirmation_of_keep ?_ hk hB hBr hva
    rw [admitVote_locks_eq]
    exact mem_unlock_of_keep hl hk hB hBr hva hu
  · refine mem_optimisticConfirmation_of_keep ?_ hk hB hBr hva
    rw [admitVote_locks_eq]
    exact hl

/-- `ac_on_message` keeps such a lock (the view of the state after the admission). -/
theorem mem_acOnMessage_of_keep_view (self : Fin sp.n) {A : SAState sp.n} (v : Vote sp.n)
    (hl : l ∈ A.locks) (hk : sp.slot t ≤ l.slot + sp.k) (hB : B ∈ Φ.tree)
    (hBr : B.root = l.block) (hva : Φ.viableAncestor B = B)
    (hu : (sp.slot t : Int) - 1 ≤ l.slot ∨ unlockTarget sp Φ
      (mergedVoteView sp (optimisticConfirmation sp (admitVote sp A t v) Φ t) Φ (sp.slot t))
      ((sp.slot t : Int) - 1) B = B) :
    l ∈ (acOnMessage sp self A Φ t v).1.locks := by
  refine mem_tryVote_of_keep_view self ?_ hk hB hBr hva hu
  refine mem_optimisticConfirmation_of_keep ?_ hk hB hBr hva
  rw [admitVote_locks_eq]
  exact hl

/-- `ac_on_block` keeps such a lock (the view of the state after the block receipt). -/
theorem mem_acOnBlock_of_keep_view (self : Fin sp.n) {A : SAState sp.n} (C : Blk sp.n FGP)
    (hl : l ∈ A.locks) (hk : sp.slot t ≤ l.slot + sp.k) (hB : B ∈ Φ.tree)
    (hBr : B.root = l.block) (hva : Φ.viableAncestor B = B)
    (hu : (sp.slot t : Int) - 1 ≤ l.slot ∨ unlockTarget sp Φ
      (mergedVoteView sp (optimisticConfirmation sp (blockReceipt sp A t C) Φ t) Φ (sp.slot t))
      ((sp.slot t : Int) - 1) B = B) :
    l ∈ (acOnBlock sp self A Φ t C).1.locks := by
  refine mem_tryVote_of_keep_view self ?_ hk hB hBr hva hu
  refine mem_optimisticConfirmation_of_keep ?_ hk hB hBr hva
  rw [blockReceipt_locks]
  exact hl

/-- `ac_on_tick` keeps such a lock (the view of the state before the call). -/
theorem mem_acOnTick_of_keep_view (self : Fin sp.n) {A : SAState sp.n} (hl : l ∈ A.locks)
    (hk : sp.slot t ≤ l.slot + sp.k) (hB : B ∈ Φ.tree) (hBr : B.root = l.block)
    (hva : Φ.viableAncestor B = B)
    (hu : (sp.slot t : Int) - 1 ≤ l.slot ∨
      unlockTarget sp Φ (mergedVoteView sp A Φ (sp.slot t)) ((sp.slot t : Int) - 1) B = B) :
    l ∈ (acOnTick sp self A Φ t).1.locks := by
  have hv := mem_tryVote_of_keep_view self hl hk hB hBr hva hu
  unfold acOnTick
  dsimp only
  split_ifs <;>
    first
    | exact hl
    | exact hv
    | exact mem_updateConfirmation_of_keep hl hk hB hBr hva
    | exact mem_updateConfirmation_of_keep hv hk hB hBr hva

/-- `ac_proposal` keeps such a lock (the slot-`(slot(t) − 1)` pool view). -/
theorem mem_acProposal_of_keep_view {A : SAState sp.n} (hl : l ∈ A.locks)
    (hk : sp.slot t ≤ l.slot + sp.k) (hB : B ∈ Φ.tree) (hBr : B.root = l.block)
    (hva : Φ.viableAncestor B = B)
    (hu : (sp.slot t : Int) - 1 ≤ l.slot ∨ unlockTarget sp Φ
      (View.ofLists (voteViewList A Φ ((sp.slot t : Int) - 1) ⊤))
      ((sp.slot t : Int) - 1) B = B) :
    l ∈ (acProposal sp A Φ t).1.locks := by
  unfold acProposal
  dsimp only
  split_ifs <;>
    first
    | exact hl
    | exact mem_unlock_of_keep hl hk hB hBr hva hu

/-- The view that an AC call `c` passes to `unlock` at time `t` from state `A` with frame `Φ`
(the merged vote view of the state `try_vote` receives; the pool view in `ac_proposal`; for
`ac_to_fg` and `ac_restart`, which do not unlock, the merged vote view of `A`). -/
noncomputable def unlockView {ro : ReplayOrder sp FGP} (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : (goldilocksSA sp FGP ro).Call → View sp.n
  | .proposal => View.ofLists (voteViewList A Φ ((sp.slot t : Int) - 1) ⊤)
  | .message v =>
    mergedVoteView sp (optimisticConfirmation sp (admitVote sp A t v) Φ t) Φ (sp.slot t)
  | .block C =>
    mergedVoteView sp (optimisticConfirmation sp (blockReceipt sp A t C) Φ t) Φ (sp.slot t)
  | _ => mergedVoteView sp A Φ (sp.slot t)

section unlockView
variable {ro : ReplayOrder sp FGP} (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)

theorem unlockView_tick :
    unlockView (ro := ro) A Φ t .tick = mergedVoteView sp A Φ (sp.slot t) := by
  unfold unlockView; rfl

theorem unlockView_proposal : unlockView (ro := ro) A Φ t .proposal =
    View.ofLists (voteViewList A Φ ((sp.slot t : Int) - 1) ⊤) := by
  unfold unlockView; rfl

theorem unlockView_message (v : Vote sp.n) : unlockView (ro := ro) A Φ t (.message v) =
    mergedVoteView sp (optimisticConfirmation sp (admitVote sp A t v) Φ t) Φ (sp.slot t) := by
  unfold unlockView; rfl

theorem unlockView_block (C : Blk sp.n FGP) : unlockView (ro := ro) A Φ t (.block C) =
    mergedVoteView sp (optimisticConfirmation sp (blockReceipt sp A t C) Φ t) Φ (sp.slot t) := by
  unfold unlockView; rfl

theorem unlockView_toFG :
    unlockView (ro := ro) A Φ t .toFG = mergedVoteView sp A Φ (sp.slot t) := by
  unfold unlockView; rfl

theorem unlockView_restart :
    unlockView (ro := ro) A Φ t .restart = mergedVoteView sp A Φ (sp.slot t) := by
  unfold unlockView; rfl

end unlockView

/-- **The keep lemma of an AC call, with the view of the call.** `mem_step_locks_of_keep` with
the unlock premise at the view `unlockView A Φ t c` that the call reads. -/
theorem mem_step_locks_of_keep_view {ro : ReplayOrder sp FGP} (self : Fin sp.n)
    {A : SAState sp.n} (c : (goldilocksSA sp FGP ro).Call) (hΦ : FrameOK Φ) (ht : 0 ≤ t)
    (hl : l ∈ A.locks) (hk : sp.slot t ≤ l.slot + sp.k) (hB : B ∈ Φ.tree)
    (hBr : B.root = l.block) (hva : Φ.viableAncestor B = B)
    (hu : (sp.slot t : Int) - 1 ≤ l.slot ∨
      unlockTarget sp Φ (unlockView A Φ t c) ((sp.slot t : Int) - 1) B = B) :
    l ∈ ((goldilocksSA sp FGP ro).step self A Φ t c).1.locks := by
  cases c with
  | tick => exact mem_acOnTick_of_keep_view self hl hk hB hBr hva hu
  | proposal => exact mem_acProposal_of_keep_view hl hk hB hBr hva hu
  | toFG =>
    change l ∈ (acToFG sp A Φ t).1.locks
    rw [acToFG_locks_eq]
    exact hl
  | message v => exact mem_acOnMessage_of_keep_view self v hl hk hB hBr hva hu
  | block C => exact mem_acOnBlock_of_keep_view self C hl hk hB hBr hva hu
  | restart =>
    change l ∈ (acRestart sp ro self A Φ t).1.locks
    rw [((restart_state sp) FGP ro self A Φ t hΦ ht).2.1]
    exact hl

end Consensus.Goldilocks.SA

end
