module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockKeepStep
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Locks

public section

/-! # Goldilocks SA: a lock floor that every lock function keeps

The floor form of the AC lock step. Fix a block `B₀` of the tree
that is its own viable ancestor, and a slot `j`. The floor of a lock set `L` is a lock `l ∈ L`
of slot `j` with expiry `≥ m` on a block `B ⪰ B₀` of the tree. Locks may move:
`live_locks` moves `l` to the viable ancestor of `B`, which is still `⪰ B₀`
(`anc_viableAncestor_of_floor`); `unlock` moves `l` to the `unlockTarget` of its block, which is
still `⪰ B₀` when `unlockTarget` keeps `B₀` (`anc_unlockTarget_of_floor`). Both keep the slot
and the expiry. So when `slot(t) ≤ m` (the floor lock is live) and `unlock` at the call's
view keeps `B₀` (or `slot(t) − 1 ≤ j`), every AC call keeps the floor
(`exists_step_locks_floor`), and the read point of a cast holds a live lock block `⪰ B₀`
(`exists_readPoint_liveLockBlocks_floor`). -/

namespace Consensus.Goldilocks.SA

/-- **`viable_ancestor` is monotone above a candidate.** In a well-formed frame, if `B₀` is its
own viable ancestor and `B₀ ⪯ B ∈ Φ.tree`, then `B₀ ⪯ viable_ancestor(Φ, B)`. -/
theorem anc_viableAncestor_of_floor {n : Nat} {FGP : Type} {Φ : Frm n FGP} (hΦ : FrameOK Φ)
    {B₀ B : Blk n FGP} (hB0 : B₀ ∈ Φ.tree) (hva0 : Φ.viableAncestor B₀ = B₀)
    (hB : B ∈ Φ.tree) (h : Φ.Anc B₀ B) : Φ.Anc B₀ (Φ.viableAncestor B) := by
  have hc := (viableAncestor_spec hΦ hB0).2.1
  rw [hva0] at hc
  exact (viableAncestor_spec hΦ hB).2.2 B₀ h hc

/-- `anc_viableAncestor_of_floor` for a candidate `B₀`: viable or at or below `fc_root`. -/
theorem anc_viableAncestor_of_candidate {n : Nat} {FGP : Type} {Φ : Frm n FGP}
    (hΦ : FrameOK Φ) {B₀ B : Blk n FGP}
    (hc : B₀ ∈ Φ.viableTree Φ.tree ∨ Φ.Anc B₀ Φ.fcRoot) (hB : B ∈ Φ.tree)
    (h : Φ.Anc B₀ B) : Φ.Anc B₀ (Φ.viableAncestor B) :=
  (viableAncestor_spec hΦ hB).2.2 B₀ h hc.symm

variable {FGP : Type} {sp : SAParams} {Φ : Frm sp.n FGP} {t : Time} {j m : Nat}
  {B₀ : Blk sp.n FGP}

/-- **`unlock_target` is monotone above a kept block.** In a well-formed frame, if
`unlockTarget(Φ, V, s, B₀) = B₀` and `B₀ ⪯ B ∈ Φ.tree`, then `B₀ ⪯ unlockTarget(Φ, V, s, B)`
(`B₀` is `Φ.F` or has fewer than half of the committee as opponents). -/
theorem anc_unlockTarget_of_floor (hΦ : FrameOK Φ) (V : View sp.n) (s : Int)
    {B : Blk sp.n FGP} (hB0 : B₀ ∈ Φ.tree) (hB : B ∈ Φ.tree) (h : Φ.Anc B₀ B)
    (hu : unlockTarget sp Φ V s B₀ = B₀) : Φ.Anc B₀ (unlockTarget sp Φ V s B) := by
  classical
  have key : B₀ = Φ.F ∨ 2 * (opponents sp Φ V s B₀).ncard < sp.n := by
    unfold unlockTarget at hu
    cases hd : deepest Φ
        {B' | B' ∈ Φ.tree ∧ Φ.Anc B' B₀ ∧ 2 * (opponents sp Φ V s B').ncard < sp.n} with
    | none =>
      rw [hd] at hu
      exact Or.inl hu.symm
    | some D =>
      rw [hd] at hu
      change D = B₀ at hu
      rw [← hu]
      exact Or.inr (deepest_mem hd).1.2.2
  rcases key with rfl | hopp
  · exact hΦ.rooted.2 _ (unlockTarget_anc sp hΦ V s hB).1
  · obtain ⟨D, hD⟩ := exists_deepest hΦ
      (S := {X | X ∈ Φ.tree ∧ Φ.Anc X B ∧ 2 * (opponents sp Φ V s X).ncard < sp.n})
      (fun X h => h.1) ⟨B₀, hB0, h, hopp⟩
    unfold unlockTarget
    rw [hD]
    exact anc_deepest hΦ (fun X h => h.1)
      (fun X hX Y hY => anc_total hΦ.coherent hX.2.1 hY.2.1) hD B₀ ⟨hB0, h, hopp⟩

/-- The floor grows with the lock set. -/
theorem floor_mono {L L' : Set Lock} (hL : L ⊆ L')
    (h : ∃ l ∈ L, l.slot = j ∧ m ≤ l.expiry ∧ ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ L', l.slot = j ∧ m ≤ l.expiry ∧ ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  obtain ⟨l, hl, hj⟩ := h
  exact ⟨l, hL hl, hj⟩

/-- `live_locks` keeps the floor (the lock moves to its viable ancestor, still `⪰ B₀`). -/
theorem floor_liveLocks {L : Set Lock} (hΦ : FrameOK Φ) (hB0 : B₀ ∈ Φ.tree)
    (hva0 : Φ.viableAncestor B₀ = B₀) (hk : sp.slot t ≤ m)
    (h : ∃ l ∈ L, l.slot = j ∧ m ≤ l.expiry ∧ ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ liveLocks sp L Φ t, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  obtain ⟨l, hl, hj, he, B, hB, hBr, hB0B⟩ := h
  subst hj
  exact ⟨_, ⟨l, hl, B, hB, hBr, hk.trans he, rfl⟩, rfl, he, _, (viableAncestor_anc hΦ hB).1, rfl,
    anc_viableAncestor_of_floor hΦ hB0 hva0 hB hB0B⟩

/-- `add_locks` keeps the floor. -/
theorem floor_addLocks {L : Set Lock} {s : Nat} {N : Set (Nat × Bool × Nat)} (hΦ : FrameOK Φ)
    (hB0 : B₀ ∈ Φ.tree) (hva0 : Φ.viableAncestor B₀ = B₀) (hk : sp.slot t ≤ m)
    (h : ∃ l ∈ L, l.slot = j ∧ m ≤ l.expiry ∧ ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ addLocks sp L Φ t s N, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B :=
  floor_liveLocks hΦ hB0 hva0 hk (floor_mono Set.subset_union_left h)

/-- `unlock` against the slot-`s` votes of `V` keeps the floor when `s ≤ j` or the unlock
target of `B₀` is `B₀`. -/
theorem floor_unlock {L : Set Lock} {s : Int} {V : View sp.n} (hΦ : FrameOK Φ)
    (hB0 : B₀ ∈ Φ.tree) (hva0 : Φ.viableAncestor B₀ = B₀) (hk : sp.slot t ≤ m)
    (hu : s ≤ j ∨ unlockTarget sp Φ V s B₀ = B₀)
    (h : ∃ l ∈ L, l.slot = j ∧ m ≤ l.expiry ∧ ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ unlock sp L Φ t s V, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  obtain ⟨l, hl, hj, he, B, hB, hBr, hB0B⟩ := floor_liveLocks hΦ hB0 hva0 hk h
  subst hj
  by_cases hs : (l.slot : Int) < s
  · have hu' := hu.resolve_left (by omega)
    exact ⟨⟨(unlockTarget sp Φ V s B).root, l.slot, l.fast, l.expiry⟩,
      ⟨l, hl, B, hB, hBr, by simp only [hs, ↓reduceIte]⟩, rfl, he, _,
      (unlockTarget_anc sp hΦ V s hB).1, rfl, anc_unlockTarget_of_floor hΦ V s hB0 hB hB0B hu'⟩
  · exact ⟨l, ⟨l, hl, B, hB, hBr, by simp only [hs, ↓reduceIte]⟩, rfl, he, B, hB, hBr, hB0B⟩

/-- The optimistic confirmation keeps the floor. -/
theorem floor_optimisticConfirmation {A : SAState sp.n} (hΦ : FrameOK Φ) (hB0 : B₀ ∈ Φ.tree)
    (hva0 : Φ.viableAncestor B₀ = B₀) (hk : sp.slot t ≤ m)
    (h : ∃ l ∈ A.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ (optimisticConfirmation sp A Φ t).locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  unfold optimisticConfirmation
  split
  · exact h
  · rw [updateLatestConfirmed_keeps_locks]
    exact floor_addLocks hΦ hB0 hva0 hk h

/-- The confirmation update keeps the floor. -/
theorem floor_updateConfirmation {A : SAState sp.n} {s : Nat} (hΦ : FrameOK Φ)
    (hB0 : B₀ ∈ Φ.tree) (hva0 : Φ.viableAncestor B₀ = B₀) (hk : sp.slot t ≤ m)
    (h : ∃ l ∈ A.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ (updateConfirmation sp A Φ t s).locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  unfold updateConfirmation
  dsimp only
  split
  · exact h
  · split_ifs <;>
      first
      | exact floor_addLocks hΦ hB0 hva0 hk h
      | (rw [updateLatestConfirmed_keeps_locks]; exact floor_addLocks hΦ hB0 hva0 hk h)

/-- `try_vote` keeps the floor when `unlock` at the merged vote view of its input keeps `B₀`. -/
theorem floor_tryVote (self : Fin sp.n) {A : SAState sp.n} (hΦ : FrameOK Φ)
    (hB0 : B₀ ∈ Φ.tree) (hva0 : Φ.viableAncestor B₀ = B₀) (hk : sp.slot t ≤ m)
    (hu : (sp.slot t : Int) - 1 ≤ j ∨
      unlockTarget sp Φ (mergedVoteView sp A Φ (sp.slot t)) ((sp.slot t : Int) - 1) B₀ = B₀)
    (h : ∃ l ∈ A.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ (tryVote sp self A Φ t).1.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  unfold tryVote
  dsimp only
  split_ifs with h₁ h₂ h₃
  · exact h
  · exact h
  · refine floor_optimisticConfirmation hΦ hB0 hva0 hk ?_
    rw [admitVote_locks_eq]
    exact floor_unlock hΦ hB0 hva0 hk hu h
  · refine floor_optimisticConfirmation hΦ hB0 hva0 hk ?_
    rw [admitVote_locks_eq]
    exact h

/-- `ac_on_message` keeps the floor (the view of the state after the admission). -/
theorem floor_acOnMessage (self : Fin sp.n) {A : SAState sp.n} (v : Vote sp.n)
    (hΦ : FrameOK Φ) (hB0 : B₀ ∈ Φ.tree) (hva0 : Φ.viableAncestor B₀ = B₀)
    (hk : sp.slot t ≤ m)
    (hu : (sp.slot t : Int) - 1 ≤ j ∨ unlockTarget sp Φ
      (mergedVoteView sp (optimisticConfirmation sp (admitVote sp A t v) Φ t) Φ (sp.slot t))
      ((sp.slot t : Int) - 1) B₀ = B₀)
    (h : ∃ l ∈ A.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ (acOnMessage sp self A Φ t v).1.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  refine floor_tryVote self hΦ hB0 hva0 hk hu ?_
  refine floor_optimisticConfirmation hΦ hB0 hva0 hk ?_
  rw [admitVote_locks_eq]
  exact h

/-- `ac_on_block` keeps the floor (the view of the state after the block receipt). -/
theorem floor_acOnBlock (self : Fin sp.n) {A : SAState sp.n} (C : Blk sp.n FGP)
    (hΦ : FrameOK Φ) (hB0 : B₀ ∈ Φ.tree) (hva0 : Φ.viableAncestor B₀ = B₀)
    (hk : sp.slot t ≤ m)
    (hu : (sp.slot t : Int) - 1 ≤ j ∨ unlockTarget sp Φ
      (mergedVoteView sp (optimisticConfirmation sp (blockReceipt sp A t C) Φ t) Φ (sp.slot t))
      ((sp.slot t : Int) - 1) B₀ = B₀)
    (h : ∃ l ∈ A.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ (acOnBlock sp self A Φ t C).1.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  refine floor_tryVote self hΦ hB0 hva0 hk hu ?_
  refine floor_optimisticConfirmation hΦ hB0 hva0 hk ?_
  rw [blockReceipt_locks]
  exact h

/-- `ac_on_tick` keeps the floor (the view of the state before the call). -/
theorem floor_acOnTick (self : Fin sp.n) {A : SAState sp.n} (hΦ : FrameOK Φ)
    (hB0 : B₀ ∈ Φ.tree) (hva0 : Φ.viableAncestor B₀ = B₀) (hk : sp.slot t ≤ m)
    (hu : (sp.slot t : Int) - 1 ≤ j ∨
      unlockTarget sp Φ (mergedVoteView sp A Φ (sp.slot t)) ((sp.slot t : Int) - 1) B₀ = B₀)
    (h : ∃ l ∈ A.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ (acOnTick sp self A Φ t).1.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  have hv := floor_tryVote self hΦ hB0 hva0 hk hu h
  unfold acOnTick
  dsimp only
  split_ifs <;>
    first
    | exact h
    | exact hv
    | exact floor_updateConfirmation hΦ hB0 hva0 hk h
    | exact floor_updateConfirmation hΦ hB0 hva0 hk hv

/-- `ac_proposal` keeps the floor (the slot-`(slot(t) − 1)` pool view). -/
theorem floor_acProposal {A : SAState sp.n} (hΦ : FrameOK Φ) (hB0 : B₀ ∈ Φ.tree)
    (hva0 : Φ.viableAncestor B₀ = B₀) (hk : sp.slot t ≤ m)
    (hu : (sp.slot t : Int) - 1 ≤ j ∨ unlockTarget sp Φ
      (View.ofLists (voteViewList A Φ ((sp.slot t : Int) - 1) ⊤))
      ((sp.slot t : Int) - 1) B₀ = B₀)
    (h : ∃ l ∈ A.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ (acProposal sp A Φ t).1.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  unfold acProposal
  dsimp only
  split_ifs <;>
    first
    | exact h
    | exact floor_unlock hΦ hB0 hva0 hk hu h

/-- **The floor lemma of an AC call.** A call of the SA at time `t ≥ 0` with a well-formed frame
`Φ` keeps the floor: if `A.locks` holds a lock of slot `j` and expiry `≥ m` on a block `⪰ B₀`
of the tree, with
`B₀ ∈ Φ.tree` its own viable ancestor, `slot(t) ≤ m`, and `unlock` at the call's view
keeping `B₀` (or `slot(t) − 1 ≤ j`), then the new locks hold a lock of slot `j` on a block
`⪰ B₀` of the tree (the moved lock), which keeps its expiry `≥ m`. -/
theorem exists_step_locks_floor {ro : ReplayOrder sp FGP} (self : Fin sp.n)
    {A : SAState sp.n} (c : (goldilocksSA sp FGP ro).Call) (hΦ : FrameOK Φ) (ht : 0 ≤ t)
    (hB0 : B₀ ∈ Φ.tree) (hva0 : Φ.viableAncestor B₀ = B₀) (hk : sp.slot t ≤ m)
    (hu : (sp.slot t : Int) - 1 ≤ j ∨
      unlockTarget sp Φ (unlockView A Φ t c) ((sp.slot t : Int) - 1) B₀ = B₀)
    (h : ∃ l ∈ A.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ ((goldilocksSA sp FGP ro).step self A Φ t c).1.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  cases c with
  | tick =>
    rw [unlockView_tick] at hu
    exact floor_acOnTick self hΦ hB0 hva0 hk hu h
  | proposal =>
    rw [unlockView_proposal] at hu
    exact floor_acProposal hΦ hB0 hva0 hk hu h
  | toFG =>
    have he : ((goldilocksSA sp FGP ro).step self A Φ t .toFG).1.locks = A.locks :=
      acToFG_locks_eq A
    rw [he]
    exact h
  | message v =>
    rw [unlockView_message] at hu
    exact floor_acOnMessage self v hΦ hB0 hva0 hk hu h
  | block C =>
    rw [unlockView_block] at hu
    exact floor_acOnBlock self C hΦ hB0 hva0 hk hu h
  | restart =>
    have he : ((goldilocksSA sp FGP ro).step self A Φ t .restart).1.locks = A.locks :=
      ((restart_state sp) FGP ro self A Φ t hΦ ht).2.1
    rw [he]
    exact h

/-! ## The read point of a cast -/

section readPoint
variable {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}
  {tr : SATrace sp FGP ro}

/-- `try_vote` keeps the floor in its read point. -/
private theorem floor_tryVote_readPoint {x : Fin sp.n} {P : SAState sp.n} {e : Em sp FGP}
    (he : e ∈ (tryVote sp x P Φ t).2) (hΦ : FrameOK Φ) (hB0 : B₀ ∈ Φ.tree)
    (hva0 : Φ.viableAncestor B₀ = B₀) (hk : sp.slot t ≤ m)
    (hu : (sp.slot t : Int) - 1 ≤ j ∨
      unlockTarget sp Φ (mergedVoteView sp P Φ (sp.slot t)) ((sp.slot t : Int) - 1) B₀ = B₀)
    (h : ∃ l ∈ P.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ e.readPoint.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  rw [tryVote_readPoint_locks_eq he]
  split_ifs
  · exact floor_unlock hΦ hB0 hva0 hk hu h
  · exact h

/-- **The floor is in the read point of a cast.** -/
theorem floor_readPoint_locks (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) (hB0 : B₀ ∈ ℓ.frame.tree)
    (hva0 : ℓ.frame.viableAncestor B₀ = B₀) (hk : sp.slot (tr.time i) ≤ m)
    (hu : (sp.slot (tr.time i) : Int) - 1 ≤ j ∨
      unlockTarget sp ℓ.frame (unlockView (tr.state y i) ℓ.frame (tr.time i) ℓ.call)
        ((sp.slot (tr.time i) : Int) - 1) B₀ = B₀)
    (h : ∃ l ∈ (tr.state y i).locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ ℓ.frame.tree, B.root = l.block ∧ ℓ.frame.Anc B₀ B) :
    ∃ l ∈ e.readPoint.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ ℓ.frame.tree, B.root = l.block ∧ ℓ.frame.Anc B₀ B := by
  obtain ⟨hc, he⟩ := hc
  have hΦ := (frameIn_of_callAt hr hy hc).1
  have hx := hr.exec i ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1] at hx
  have he' : e ∈ ((goldilocksSA sp FGP ro).step y (tr.state y i) ℓ.frame (tr.time i)
      ℓ.call).2 := by
    rw [hx]
    exact he
  clear hx he
  cases hcall : ℓ.call with
  | tick =>
    rw [hcall] at he' hu
    rw [unlockView_tick] at hu
    change e ∈ (acOnTick sp y _ ℓ.frame _).2 at he'
    unfold acOnTick at he'
    dsimp only at he'
    split_ifs at he' <;>
      first
      | exact floor_tryVote_readPoint he' hΦ hB0 hva0 hk hu h
      | simp at he'
  | proposal =>
    rw [hcall] at he'
    simp [ACInterface.step] at he'
  | toFG =>
    rw [hcall] at he'
    simp [ACInterface.step] at he'
  | message m =>
    rw [hcall] at he' hu
    rw [unlockView_message] at hu
    refine floor_tryVote_readPoint he' hΦ hB0 hva0 hk hu
      (floor_optimisticConfirmation hΦ hB0 hva0 hk ?_)
    rw [admitVote_locks_eq]
    exact h
  | block C =>
    rw [hcall] at he' hu
    rw [unlockView_block] at hu
    refine floor_tryVote_readPoint he' hΦ hB0 hva0 hk hu
      (floor_optimisticConfirmation hΦ hB0 hva0 hk ?_)
    rw [blockReceipt_locks]
    exact h
  | restart =>
    rw [hcall] at he'
    change e ∈ (acRestart sp ro y _ ℓ.frame (tr.time i)).2 at he'
    rw [((restart_state sp) FGP ro y _ ℓ.frame (tr.time i) hΦ (hr.time_nonneg i)).1] at he'
    simp at he'

/-- **The read point of a cast holds a live lock block `⪰ B₀`.** -/
theorem exists_readPoint_liveLockBlocks_floor
    (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e)
    (hB0 : B₀ ∈ ℓ.frame.tree) (hva0 : ℓ.frame.viableAncestor B₀ = B₀)
    (hk : sp.slot (tr.time i) ≤ m)
    (hu : (sp.slot (tr.time i) : Int) - 1 ≤ j ∨
      unlockTarget sp ℓ.frame (unlockView (tr.state y i) ℓ.frame (tr.time i) ℓ.call)
        ((sp.slot (tr.time i) : Int) - 1) B₀ = B₀)
    (h : ∃ l ∈ (tr.state y i).locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ ℓ.frame.tree, B.root = l.block ∧ ℓ.frame.Anc B₀ B) :
    ∃ C ∈ liveLockBlocks sp e.readPoint.locks ℓ.frame (tr.time i), ℓ.frame.Anc B₀ C := by
  have hΦ := (frameIn_of_callAt hr hy hc.1).1
  obtain ⟨l, hl, -, -, B, hB, hBr, hB0B⟩ := floor_liveLocks hΦ hB0 hva0 hk
    (floor_readPoint_locks hr hy hc hB0 hva0 hk hu h)
  exact ⟨B, ⟨hB, l, hl, hBr.symm⟩, hB0B⟩

end readPoint

end Consensus.Goldilocks.SA

end
