module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockFloorStep
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.RelTrace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WriteMode
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Walk
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Restart

public section

/-! # Tier A protection, the joint invariant over AC traces: the floor across a call with the
unlock given

The floor form of the AC lock step (`AC/LockFloorStep`) for a call that executes with the locks
`L₁` after its unlock given, at a write mode (`stepWithM`). Fix a block `B₀` of the frame's tree
that is its own viable ancestor, and a slot `j`; the floor of a lock set is a lock of slot `j`
with expiry `≥ m` on a block `⪰ B₀` of the tree.

* `floor_stepWithM`: within the floor lock's life (`slot(t) ≤ m`), a call keeps the floor when
  both the state's locks and the given locks `L₁` hold it: the call either keeps the state's locks
  (passed through `add_locks` by the confirmation writes) or replaces them by `L₁` (`try_vote`,
  `ac_proposal`), and every write of the mode is an `add_locks`, which keeps the floor
  (`SA.floor_addLocks`). Nothing is read about how `L₁` relates to the unlock input.
* `anc_getHead_of_floorAC`: the head walk extends `B` when a live lock block extends `B` and every
  live lock block is compatible with `B`: the anchor, the deepest of the live lock blocks and
  `fc_root`, is then at or above `B` (no chain of the live lock blocks is needed). -/

namespace Consensus.Goldilocks.Comparison

open SA

variable {sp : SAParams} {FGP : Type} {Φ : Frm sp.n FGP} {t : Time} {j m : Nat}
  {B₀ : Blk sp.n FGP}

/-! ### The floor across the writes and the vote of a mode -/

private theorem floor_optimisticConfirmationM (wm : WriteMode) {A : SAState sp.n}
    (hΦ : FrameOK Φ) (hB0 : B₀ ∈ Φ.tree) (hva0 : Φ.viableAncestor B₀ = B₀) (hk : sp.slot t ≤ m)
    (h : ∃ l ∈ A.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ (optimisticConfirmationM sp wm A Φ t).locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B :=
  optimisticConfirmationM_of (P := fun X => ∃ l ∈ X.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B)
    (floor_optimisticConfirmation hΦ hB0 hva0 hk h) h

private theorem floor_updateConfirmationM (wm : WriteMode) {A : SAState sp.n} {s : Nat}
    (hΦ : FrameOK Φ) (hB0 : B₀ ∈ Φ.tree) (hva0 : Φ.viableAncestor B₀ = B₀) (hk : sp.slot t ≤ m)
    (h : ∃ l ∈ A.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ (updateConfirmationM sp wm A Φ t s).locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  rcases hC : getConfirmation sp A Φ s with _ | C
  · rw [updateConfirmationM_locks_of_none hC]
    exact h
  · rw [updateConfirmationM_locks_of_some hC]
    exact floor_addLocks hΦ hB0 hva0 hk h

private theorem floor_tryVoteWithM (wm : WriteMode) (x : Fin sp.n) {L₁ : Set Lock}
    {A : SAState sp.n} (hΦ : FrameOK Φ) (hB0 : B₀ ∈ Φ.tree) (hva0 : Φ.viableAncestor B₀ = B₀)
    (hk : sp.slot t ≤ m)
    (h : ∃ l ∈ A.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B)
    (hL : ∃ l ∈ L₁, l.slot = j ∧ m ≤ l.expiry ∧ ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ (tryVoteWithM sp wm x L₁ A Φ t).1.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  unfold tryVoteWithM
  dsimp only
  split_ifs with h₁ h₂ h₃
  · exact h
  · exact h
  · refine floor_optimisticConfirmationM wm hΦ hB0 hva0 hk ?_
    rw [admitVote_locks_eq]
    exact hL
  · refine floor_optimisticConfirmationM wm hΦ hB0 hva0 hk ?_
    rw [admitVote_locks_eq]
    exact h

/-- **The floor across a call with the unlock given.** A call at time `t ≥ 0` with a well-formed
frame, executing at mode `wm` with the locks `L₁`, keeps the floor when the state's locks and
`L₁` both hold it, `B₀` is its own viable ancestor and `slot(t) ≤ m`. -/
theorem floor_stepWithM {ro : ReplayOrder sp FGP} (wm : WriteMode) (x : Fin sp.n)
    {L₁ : Set Lock} {A : SAState sp.n} (c : (goldilocksSA sp FGP ro).Call) (hΦ : FrameOK Φ)
    (ht : 0 ≤ t) (hB0 : B₀ ∈ Φ.tree) (hva0 : Φ.viableAncestor B₀ = B₀) (hk : sp.slot t ≤ m)
    (h : ∃ l ∈ A.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B)
    (hL : ∃ l ∈ L₁, l.slot = j ∧ m ≤ l.expiry ∧ ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B) :
    ∃ l ∈ (stepWithM sp ro wm x L₁ A Φ t c).1.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := by
  have hopt : ∀ {A' : SAState sp.n}, A'.locks = A.locks →
      ∃ l ∈ (optimisticConfirmationM sp wm A' Φ t).locks, l.slot = j ∧ m ≤ l.expiry ∧
        ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B := fun hA =>
    floor_optimisticConfirmationM wm hΦ hB0 hva0 hk (hA ▸ h)
  cases c with
  | tick =>
    change ∃ l ∈ (acOnTickWithM sp wm x L₁ A Φ t).1.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B
    have hv := floor_tryVoteWithM wm x hΦ hB0 hva0 hk h hL (t := t)
    unfold acOnTickWithM
    dsimp only
    split_ifs <;>
      first
      | exact floor_updateConfirmationM wm hΦ hB0 hva0 hk hv
      | exact hv
      | exact floor_updateConfirmationM wm hΦ hB0 hva0 hk h
      | exact h
  | proposal =>
    change ∃ l ∈ (acProposalWith sp L₁ A Φ t).1.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B
    unfold acProposalWith
    dsimp only
    split_ifs
    · exact hL
    · exact h
  | toFG =>
    change ∃ l ∈ (acToFG sp A Φ t).1.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B
    rw [acToFG_locks_eq]
    exact h
  | message v =>
    exact floor_tryVoteWithM wm x hΦ hB0 hva0 hk (hopt (admitVote_locks_eq A t v)) hL
  | block B =>
    exact floor_tryVoteWithM wm x hΦ hB0 hva0 hk (hopt (blockReceipt_locks A t B)) hL
  | restart =>
    obtain ⟨-, hl, -⟩ := (restart_state sp) FGP ro x A Φ t hΦ ht
    change ∃ l ∈ (acRestart sp ro x A Φ t).1.locks, l.slot = j ∧ m ≤ l.expiry ∧
      ∃ B ∈ Φ.tree, B.root = l.block ∧ Φ.Anc B₀ B
    rw [hl]
    exact h

/-! ### The head walk above a floor -/

/-- **The walk extends `B` above a live floor block.** In a well-formed frame, if a live lock
block `C` extends `B` and every live lock block is compatible with `B`, every head extends `B`:
the anchor is at or above `B`. -/
theorem anc_getHead_of_floorAC (hΦ : FrameOK Φ) {A : SAState sp.n} {B C : Blk sp.n FGP}
    (hC : C ∈ liveLockBlocks sp A.locks Φ t) (hBC : Φ.Anc B C)
    (hcomp : ∀ L ∈ liveLockBlocks sp A.locks Φ t, Compatible Φ.tree L B)
    {tree : Set (Blk sp.n FGP)} (htree : tree ⊆ Φ.tree) (V : View sp.n) (s : Int) :
    Φ.Anc B (getHead sp A Φ t tree V s) := by
  have hS : liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot} ⊆ Φ.tree := by
    rintro X (hX | hX)
    · exact hX.1
    · exact (Set.mem_singleton_iff.1 hX) ▸ hΦ.fcRoot_mem
  have hCt : C ∈ Φ.tree := hC.1
  obtain ⟨D, hD⟩ := exists_deepest hΦ hS ⟨C, Or.inl hC⟩
  have hA : getAnchor sp A Φ t = D := by unfold getAnchor; rw [hD]; rfl
  obtain ⟨hDS, hmax⟩ := deepest_mem hD
  -- a block strictly below `C` is not the deepest
  have below : Φ.Anc D C → Φ.Anc C D := by
    intro hDC
    by_cases hne : D = C
    · exact hne ▸ Relation.ReflTransGen.refl
    · have hlt := depth_lt_of_anc hΦ hDC hne hCt
      rcases hmax C (Or.inl hC) (Ne.symm hne) with h | ⟨h, -⟩ <;> omega
  have hBD : Φ.Anc B D := by
    rcases hDS with hDl | hDf
    · rcases hcomp D hDl with h | h
      · exact hBC.trans (below (h.trans hBC))
      · exact h
    · rw [Set.mem_singleton_iff.1 hDf] at below ⊢
      rcases liveLockBlock_candidate hΦ hC with h | h
      · exact hBC.trans (below h.2.1)
      · exact hBC.trans h
  unfold getHead
  rw [hA]
  exact hBD.trans (anc_ghost htree _ (hS hDS))

end Consensus.Goldilocks.Comparison

end
