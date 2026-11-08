module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.WeightedEm
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.EvidenceRelease.Handlers
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.EvidenceRelease.Write
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Restart
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.RelTrace

public section

/-! # The evidence-release SA projects to the parent's step with the unlock replaced

The forgetful projection of the evidence-release SA (`Spec/WeightedLocks`) to the parent's state:

* **the invariant** `LocksForget`: the parent state's locks are the forgotten weighted locks. It
  holds initially and every handler keeps it, also at the read point of every emission
  (`locksForget_initial`, `locksForget_tryVoteW`, `locksForget_acOnMessageW`,
  `locksForget_acOnBlockW`, `locksForget_acOnTickW`, `locksForget_acProposalW`,
  `locksForget_acToFGW`, and for the restart the third conjunct of `acRestartW_proj`);
* **the writes are the parent's**: under the invariant, the forgotten optimistic confirmation and
  the forgotten update are the parent's (`optimisticConfirmationW_ac`, `updateConfirmationW_ac`);
* **the unlock is the only change**: `tryVoteWith` and `acProposalWith` are the parent's `try_vote`
  and `ac_proposal` with the locks after their unlock given as an argument. The parent's handlers
  are these with the parent's `unlock` (`tryVote_eq_tryVoteWith`, `acProposal_eq_acProposalWith`),
  and under the invariant the forgotten handlers of the candidate are these with the forgotten
  `unlockW` (`tryVoteW_proj`, `acProposalW_proj`), emissions included (`projEm`).

So a forgotten run of the candidate is a run of the parent's step in which the locks after each
unlock are those of `unlockW`, which the lock-rule interface relates to the parent's unlock by
(B), (S), (K) and no removal (`Rule`, `Lemmas/AC/LockRule`). This is a step correspondence, not
an equivalence of runs. -/

namespace Consensus.Goldilocks.EvidenceRelease

open SA

variable {sp : SAParams} {FGP : Type} {σ : Type} (E : UnlockStage sp wlockStore σ) (c : σ)

/-- The parent state's locks are the forgotten weighted locks. -/
def LocksForget {n : Nat} (X : WState n) : Prop :=
  X.ac.locks = WLock.lock '' X.wlocks

theorem locksForget_iff {n : Nat} (X : WState n) :
    LocksForget X ↔ X.ac.locks = WLock.lock '' X.wlocks :=
  Iff.rfl

theorem locksForget_initial {n : Nat} (g : Nat) : LocksForget (WState.initial g : WState n) := by
  rw [locksForget_iff]
  exact (Set.image_empty _).symm

theorem locksForget_withLocks (X : WState sp.n) (A : SAState sp.n) (W : Set WLock) :
    LocksForget (withLocks sp X A W) :=
  (locksForget_iff _).2 rfl

/-- Admitting a vote keeps the invariant. -/
theorem locksForget_admitVote {Y : WState sp.n} (hY : LocksForget Y) (t : Time) (v : Vote sp.n) :
    LocksForget { Y with ac := admitVote sp Y.ac t v } :=
  (locksForget_iff _).2 ((admitVote_keeps_locks Y.ac t v).1.trans hY)

theorem projEm_eq (e : EmW sp FGP) : projEm e = ⟨e.msg, e.readPoint.ac, e.head⟩ := by
  rfl

/-! ### The writes -/

theorem optimisticConfirmationW_ac {X : WState sp.n} (hX : LocksForget X) (Φ : Frm sp.n FGP)
    (t : Time) : (optimisticConfirmationW sp X Φ t).ac = optimisticConfirmation sp X.ac Φ t := by
  have h := lock_image_optimisticLocksW (W := X.wlocks) (A := X.ac) hX.symm Φ t
  change { optimisticConfirmation sp X.ac Φ t with
    locks := WLock.lock '' optimisticLocksW sp X.wlocks X.ac Φ t } = _
  rw [h]

theorem updateConfirmationW_ac {X : WState sp.n} (hX : LocksForget X) (Φ : Frm sp.n FGP)
    (t : Time) (s : Nat) :
    (updateConfirmationW sp X Φ t s).ac = updateConfirmation sp X.ac Φ t s := by
  have h := lock_image_updateLocksW (W := X.wlocks) (A := X.ac) hX.symm X.counts Φ t s
  change { updateConfirmation sp X.ac Φ t s with
    locks := WLock.lock '' updateLocksW sp X.wlocks X.ac X.counts Φ t s } = _
  rw [h]

/-! ### The parent's handlers with the locks after the unlock given -/

/-- `tryVoteW_proj` for any unlock stage. -/
theorem tryVoteE_proj {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    ((tryVoteE sp E c self X Φ t).1.ac, (tryVoteE sp E c self X Φ t).2.map projEm) =
      tryVoteWith sp self (WLock.lock '' wlockStore.unlockWith sp E c
        X.wlocks Φ t ((sp.slot t : Int) - 1)
        (mergedVoteView sp X.ac Φ (sp.slot t))) X.ac Φ t := by
  unfold tryVoteE tryVoteWith
  dsimp only
  split_ifs with h₁ h₂ h₃
  · rfl
  · rfl
  · rw [optimisticConfirmationW_ac (locksForget_admitVote
      (Y := { (unlockStateE sp E c X Φ t ((sp.slot t : Int) - 1)
          (mergedVoteView sp X.ac Φ (sp.slot t)))
        with ac := { (unlockStateE sp E c X Φ t _ _).ac with votedSlot := sp.slot t } })
      ((locksForget_iff _).2 rfl) t _)]
    rfl
  · rw [optimisticConfirmationW_ac (locksForget_admitVote
      (Y := { X with ac := { X.ac with votedSlot := sp.slot t } }) hX t _)]
    rfl

/-- **The candidate's `try_vote`, forgotten**, is `tryVoteWith` of the forgotten `unlockW`. -/
theorem tryVoteW_proj {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    ((tryVoteW sp self X Φ t).1.ac, (tryVoteW sp self X Φ t).2.map projEm) =
      tryVoteWith sp self (WLock.lock '' unlockW sp X.wlocks Φ t ((sp.slot t : Int) - 1)
        (mergedVoteView sp X.ac Φ (sp.slot t))) X.ac Φ t :=
  tryVoteE_proj (evidenceStage sp) () hX self Φ t

/-- Under the invariant, the locks after the candidate's unlock move the parent state's locks only
back (A0.4 (c), the parent's `MovesBack`), the relation the routes read of the unlock. -/
theorem unlockState_movesBack {X : WState sp.n} (hX : LocksForget X) {Φ : Frm sp.n FGP}
    (hΦ : FrameOK Φ) (t : Time) (s : Int) (V : View sp.n) :
    MovesBack sp Φ X.ac.locks (unlockState sp X Φ t s V).ac.locks := by
  rw [hX]
  exact LockStore.unlockWith_movesBack wlockStore_lawful (evidenceStage_lawful sp) () hΦ
    X.wlocks t s V

/-! ### The invariant through every handler -/

theorem locksForget_optimisticConfirmationW (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    LocksForget (optimisticConfirmationW sp X Φ t) :=
  locksForget_withLocks _ _ _

theorem locksForget_updateConfirmationW (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (s : Nat) : LocksForget (updateConfirmationW sp X Φ t s) :=
  (locksForget_iff _).2 rfl

theorem locksForget_unlockState (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) (s : Int)
    (V : View sp.n) : LocksForget (unlockState sp X Φ t s V) :=
  locksForget_withLocks _ _ _

/-- `locksForget_tryVoteW` for any unlock stage. -/
theorem locksForget_tryVoteE {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    LocksForget (tryVoteE sp E c self X Φ t).1 ∧
      ∀ e ∈ (tryVoteE sp E c self X Φ t).2, LocksForget e.readPoint := by
  unfold tryVoteE
  dsimp only
  split_ifs with h₁ h₂ h₃
  · exact ⟨hX, fun _ h => absurd h List.not_mem_nil⟩
  · exact ⟨hX, fun _ h => absurd h List.not_mem_nil⟩
  · refine ⟨locksForget_optimisticConfirmationW _ _ _, fun e he => ?_⟩
    rw [List.mem_singleton] at he
    subst he
    exact (locksForget_iff _).2 rfl
  · refine ⟨locksForget_optimisticConfirmationW _ _ _, fun e he => ?_⟩
    rw [List.mem_singleton] at he
    subst he
    exact (locksForget_iff _).2 hX

/-- `try_vote` keeps the invariant, also at the read point of its emission. -/
theorem locksForget_tryVoteW {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    LocksForget (tryVoteW sp self X Φ t).1 ∧
      ∀ e ∈ (tryVoteW sp self X Φ t).2, LocksForget e.readPoint :=
  locksForget_tryVoteE (evidenceStage sp) () hX self Φ t

/-- `locksForget_acOnMessageW` for any unlock stage. -/
theorem locksForget_acOnMessageE (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (v : Vote sp.n) :
    LocksForget (acOnMessageE sp E c self X Φ t v).1 ∧
      ∀ e ∈ (acOnMessageE sp E c self X Φ t v).2, LocksForget e.readPoint :=
  locksForget_tryVoteE E c (locksForget_optimisticConfirmationW _ _ _) self Φ t

/-- `ac_on_message` establishes the invariant, also at its emissions' read points. -/
theorem locksForget_acOnMessageW (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (v : Vote sp.n) :
    LocksForget (acOnMessageW sp self X Φ t v).1 ∧
      ∀ e ∈ (acOnMessageW sp self X Φ t v).2, LocksForget e.readPoint :=
  locksForget_acOnMessageE (evidenceStage sp) () self X Φ t v

/-- `locksForget_acOnBlockW` for any unlock stage. -/
theorem locksForget_acOnBlockE (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (B : Blk sp.n FGP) :
    LocksForget (acOnBlockE sp E c self X Φ t B).1 ∧
      ∀ e ∈ (acOnBlockE sp E c self X Φ t B).2, LocksForget e.readPoint :=
  locksForget_tryVoteE E c (locksForget_optimisticConfirmationW _ _ _) self Φ t

/-- `ac_on_block` establishes the invariant, also at its emissions' read points. -/
theorem locksForget_acOnBlockW (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (B : Blk sp.n FGP) :
    LocksForget (acOnBlockW sp self X Φ t B).1 ∧
      ∀ e ∈ (acOnBlockW sp self X Φ t B).2, LocksForget e.readPoint :=
  locksForget_acOnBlockE (evidenceStage sp) () self X Φ t B

/-- `locksForget_acOnTickW` for any unlock stage. -/
theorem locksForget_acOnTickE {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    LocksForget (acOnTickE sp E c self X Φ t).1 ∧
      ∀ e ∈ (acOnTickE sp E c self X Φ t).2, LocksForget e.readPoint := by
  have hv := locksForget_tryVoteE E c hX self Φ t
  unfold acOnTickE
  dsimp only
  split_ifs <;>
    first
    | exact ⟨hX, fun _ h => absurd h List.not_mem_nil⟩
    | exact ⟨locksForget_updateConfirmationW _ _ _ _, hv.2⟩
    | exact hv
    | exact ⟨locksForget_updateConfirmationW _ _ _ _, fun _ h => absurd h List.not_mem_nil⟩

/-- `ac_on_tick` keeps the invariant, also at its emissions' read points. -/
theorem locksForget_acOnTickW {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    LocksForget (acOnTickW sp self X Φ t).1 ∧
      ∀ e ∈ (acOnTickW sp self X Φ t).2, LocksForget e.readPoint :=
  locksForget_acOnTickE (evidenceStage sp) () hX self Φ t

/-- `locksForget_acProposalW` for any unlock stage. -/
theorem locksForget_acProposalE {X : WState sp.n} (hX : LocksForget X) (Φ : Frm sp.n FGP)
    (t : Time) : LocksForget (acProposalE sp E c X Φ t).1 := by
  unfold acProposalE
  dsimp only
  split_ifs <;> first | exact hX | exact locksForget_withLocks _ _ _

/-- `ac_proposal` keeps the invariant. -/
theorem locksForget_acProposalW {X : WState sp.n} (hX : LocksForget X) (Φ : Frm sp.n FGP)
    (t : Time) : LocksForget (acProposalW sp X Φ t).1 :=
  locksForget_acProposalE (evidenceStage sp) () hX Φ t

/-- The parent's `ac_to_fg` keeps the locks. -/
theorem acToFG_locks (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acToFG sp A Φ t).1.locks = A.locks := by
  unfold acToFG
  split_ifs
  · split
    · rfl
    · split_ifs <;> rfl
  · rfl

/-- `ac_to_fg` keeps the invariant, and is the parent's on the parent's state. -/
theorem locksForget_acToFGW {X : WState sp.n} (hX : LocksForget X) (Φ : Frm sp.n FGP)
    (t : Time) : LocksForget (acToFGW sp X Φ t).1 :=
  (locksForget_iff _).2 ((acToFG_locks X.ac Φ t).trans hX)

theorem acToFGW_proj (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    ((acToFGW sp X Φ t).1.ac, (acToFGW sp X Φ t).2) = acToFG sp X.ac Φ t :=
  rfl

/-! ### `ac_proposal` -/

/-- `acProposalW_proj` for any unlock stage. -/
theorem acProposalE_proj (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    ((acProposalE sp E c X Φ t).1.ac, (acProposalE sp E c X Φ t).2) = acProposalWith sp
      (WLock.lock '' wlockStore.unlockWith sp E c
        X.wlocks Φ t ((sp.slot t : Int) - 1)
        (View.ofLists (voteViewList X.ac Φ ((sp.slot t : Int) - 1) ⊤))) X.ac Φ t := by
  unfold acProposalE acProposalWith
  dsimp only
  split_ifs <;> rfl

/-- **The candidate's `ac_proposal`, forgotten**, is `acProposalWith` of the forgotten
`unlockW`. -/
theorem acProposalW_proj (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    ((acProposalW sp X Φ t).1.ac, (acProposalW sp X Φ t).2) = acProposalWith sp
      (WLock.lock '' unlockW sp X.wlocks Φ t ((sp.slot t : Int) - 1)
        (View.ofLists (voteViewList X.ac Φ ((sp.slot t : Int) - 1) ⊤))) X.ac Φ t :=
  acProposalE_proj (evidenceStage sp) () X Φ t

/-! ### `ac_on_message`, `ac_on_block`, `ac_on_tick` -/

/-- `acOnMessageW_proj` for any unlock stage. -/
theorem acOnMessageE_proj {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (v : Vote sp.n) :
    let Y := optimisticConfirmationW sp { X with ac := admitVote sp X.ac t v } Φ t
    ((acOnMessageE sp E c self X Φ t v).1.ac, (acOnMessageE sp E c self X Φ t v).2.map projEm) =
      tryVoteWith sp self (WLock.lock '' wlockStore.unlockWith sp E c
        Y.wlocks Φ t ((sp.slot t : Int) - 1)
        (mergedVoteView sp Y.ac Φ (sp.slot t)))
        (optimisticConfirmation sp (admitVote sp X.ac t v) Φ t) Φ t := by
  intro Y
  have hY : Y.ac = optimisticConfirmation sp (admitVote sp X.ac t v) Φ t :=
    optimisticConfirmationW_ac (locksForget_admitVote hX t v) Φ t
  rw [← hY]
  exact tryVoteE_proj E c (locksForget_optimisticConfirmationW _ _ _) self Φ t

/-- **`ac_on_message`, forgotten**: the parent's admission and optimistic confirmation, then
`tryVoteWith` of the forgotten `unlockW` of the state after them. -/
theorem acOnMessageW_proj {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (v : Vote sp.n) :
    let Y := optimisticConfirmationW sp { X with ac := admitVote sp X.ac t v } Φ t
    ((acOnMessageW sp self X Φ t v).1.ac, (acOnMessageW sp self X Φ t v).2.map projEm) =
      tryVoteWith sp self (WLock.lock '' unlockW sp Y.wlocks Φ t ((sp.slot t : Int) - 1)
        (mergedVoteView sp Y.ac Φ (sp.slot t)))
        (optimisticConfirmation sp (admitVote sp X.ac t v) Φ t) Φ t :=
  acOnMessageE_proj (evidenceStage sp) () hX self Φ t v

/-- `acOnBlockW_proj` for any unlock stage. -/
theorem acOnBlockE_proj {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (B : Blk sp.n FGP) :
    let Y := optimisticConfirmationW sp { X with ac := blockReceipt sp X.ac t B } Φ t
    ((acOnBlockE sp E c self X Φ t B).1.ac, (acOnBlockE sp E c self X Φ t B).2.map projEm) =
      tryVoteWith sp self (WLock.lock '' wlockStore.unlockWith sp E c
        Y.wlocks Φ t ((sp.slot t : Int) - 1)
        (mergedVoteView sp Y.ac Φ (sp.slot t)))
        (optimisticConfirmation sp (blockReceipt sp X.ac t B) Φ t) Φ t := by
  intro Y
  have hR : LocksForget { X with ac := blockReceipt sp X.ac t B } :=
    (locksForget_iff _).2 ((blockReceipt_keeps_locks X.ac t B).1.trans hX)
  have hY : Y.ac = optimisticConfirmation sp (blockReceipt sp X.ac t B) Φ t :=
    optimisticConfirmationW_ac hR Φ t
  rw [← hY]
  exact tryVoteE_proj E c (locksForget_optimisticConfirmationW _ _ _) self Φ t

/-- **`ac_on_block`, forgotten**: the parent's receipt and optimistic confirmation, then
`tryVoteWith` of the forgotten `unlockW` of the state after them. -/
theorem acOnBlockW_proj {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (B : Blk sp.n FGP) :
    let Y := optimisticConfirmationW sp { X with ac := blockReceipt sp X.ac t B } Φ t
    ((acOnBlockW sp self X Φ t B).1.ac, (acOnBlockW sp self X Φ t B).2.map projEm) =
      tryVoteWith sp self (WLock.lock '' unlockW sp Y.wlocks Φ t ((sp.slot t : Int) - 1)
        (mergedVoteView sp Y.ac Φ (sp.slot t)))
        (optimisticConfirmation sp (blockReceipt sp X.ac t B) Φ t) Φ t :=
  acOnBlockE_proj (evidenceStage sp) () hX self Φ t B

/-- `acOnTickW_proj` for any unlock stage. -/
theorem acOnTickE_proj {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    ((acOnTickE sp E c self X Φ t).1.ac, (acOnTickE sp E c self X Φ t).2.map projEm) =
      acOnTickWith sp self (WLock.lock '' wlockStore.unlockWith sp E c
        X.wlocks Φ t ((sp.slot t : Int) - 1)
        (mergedVoteView sp X.ac Φ (sp.slot t))) X.ac Φ t := by
  have hv := tryVoteE_proj E c hX self Φ t
  have hf := (locksForget_tryVoteE E c hX self Φ t).1
  unfold acOnTickE acOnTickWith
  dsimp only
  split_ifs <;>
    first
    | rfl
    | exact hv
    | (rw [updateConfirmationW_ac hf, ← hv])
    | (rw [updateConfirmationW_ac hX]; rfl)

/-- **`ac_on_tick`, forgotten**: `acOnTickWith` of the forgotten `unlockW`. -/
theorem acOnTickW_proj {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    ((acOnTickW sp self X Φ t).1.ac, (acOnTickW sp self X Φ t).2.map projEm) =
      acOnTickWith sp self (WLock.lock '' unlockW sp X.wlocks Φ t ((sp.slot t : Int) - 1)
        (mergedVoteView sp X.ac Φ (sp.slot t))) X.ac Φ t :=
  acOnTickE_proj (evidenceStage sp) () hX self Φ t

/-! ### The restart -/

/-- `acOnBlockW_of_not_joined` for any unlock stage. -/
theorem acOnBlockE_of_not_joined {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (B : Blk sp.n FGP)
    (hnj : ¬ joined sp (blockReceipt sp X.ac t B) t) :
    acOnBlockE sp E c self X Φ t B = ({ X with ac := blockReceipt sp X.ac t B }, []) := by
  have hsel : optimisticSelect sp (blockReceipt sp X.ac t B) Φ t = none := by
    simp only [optimisticSelect, hnj, not_false_eq_true, true_or, ite_true]
  have hopt : optimisticConfirmationW sp { X with ac := blockReceipt sp X.ac t B } Φ t =
      { X with ac := blockReceipt sp X.ac t B } := by
    have hl : WLock.lock '' X.wlocks = (blockReceipt sp X.ac t B).locks :=
      hX.symm.trans (blockReceipt_keeps_locks X.ac t B).1.symm
    simp only [optimisticConfirmationW, withLocks, optimisticLocksW, optimisticConfirmation,
      hsel, hl]
  simp only [acOnBlockE, hopt, tryVoteE, hnj, not_false_eq_true, true_or, ite_true]

/-- At a state whose receipt is not joined, `ac_on_block` is the receipt and emits nothing. -/
theorem acOnBlockW_of_not_joined {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (B : Blk sp.n FGP)
    (hnj : ¬ joined sp (blockReceipt sp X.ac t B) t) :
    acOnBlockW sp self X Φ t B = ({ X with ac := blockReceipt sp X.ac t B }, []) :=
  acOnBlockE_of_not_joined (evidenceStage sp) () hX self Φ t B hnj

/-- `acRestartW_proj` for any unlock stage. -/
theorem acRestartE_proj {X : WState sp.n} (hX : LocksForget X) (ro : ReplayOrder sp FGP)
    (self : Fin sp.n) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} (ht : 0 ≤ t) :
    (acRestartE sp E c ro self X Φ t).1.ac = (acRestart sp ro self X.ac Φ t).1 ∧
      (acRestartE sp E c ro self X Φ t).2 = [] ∧ LocksForget (acRestartE sp E c ro self X Φ
          t).1 := by
  have hl := ro.parentOrder t Φ (parentOrder_exists sp hΦ)
  let A' : SAState sp.n := { SAState.initial sp.genesisRoot with
    locks := X.ac.locks, latestConfirmed := X.ac.latestConfirmed,
    restartTime := (t : WithBot Time) }
  have h₀ : RestartInv sp X.ac Φ t A' :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun σ x hx => by simp [A', SAState.initial] at hx,
      fun x => Or.inl rfl, fun q => Or.inl rfl⟩
  have key : ∀ l : List (Blk sp.n FGP), (∀ B ∈ l, B ∈ Φ.tree ∧ B.root ≠ sp.genesisRoot) →
      ∀ (acc : WState sp.n × List (EmW sp FGP)) (pacc : SAState sp.n × List (Em sp FGP)),
      acc.1.ac = pacc.1 → acc.2 = [] → pacc.2 = [] → LocksForget acc.1 →
      RestartInv sp X.ac Φ t pacc.1 →
      let r := l.foldl (fun acc B => let r := acOnBlockE sp E c self acc.1 Φ t B;
        (r.1, acc.2 ++ r.2)) acc
      let q := l.foldl (fun acc B => let r := SA.acOnBlock sp self acc.1 Φ t B;
        (r.1, acc.2 ++ r.2)) pacc
      r.1.ac = q.1 ∧ r.2 = [] ∧ q.2 = [] ∧ LocksForget r.1 := by
    intro l
    induction l with
    | nil => intro _ acc pacc he h₂ h₂' hf _; exact ⟨he, h₂, h₂', hf⟩
    | cons B l ih =>
      intro hl acc pacc he h₂ h₂' hf h₁
      obtain ⟨hB, hg⟩ := hl B List.mem_cons_self
      have hR := h₁.blockReceipt sp hB hg
      have hnj := not_joined_of_restartTime sp ht hR.restartTime
      rw [← he] at hnj
      have hw := acOnBlockE_of_not_joined E c hf self Φ t B hnj
      have hp := h₁.acOnBlock sp ht hB hg self
      simp only [List.foldl_cons]
      apply ih (fun C hC => hl C (List.mem_cons_of_mem _ hC))
      · simp only [hw, hp, he]
      · simp only [hw, h₂, List.append_nil]
      · simp only [hp, h₂', List.append_nil]
      · simp only [hw]
        exact (locksForget_iff _).2 ((blockReceipt_keeps_locks acc.1.ac t B).1.trans hf)
      · simp only [hp]
        exact hR
  obtain ⟨h1, h2, -, h4⟩ := key (ro.order t Φ) (fun B hB => (hl.2.1 B).mp hB)
    ({ ac := A', wlocks := X.wlocks, counts := fun _ _ => 0 }, []) (A', []) rfl rfl rfl hX h₀
  exact ⟨h1, h2, h4⟩

/-- **The restart, forgotten**: in a well-formed frame at `t ≥ 0`, the forgotten restart of the
candidate is the parent's restart, and neither emits. -/
theorem acRestartW_proj {X : WState sp.n} (hX : LocksForget X) (ro : ReplayOrder sp FGP)
    (self : Fin sp.n) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} (ht : 0 ≤ t) :
    (acRestartW sp ro self X Φ t).1.ac = (acRestart sp ro self X.ac Φ t).1 ∧
      (acRestartW sp ro self X Φ t).2 = [] ∧ LocksForget (acRestartW sp ro self X Φ t).1 :=
  acRestartE_proj (evidenceStage sp) () hX ro self hΦ ht

end Consensus.Goldilocks.EvidenceRelease

end
