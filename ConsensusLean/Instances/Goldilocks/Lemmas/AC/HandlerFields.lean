module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Actions

public section

/-! # Goldilocks SA: the fields each handler keeps

The SA handlers below write only some fields of the state. `admitVote` and `blockReceipt` keep
`voted_slot`, `restart_time`, the locks and `latest_confirmed`; `updateLatestConfirmed` keeps
`voted_slot`, `restart_time` and the locks; `optimisticConfirmation`, `updateConfirmation`,
`acProposal` and `acToFG` keep `voted_slot` and `restart_time`. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

theorem admitVote_keeps (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).votedSlot = A.votedSlot ∧
      (admitVote sp A t v).restartTime = A.restartTime := by
  unfold admitVote
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem admitVote_keeps_locks (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).locks = A.locks ∧
      (admitVote sp A t v).latestConfirmed = A.latestConfirmed := by
  unfold admitVote
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem updateLatestConfirmed_keeps (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (C : Blk sp.n FGP) : (updateLatestConfirmed sp A Φ C).votedSlot = A.votedSlot ∧
      (updateLatestConfirmed sp A Φ C).restartTime = A.restartTime := by
  unfold updateLatestConfirmed
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem updateLatestConfirmed_keeps_locks (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (C : Blk sp.n FGP) : (updateLatestConfirmed sp A Φ C).locks = A.locks := by
  unfold updateLatestConfirmed
  split_ifs <;> rfl

theorem optimistic_keeps (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).votedSlot = A.votedSlot ∧
      (optimisticConfirmation sp A Φ t).restartTime = A.restartTime := by
  unfold optimisticConfirmation
  split
  · exact ⟨rfl, rfl⟩
  · exact updateLatestConfirmed_keeps _ _ _

theorem updateConfirmation_keeps (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (s : Nat) : (updateConfirmation sp A Φ t s).votedSlot = A.votedSlot ∧
      (updateConfirmation sp A Φ t s).restartTime = A.restartTime := by
  unfold updateConfirmation
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · split_ifs <;> first | exact ⟨rfl, rfl⟩ | exact updateLatestConfirmed_keeps _ _ _

/-- Admitting a list of votes keeps every field that `admitVote` keeps. -/
private theorem foldl_admitVote_keeps (t : Time) (l : List (Vote sp.n)) (A : SAState sp.n) :
    (l.foldl (fun A v => admitVote sp A t v) A).votedSlot = A.votedSlot ∧
      (l.foldl (fun A v => admitVote sp A t v) A).restartTime = A.restartTime ∧
      (l.foldl (fun A v => admitVote sp A t v) A).locks = A.locks ∧
      (l.foldl (fun A v => admitVote sp A t v) A).latestConfirmed = A.latestConfirmed := by
  induction l generalizing A with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons v l ih =>
    simp only [List.foldl_cons]
    obtain ⟨h₁, h₂, h₃, h₄⟩ := ih (admitVote sp A t v)
    exact ⟨h₁.trans (admitVote_keeps _ _ _).1, h₂.trans (admitVote_keeps _ _ _).2,
      h₃.trans (admitVote_keeps_locks _ _ _).1, h₄.trans (admitVote_keeps_locks _ _ _).2⟩

theorem blockReceipt_keeps (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).votedSlot = A.votedSlot ∧
      (blockReceipt sp A t B).restartTime = A.restartTime :=
  have h := foldl_admitVote_keeps t (blockVotes B)
    { A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) }
  ⟨h.1, h.2.1⟩

theorem blockReceipt_keeps_locks (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).locks = A.locks ∧
      (blockReceipt sp A t B).latestConfirmed = A.latestConfirmed :=
  have h := foldl_admitVote_keeps t (blockVotes B)
    { A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) }
  ⟨h.2.2.1, h.2.2.2⟩

theorem acProposal_keeps (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acProposal sp A Φ t).1.votedSlot = A.votedSlot ∧
      (acProposal sp A Φ t).1.restartTime = A.restartTime := by
  unfold acProposal
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem acToFG_keeps (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acToFG sp A Φ t).1.votedSlot = A.votedSlot ∧
      (acToFG sp A Φ t).1.restartTime = A.restartTime := by
  unfold acToFG
  split_ifs
  · split
    · exact ⟨rfl, rfl⟩
    · split_ifs <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

end Consensus.Goldilocks.SA

end
