module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Actions
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Restart
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Trace

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

/-- Receipt admission never changes the execution-installed permission. -/
theorem admitVote_mayVote (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).mayVote = A.mayVote := by
  unfold admitVote
  split_ifs <;> rfl

theorem updateLatestConfirmed_mayVote (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (C : Blk sp.n FGP) : (updateLatestConfirmed sp A Φ C).mayVote = A.mayVote := by
  unfold updateLatestConfirmed
  split_ifs <;> rfl

theorem optimisticConfirmation_mayVote (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).mayVote = A.mayVote := by
  unfold optimisticConfirmation
  split
  · rfl
  · exact updateLatestConfirmed_mayVote _ _ _

theorem updateConfirmation_mayVote (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (s : Nat) : (updateConfirmation sp A Φ t s).mayVote = A.mayVote := by
  unfold updateConfirmation
  dsimp only
  split
  · rfl
  · split_ifs <;> first | rfl | exact updateLatestConfirmed_mayVote _ _ _

/-- Permission gates own creation, but is itself immutable under voting. -/
theorem tryVote_mayVote (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (tryVote sp self A Φ t).1.mayVote = A.mayVote := by
  unfold tryVote
  dsimp only
  split_ifs <;> simp only [optimisticConfirmation_mayVote, admitVote_mayVote] <;> rfl

private theorem foldl_admitVote_mayVote (t : Time) (vs : List (Vote sp.n)) (A : SAState sp.n) :
    (vs.foldl (fun st v => admitVote sp st t v) A).mayVote = A.mayVote := by
  induction vs generalizing A with
  | nil => rfl
  | cons v vs ih => exact (ih _).trans (admitVote_mayVote _ _ _)

theorem blockReceipt_mayVote (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).mayVote = A.mayVote :=
  foldl_admitVote_mayVote t (blockVotes B) _

theorem acOnMessage_mayVote (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (v : Vote sp.n) : (acOnMessage sp self A Φ t v).1.mayVote = A.mayVote := by
  simp only [acOnMessage, tryVote_mayVote, optimisticConfirmation_mayVote, admitVote_mayVote]

theorem acOnBlock_mayVote (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (B : Blk sp.n FGP) : (acOnBlock sp self A Φ t B).1.mayVote = A.mayVote := by
  simp only [acOnBlock, tryVote_mayVote, optimisticConfirmation_mayVote, blockReceipt_mayVote]

theorem acOnTick_mayVote (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acOnTick sp self A Φ t).1.mayVote = A.mayVote := by
  unfold acOnTick
  dsimp only
  split_ifs <;> simp only [tryVote_mayVote, updateConfirmation_mayVote]

theorem acProposal_mayVote (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acProposal sp A Φ t).1.mayVote = A.mayVote := by
  unfold acProposal
  split_ifs <;> rfl

theorem acToFG_mayVote (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acToFG sp A Φ t).1.mayVote = A.mayVote := by
  unfold acToFG
  split_ifs
  · split
    · rfl
    · split_ifs <;> rfl
  · rfl

/-- Restart replays receipts without changing the installed permission. -/
theorem acRestart_mayVote (ro : ReplayOrder sp FGP) (self : Fin sp.n)
    (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acRestart sp ro self A Φ t).1.mayVote = A.mayVote := by
  have keeps (bs : List (Blk sp.n FGP)) (acc : SAState sp.n × List (Em sp FGP)) :
      (bs.foldl (fun acc B =>
        let r := acOnBlock sp self acc.1 Φ t B
        (r.1, acc.2 ++ r.2)) acc).1.mayVote = acc.1.mayVote := by
    induction bs generalizing acc with
    | nil => rfl
    | cons B bs ih =>
      exact (ih _).trans (acOnBlock_mayVote self acc.1 Φ t B)
  exact keeps (ro.order t Φ) _

/-- Every AC call preserves the permission installed before execution. -/
theorem step_mayVote (ro : ReplayOrder sp FGP) (self : Fin sp.n)
    (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (c : (goldilocksSA sp FGP ro).Call) :
    ((goldilocksSA sp FGP ro).step self A Φ t c).1.mayVote = A.mayVote := by
  cases c with
  | tick => exact acOnTick_mayVote self A Φ t
  | proposal => exact acProposal_mayVote A Φ t
  | toFG => exact acToFG_mayVote A Φ t
  | message v => exact acOnMessage_mayVote self A Φ t v
  | block B => exact acOnBlock_mayVote self A Φ t B
  | restart => exact acRestart_mayVote ro self A Φ t

/-- A trace preserves each honest node's supplied initial permission at every cut. -/
theorem trace_mayVote {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro} {ini : Fin sp.n → SAState sp.n}
    (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr ini) {y : Fin sp.n} (hy : y ∈ H)
    (i : Nat) : (tr.state y i).mayVote = (ini y).mayVote := by
  induction i with
  | zero => change (tr.init y).mayVote = _; rw [hr.init y hy]
  | succ i ih =>
    by_cases hc : ∃ ℓ, tr.CallAt y i ℓ
    · obtain ⟨ℓ, hc⟩ := hc
      have he := hr.exec i ℓ hc.2 (hc.1 ▸ hy)
      rw [hc.1] at he
      have hp := step_mayVote ro y (tr.state y i) ℓ.frame (tr.time i) ℓ.call
      rw [he] at hp
      have hs : tr.state y (i + 1) = tr.post i := by
        simp [Trace.state, hc.1, hc.2]
      rw [hs]
      exact hp.trans ih
    · have hs : tr.state y (i + 1) = tr.state y i := by
        rw [Trace.state]
        split_ifs with h
        · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp h.2
          exact False.elim (hc ⟨ℓ, h.1, hℓ⟩)
        · rfl
      rw [hs]
      exact ih

/-- Stock traces retain the always-permitted initial binding. -/
theorem trace_mayVote_stock {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H)
    (i s : Nat) : (tr.state y i).mayVote s = true := by
  rw [trace_mayVote hr hy i]
  rfl

/-- A ready nonmember performs the unlock and voted-slot update without own admission,
emission, or an optimistic check. -/
theorem tryVote_of_not_selected (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (hj : joined sp A t) (hv : A.votedSlot ≠ sp.slot t)
    (ht : t ≤ sp.ts (sp.slot t) + sp.Δ)
    (hr : ¬ (t < sp.ts (sp.slot t) + sp.Δ ∧ (sp.slot t = 0 ∨ ¬ voteReady sp Φ (sp.slot t))))
    (hp : A.mayVote (sp.slot t) = false) :
    tryVote sp self A Φ t =
      let s := sp.slot t
      let V := mergedVoteView sp A Φ s
      let A₁ := if 0 < s then { A with locks := unlock sp A.locks Φ t ((s : Int) - 1) V } else A
      ({ A₁ with votedSlot := s }, []) := by
  simp [tryVote, hj, hv, not_lt.mpr ht, hr, hp]

end Consensus.Goldilocks.SA

end
