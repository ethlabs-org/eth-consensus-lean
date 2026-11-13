module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Actions
public import ConsensusLean.Instances.Goldilocks.Spec.SA.Restart
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Trace

public section

/-! # Goldilocks SA: the fields each handler keeps

The SA handlers below write only some fields of the state. `admitVote` and `blockReceipt` keep
`voted_slot`, `restart_time`, the locks and `latest_confirmed`; `updateLatestConfirmed` keeps
`voted_slot`, `restart_time` and the locks; `optimisticConfirmation`, `updateConfirmation`,
`acProposal` and `acToFG` keep `voted_slot` and `restart_time`. Every handler keeps `mayVote`
(`step_mayVote`), and every emission is of a slot whose `mayVote` holds in the call's input
state (`tryVote_emits_mayVote`, `emits_mayVote`: the emission gate). -/

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

/-- `updateLatestConfirmed` keeps the permission `mayVote`. -/
private theorem updateLatestConfirmed_mayVote (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (C : Blk sp.n FGP) : (updateLatestConfirmed sp A Φ C).mayVote = A.mayVote := by
  unfold updateLatestConfirmed
  split_ifs <;> rfl

/-- `optimistic_confirmation` keeps the permission `mayVote`. -/
theorem optimisticConfirmation_mayVote (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).mayVote = A.mayVote := by
  unfold optimisticConfirmation
  split
  · rfl
  · exact updateLatestConfirmed_mayVote _ _ _

/-- `update_confirmation` keeps the permission `mayVote`. -/
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
  split_ifs <;> simp only [optimisticConfirmation_mayVote, admitVote_mayVote]

private theorem foldl_admitVote_mayVote (t : Time) (vs : List (Vote sp.n)) (A : SAState sp.n) :
    (vs.foldl (fun st v => admitVote sp st t v) A).mayVote = A.mayVote := by
  induction vs generalizing A with
  | nil => rfl
  | cons v vs ih => exact (ih _).trans (admitVote_mayVote _ _ _)

/-- Block receipt, which admits the block's votes, keeps the permission `mayVote`. -/
theorem blockReceipt_mayVote (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).mayVote = A.mayVote :=
  foldl_admitVote_mayVote t (blockVotes B) _

/-- The vote handler `ac_on_message` keeps the permission `mayVote`. -/
private theorem acOnMessage_mayVote (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (v : Vote sp.n) : (acOnMessage sp self A Φ t v).1.mayVote = A.mayVote := by
  simp only [acOnMessage, tryVote_mayVote, optimisticConfirmation_mayVote, admitVote_mayVote]

/-- The block handler `ac_on_block` keeps the permission `mayVote`. -/
private theorem acOnBlock_mayVote (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (B : Blk sp.n FGP) : (acOnBlock sp self A Φ t B).1.mayVote = A.mayVote := by
  simp only [acOnBlock, tryVote_mayVote, optimisticConfirmation_mayVote, blockReceipt_mayVote]

/-- The tick handler `ac_on_tick` keeps the permission `mayVote`. -/
private theorem acOnTick_mayVote (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) :
    (acOnTick sp self A Φ t).1.mayVote = A.mayVote := by
  unfold acOnTick
  dsimp only
  split_ifs <;> simp only [tryVote_mayVote, updateConfirmation_mayVote]

/-- The proposal handler `ac_proposal` keeps the permission `mayVote`. -/
private theorem acProposal_mayVote (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acProposal sp A Φ t).1.mayVote = A.mayVote := by
  unfold acProposal
  split_ifs <;> rfl

/-- The finality-gadget handler `ac_to_fg` keeps the permission `mayVote`. -/
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

/-! ## The emission gate -/

/-- **The emission gate.** `try_vote` emits only a vote of a slot its state may vote in. -/
theorem tryVote_emits_mayVote (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : ∀ e ∈ (tryVote sp self A Φ t).2, A.mayVote e.msg.slot = true := by
  unfold tryVote
  dsimp only
  split_ifs <;> simp_all

/-- Every vote emitted by `ac_on_block` is of a slot that the input state may vote in. -/
private theorem acOnBlock_emits_mayVote (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (B : Blk sp.n FGP) :
    ∀ e ∈ (acOnBlock sp self A Φ t B).2, A.mayVote e.msg.slot = true := fun e he => by
  have h := tryVote_emits_mayVote self _ Φ t e he
  rwa [optimisticConfirmation_mayVote, blockReceipt_mayVote] at h

/-- The restart replay keeps the permission and emits only gated votes. -/
private theorem foldl_acOnBlock_emits_mayVote (self : Fin sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (p : Nat → Bool) :
    ∀ (l : List (Blk sp.n FGP)) (acc : SAState sp.n × List (Em sp FGP)),
      acc.1.mayVote = p → (∀ e ∈ acc.2, p e.msg.slot = true) →
        ∀ e ∈ (l.foldl (fun acc B => let r := acOnBlock sp self acc.1 Φ t B;
          (r.1, acc.2 ++ r.2)) acc).2, p e.msg.slot = true
  | [], _, _, h => h
  | B :: l, acc, h₁, h₂ => foldl_acOnBlock_emits_mayVote self Φ t p l _
      ((acOnBlock_mayVote self acc.1 Φ t B).trans h₁)
      fun e he => by
        rcases List.mem_append.mp he with he | he
        · exact h₂ e he
        · rw [← h₁]
          exact acOnBlock_emits_mayVote self acc.1 Φ t B e he

/-- **Every SA call is gated.** Every emission of an SA call passes the call's input gate: a
vote of slot `s` only when `mayVote s`. -/
theorem emits_mayVote (ro : ReplayOrder sp FGP) (self : Fin sp.n) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (c : (goldilocksSA sp FGP ro).Call) :
    ∀ e ∈ ((goldilocksSA sp FGP ro).step self A Φ t c).2, A.mayVote e.msg.slot = true := by
  intro e he
  cases c with
  | tick =>
    change e ∈ (acOnTick sp self A Φ t).2 at he
    unfold acOnTick at he
    dsimp only at he
    split_ifs at he
    all_goals first
      | exact absurd he List.not_mem_nil
      | exact tryVote_emits_mayVote self A Φ t e he
  | proposal => exact absurd he List.not_mem_nil
  | toFG => exact absurd he List.not_mem_nil
  | message v =>
    change e ∈ (acOnMessage sp self A Φ t v).2 at he
    have h := tryVote_emits_mayVote self _ Φ t e he
    rwa [optimisticConfirmation_mayVote, admitVote_mayVote] at h
  | block B => exact acOnBlock_emits_mayVote self A Φ t B e he
  | restart =>
    change e ∈ (acRestart sp ro self A Φ t).2 at he
    unfold acRestart at he
    exact foldl_acOnBlock_emits_mayVote self Φ t A.mayVote _ _ rfl
      (fun _ h => absurd h List.not_mem_nil) e he

end Consensus.Goldilocks.SA

end
