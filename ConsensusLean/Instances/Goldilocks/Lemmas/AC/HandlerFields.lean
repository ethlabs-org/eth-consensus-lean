module
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Actions
public import ConsensusLean.Instances.Goldilocks.Spec.AC.Restart
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Premises
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.RestartStamp

public section

/-! # Goldilocks AC: the fields each handler keeps

The AC handlers below write only some fields of the state. `admitVote` and `blockReceipt` (a
stamp only) keep `voted_slot`, `restart_time`, the locks and `latest_confirmed`;
`updateLatestConfirmed` keeps `voted_slot`, `restart_time` and the locks;
`optimisticConfirmation`, `updateConfirmation`, `acProposal` and `acToFG` keep `voted_slot` and
`restart_time`. Every handler keeps `mayVote` (`step_mayVote`), and every emission is of a slot
whose `mayVote` holds in the call's input state (`tryVote_emits_mayVote`, `emits_mayVote`: the
emission gate). -/

namespace Consensus.Goldilocks.AC

variable {FGP : Type} {sp : ACParams}

theorem admitVote_keeps (A : ACState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).votedSlot = A.votedSlot ∧
      (admitVote sp A t v).restartTime = A.restartTime := by
  unfold admitVote
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem admitVote_keeps_locks (A : ACState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).locks = A.locks ∧
      (admitVote sp A t v).latestConfirmed = A.latestConfirmed := by
  unfold admitVote
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem updateLatestConfirmed_keeps (A : ACState sp.n) (Φ : Frm sp.n FGP)
    (C : Blk sp.n FGP) : (updateLatestConfirmed sp A Φ C).votedSlot = A.votedSlot ∧
      (updateLatestConfirmed sp A Φ C).restartTime = A.restartTime := by
  unfold updateLatestConfirmed
  split_ifs <;> exact ⟨rfl, rfl⟩

theorem updateLatestConfirmed_keeps_locks (A : ACState sp.n) (Φ : Frm sp.n FGP)
    (C : Blk sp.n FGP) : (updateLatestConfirmed sp A Φ C).locks = A.locks := by
  unfold updateLatestConfirmed
  split_ifs <;> rfl

theorem optimistic_keeps (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).votedSlot = A.votedSlot ∧
      (optimisticConfirmation sp A Φ t).restartTime = A.restartTime := by
  unfold optimisticConfirmation
  split
  · exact ⟨rfl, rfl⟩
  · exact updateLatestConfirmed_keeps _ _ _

theorem updateConfirmation_keeps (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (s : Nat) : (updateConfirmation sp A Φ t s).votedSlot = A.votedSlot ∧
      (updateConfirmation sp A Φ t s).restartTime = A.restartTime := by
  unfold updateConfirmation
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · split_ifs <;> first | exact ⟨rfl, rfl⟩ | exact updateLatestConfirmed_keeps _ _ _

theorem blockReceipt_keeps (A : ACState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).votedSlot = A.votedSlot ∧
      (blockReceipt sp A t B).restartTime = A.restartTime :=
  ⟨rfl, rfl⟩

theorem blockReceipt_keeps_locks (A : ACState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).locks = A.locks ∧
      (blockReceipt sp A t B).latestConfirmed = A.latestConfirmed :=
  ⟨rfl, rfl⟩

theorem acToFG_keeps (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acToFG sp A Φ t).1.votedSlot = A.votedSlot ∧
      (acToFG sp A Φ t).1.restartTime = A.restartTime := by
  unfold acToFG
  split_ifs <;> exact ⟨rfl, rfl⟩

/-- Receipt admission never changes the execution-installed permission. -/
theorem admitVote_mayVote (A : ACState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).mayVote = A.mayVote := by
  unfold admitVote
  split_ifs <;> rfl

/-- `updateLatestConfirmed` keeps the permission `mayVote`. -/
private theorem updateLatestConfirmed_mayVote (A : ACState sp.n) (Φ : Frm sp.n FGP)
    (C : Blk sp.n FGP) : (updateLatestConfirmed sp A Φ C).mayVote = A.mayVote := by
  unfold updateLatestConfirmed
  split_ifs <;> rfl

/-- `optimistic_confirmation` keeps the permission `mayVote`. -/
theorem optimisticConfirmation_mayVote (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).mayVote = A.mayVote := by
  unfold optimisticConfirmation
  split
  · rfl
  · exact updateLatestConfirmed_mayVote _ _ _

/-- `update_confirmation` keeps the permission `mayVote`. -/
theorem updateConfirmation_mayVote (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (s : Nat) : (updateConfirmation sp A Φ t s).mayVote = A.mayVote := by
  unfold updateConfirmation
  dsimp only
  split
  · rfl
  · split_ifs <;> first | rfl | exact updateLatestConfirmed_mayVote _ _ _

/-- Permission gates own creation, but is itself immutable under voting. -/
theorem tryVote_mayVote (self : Fin sp.n) (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (tryVote sp self A Φ t).1.mayVote = A.mayVote := by
  unfold tryVote
  lift_lets
  extract_lets s V A₁ dom H A₂ vote A₃
  have hA₂ : A₂.mayVote = A.mayVote := by simp only [A₂, A₁]; split <;> rfl
  split_ifs with h₁ h₂ h₃
  · rfl
  · rfl
  · simp only [A₃, h₃, ↓reduceIte, optimisticConfirmation_mayVote, admitVote_mayVote]
    exact hA₂
  · simpa only [A₃, h₃, Bool.false_eq_true, ↓reduceIte] using hA₂

/-- Block receipt, which only stamps the block, keeps the permission `mayVote`. -/
theorem blockReceipt_mayVote (A : ACState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).mayVote = A.mayVote :=
  rfl

/-- The vote handler `ac_on_message` keeps the permission `mayVote`. -/
private theorem acOnMessage_mayVote (self : Fin sp.n) (A : ACState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (v : Vote sp.n) : (acOnMessage sp self A Φ t v).1.mayVote = A.mayVote := by
  simp only [acOnMessage, tryVote_mayVote, optimisticConfirmation_mayVote, admitVote_mayVote]

/-- The block handler `ac_on_block` keeps the permission `mayVote`. -/
private theorem acOnBlock_mayVote (self : Fin sp.n) (A : ACState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (B : Blk sp.n FGP) : (acOnBlock sp self A Φ t B).1.mayVote = A.mayVote := by
  simp only [acOnBlock, tryVote_mayVote, optimisticConfirmation_mayVote, blockReceipt_mayVote]

/-- The tick handler `ac_on_tick` keeps the permission `mayVote`. -/
private theorem acOnTick_mayVote (self : Fin sp.n) (A : ACState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) :
    (acOnTick sp self A Φ t).1.mayVote = A.mayVote := by
  unfold acOnTick
  dsimp only
  split_ifs <;> simp only [tryVote_mayVote, updateConfirmation_mayVote]

/-- The proposal handler `ac_proposal` keeps the permission `mayVote`. -/
private theorem acProposal_mayVote (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acProposal sp A Φ t).1.mayVote = A.mayVote := by
  unfold acProposal
  split_ifs <;> rfl

/-- The finality-gadget handler `ac_to_fg` keeps the permission `mayVote`. -/
theorem acToFG_mayVote (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acToFG sp A Φ t).1.mayVote = A.mayVote := by
  unfold acToFG
  split_ifs <;> rfl

/-- Restart replays receipts without changing the installed permission. -/
theorem acRestart_mayVote (ro : ReplayOrder sp FGP) (self : Fin sp.n)
    (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acRestart sp ro self A Φ t).1.mayVote = A.mayVote := by
  classical
  by_cases h : FrameOK Φ ∧ 0 ≤ t
  · rw [acRestart_eq_stamp sp ro self A Φ t h.1 h.2, restartStamp_eq]
  clear h
  have keeps (bs : List (Blk sp.n FGP)) (acc : ACState sp.n × List (Em sp FGP)) :
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
    (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (c : (goldilocksAC sp FGP ro).Call) :
    ((goldilocksAC sp FGP ro).step self A Φ t c).1.mayVote = A.mayVote := by
  cases c with
  | tick => exact acOnTick_mayVote self A Φ t
  | proposal => exact acProposal_mayVote A Φ t
  | toFG => exact acToFG_mayVote A Φ t
  | message v => exact acOnMessage_mayVote self A Φ t v
  | block B => exact acOnBlock_mayVote self A Φ t B
  | restart => exact acRestart_mayVote ro self A Φ t

/-- A trace preserves each honest node's supplied initial permission at every cut. -/
theorem trace_mayVote {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : GTrace sp FGP ro} {ini : Fin sp.n → ACState sp.n}
    (hr : ACLocalRun (goldilocksAC sp FGP ro) H U tr ini) {y : Fin sp.n} (hy : y ∈ H)
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

/-- **The read-time gate**: on a trace from the canonical committee start, an honest node may
vote in slot `s` at a cut iff it is a member of the slot-`s` committee. -/
theorem trace_mayVote_iff {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : GTrace sp FGP ro} {K : CommitteeDict sp.n}
    (hr : ACLocalRun (goldilocksAC sp FGP ro) H U tr (committeeStart sp.genesisRoot K))
    {y : Fin sp.n} (hy : y ∈ H) (i s : Nat) :
    (tr.state y i).mayVote s = true ↔ y ∈ K.committee s := by
  rw [trace_mayVote hr hy i, committeeStart_mayVote]

/-- Stock traces retain the always-permitted initial binding: the gate at the full committee,
whose canonical start is the stock one (`committeeStart_full`). -/
theorem trace_mayVote_stock {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {tr : GTrace sp FGP ro}
    (hr : ACLocalRun (goldilocksAC sp FGP ro) H U tr) {y : Fin sp.n} (hy : y ∈ H)
    (i s : Nat) : (tr.state y i).mayVote s = true :=
  (trace_mayVote_iff (K := CommitteeDict.full sp.n) (by rw [committeeStart_full]; exact hr) hy
    i s).2 (Set.mem_univ y)

/-! ## The emission gate -/

/-- **The emission gate.** `try_vote` emits only a vote of a slot its state may vote in. -/
private theorem tryVote_emits_mayVote (self : Fin sp.n) (A : ACState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : ∀ e ∈ (tryVote sp self A Φ t).2, A.mayVote e.msg.slot = true := by
  unfold tryVote
  lift_lets
  extract_lets s V A₁ dom H A₂ vote A₃
  split_ifs with h₁ h₂ h₃
  · simp
  · simp
  · intro e he
    rw [List.mem_singleton] at he
    subst he
    exact h₃
  · simp

/-- Every vote emitted by `ac_on_block` is of a slot that the input state may vote in. -/
private theorem acOnBlock_emits_mayVote (self : Fin sp.n) (A : ACState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (B : Blk sp.n FGP) :
    ∀ e ∈ (acOnBlock sp self A Φ t B).2, A.mayVote e.msg.slot = true := fun e he => by
  have h := tryVote_emits_mayVote self _ Φ t e he
  rwa [optimisticConfirmation_mayVote, blockReceipt_mayVote] at h

/-- The restart replay keeps the permission and emits only gated votes. -/
private theorem foldl_acOnBlock_emits_mayVote (self : Fin sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (p : Nat → Bool) :
    ∀ (l : List (Blk sp.n FGP)) (acc : ACState sp.n × List (Em sp FGP)),
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

/-- **Every AC call is gated.** Every emission of an AC call passes the call's input gate: a
vote of slot `s` only when `mayVote s`. -/
theorem emits_mayVote (ro : ReplayOrder sp FGP) (self : Fin sp.n) (A : ACState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (c : (goldilocksAC sp FGP ro).Call) :
    ∀ e ∈ ((goldilocksAC sp FGP ro).step self A Φ t c).2, A.mayVote e.msg.slot = true := by
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

end Consensus.Goldilocks.AC

end
