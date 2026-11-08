module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Nodes
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Origin

public section

/-! # Goldilocks SA: the locks at a vote's read point

The input of the `try_vote` that emits an honest vote (`vote_tryVote_input`), the read point's
locks (`tryVote_readPoint_locks_eq`), and that a read-point lock of a slot other than the vote's
sits below a stored lock of the same slot (`readPoint_locks_below_stored`). Public SA-level
copies of private lemmas of `Lemmas/Compose/Sleepy/Transfer`, for H.1's transfer steps. Every
read-point lock, of any slot, sits below a stored lock or below the block of the receipt's
optimistic confirmation at the same cut (`readPoint_locks_provenance`). -/

namespace Consensus.Goldilocks.SA

variable {wm : SA.WriteMode}

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}

/-- `tryVote_readPoint_locks_eq` with the unlock given. -/
theorem tryVote_readPoint_locks_eqWith
    {L : Set Lock} {x : Fin sp.n} {A : SAState sp.n}
    {Φ : Frm sp.n FGP} {t : Time} {e : Em sp FGP} (he : e ∈ (tryVoteWithM sp wm x L A Φ t).2) :
    e.readPoint.locks = if 0 < sp.slot t then L else A.locks := by
  unfold tryVoteWithM at he
  dsimp only at he
  split_ifs at he with h1 h2 h3
  · simp at he
  · simp at he
  all_goals
    rw [List.mem_singleton] at he
    subst he
    split_ifs
    rfl

/-- The read point of `try_vote`'s emission holds the input's locks, unlocked against the merged
view for a slot `s > 0`. -/
theorem tryVote_readPoint_locks_eq {x : Fin sp.n} {A : SAState sp.n}
    {Φ : Frm sp.n FGP} {t : Time} {e : Em sp FGP} (he : e ∈ (tryVote sp x A Φ t).2) :
    e.readPoint.locks = if 0 < sp.slot t then
      unlock sp A.locks Φ t ((sp.slot t : Int) - 1) (mergedVoteView sp A Φ (sp.slot t))
      else A.locks := by
  unfold tryVote at he
  dsimp only at he
  split_ifs at he with h1 h2 h3
  · simp at he
  · simp at he
  all_goals
    rw [List.mem_singleton] at he
    subst he
    split_ifs
    rfl

/-- `vote_tryVote_input` with the unlock given, the receipt's optimistic check at the writes of
`wm`. -/
theorem vote_tryVote_inputU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    ∃ P, e ∈ (tryVoteWithM sp wm y (u i) P ℓ.frame (tr.time i)).2 ∧
      P = callInputM sp wm (tr.state y i) ℓ.frame (tr.time i) ℓ.call ∧
      callViewM sp wm (tr.state y i) ℓ.frame (tr.time i) ℓ.call =
        mergedVoteView sp P ℓ.frame (sp.slot (tr.time i)) ∧ (P = tr.state y i ∨
      ∃ A : SAState sp.n, P = optimisticConfirmationM sp wm A ℓ.frame (tr.time i) ∧
        A.locks = (tr.state y i).locks) := by
  obtain ⟨hc, he⟩ := hc
  have hΦ := (frameIn_of_callAtU hr hy hc).1
  have hx := hr.exec i ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1] at hx
  have he' : e ∈ (stepWithM sp ro wm y (u i) (tr.state y i) ℓ.frame (tr.time i)
      ℓ.call).2 := by
    rw [hx]
    exact he
  clear hx he
  cases hcall : ℓ.call with
  | tick =>
    rw [hcall] at he'
    change e ∈ (acOnTickWithM sp wm y (u i) _ ℓ.frame _).2 at he'
    unfold acOnTickWithM at he'
    dsimp only at he'
    split_ifs at he' <;> first | exact ⟨_, he', rfl, rfl, Or.inl rfl⟩ | simp at he'
  | proposal =>
    rw [hcall] at he'
    simp at he'
  | toFG =>
    rw [hcall] at he'
    simp at he'
  | message m =>
    rw [hcall] at he'
    exact ⟨_, he', rfl, rfl, Or.inr ⟨_, rfl, admitVote_locks_eq _ _ _⟩⟩
  | block B =>
    rw [hcall] at he'
    exact ⟨_, he', rfl, rfl, Or.inr ⟨_, rfl, blockReceipt_locks _ _ _⟩⟩
  | restart =>
    rw [hcall] at he'
    change e ∈ (acRestart sp ro y _ ℓ.frame (tr.time i)).2 at he'
    rw [((restart_state sp) FGP ro y _ ℓ.frame (tr.time i) hΦ (hr.time_nonneg i)).1] at he'
    simp at he'

/-- The input of the `try_vote` that emits an honest vote: the state before the call, or the
optimistic check after the receipt of a message or a block, which keeps the locks. -/
theorem vote_tryVote_input (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) :
    ∃ P, e ∈ (tryVote sp y P ℓ.frame (tr.time i)).2 ∧ (P = tr.state y i ∨
      ∃ A : SAState sp.n, P = optimisticConfirmation sp A ℓ.frame (tr.time i) ∧
        A.locks = (tr.state y i).locks) := by
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
    rw [hcall] at he'
    change e ∈ (acOnTick sp y _ ℓ.frame _).2 at he'
    unfold acOnTick at he'
    dsimp only at he'
    split_ifs at he' <;> first | exact ⟨_, he', Or.inl rfl⟩ | simp at he'
  | proposal =>
    rw [hcall] at he'
    simp [ACInterface.step] at he'
  | toFG =>
    rw [hcall] at he'
    simp [ACInterface.step] at he'
  | message m =>
    rw [hcall] at he'
    exact ⟨_, he', Or.inr ⟨_, rfl, admitVote_locks_eq _ _ _⟩⟩
  | block B =>
    rw [hcall] at he'
    exact ⟨_, he', Or.inr ⟨_, rfl, blockReceipt_locks _ _ _⟩⟩
  | restart =>
    rw [hcall] at he'
    change e ∈ (acRestart sp ro y _ ℓ.frame (tr.time i)).2 at he'
    rw [((restart_state sp) FGP ro y _ ℓ.frame (tr.time i) hΦ (hr.time_nonneg i)).1] at he'
    simp at he'

/-- `readPoint_locks_below_stored` with the unlock given. -/
theorem readPoint_locks_below_storedU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) (hpos : 0 < sp.slot (tr.time i)) :
    ∀ l' ∈ e.readPoint.locks, l'.slot ≠ sp.slot (tr.time i) →
      ∃ l ∈ (tr.state y i).locks, l'.slot = l.slot ∧ ∃ B ∈ ℓ.frame.tree, B.root = l.block ∧
        ∃ B' ∈ ℓ.frame.tree, B'.root = l'.block ∧ ℓ.frame.Anc B' B := by
  obtain ⟨P, he, hPi, hV, hP⟩ := vote_tryVote_inputU hr hy hc
  have hΦ := (frameIn_of_callAtU hr hy hc.1).1
  have hlaw := hr.lawfulAt hy hc.1 hΦ
  rw [← hPi, hV] at hlaw
  intro l' hl' hne
  rw [tryVote_readPoint_locks_eqWith he] at hl'
  simp only [hpos, ↓reduceIte] at hl'
  obtain ⟨l₁, hl₁, hs₁, -, -, B₁, hB₁, hB₁r, B', hB', hB'r, hA⟩ := hlaw.movesBack hΦ l' hl'
  rcases hP with rfl | ⟨A, rfl, hAl⟩
  · exact ⟨l₁, hl₁, hs₁, B₁, hB₁, hB₁r, B', hB', hB'r, hA⟩
  rw [optimisticConfirmationM_eq] at hl₁
  split_ifs at hl₁
  swap
  · exact ⟨l₁, hAl ▸ hl₁, hs₁, B₁, hB₁, hB₁r, B', hB', hB'r, hA⟩
  unfold optimisticConfirmation at hl₁
  split at hl₁
  · exact ⟨l₁, hAl ▸ hl₁, hs₁, B₁, hB₁, hB₁r, B', hB', hB'r, hA⟩
  rw [updateLatestConfirmed_keeps_locks] at hl₁
  obtain ⟨l₂, hl₂, hs₂, -, -, B₂, hB₂, hB₂r, B₁', hB₁', hB₁'r, hA'⟩ :=
    ((locks_move_back sp) FGP ℓ.frame A.locks (tr.time i) hΦ).2.1 _ _ l₁ hl₁
  rcases hl₂ with hl₂ | ⟨p, hp, rfl⟩
  · obtain rfl : B₁' = B₁ := hΦ.coherent.1 hB₁' hB₁ (hB₁'r.trans hB₁r.symm)
    exact ⟨l₂, hAl ▸ hl₂, hs₁.trans hs₂, B₂, hB₂, hB₂r, B', hB', hB'r, hA.trans hA'⟩
  · rw [Set.mem_singleton_iff] at hp
    subst hp
    exact absurd (hs₁.trans hs₂) hne

/-- **The read point's locks come from the stored ones.** At an honest vote of a slot `> 0`,
a lock of the read point of a slot other than the vote's sits (in the frame) below a stored
lock of the same slot: `try_vote`'s unlocking and the receipt's optimistic check only move
locks back, and the optimistic check writes locks of the vote's slot. -/
theorem readPoint_locks_below_stored (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) (hpos : 0 < sp.slot (tr.time i)) :
    ∀ l' ∈ e.readPoint.locks, l'.slot ≠ sp.slot (tr.time i) →
      ∃ l ∈ (tr.state y i).locks, l'.slot = l.slot ∧ ∃ B ∈ ℓ.frame.tree, B.root = l.block ∧
        ∃ B' ∈ ℓ.frame.tree, B'.root = l'.block ∧ ℓ.frame.Anc B' B :=
  readPoint_locks_below_storedU (hr := hr.toU) (y := y) (hy := hy) (i := i) (ℓ := ℓ) (e := e)
      (hc := hc) (hpos := hpos)

/-- `vote_tryVote_input`, naming the optimistic point: after a message or block receipt, the
`try_vote` input is the optimistic confirmation of the receipt state. -/
private theorem vote_tryVote_input_point (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) :
    ∃ P, e ∈ (tryVote sp y P ℓ.frame (tr.time i)).2 ∧ (P = tr.state y i ∨
      ∃ A : SAState sp.n, P = optimisticConfirmation sp A ℓ.frame (tr.time i) ∧
        A.locks = (tr.state y i).locks ∧ OptimisticPoint tr y i ℓ A ∧
        ((∃ m, ℓ.call = .message m ∧ A = admitVote sp (tr.state y i) (tr.time i) m) ∨
          ∃ B, ℓ.call = .block B ∧ A = blockReceipt sp (tr.state y i) (tr.time i) B)) := by
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
    rw [hcall] at he'
    change e ∈ (acOnTick sp y _ ℓ.frame _).2 at he'
    unfold acOnTick at he'
    dsimp only at he'
    split_ifs at he' <;> first | exact ⟨_, he', Or.inl rfl⟩ | simp at he'
  | proposal =>
    rw [hcall] at he'
    simp [ACInterface.step] at he'
  | toFG =>
    rw [hcall] at he'
    simp [ACInterface.step] at he'
  | message m =>
    rw [hcall] at he'
    exact ⟨_, he', Or.inr ⟨_, rfl, admitVote_locks_eq _ _ _, ⟨hc, Or.inl ⟨m, hcall, rfl⟩⟩,
      Or.inl ⟨m, rfl, rfl⟩⟩⟩
  | block B =>
    rw [hcall] at he'
    exact ⟨_, he', Or.inr ⟨_, rfl, blockReceipt_locks _ _ _, ⟨hc, Or.inr (Or.inl ⟨B, hcall, rfl⟩)⟩,
      Or.inr ⟨B, rfl, rfl⟩⟩⟩
  | restart =>
    rw [hcall] at he'
    change e ∈ (acRestart sp ro y _ ℓ.frame (tr.time i)).2 at he'
    rw [((restart_state sp) FGP ro y _ ℓ.frame (tr.time i) hΦ (hr.time_nonneg i)).1] at he'
    simp at he'

/-- **Read-point lock provenance.** At an honest vote of a slot `> 0`, every lock of the read
point names a frame block below the block of a stored lock, or below the block that the
receipt's optimistic confirmation at the same cut selects (a lock of the vote's slot). -/
theorem readPoint_locks_provenance (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y i ℓ e) (hpos : 0 < sp.slot (tr.time i)) :
    ∀ l' ∈ e.readPoint.locks, ∃ B' ∈ ℓ.frame.tree, B'.root = l'.block ∧
      ((∃ l ∈ (tr.state y i).locks, ∃ B ∈ ℓ.frame.tree, B.root = l.block ∧ ℓ.frame.Anc B' B) ∨
       ∃ B CV, OptimisticLockAt tr y i (sp.slot (tr.time i)) B CV ∧ ℓ.frame.Anc B' B) := by
  obtain ⟨P, he, hP⟩ := vote_tryVote_input_point hr hy hc
  have hΦ := (frameIn_of_callAt hr hy hc.1).1
  intro l' hl'
  rw [tryVote_readPoint_locks_eq he] at hl'
  simp only [hpos, ↓reduceIte] at hl'
  obtain ⟨l₁, hl₁, -, -, -, B₁, hB₁, hB₁r, B', hB', hB'r, hA⟩ :=
    ((locks_move_back sp) FGP ℓ.frame P.locks (tr.time i) hΦ).2.2 _ _ l' hl'
  refine ⟨B', hB', hB'r, ?_⟩
  rcases hP with rfl | ⟨A, rfl, hAl, hpt, -⟩
  · exact Or.inl ⟨l₁, hl₁, B₁, hB₁, hB₁r, hA⟩
  unfold optimisticConfirmation at hl₁
  split at hl₁
  · exact Or.inl ⟨l₁, hAl ▸ hl₁, B₁, hB₁, hB₁r, hA⟩
  rename_i B hsel
  rw [updateLatestConfirmed_keeps_locks] at hl₁
  obtain ⟨l₂, hl₂, -, -, -, B₂, hB₂, hB₂r, B₁', hB₁', hB₁'r, hA'⟩ :=
    ((locks_move_back sp) FGP ℓ.frame A.locks (tr.time i) hΦ).2.1 _ _ l₁ hl₁
  obtain rfl : B₁' = B₁ := hΦ.coherent.1 hB₁' hB₁ (hB₁'r.trans hB₁r.symm)
  rcases hl₂ with hl₂ | ⟨p, hp, rfl⟩
  · exact Or.inl ⟨l₂, hAl ▸ hl₂, B₂, hB₂, hB₂r, hA.trans hA'⟩
  · rw [Set.mem_singleton_iff] at hp
    subst hp
    have hBt : B ∈ ℓ.frame.tree := by
      have h := hsel
      unfold optimisticSelect at h
      dsimp only at h
      split_ifs at h
      exact (deepest_mem h).1.1
    obtain rfl : B₂ = B := hΦ.coherent.1 hB₂ hBt hB₂r
    exact Or.inr ⟨B₂, _, ⟨ℓ, A, hpt, rfl, hsel, rfl⟩, hA.trans hA'⟩

/-- `readPoint_locks_provenance` with the cut bound of the optimistic arm: the read point's
optimistic lock is written by the receipt's check (`on_message`/`on_block`, before the own vote of
the call), so its counted honest votes were cast at cuts before `i`. -/
theorem readPoint_locks_provenance_strict {proposer : Nat → Fin sp.n}
    (hrun : ACRun proposer tr H U) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP} (hc : CastAt tr y i ℓ e)
    (hpos : 0 < sp.slot (tr.time i)) :
    ∀ l' ∈ e.readPoint.locks, ∃ B' ∈ ℓ.frame.tree, B'.root = l'.block ∧
      ((∃ l ∈ (tr.state y i).locks, ∃ B ∈ ℓ.frame.tree, B.root = l.block ∧ ℓ.frame.Anc B' B) ∨
       ∃ B CV, OptimisticLockAt tr y i (sp.slot (tr.time i)) B CV ∧
         (∀ v ∈ CV, v.val ∈ H → ∃ j < i, ∃ e', VoteAt tr v.val j e' ∧ e'.msg = v) ∧
         ℓ.frame.Anc B' B) := by
  have hr := hrun.localRun
  obtain ⟨P, he, hP⟩ := vote_tryVote_input_point hr hy hc
  have hΦ := (frameIn_of_callAt hr hy hc.1).1
  intro l' hl'
  rw [tryVote_readPoint_locks_eq he] at hl'
  simp only [hpos, ↓reduceIte] at hl'
  obtain ⟨l₁, hl₁, -, -, -, B₁, hB₁, hB₁r, B', hB', hB'r, hA⟩ :=
    ((locks_move_back sp) FGP ℓ.frame P.locks (tr.time i) hΦ).2.2 _ _ l' hl'
  refine ⟨B', hB', hB'r, ?_⟩
  rcases hP with rfl | ⟨A, rfl, hAl, hpt, hrcpt⟩
  · exact Or.inl ⟨l₁, hl₁, B₁, hB₁, hB₁r, hA⟩
  unfold optimisticConfirmation at hl₁
  split at hl₁
  · exact Or.inl ⟨l₁, hAl ▸ hl₁, B₁, hB₁, hB₁r, hA⟩
  rename_i B hsel
  rw [updateLatestConfirmed_keeps_locks] at hl₁
  obtain ⟨l₂, hl₂, -, -, -, B₂, hB₂, hB₂r, B₁', hB₁', hB₁'r, hA'⟩ :=
    ((locks_move_back sp) FGP ℓ.frame A.locks (tr.time i) hΦ).2.1 _ _ l₁ hl₁
  obtain rfl : B₁' = B₁ := hΦ.coherent.1 hB₁' hB₁ (hB₁'r.trans hB₁r.symm)
  rcases hl₂ with hl₂ | ⟨p, hp, rfl⟩
  · exact Or.inl ⟨l₂, hAl ▸ hl₂, B₂, hB₂, hB₂r, hA.trans hA'⟩
  · rw [Set.mem_singleton_iff] at hp
    subst hp
    have hBt : B ∈ ℓ.frame.tree := by
      have h := hsel
      unfold optimisticSelect at h
      dsimp only at h
      split_ifs at h
      exact (deepest_mem h).1.1
    obtain rfl : B₂ = B := hΦ.coherent.1 hB₂ hBt hB₂r
    exact Or.inr ⟨B₂, _, ⟨ℓ, A, hpt, rfl, hsel, rfl⟩,
      fun v hv hvH => receipt_pool_vote hrun hy hc.1 hrcpt hv.1 hvH, hA.trans hA'⟩

end Consensus.Goldilocks.SA

end
