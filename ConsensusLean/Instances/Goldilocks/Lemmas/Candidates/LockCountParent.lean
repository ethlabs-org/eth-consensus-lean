module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Candidates.LockCount
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WriteMode
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Restart
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.ParentOracleM

public section

/-! # Counting the parent's stored locks and saved rows at a write mode

The parent's calls at a write mode `m` without the optimistic write, at the parent's unlock of
the call (`parentUnlockM`), are lock steps of the parent's lock store (`parent_lockStep`) and row
steps of its saved rows (`parent_rowStep`): the unlock is `unlock` of the call's input, whose
locks are the state's (the receipt and the optimistic write off keep them), and only the update
of slot `s − 1` at the tick at `t_s + 2Δ` writes locks (one per fast bit, of slot `s − 1`, expiry
at most `s − 1 + k`) and a saved row. So along an AC trace of the parent's stage at mode `m` with
one tick per honest node and time, every honest node holds at most `(fast arm ? 2 : 1) · k`
unexpired locks, saves no row of a slot `≥ slot(t)`, and holds at most `max w 1` saved rows of
the slots `slot(t) − max w 1 ≤ j`, at every `w` (`parent_lockMemory`). -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}

/-! ### The fields of the handlers -/

private theorem admitVote_saved (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).saved = A.saved := by
  unfold admitVote
  split_ifs <;> rfl

private theorem blockReceipt_saved (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).saved = A.saved := by
  have key : ∀ (l : List (Vote sp.n)) (X : SAState sp.n),
      (l.foldl (fun A v => admitVote sp A t v) X).saved = X.saved := by
    intro l
    induction l with
    | nil => intro X; rfl
    | cons v l ih => intro X; rw [List.foldl_cons, ih, admitVote_saved]
  unfold blockReceipt
  rw [key]

private theorem tryVoteWithM_fields {m : WriteMode} (h : m.optimistic = false) (self : Fin sp.n)
    (L₁ : Set Lock) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    ((tryVoteWithM sp m self L₁ A Φ t).1.locks = A.locks ∨
      (tryVoteWithM sp m self L₁ A Φ t).1.locks = L₁) ∧
      (tryVoteWithM sp m self L₁ A Φ t).1.saved = A.saved := by
  unfold tryVoteWithM
  dsimp only
  split_ifs with h₁ h₂ h₃
  · exact ⟨Or.inl rfl, rfl⟩
  · exact ⟨Or.inl rfl, rfl⟩
  · rw [optimisticConfirmationM_off h, (admitVote_keeps_locks _ _ _).1, admitVote_saved]
    exact ⟨Or.inr rfl, rfl⟩
  · rw [optimisticConfirmationM_off h, (admitVote_keeps_locks _ _ _).1, admitVote_saved]
    exact ⟨Or.inl rfl, rfl⟩

private theorem acToFG_fields (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acToFG sp A Φ t).1.locks = A.locks ∧ (acToFG sp A Φ t).1.saved = A.saved := by
  unfold acToFG
  split_ifs <;> first
    | exact ⟨rfl, rfl⟩
    | (split <;> first | exact ⟨rfl, rfl⟩ | (split_ifs <;> exact ⟨rfl, rfl⟩))

private theorem acProposalWith_fields (L₁ : Set Lock) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : ((acProposalWith sp L₁ A Φ t).1.locks = A.locks ∨
      (acProposalWith sp L₁ A Φ t).1.locks = L₁) ∧
      (acProposalWith sp L₁ A Φ t).1.saved = A.saved := by
  unfold acProposalWith
  split_ifs <;> first | exact ⟨Or.inl rfl, rfl⟩ | exact ⟨Or.inr rfl, rfl⟩

private theorem updateConfirmationM_saved (m : WriteMode) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (s : Nat) : ∀ j : Int, (updateConfirmationM sp m A Φ t s).saved j ≠ none →
      A.saved j ≠ none ∨ j = s := by
  intro j hj
  rw [updateConfirmationM_field SAState.saved (fun _ _ => rfl)] at hj
  unfold updateConfirmation at hj
  dsimp only at hj
  have key : ∀ X : SAState sp.n, X.saved = Function.update A.saved s
      ((getConfirmation sp A Φ s).map Block.root) → X.saved j ≠ none → A.saved j ≠ none ∨ j = s :=
    fun X hX h => by
      rw [hX] at h
      by_cases hjs : j = (s : Int)
      · exact Or.inr hjs
      · rw [Function.update_of_ne hjs] at h
        exact Or.inl h
  split at hj
  · exact key _ rfl hj
  · split_ifs at hj
    · exact key _ rfl hj
    · exact key _ (by unfold updateLatestConfirmed; split_ifs <;> rfl) hj

/-- The new locks of the update of slot `s` at mode `m`, as the parent's stored locks. -/
private theorem newOK_newLocksM {m : WriteMode} {A : SAState sp.n} {Φ : Frm sp.n FGP}
    {t : Time} {s : Nat} {C : Blk sp.n FGP} {sv : Int → Option Nat} {L : Set Lock} :
    NewOK sp lockStore m.fastArm s {l | ∃ p ∈ newLocksM sp m A Φ t s C sv L,
      l = ⟨p.1, s, p.2.1, p.2.2⟩} := by
  rw [newOK_iff, keyInj_iff]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    refine ⟨rfl, ?_, fun hf => newLocksM_no_fast hf p hp⟩
    rcases mem_newLocksM.1 hp with ⟨-, B, -, rfl⟩ | ⟨B, -, rfl⟩
    · exact min_le_left _ _
    · exact le_rfl
  · rintro _ ⟨p₁, hp₁, rfl⟩ _ ⟨p₂, hp₂, rfl⟩ - hf
    change p₁.2.1 = p₂.2.1 at hf
    rcases mem_newLocksM.1 hp₁ with ⟨-, B₁, h₁, rfl⟩ | ⟨B₁, h₁, rfl⟩ <;>
      rcases mem_newLocksM.1 hp₂ with ⟨-, B₂, h₂, rfl⟩ | ⟨B₂, h₂, rfl⟩
    · obtain rfl : B₁ = B₂ := Option.some_injective _ (h₁.symm.trans h₂)
      rfl
    · exact absurd hf Bool.noConfusion
    · exact absurd hf Bool.noConfusion
    · obtain rfl : B₁ = B₂ := Option.some_injective _ (h₁.symm.trans h₂)
      rfl

/-- The update at mode `m` as an `addLocksWith` of the parent's lock store, or no write. -/
private theorem updateConfirmationM_lockStep {m : WriteMode} (X : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (s : Nat) :
    (updateConfirmationM sp m X Φ t s).locks = X.locks ∨
      ∃ N, NewOK sp lockStore m.fastArm s N ∧
        (updateConfirmationM sp m X Φ t s).locks = lockStore.addLocksWith sp X.locks N Φ t := by
  cases hC : getConfirmation sp X Φ s with
  | none => exact Or.inl (updateConfirmationM_locks_of_none hC)
  | some C =>
    refine Or.inr ⟨_, newOK_newLocksM (A := X) (Φ := Φ) (t := t) (C := C)
      (sv := Function.update X.saved s (some C.root)) (L := X.locks), ?_⟩
    rw [updateConfirmationM_locks_of_some hC, addLocksWith_lockStore]

/-! ### The steps -/

/-- The locks of a call's input at mode `m` without the optimistic write are the state's. -/
private theorem callInputM_locks {m : WriteMode} (h : m.optimistic = false) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (c : (goldilocksSA sp FGP ro).Call) :
    (callInputM sp m A Φ t c).locks = A.locks := by
  cases c with
  | message v => rw [callInputM, optimisticConfirmationM_off h, (admitVote_keeps_locks _ _ _).1]
  | block B => rw [callInputM, optimisticConfirmationM_off h, (blockReceipt_keeps_locks _ _ _).1]
  | _ => rfl

/-- A kept or unlocked store that writes nothing is a lock step. -/
private theorem keep_lockStep {fa : Bool} {W L : Set Lock} {Φ : Frm sp.n FGP} {t : Time}
    (tk : Prop) (hL : L = W ∨ ∃ (σ : Type) (E : UnlockStage sp lockStore σ) (c : σ) (s : Int)
      (V : View sp.n), L = lockStore.unlockWith sp E c W Φ t s V) :
    LockStep sp lockStore fa W L Φ t tk :=
  (lockStep_iff _ _ _ _ _ _).2 ⟨L, hL.elim (fun h => Or.inl h) Or.inr, Or.inl rfl⟩

/-- The update after a kept or unlocked store, at a tick at `t_s + 2Δ`, is a lock step. -/
private theorem upd_lockStep {m : WriteMode} {W : Set Lock} {Φ : Frm sp.n FGP} {t : Time}
    {tk : Prop} (htk : tk) {X : SAState sp.n} (hX : X.locks = W ∨ ∃ (σ : Type)
      (E : UnlockStage sp lockStore σ) (c : σ) (s : Int) (V : View sp.n),
      X.locks = lockStore.unlockWith sp E c W Φ t s V)
    (hu : t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t) :
    LockStep sp lockStore m.fastArm W (updateConfirmationM sp m X Φ t (sp.slot t - 1)).locks Φ t
      tk := by
  rcases updateConfirmationM_lockStep (m := m) X Φ t (sp.slot t - 1) with he | ⟨N, hN, he⟩
  · rw [he]
    exact keep_lockStep tk hX
  · rw [he]
    exact (lockStep_iff _ _ _ _ _ _).2 ⟨X.locks, hX, Or.inr ⟨htk, hu.1, hu.2, N, hN, rfl⟩⟩

/-- **The parent's calls at mode `m` without the optimistic write are lock steps.** -/
theorem parent_lockStep {m : WriteMode} (h : m.optimistic = false) (self : Fin sp.n)
    (A : SAState sp.n) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} (ht : 0 ≤ t)
    (c : (goldilocksSA sp FGP ro).Call) :
    LockStep sp lockStore m.fastArm A.locks
      (stepWithM sp ro m self (parentUnlockM sp m A Φ t c) A Φ t c).1.locks Φ t
      (c = .tick) := by
  have hL₁ : parentUnlockM sp m A Φ t c = lockStore.unlockWith sp (UnlockStage.id sp lockStore Unit)
      () A.locks Φ t ((sp.slot t : Int) - 1) (callViewM sp m A Φ t c) := by
    rw [unlockWith_id_eq_unlock, parentUnlockM, callInputM_locks h]
  have hU : ∀ L, L = A.locks ∨ L = parentUnlockM sp m A Φ t c → L = A.locks ∨
      ∃ (σ : Type) (E : UnlockStage sp lockStore σ) (c' : σ) (s : Int) (V : View sp.n),
        L = lockStore.unlockWith sp E c' A.locks Φ t s V := by
    rintro L (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr ⟨Unit, _, (), _, _, hL₁⟩
  cases c with
  | tick =>
    simp only [stepWithM, acOnTickWithM]
    split_ifs <;> first
      | exact keep_lockStep _ (Or.inl rfl)
      | exact keep_lockStep _ (hU _ (tryVoteWithM_fields h _ _ _ _ _).1)
      | exact upd_lockStep trivial (hU _ (tryVoteWithM_fields h _ _ _ _ _).1) ‹_›
      | exact upd_lockStep trivial (Or.inl rfl) ‹_›
  | proposal => exact keep_lockStep _ (hU _ (acProposalWith_fields _ _ _ _).1)
  | toFG => exact keep_lockStep _ (Or.inl (acToFG_fields _ _ _).1)
  | message v =>
    simp only [stepWithM, acOnMessageWithM]
    rw [optimisticConfirmationM_off h]
    have := (tryVoteWithM_fields h self (parentUnlockM sp m A Φ t (.message v))
      (admitVote sp A t v) Φ t).1
    rw [(admitVote_keeps_locks _ _ _).1] at this
    exact keep_lockStep _ (hU _ this)
  | block B =>
    simp only [stepWithM, acOnBlockWithM]
    rw [optimisticConfirmationM_off h]
    have := (tryVoteWithM_fields h self (parentUnlockM sp m A Φ t (.block B))
      (blockReceipt sp A t B) Φ t).1
    rw [(blockReceipt_keeps_locks _ _ _).1] at this
    exact keep_lockStep _ (hU _ this)
  | restart =>
    simp only [stepWithM]
    rw [(restart_state sp FGP ro self A Φ t hΦ ht).2.1]
    exact keep_lockStep _ (Or.inl rfl)

/-- A kept row set is a row step. -/
private theorem keep_rowStep {R : Set Int} {X : SAState sp.n} {t : Time} (tk : Prop)
    (hX : ∀ j, X.saved j ≠ none → j ∈ R) : RowStep (sp := sp) R {j | X.saved j ≠ none} t tk :=
  (rowStep_iff _ _ _ _).2 fun j hj => Or.inl (hX j hj)

/-- The update of slot `slot(t) − 1` at a tick at `t_s + 2Δ` is a row step. -/
private theorem upd_rowStep {m : WriteMode} {R : Set Int} {Φ : Frm sp.n FGP} {t : Time}
    {tk : Prop} (htk : tk) {X : SAState sp.n} (hX : ∀ j, X.saved j ≠ none → j ∈ R)
    (hu : t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t) :
    RowStep (sp := sp) R {j | (updateConfirmationM sp m X Φ t (sp.slot t - 1)).saved j ≠ none} t
      tk := by
  refine (rowStep_iff _ _ _ _).2 fun j hj => ?_
  rcases updateConfirmationM_saved m X Φ t _ j hj with hj | rfl
  · exact Or.inl (hX j hj)
  · exact Or.inr ⟨htk, hu.1, hu.2, rfl⟩

/-- **The parent's calls at mode `m` without the optimistic write are row steps** of the saved
rows. -/
theorem parent_rowStep {m : WriteMode} (h : m.optimistic = false) (self : Fin sp.n)
    (L₁ : Set Lock) (A : SAState sp.n) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time}
    (ht : 0 ≤ t) (c : (goldilocksSA sp FGP ro).Call) :
    RowStep (sp := sp) {j | A.saved j ≠ none}
      {j | (stepWithM sp ro m self L₁ A Φ t c).1.saved j ≠ none} t (c = .tick) := by
  have same : ∀ X : SAState sp.n, X.saved = A.saved → ∀ j, X.saved j ≠ none →
      j ∈ {j | A.saved j ≠ none} := fun X hX j hj => by rw [← hX]; exact hj
  cases c with
  | tick =>
    simp only [stepWithM, acOnTickWithM]
    split_ifs <;> first
      | exact keep_rowStep _ (same _ rfl)
      | exact keep_rowStep _ (same _ (tryVoteWithM_fields h _ _ _ _ _).2)
      | exact upd_rowStep trivial (same _ (tryVoteWithM_fields h _ _ _ _ _).2) ‹_›
      | exact upd_rowStep trivial (same _ rfl) ‹_›
  | proposal => exact keep_rowStep _ (same _ (acProposalWith_fields _ _ _ _).2)
  | toFG => exact keep_rowStep _ (same _ (acToFG_fields _ _ _).2)
  | message v =>
    simp only [stepWithM, acOnMessageWithM]
    refine keep_rowStep _ (same _ ?_)
    rw [(tryVoteWithM_fields h _ _ _ _ _).2, optimisticConfirmationM_off h, admitVote_saved]
  | block B =>
    simp only [stepWithM, acOnBlockWithM]
    refine keep_rowStep _ (same _ ?_)
    rw [(tryVoteWithM_fields h _ _ _ _ _).2, optimisticConfirmationM_off h, blockReceipt_saved]
  | restart =>
    refine keep_rowStep _ fun j hj => ?_
    simp only [stepWithM] at hj
    rw [(restart_state sp FGP ro self A Φ t hΦ ht).2.2.2.1] at hj
    exact absurd rfl hj

/-! ### Along a trace of the parent's stage -/

variable {m : WriteMode} {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}

private theorem frameOK_of_callU {u : Nat → Set Lock} (h : ACLocalRunU m u H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) :
    FrameOK ℓ.frame := by
  rcases h.frameLaw y hy i ℓ hc with ⟨-, Φ₀, -, -, hk⟩ | ⟨-, ℓ₀, -, -, -, hk⟩ <;> exact hk.1.1

/-- A call of an honest node of the parent's stage at mode `m` is the step at the parent's
unlock of the call. -/
private theorem post_eq (h : ACLocalRunU m (parentOracleM sp m tr) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) :
    tr.post i = (stepWithM sp ro m y (parentUnlockM sp m (tr.state y i) ℓ.frame (tr.time i) ℓ.call)
      (tr.state y i) ℓ.frame (tr.time i) ℓ.call).1 := by
  have he := h.exec i ℓ hc.2 (hc.1 ▸ hy)
  simp only [parentOracleM, hc.2, hc.1] at he
  rw [he]

/-- **The parent's stage at mode `m` without the optimistic write: lock memory and working
rows.** On an AC trace of the parent's stage at mode `m` (the unlock given by the parent's unlock
at mode `m`) with one tick per honest node and time, every honest node holds before each cut at
most `(fast arm ? 2 : 1) · k` unexpired locks, saves no row of a slot `≥ slot(t)`, and holds at
most `max w 1` saved rows of the slots `slot(t) − max w 1 ≤ j`, at every `w`. -/
theorem parent_lockMemory (hopt : m.optimistic = false)
    (h : ACLocalRunU m (parentOracleM sp m tr) H U tr)
    (hone : ∀ y ∈ H, ∀ i j (ℓ ℓ' : ACLabel (goldilocksSA sp FGP ro)), tr.CallAt y i ℓ →
      tr.CallAt y j ℓ' → ℓ.call = .tick → ℓ'.call = .tick → tr.time i = tr.time j → i = j)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    {l | l ∈ (tr.state y i).locks ∧ l.LiveAt sp (tr.time i)}.encard ≤
        ((if m.fastArm then 2 else 1) * sp.k : ℕ) ∧
      (∀ j : Int, (tr.state y i).saved j ≠ none → j < sp.slot (tr.time i)) ∧
      ∀ w : Nat, {j : Int | (sp.slot (tr.time i) : Int) - (max w 1 : Nat) ≤ j ∧
        (tr.state y i).saved j ≠ none}.encard ≤ (max w 1 : ℕ) := by
  have h0 : tr.state y 0 = SAState.initial sp.genesisRoot := h.init y hy
  have hinv := lockInv_of_steps (tr := tr) (y := y) lockStore_lawful SAState.locks m.fastArm
    (by rw [h0]; rfl) (fun i ℓ hc => by
      have hΦ := frameOK_of_callU h hy hc
      refine ⟨ℓ.frame, hΦ.coherent.1, ?_⟩
      rw [post_eq h hy hc]
      exact parent_lockStep hopt y _ hΦ (h.time_nonneg i) ℓ.call)
    (hone y hy) i
  have hrows := rowInv_of_steps (tr := tr) (y := y) (fun A => {j | A.saved j ≠ none})
    (by rw [h0]; ext j; simp [SAState.initial]) (fun i ℓ hc => by
      have hΦ := frameOK_of_callU h hy hc
      rw [post_eq h hy hc]
      exact parent_rowStep hopt y _ _ hΦ (h.time_nonneg i) ℓ.call) i
  have hlt := row_lt_slot (tr := tr) h.time_mono (h.time_nonneg i) hrows
  refine ⟨held_encard_le h.time_mono (h.time_nonneg i) hinv, fun j hj => hlt j hj,
    fun w => ?_⟩
  exact rows_encard_le (R := {j | (tr.state y i).saved j ≠ none}) hlt (max w 1)

end Consensus.Goldilocks.SA

end
