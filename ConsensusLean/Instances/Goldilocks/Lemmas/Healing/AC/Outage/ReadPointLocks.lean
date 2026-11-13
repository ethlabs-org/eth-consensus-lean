module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.ReadPoint
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLock
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Saved
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Fast locks and read-point locks over AC traces with the unlock given

Over an AC trace of the SA with the unlock given at a write mode (`ACLocalRunU wm u`,
`ACRunU wm u`), with the honest blocks read as `U`:

* `fastLock_countedU` (`SA.fastLock_counted` with the unlock given): the counted votes of an
  honest fast lock of slot `s` on `B` have at least half of the committee as validators, and each
  is a slot-`s` vote whose head, of slot at most `s`, extends `B` inside `U`;
* `readPoint_locks_provenance_strictAC` (`SA.readPoint_locks_provenance_strict` with the unlock
  given): every lock of an honest vote's read point names a block of the call's frame below a
  lock stored before the call, or below the receipt's optimistic selection, whose counted honest
  votes were cast at earlier cuts. The unlock is read only through the unlock relation
  (`UnlockRel.movesBack`). -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {wm : WriteMode} {u : Nat → Set Lock}
  {proposer : Nat → Fin sp.n}

/-- `SA.fastLock_counted` with the unlock given: the counted votes of an honest fast lock of slot
`s` on `B` have at least half of the committee as validators, and each is a slot-`s` vote whose
head, of slot at most `s`, extends `B` inside `U`. -/
theorem fastLock_countedU
    (hr : ACLocalRunU wm u H U tr) {w : Fin sp.n} (hw : w ∈ H)
    {i₀ s : Nat} {B : Blk sp.n FGP} {CV : Set (Vote sp.n)} (hfl : FastLockAt tr w i₀ s B CV) :
    sp.committeeSize ≤ 2 * {x | ∃ v ∈ CV, v.val = x}.ncard ∧
      ∀ v ∈ CV, v.slot = s ∧ ∃ R ∈ U, R.root = v.head ∧ R.slot ≤ s ∧ Anc U B R := by
  rcases hfl with ⟨ℓ, C, ⟨hc, -, -, -⟩, -, hD, rfl⟩ | ⟨ℓ, A, hpt, hsl, hsel, rfl⟩
  · obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hw hc
    refine ⟨?_, ?_⟩
    · have hfast := (deepest_mem hD).1.2.2
      unfold FastTest confirmationScore at hfast
      refine hfast.trans (Nat.mul_le_mul_left 2 (Set.ncard_le_ncard ?_))
      rintro x ⟨hx, y, ⟨hy, hres⟩, hval, -, hanc⟩
      exact ⟨y, ⟨hy, hval ▸ hx, hres, hanc⟩, hval⟩
    · rintro v ⟨hvp, -, hres, R, hR, hRr, hBR⟩
      have hvs := state_pool_slotU sp hr hw i₀ s v hvp
      refine ⟨hvs, R, hΦU hR, hRr, ?_, Anc.mono hΦU hBR⟩
      unfold resolutionTime at hres
      split at hres
      · exact absurd hres (by simp [ETime.of])
      · rename_i Hd hl
        obtain ⟨hHd, hHdr⟩ := lookup_eq_some hl
        obtain rfl : Hd = R := hΦ.coherent.1 hHd hR (hHdr.trans hRr.symm)
        split_ifs at hres with hlt
        · exact absurd hres (by simp [ETime.of])
        · omega
  · obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hw hpt.1
    unfold optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel
    have h34 := (deepest_mem hsel).1.2.1
    refine ⟨?_, ?_⟩
    · have hsub : optimisticVoters sp A ℓ.frame (sp.slot (tr.time i₀)) B ⊆
          {x | ∃ v ∈ {v | v ∈ A.pool s ∧ AncR ℓ.frame B v.head}, v.val = x} := by
        rintro x ⟨v, hv, rfl, hanc⟩
        exact ⟨v, ⟨hsl ▸ hv, hanc⟩, rfl⟩
      have := Set.ncard_le_ncard hsub
      omega
    · rintro v ⟨hv, R, hR, hRr, hBR⟩
      refine ⟨optimisticPoint_pool_slotU hr hw hpt hv, R, hΦU hR, hRr, ?_, Anc.mono hΦU hBR⟩
      have := frame_slot_leU sp hr hw hpt.1 R hR
      omega

private theorem admit_pool_memAC {A : SAState sp.n} {t : Time} {m v : Vote sp.n} {σ : Nat}
    (h : v ∈ (admitVote sp A t m).pool σ) : v ∈ A.pool σ ∨ v = m ∧ m.slot = σ := by
  unfold admitVote at h
  split_ifs at h
  · exact Or.inl h
  · exact Or.inl h
  · simp only [Function.update_apply] at h
    split_ifs at h with hs
    · subst hs
      rcases List.mem_append.1 h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨List.mem_singleton.1 h, rfl⟩
    · exact Or.inl h

private theorem receipt_pool_memAC {A : SAState sp.n} {t : Time} {B : Blk sp.n FGP}
    {v : Vote sp.n} {σ : Nat} (h : v ∈ (blockReceipt sp A t B).pool σ) :
    v ∈ A.pool σ ∨ v ∈ blockVotes B ∧ v.slot = σ := by
  have key : ∀ (l : List (Vote sp.n)) (A₀ : SAState sp.n),
      v ∈ (l.foldl (fun A v => admitVote sp A t v) A₀).pool σ →
        v ∈ A₀.pool σ ∨ v ∈ l ∧ v.slot = σ := by
    intro l
    induction l with
    | nil => exact fun _ h => Or.inl h
    | cons x l ih =>
      intro A₀ h
      rcases ih _ h with h | h
      · rcases admit_pool_memAC h with h | ⟨rfl, hs⟩
        · exact Or.inl h
        · exact Or.inr ⟨List.mem_cons_self, hs⟩
      · exact Or.inr ⟨List.mem_cons_of_mem _ h.1, h.2⟩
  unfold blockReceipt at h
  exact (key _ _ h :)

/-- The honest votes of a pool after the receipt of a message or a block at cut `j` were emitted
before `j`. -/
private theorem receipt_pool_voteAC (hrun : ACRunU wm u proposer tr H U) {y : Fin sp.n}
    (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y j ℓ)
    {A : SAState sp.n}
    (h : (∃ m, ℓ.call = .message m ∧ A = admitVote sp (tr.state y j) (tr.time j) m) ∨
      ∃ B, ℓ.call = .block B ∧ A = blockReceipt sp (tr.state y j) (tr.time j) B)
    {σ : Nat} {v : Vote sp.n} (hv : v ∈ A.pool σ) (hvH : v.val ∈ H) :
    ∃ j' < j, ∃ e', VoteAt tr v.val j' e' ∧ e'.msg = v := by
  rcases h with ⟨m, hm, rfl⟩ | ⟨B, hB, rfl⟩
  · rcases admit_pool_memAC hv with hv | ⟨rfl, -⟩
    · exact hrun.honest.pool_vote y hy j σ v hv hvH
    · exact hrun.honest.message_vote y hy j ℓ _ hc hm hvH
  · rcases receipt_pool_memAC hv with hv | ⟨hv, -⟩
    · exact hrun.honest.pool_vote y hy j σ v hv hvH
    · exact hrun.honest.carried_vote y hy j ℓ hc B
        ((accept_newU sp hrun.localRun hy ⟨ℓ, hc, hB⟩).1 ℓ hc) v hv hvH

/-- `SA.readPoint_locks_provenance_strict` with the unlock given: at an honest vote of a slot
`> 0`, every lock of the read point names a frame block below the block of a stored lock, or below
the block that the receipt's optimistic check at the same cut selects, whose counted honest votes
were cast at cuts before `i`. The read-point locks move back from the call's unlock input
(`UnlockRel.movesBack`). -/
theorem readPoint_locks_provenance_strictAC (hrun : ACRunU wm u proposer tr H U) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} {e : Em sp FGP}
    (hc : CastAt tr y i ℓ e) (hpos : 0 < sp.slot (tr.time i)) :
    ∀ l' ∈ e.readPoint.locks, ∃ B' ∈ ℓ.frame.tree, B'.root = l'.block ∧
      ((∃ l ∈ (tr.state y i).locks, ∃ B ∈ ℓ.frame.tree, B.root = l.block ∧ ℓ.frame.Anc B' B) ∨
       ∃ B CV, OptimisticLockAt tr y i (sp.slot (tr.time i)) B CV ∧
         (∀ v ∈ CV, v.val ∈ H → ∃ j < i, ∃ e', VoteAt tr v.val j e' ∧ e'.msg = v) ∧
         ℓ.frame.Anc B' B) := by
  have hr := hrun.localRun
  obtain ⟨P, he, hPi, -, -⟩ := vote_tryVote_inputU hr hy hc
  have hΦ := (frameIn_of_callAtU hr hy hc.1).1
  have hlaw := hr.lawfulAt hy hc.1 hΦ
  rw [← hPi] at hlaw
  intro l' hl'
  rw [tryVote_readPoint_locks_eqWith he] at hl'
  simp only [hpos, ↓reduceIte] at hl'
  obtain ⟨l₁, hl₁, -, -, -, B₁, hB₁, hB₁r, B', hB', hB'r, hA⟩ := hlaw.movesBack hΦ l' hl'
  refine ⟨B', hB', hB'r, ?_⟩
  subst hPi
  have opt : ∀ A : SAState sp.n, OptimisticPoint tr y i ℓ A →
      ((∃ m, ℓ.call = .message m ∧ A = admitVote sp (tr.state y i) (tr.time i) m) ∨
        ∃ B, ℓ.call = .block B ∧ A = blockReceipt sp (tr.state y i) (tr.time i) B) →
      A.locks = (tr.state y i).locks →
      l₁ ∈ (optimisticConfirmationM sp wm A ℓ.frame (tr.time i)).locks →
      ((∃ l ∈ (tr.state y i).locks, ∃ B ∈ ℓ.frame.tree, B.root = l.block ∧
          ℓ.frame.Anc B' B) ∨
        ∃ B CV, OptimisticLockAt tr y i (sp.slot (tr.time i)) B CV ∧
          (∀ v ∈ CV, v.val ∈ H → ∃ j < i, ∃ e', VoteAt tr v.val j e' ∧ e'.msg = v) ∧
          ℓ.frame.Anc B' B) := by
    intro A hpt hrcpt hAl hl₁
    rw [optimisticConfirmationM_eq] at hl₁
    split_ifs at hl₁
    · unfold optimisticConfirmation at hl₁
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
          fun v hv hvH => receipt_pool_voteAC hrun hy hc.1 hrcpt hv.1 hvH, hA.trans hA'⟩
    · exact Or.inl ⟨l₁, hAl ▸ hl₁, B₁, hB₁, hB₁r, hA⟩
  cases hcall : ℓ.call with
  | message m =>
    rw [hcall] at hl₁
    exact opt _ ⟨hc.1, Or.inl ⟨m, hcall, rfl⟩⟩ (Or.inl ⟨m, hcall, rfl⟩)
      (admitVote_locks_eq _ _ _) hl₁
  | block C =>
    rw [hcall] at hl₁
    exact opt _ ⟨hc.1, Or.inr (Or.inl ⟨C, hcall, rfl⟩)⟩ (Or.inr ⟨C, hcall, rfl⟩)
      (blockReceipt_locks _ _ _) hl₁
  | tick => rw [hcall] at hl₁; exact Or.inl ⟨l₁, hl₁, B₁, hB₁, hB₁r, hA⟩
  | proposal => rw [hcall] at hl₁; exact Or.inl ⟨l₁, hl₁, B₁, hB₁, hB₁r, hA⟩
  | toFG => rw [hcall] at hl₁; exact Or.inl ⟨l₁, hl₁, B₁, hB₁, hB₁r, hA⟩
  | restart => rw [hcall] at hl₁; exact Or.inl ⟨l₁, hl₁, B₁, hB₁, hB₁r, hA⟩

end Consensus.Goldilocks.SA

end
