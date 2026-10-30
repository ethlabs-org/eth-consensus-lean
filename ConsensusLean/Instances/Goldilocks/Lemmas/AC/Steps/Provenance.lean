module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Statements.AC.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Tree

public section

/-! # Goldilocks SA: where a node's fast locks come from

Every fast lock that an honest node holds sits below (inside `U`) the block of a fast lock of the
same slot that the node itself wrote at an earlier cut, by the fast test of an update
(`FastUpdateAt`) or by an optimistic confirmation (`OptimisticLockAt`): the SA's lock functions
only move locks back (A0.4 (c)), a restart keeps the locks (A0.7), and the only writers of fast
locks are those two events. A1.5 and A1.9 read this. -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

/-! ## Locks that sit below others -/

/-- The block of `l'` is an ancestor (inside `U`) of the block of `l`, or `l' = l`. -/
private def SitsBelow (U : Set (Blk sp.n FGP)) (l' l : Lock) : Prop :=
  l' = l ∨ ∃ L₁ ∈ U, L₁.root = l'.block ∧ ∃ L₂ ∈ U, L₂.root = l.block ∧ Anc U L₁ L₂

/-- The block of `l` is in `U` and an ancestor of `B` there. -/
private def Below (U : Set (Blk sp.n FGP)) (l : Lock) (B : Blk sp.n FGP) : Prop :=
  ∃ L ∈ U, L.root = l.block ∧ Anc U L B

/-- Every fast lock of `L'` sits below a fast lock of `L` with its slot, or below a block `B`
with `New l'.slot B`. -/
private def FromP (U : Set (Blk sp.n FGP)) (L L' : Set Lock) (New : Nat → Blk sp.n FGP → Prop) :
    Prop :=
  ∀ l' ∈ L', l'.fast = true →
    (∃ l ∈ L, l.fast = true ∧ l'.slot = l.slot ∧ SitsBelow U l' l) ∨
      ∃ B, New l'.slot B ∧ Below U l' B

private theorem FromP.of_eq {U : Set (Blk sp.n FGP)} {L L' : Set Lock}
    {New : Nat → Blk sp.n FGP → Prop} (h : L' = L) : FromP U L L' New := by
  subst h
  exact fun l hl hf => Or.inl ⟨l, hl, hf, rfl, Or.inl rfl⟩

private theorem FromP.mono {U : Set (Blk sp.n FGP)} {L L' : Set Lock}
    {New New' : Nat → Blk sp.n FGP → Prop} (h : FromP U L L' New)
    (hN : ∀ s B, New s B → New' s B) : FromP U L L' New' := fun l hl hf =>
  (h l hl hf).imp_right fun ⟨B, h1, h2⟩ => ⟨B, hN _ _ h1, h2⟩

private theorem FromP.trans {U : Set (Blk sp.n FGP)} (hU : Coherent U) {L₁ L₂ L₃ : Set Lock}
    {New : Nat → Blk sp.n FGP → Prop} (h₁ : FromP U L₁ L₂ New) (h₂ : FromP U L₂ L₃ New) :
    FromP U L₁ L₃ New := by
  intro l₃ hl₃ hf₃
  rcases h₂ l₃ hl₃ hf₃ with ⟨l₂, hl₂, hf₂, hs₂, hb₂⟩ | ⟨B, hN, hB⟩
  · rcases h₁ l₂ hl₂ hf₂ with ⟨l₁, hl₁, hf₁, hs₁, hb₁⟩ | ⟨B, hN, L, hL, hLr, hLB⟩
    · refine Or.inl ⟨l₁, hl₁, hf₁, hs₂.trans hs₁, ?_⟩
      rcases hb₂ with rfl | ⟨A₁, hA₁, hA₁r, A₂, hA₂, hA₂r, hA⟩
      · exact hb₁
      rcases hb₁ with rfl | ⟨C₁, hC₁, hC₁r, C₂, hC₂, hC₂r, hC⟩
      · exact Or.inr ⟨A₁, hA₁, hA₁r, A₂, hA₂, hA₂r, hA⟩
      have : A₂ = C₁ := hU.1 hA₂ hC₁ (hA₂r.trans hC₁r.symm)
      subst this
      exact Or.inr ⟨A₁, hA₁, hA₁r, C₂, hC₂, hC₂r, hA.trans hC⟩
    · refine Or.inr ⟨B, hs₂ ▸ hN, ?_⟩
      rcases hb₂ with rfl | ⟨A₁, hA₁, hA₁r, A₂, hA₂, hA₂r, hA⟩
      · exact ⟨L, hL, hLr, hLB⟩
      have : A₂ = L := hU.1 hA₂ hL (hA₂r.trans hLr.symm)
      subst this
      exact ⟨A₁, hA₁, hA₁r, hA.trans hLB⟩
  · exact Or.inr ⟨B, hN, hB⟩

/-- Locks that move back in a frame inside `U` sit below the locks they come from. -/
private theorem FromP.of_movesBack {U : Set (Blk sp.n FGP)} {Φ : Frm sp.n FGP}
    (hΦ : Φ.tree ⊆ U) {L L' : Set Lock} {New : Nat → Blk sp.n FGP → Prop}
    (h : MovesBack sp Φ L L') : FromP U L L' New := by
  intro l' hl' hf
  obtain ⟨l, hl, hs, hfa, B, hB, hBr, B', hB', hB'r, hA⟩ := h l' hl'
  exact Or.inl ⟨l, hl, hfa ▸ hf, hs, Or.inr ⟨B', hΦ hB', hB'r, B, hΦ hB, hBr,
    hA.mono hΦ⟩⟩

/-- `add_locks` with new locks: the new fast locks are on the blocks of `N`'s fast entries. -/
private theorem FromP.of_addLocks {U : Set (Blk sp.n FGP)} (hU : Coherent U) {Φ : Frm sp.n FGP}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {L : Set Lock} {t : Time} {s : Nat}
    {N : Set (Nat × Bool)} {New : Nat → Blk sp.n FGP → Prop} {L₀ : Set Lock} (hL : L₀ = L)
    (hN : ∀ r, (r, true) ∈ N → ∃ B ∈ Φ.tree, B.root = r ∧ New s B) :
    FromP U L (addLocks sp L₀ Φ t s N) New := by
  subst hL
  intro l' hl' hf
  obtain ⟨l, hl, hs, hfa, B, hB, hBr, B', hB', hB'r, hA⟩ :=
    ((locks_move_back sp) FGP Φ L₀ t hΦ).2.1 s N l' hl'
  rcases hl with hl | ⟨p, hp, rfl⟩
  · exact Or.inl ⟨l, hl, hfa ▸ hf, hs, Or.inr ⟨B', hΦU hB', hB'r, B, hΦU hB, hBr,
      Goldilocks.Anc.mono hΦU hA⟩⟩
  · obtain ⟨r, b⟩ := p
    simp only at hfa hs hBr
    subst hfa
    obtain ⟨D, hD, hDr, hND⟩ := hN r (hf ▸ hp)
    have : B = D := hU.1 (hΦU hB) (hΦU hD) (hBr.trans hDr.symm)
    subst this
    exact Or.inr ⟨B, hs ▸ hND, B', hΦU hB', hB'r, Goldilocks.Anc.mono hΦU hA⟩

/-! ## What each SA function does to the locks -/

private theorem admitVote_locks (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).locks = A.locks := by
  unfold admitVote
  split_ifs <;> rfl

private theorem blockReceipt_locks (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).locks = A.locks := by
  unfold blockReceipt
  generalize hA' : ({ A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) } :
    SAState sp.n) = A'
  have : A'.locks = A.locks := by rw [← hA']
  rw [← this]
  clear hA' this
  induction (blockVotes B) generalizing A' with
  | nil => rfl
  | cons v l ih => rw [List.foldl_cons, ih, admitVote_locks]

private theorem updateLatestConfirmed_locks (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (C : Blk sp.n FGP) : (updateLatestConfirmed sp A Φ C).locks = A.locks := by
  unfold updateLatestConfirmed
  split_ifs <;> rfl

variable {U : Set (Blk sp.n FGP)} {Φ : Frm sp.n FGP}

private theorem FromP.of_optimistic (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    (A : SAState sp.n) (t : Time) :
    FromP U A.locks (optimisticConfirmation sp A Φ t).locks
      (fun s B => s = sp.slot t ∧ optimisticSelect sp A Φ t = some B) := by
  unfold optimisticConfirmation
  rcases h : optimisticSelect sp A Φ t with _ | B
  · exact FromP.of_eq rfl
  · rw [updateLatestConfirmed_locks]
    refine FromP.of_addLocks hU hΦ hΦU rfl fun r hr => ?_
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, and_true] at hr
    subst hr
    have hB := h
    unfold optimisticSelect at hB
    dsimp only at hB
    split_ifs at hB
    exact ⟨B, (deepest_mem hB).1.1, rfl, rfl, rfl⟩

private theorem FromP.of_optimistic_admit (hU : Coherent U) (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {L : Set Lock} (A : SAState sp.n) (hL : A.locks = L) (t : Time)
    (v : Vote sp.n) :
    FromP U L (optimisticConfirmation sp (admitVote sp A t v) Φ t).locks
      (fun s B => s = sp.slot t ∧ optimisticSelect sp (admitVote sp A t v) Φ t = some B) := by
  have := FromP.of_optimistic hU hΦ hΦU (admitVote sp A t v) t
  rwa [admitVote_locks, hL] at this

private theorem FromP.of_tryVote (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    (x : Fin sp.n) (A : SAState sp.n) (t : Time) :
    FromP U A.locks (tryVote sp x A Φ t).1.locks
      (fun s B => ∃ e ∈ (tryVote sp x A Φ t).2, s = sp.slot t ∧
        optimisticSelect sp (admitVote sp e.readPoint t e.msg) Φ t = some B) := by
  unfold tryVote
  dsimp only
  split_ifs with h1 h2 h3
  · exact FromP.of_eq rfl
  · exact FromP.of_eq rfl
  · refine FromP.trans hU (FromP.of_movesBack hΦU
      (((locks_move_back sp) FGP Φ A.locks t hΦ).2.2 ((sp.slot t : Int) - 1)
        (mergedVoteView sp A Φ (sp.slot t))))
      (FromP.mono (FromP.of_optimistic_admit hU hΦ hΦU _ ?_ t _) ?_)
    · rfl
    · exact fun s B h => ⟨_, List.mem_singleton_self _, h⟩
  · refine FromP.mono (FromP.of_optimistic_admit hU hΦ hΦU _ ?_ t _) ?_
    · rfl
    · exact fun s B h => ⟨_, List.mem_singleton_self _, h⟩

private theorem FromP.of_updateConfirmation (hU : Coherent U) (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) (A : SAState sp.n) (t : Time) (s : Nat) :
    FromP U A.locks (updateConfirmation sp A Φ t s).locks
      (fun s' B => s' = s ∧ ∃ C, getConfirmation sp A Φ s = some C ∧
        ¬ conflictsWithLock sp A.locks Φ t C ∧ fastSelect sp A Φ s C = some B) := by
  unfold updateConfirmation
  dsimp only
  rcases hC : getConfirmation sp A Φ s with _ | C
  · exact FromP.of_eq rfl
  · dsimp only
    split_ifs with hconf
    · exact FromP.of_eq rfl
    · refine FromP.of_addLocks hU hΦ hΦU (updateLatestConfirmed_locks _ _ _) fun r hr => ?_
      rcases hr with ⟨D, hD, hr⟩ | ⟨-, D, -, hr⟩
      · simp only [Prod.mk.injEq, and_true] at hr
        subst hr
        exact ⟨D, (deepest_mem hD).1.1.1, rfl, rfl, C, rfl, hconf, hD⟩
      · simp at hr

private theorem FromP.of_onTick (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    (x : Fin sp.n) (A : SAState sp.n) (t : Time) :
    FromP U A.locks (acOnTick sp x A Φ t).1.locks
      (fun s B => (∃ e ∈ (acOnTick sp x A Φ t).2, s = sp.slot t ∧
        optimisticSelect sp (admitVote sp e.readPoint t e.msg) Φ t = some B) ∨
        (t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t ∧ joined sp A t ∧
          s = sp.slot t - 1 ∧ ∃ C, getConfirmation sp A Φ s = some C ∧
          ¬ conflictsWithLock sp A.locks Φ t C ∧ fastSelect sp A Φ s C = some B)) := by
  unfold acOnTick
  dsimp only
  split_ifs with hj ht hu hu
  · exfalso
    have := sp.toParams.hΔ
    linarith [ht.1.symm.trans hu]
  · refine (FromP.of_updateConfirmation hU hΦ hΦU A t _).mono fun s B h => ?_
    obtain ⟨rfl, h2⟩ := h
    exact Or.inr ⟨ht.1, ht.2, hj, rfl, h2⟩
  · exact (FromP.of_tryVote hU hΦ hΦU x A t).mono fun s B h => Or.inl h
  · exact FromP.of_eq rfl
  · exact FromP.of_eq rfl

private theorem FromP.of_proposal (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) (A : SAState sp.n)
    (t : Time) {New : Nat → Blk sp.n FGP → Prop} :
    FromP U A.locks (acProposal sp A Φ t).1.locks New := by
  unfold acProposal
  dsimp only
  split_ifs
  · exact FromP.of_movesBack hΦU (((locks_move_back sp) FGP Φ A.locks t hΦ).2.2 _ _)
  · exact FromP.of_eq rfl

private theorem toFG_locks (A : SAState sp.n) (t : Time) :
    (acToFG sp A Φ t).1.locks = A.locks := by
  unfold acToFG
  dsimp only
  split_ifs
  · split
    · rfl
    · split_ifs <;> rfl
  · rfl

/-! ## Over an SA trace -/

variable {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)} {tr : SATrace sp FGP ro}

private theorem frameIn_of_call (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
  rcases hr.frameLaw x hx i ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1

/-- A call of an honest node keeps its fast locks below earlier ones or writes fast locks of
its own cut. -/
private theorem call_fromP (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    FromP U (tr.state x i).locks (tr.post i).locks
      (fun s B => ∃ CV, FastLockAt tr x i s B CV) := by
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_call hr hx hc
  have hU := hr.coherent
  have he := hr.exec i ℓ hc.2 (hc.1 ▸ hx)
  rw [hc.1] at he
  have hpost := congrArg Prod.fst he
  have hemits := congrArg Prod.snd he
  simp only at hpost hemits
  rw [← hpost]
  generalize hA : tr.state x i = A at hpost hemits
  cases hcall : ℓ.call with
  | tick =>
    rw [hcall] at hemits
    refine (FromP.of_onTick hU hΦ hΦU x A _).mono fun s B h => ?_
    rcases h with ⟨e, he', hs, hsel⟩ | ⟨ht, hs0, hj, hs, C, hC, hconf, hD⟩
    · exact ⟨_, Or.inr ⟨ℓ, _, ⟨hc, Or.inr (Or.inr ⟨e, hemits ▸ he', rfl⟩)⟩, hs.symm, hsel, rfl⟩⟩
    · refine ⟨_, Or.inl ⟨ℓ, C, ⟨hc, hcall, ?_, hA ▸ hj⟩, hA ▸ hC, hA ▸ hconf, hA ▸ hD, rfl⟩⟩
      rw [hs]
      conv_lhs => rw [ht]
      simp only [SAParams.ts]
      push_cast [Nat.cast_sub hs0]
      ring
  | proposal => exact FromP.of_proposal hΦ hΦU A _
  | toFG => exact FromP.of_eq (toFG_locks A _)
  | message m =>
    rw [hcall] at hemits
    refine FromP.trans hU ((FromP.of_optimistic_admit hU hΦ hΦU A rfl _ m).mono
      fun s B h => ?_) ((FromP.of_tryVote hU hΦ hΦU x _ _).mono fun s B h => ?_)
    · exact ⟨_, Or.inr ⟨ℓ, _, ⟨hc, Or.inl ⟨m, hcall, hA ▸ rfl⟩⟩, h.1.symm, h.2, rfl⟩⟩
    · obtain ⟨e, he', hs, hsel⟩ := h
      exact ⟨_, Or.inr ⟨ℓ, _, ⟨hc, Or.inr (Or.inr ⟨e, hemits ▸ he', rfl⟩)⟩, hs.symm, hsel, rfl⟩⟩
  | block B =>
    rw [hcall] at hemits
    have h₁ := FromP.of_optimistic hU hΦ hΦU (blockReceipt sp A (tr.time i) B) (tr.time i)
    rw [blockReceipt_locks] at h₁
    refine FromP.trans hU (h₁.mono fun s B' h => ?_)
      ((FromP.of_tryVote hU hΦ hΦU x _ _).mono fun s B' h => ?_)
    · exact ⟨_, Or.inr ⟨ℓ, _, ⟨hc, Or.inr (Or.inl ⟨B, hcall, hA ▸ rfl⟩)⟩, h.1.symm, h.2, rfl⟩⟩
    · obtain ⟨e, he', hs, hsel⟩ := h
      exact ⟨_, Or.inr ⟨ℓ, _, ⟨hc, Or.inr (Or.inr ⟨e, hemits ▸ he', rfl⟩)⟩, hs.symm, hsel, rfl⟩⟩
  | restart =>
    exact FromP.of_eq ((restart_state sp) FGP ro x A ℓ.frame (tr.time i) hΦ
      (hr.time_nonneg i)).2.1

private theorem Below.of_sitsBelow (hU : Coherent U) {l' l : Lock} {B : Blk sp.n FGP}
    (h : SitsBelow U l' l) (hB : Below U l B) : Below U l' B := by
  rcases h with rfl | ⟨A₁, hA₁, hA₁r, A₂, hA₂, hA₂r, hA⟩
  · exact hB
  obtain ⟨L, hL, hLr, hLB⟩ := hB
  have : A₂ = L := hU.1 hA₂ hL (hA₂r.trans hLr.symm)
  subst this
  exact ⟨A₁, hA₁, hA₁r, hA.trans hLB⟩

/-- **Fast-lock provenance.** Every fast lock that an honest node holds before cut `i` sits below
the block of a fast lock of its slot that the node wrote at an earlier cut. -/
theorem fast_lock_provenance (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state x i).locks, l.fast = true →
      ∃ j < i, ∃ B CV, FastLockAt tr x j l.slot B CV ∧ ∃ L ∈ U, L.root = l.block ∧ Anc U L B := by
  induction i with
  | zero =>
    intro l hl
    change l ∈ (tr.init x).locks at hl
    rw [hr.init x hx] at hl
    exact absurd hl (Set.notMem_empty l)
  | succ i ih =>
    intro l hl hf
    rw [Trace.state] at hl
    split_ifs at hl with hnode
    · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 hnode.2
      rcases call_fromP hr hx ⟨hnode.1, hℓ⟩ l hl hf with ⟨l₀, hl₀, hf₀, hs, hb⟩ | ⟨B, ⟨CV, h⟩, hB⟩
      · obtain ⟨j, hj, B, CV, h, hB⟩ := ih l₀ hl₀ hf₀
        exact ⟨j, hj.trans (Nat.lt_succ_self i), B, CV, hs ▸ h,
          Below.of_sitsBelow hr.coherent hb hB⟩
      · exact ⟨i, Nat.lt_succ_self i, B, CV, h, hB⟩
    · obtain ⟨j, hj, h⟩ := ih l hl hf
      exact ⟨j, hj.trans (Nat.lt_succ_self i), h⟩

end Consensus.Goldilocks.SA

end
