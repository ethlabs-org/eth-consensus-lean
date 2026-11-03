module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Defs

public section

/-! # Goldilocks Healing, HR.4: stored fast-lock provenance

`SA.fast_lock_provenance` places every fast lock below the **raw** selection `D` of a fast-lock
write; HR.4's rows need the **stored** block `O = Φ.viableAncestor D` of that write (`Φ` the frame
of the writing call), since `Q ⪯ D` and `O ⪯ D` do not give `Q ⪯ O` (`hr4-cut-scope.md` §4).
`stored_fast_lock_provenance` keeps `O`: `add_locks` stores exactly `O` (`liveLocks` moves the new
lock to its viable ancestor), the lock functions only move locks back (A0.4 (c)), a restart keeps
the locks (A0.7), and every insertion is an optimistic check or the fast test of an update, in
the frame of the call that runs it. A fast-lock write is joined (`joined_of_fastLockAt`): the
update's guard, or the optimistic check's guard at a substep that keeps `restart_time`. -/

namespace Consensus.Goldilocks.Healing

open SA

variable {FGP : Type} {sp : SAParams}

/-! ## Locks below stored blocks -/

/-- The block of `l'` is an ancestor (inside `U`) of the block of `l`, or `l' = l`. -/
private def LockSitsBelow (U : Set (Blk sp.n FGP)) (l' l : Lock) : Prop :=
  l' = l ∨ ∃ L₁ ∈ U, L₁.root = l'.block ∧ ∃ L₂ ∈ U, L₂.root = l.block ∧ Anc U L₁ L₂

/-- The block of `l` is in `U` and an ancestor of `B` there. -/
private def LockBelow (U : Set (Blk sp.n FGP)) (l : Lock) (B : Blk sp.n FGP) : Prop :=
  ∃ L ∈ U, L.root = l.block ∧ Anc U L B

/-- Every lock of `L'` sits below a lock of `L` with its slot and fast bit, or below a block `O`
with `New l'.slot l'.fast O`. -/
private def StoredFrom (U : Set (Blk sp.n FGP)) (L L' : Set Lock)
    (New : Nat → Bool → Blk sp.n FGP → Prop) : Prop :=
  ∀ l' ∈ L', (∃ l ∈ L, l.fast = l'.fast ∧ l'.slot = l.slot ∧ LockSitsBelow U l' l) ∨
    ∃ O, New l'.slot l'.fast O ∧ LockBelow U l' O

private theorem StoredFrom.of_eq {U : Set (Blk sp.n FGP)} {L L' : Set Lock}
    {New : Nat → Bool → Blk sp.n FGP → Prop} (h : L' = L) : StoredFrom U L L' New := by
  subst h
  exact fun l hl => Or.inl ⟨l, hl, rfl, rfl, Or.inl rfl⟩

private theorem StoredFrom.mono {U : Set (Blk sp.n FGP)} {L L' : Set Lock}
    {New New' : Nat → Bool → Blk sp.n FGP → Prop} (h : StoredFrom U L L' New)
    (hN : ∀ s f B, New s f B → New' s f B) : StoredFrom U L L' New' := fun l hl =>
  (h l hl).imp_right fun ⟨B, h1, h2⟩ => ⟨B, hN _ _ _ h1, h2⟩

private theorem LockBelow.of_sitsBelow {U : Set (Blk sp.n FGP)} (hU : Coherent U) {l' l : Lock}
    {B : Blk sp.n FGP} (h : LockSitsBelow U l' l) (hB : LockBelow U l B) : LockBelow U l' B := by
  rcases h with rfl | ⟨A₁, hA₁, hA₁r, A₂, hA₂, hA₂r, hA⟩
  · exact hB
  obtain ⟨L, hL, hLr, hLB⟩ := hB
  obtain rfl : A₂ = L := hU.1 hA₂ hL (hA₂r.trans hLr.symm)
  exact ⟨A₁, hA₁, hA₁r, hA.trans hLB⟩

private theorem StoredFrom.trans {U : Set (Blk sp.n FGP)} (hU : Coherent U) {L₁ L₂ L₃ : Set Lock}
    {New : Nat → Bool → Blk sp.n FGP → Prop} (h₁ : StoredFrom U L₁ L₂ New)
    (h₂ : StoredFrom U L₂ L₃ New) : StoredFrom U L₁ L₃ New := by
  intro l₃ hl₃
  rcases h₂ l₃ hl₃ with ⟨l₂, hl₂, hf₂, hs₂, hb₂⟩ | ⟨B, hN, hB⟩
  · rcases h₁ l₂ hl₂ with ⟨l₁, hl₁, hf₁, hs₁, hb₁⟩ | ⟨B, hN, hB⟩
    · refine Or.inl ⟨l₁, hl₁, hf₁.trans hf₂, hs₂.trans hs₁, ?_⟩
      rcases hb₂ with rfl | ⟨A₁, hA₁, hA₁r, A₂, hA₂, hA₂r, hA⟩
      · exact hb₁
      rcases hb₁ with rfl | ⟨C₁, hC₁, hC₁r, C₂, hC₂, hC₂r, hC⟩
      · exact Or.inr ⟨A₁, hA₁, hA₁r, A₂, hA₂, hA₂r, hA⟩
      obtain rfl : A₂ = C₁ := hU.1 hA₂ hC₁ (hA₂r.trans hC₁r.symm)
      exact Or.inr ⟨A₁, hA₁, hA₁r, C₂, hC₂, hC₂r, hA.trans hC⟩
    · exact Or.inr ⟨B, hs₂ ▸ hf₂ ▸ hN, LockBelow.of_sitsBelow hU hb₂ hB⟩
  · exact Or.inr ⟨B, hN, hB⟩

/-- Locks that move back in a frame inside `U` sit below the locks they come from. -/
private theorem StoredFrom.of_movesBack {U : Set (Blk sp.n FGP)} {Φ : Frm sp.n FGP}
    (hΦ : Φ.tree ⊆ U) {L L' : Set Lock} {New : Nat → Bool → Blk sp.n FGP → Prop}
    (h : MovesBack sp Φ L L') : StoredFrom U L L' New := by
  intro l' hl'
  obtain ⟨l, hl, hs, hfa, B, hB, hBr, B', hB', hB'r, hA⟩ := h l' hl'
  exact Or.inl ⟨l, hl, hfa.symm, hs, Or.inr ⟨B', hΦ hB', hB'r, B, hΦ hB, hBr, hA.mono hΦ⟩⟩

/-- `add_locks` with new locks: each new lock is stored on the viable ancestor of its block
(`liveLocks`), and the old locks move back. -/
private theorem StoredFrom.of_addLocks {U : Set (Blk sp.n FGP)} (hU : Coherent U)
    {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {L : Set Lock} {t : Time} {s : Nat}
    {N : Set (Nat × Bool)} {New : Nat → Bool → Blk sp.n FGP → Prop} {L₀ : Set Lock}
    (hL : L₀ = L)
    (hN : ∀ r f, (r, f) ∈ N → ∃ D ∈ Φ.tree, D.root = r ∧ New s f (Φ.viableAncestor D)) :
    StoredFrom U L (addLocks sp L₀ Φ t s N) New := by
  subst hL
  rintro l' ⟨l, hl, B, hB, hBr, -, rfl⟩
  obtain ⟨hvt, hva⟩ := viableAncestor_anc hΦ hB
  rcases hl with hl | ⟨p, hp, rfl⟩
  · exact Or.inl ⟨l, hl, rfl, rfl, Or.inr ⟨_, hΦU hvt, rfl, B, hΦU hB, hBr, hva.mono hΦU⟩⟩
  · obtain ⟨D, hD, hDr, hND⟩ := hN p.1 p.2 hp
    obtain rfl : B = D := hU.1 (hΦU hB) (hΦU hD) (hBr.trans hDr.symm)
    exact Or.inr ⟨_, hND, _, hΦU hvt, rfl, .refl⟩

/-! ## What each SA function does to the locks -/

variable {U : Set (Blk sp.n FGP)} {Φ : Frm sp.n FGP}

private theorem StoredFrom.of_optimistic (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    (A : SAState sp.n) (t : Time) :
    StoredFrom U A.locks (optimisticConfirmation sp A Φ t).locks
      (fun s _ O => s = sp.slot t ∧ ∃ D, optimisticSelect sp A Φ t = some D ∧
        O = Φ.viableAncestor D) := by
  unfold optimisticConfirmation
  rcases h : optimisticSelect sp A Φ t with _ | B
  · exact StoredFrom.of_eq rfl
  · rw [updateLatestConfirmed_locks_eq]
    refine StoredFrom.of_addLocks hU hΦ hΦU rfl fun r f hr => ?_
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    have hB := h
    unfold optimisticSelect at hB
    dsimp only at hB
    split_ifs at hB
    exact ⟨B, (deepest_mem hB).1.1, rfl, rfl, B, rfl, rfl⟩

private theorem StoredFrom.of_optimistic_admit (hU : Coherent U) (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {L : Set Lock} (A : SAState sp.n) (hL : A.locks = L) (t : Time)
    (v : Vote sp.n) :
    StoredFrom U L (optimisticConfirmation sp (admitVote sp A t v) Φ t).locks
      (fun s _ O => s = sp.slot t ∧ ∃ D, optimisticSelect sp (admitVote sp A t v) Φ t = some D ∧
        O = Φ.viableAncestor D) := by
  have := StoredFrom.of_optimistic hU hΦ hΦU (admitVote sp A t v) t
  rwa [admitVote_locks_eq, hL] at this

private theorem StoredFrom.of_tryVote (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    (x : Fin sp.n) (A : SAState sp.n) (t : Time) :
    StoredFrom U A.locks (tryVote sp x A Φ t).1.locks
      (fun s _ O => ∃ e ∈ (tryVote sp x A Φ t).2, s = sp.slot t ∧ ∃ D,
        optimisticSelect sp (admitVote sp e.readPoint t e.msg) Φ t = some D ∧
        O = Φ.viableAncestor D) := by
  unfold tryVote
  dsimp only
  split_ifs with h1 h2 h3
  · exact StoredFrom.of_eq rfl
  · exact StoredFrom.of_eq rfl
  · refine StoredFrom.trans hU (StoredFrom.of_movesBack hΦU
      (((locks_move_back sp) FGP Φ A.locks t hΦ).2.2 ((sp.slot t : Int) - 1)
        (mergedVoteView sp A Φ (sp.slot t))))
      (StoredFrom.mono (StoredFrom.of_optimistic_admit hU hΦ hΦU _ ?_ t _) ?_)
    · rfl
    · exact fun s f B h => ⟨_, List.mem_singleton_self _, h⟩
  · refine StoredFrom.mono (StoredFrom.of_optimistic_admit hU hΦ hΦU _ ?_ t _) ?_
    · rfl
    · exact fun s f B h => ⟨_, List.mem_singleton_self _, h⟩

private theorem StoredFrom.of_updateConfirmation (hU : Coherent U) (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) (A : SAState sp.n) (t : Time) (s : Nat) :
    StoredFrom U A.locks (updateConfirmation sp A Φ t s).locks
      (fun s' f O => s' = s ∧ (f = true → ∃ C D, getConfirmation sp A Φ s = some C ∧
        ¬ conflictsWithLock sp A.locks Φ t C ∧ fastSelect sp A Φ s C = some D ∧
        O = Φ.viableAncestor D)) := by
  unfold updateConfirmation
  dsimp only
  rcases hC : getConfirmation sp A Φ s with _ | C
  · exact StoredFrom.of_eq rfl
  · dsimp only
    split_ifs with hconf
    · exact StoredFrom.of_eq rfl
    · refine StoredFrom.of_addLocks hU hΦ hΦU (updateLatestConfirmed_locks_eq _ _ _)
        fun r f hr => ?_
      rcases hr with ⟨D, hD, hr⟩ | ⟨-, D, hD, hr⟩
      · simp only [Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ⟨D, (deepest_mem hD).1.1.1, rfl, rfl, fun _ => ⟨C, D, rfl, hconf, hD, rfl⟩⟩
      · simp only [Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ⟨D, (deepest_mem hD).1.1.1, rfl, rfl, Bool.false_ne_true.elim⟩

private theorem StoredFrom.of_onTick (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    (x : Fin sp.n) (A : SAState sp.n) (t : Time) :
    StoredFrom U A.locks (acOnTick sp x A Φ t).1.locks
      (fun s f O => (∃ e ∈ (acOnTick sp x A Φ t).2, s = sp.slot t ∧ ∃ D,
        optimisticSelect sp (admitVote sp e.readPoint t e.msg) Φ t = some D ∧
        O = Φ.viableAncestor D) ∨
        (t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t ∧ joined sp A t ∧
          s = sp.slot t - 1 ∧ (f = true → ∃ C D, getConfirmation sp A Φ s = some C ∧
          ¬ conflictsWithLock sp A.locks Φ t C ∧ fastSelect sp A Φ s C = some D ∧
          O = Φ.viableAncestor D))) := by
  unfold acOnTick
  dsimp only
  split_ifs with hj ht hu hu
  · exfalso
    have := sp.toParams.hΔ
    linarith [ht.1.symm.trans hu]
  · refine (StoredFrom.of_updateConfirmation hU hΦ hΦU A t _).mono fun s f B h => ?_
    obtain ⟨rfl, h2⟩ := h
    exact Or.inr ⟨ht.1, ht.2, hj, rfl, h2⟩
  · exact (StoredFrom.of_tryVote hU hΦ hΦU x A t).mono fun s f B h => Or.inl h
  · exact StoredFrom.of_eq rfl
  · exact StoredFrom.of_eq rfl

private theorem StoredFrom.of_proposal (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) (A : SAState sp.n)
    (t : Time) {New : Nat → Bool → Blk sp.n FGP → Prop} :
    StoredFrom U A.locks (acProposal sp A Φ t).1.locks New := by
  unfold acProposal
  dsimp only
  split_ifs
  · exact StoredFrom.of_movesBack hΦU (((locks_move_back sp) FGP Φ A.locks t hΦ).2.2 _ _)
  · exact StoredFrom.of_eq rfl

private theorem acToFG_locks_eq (A : SAState sp.n) (t : Time) :
    (acToFG sp A Φ t).1.locks = A.locks := by
  unfold acToFG
  split_ifs
  · split
    · rfl
    · split_ifs <;> rfl
  · rfl

/-! ## Over an SA trace -/

variable {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)} {tr : SATrace sp FGP ro}

/-- A call of an honest node keeps its locks below earlier ones or writes fast locks stored on
the viable ancestor (in the call's frame) of a fast-lock write's selection at its own cut. -/
private theorem call_storedFrom (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    StoredFrom U (tr.state x i).locks (tr.post i).locks
      (fun s f O => f = true → ∃ CV ℓ' D, tr.CallAt x i ℓ' ∧ FastLockAt tr x i s D CV ∧
        O = ℓ'.frame.viableAncestor D) := by
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc
  have hU := hr.coherent
  have opt : ∀ s (f : Bool) D, (∃ CV, OptimisticLockAt tr x i s D CV) →
      f = true → ∃ CV ℓ' D', tr.CallAt x i ℓ' ∧ FastLockAt tr x i s D' CV ∧
        ℓ.frame.viableAncestor D = ℓ'.frame.viableAncestor D' :=
    fun s f D ⟨CV, h⟩ _ => ⟨CV, ℓ, D, hc, Or.inr h, rfl⟩
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
    refine (StoredFrom.of_onTick hU hΦ hΦU x A _).mono fun s f O h => ?_
    rcases h with ⟨e, he', hs, D, hsel, rfl⟩ | ⟨ht, hs0, hj, hs, hC⟩
    · exact opt _ _ D
        ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr ⟨e, hemits ▸ he', rfl⟩)⟩, hs.symm, hsel, rfl⟩
    · have hu : UpdateAt tr x i s ℓ := by
        refine ⟨hc, hcall, ?_, hA ▸ hj⟩
        rw [hs]
        conv_lhs => rw [ht]
        simp only [SAParams.ts]
        push_cast [Nat.cast_sub hs0]
        ring
      intro hf
      obtain ⟨C₀, D₀, hC₀, hconf, hD₀, hO⟩ := hC hf
      exact ⟨_, ℓ, D₀, hc, Or.inl ⟨ℓ, C₀, hu, hA ▸ hC₀, hA ▸ hconf, hA ▸ hD₀, rfl⟩, hO⟩
  | proposal => exact StoredFrom.of_proposal hΦ hΦU A _
  | toFG => exact StoredFrom.of_eq (acToFG_locks_eq A _)
  | message m =>
    rw [hcall] at hemits
    refine StoredFrom.trans hU ((StoredFrom.of_optimistic_admit hU hΦ hΦU A rfl _ m).mono
      fun s f O h => ?_) ((StoredFrom.of_tryVote hU hΦ hΦU x _ _).mono fun s f O h => ?_)
    · obtain ⟨hs, D, hsel, rfl⟩ := h
      exact opt _ _ D ⟨_, ℓ, _, ⟨hc, Or.inl ⟨m, hcall, hA ▸ rfl⟩⟩, hs.symm, hsel, rfl⟩
    · obtain ⟨e, he', hs, D, hsel, rfl⟩ := h
      exact opt _ _ D
        ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr ⟨e, hemits ▸ he', rfl⟩)⟩, hs.symm, hsel, rfl⟩
  | block B =>
    rw [hcall] at hemits
    have h₁ := StoredFrom.of_optimistic hU hΦ hΦU (blockReceipt sp A (tr.time i) B) (tr.time i)
    rw [blockReceipt_locks] at h₁
    refine StoredFrom.trans hU (h₁.mono fun s f O h => ?_)
      ((StoredFrom.of_tryVote hU hΦ hΦU x _ _).mono fun s f O h => ?_)
    · obtain ⟨hs, D, hsel, rfl⟩ := h
      exact opt _ _ D ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inl ⟨B, hcall, hA ▸ rfl⟩)⟩, hs.symm, hsel, rfl⟩
    · obtain ⟨e, he', hs, D, hsel, rfl⟩ := h
      exact opt _ _ D
        ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr ⟨e, hemits ▸ he', rfl⟩)⟩, hs.symm, hsel, rfl⟩
  | restart =>
    exact StoredFrom.of_eq ((restart_state sp) FGP ro x A ℓ.frame (tr.time i) hΦ
      (hr.time_nonneg i)).2.1

/-- **Stored fast-lock provenance.** Every fast lock that an honest node holds before cut `i`
sits below (inside `U`) the stored block `O = Φ.viableAncestor D` of a fast-lock write of its
slot at an earlier cut of the node, `D` the write's selection and `Φ` the frame of its call. -/
theorem stored_fast_lock_provenance (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {x : Fin sp.n} (hx : x ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state x i).locks, l.fast = true →
      ∃ r < i, ∃ CV ℓ D, tr.CallAt x r ℓ ∧ FastLockAt tr x r l.slot D CV ∧
        ∃ L ∈ U, L.root = l.block ∧ Anc U L (ℓ.frame.viableAncestor D) := by
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
      rcases call_storedFrom hr hx ⟨hnode.1, hℓ⟩ l hl with ⟨l₀, hl₀, hf₀, hs, hb⟩ | ⟨O, h, hB⟩
      · obtain ⟨r, hri, CV, ℓ', D, hc, hfl, hB⟩ := ih l₀ hl₀ (hf₀.trans hf)
        exact ⟨r, hri.trans (Nat.lt_succ_self i), CV, ℓ', D, hc, hs ▸ hfl,
          LockBelow.of_sitsBelow hr.coherent hb hB⟩
      · obtain ⟨CV, ℓ', D, hc, hfl, rfl⟩ := h hf
        exact ⟨i, Nat.lt_succ_self i, CV, ℓ', D, hc, hfl, hB⟩
    · obtain ⟨r, hri, h⟩ := ih l hl hf
      exact ⟨r, hri.trans (Nat.lt_succ_self i), h⟩

/-! ## The joined guard of a write -/

private theorem admitVote_restartTime (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).restartTime = A.restartTime := by
  unfold admitVote
  split_ifs <;> rfl

private theorem blockReceipt_restartTime (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).restartTime = A.restartTime := by
  unfold blockReceipt
  generalize hA' : ({ A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) } :
    SAState sp.n) = A'
  have : A'.restartTime = A.restartTime := by rw [← hA']
  rw [← this]
  clear hA' this
  induction (blockVotes B) generalizing A' with
  | nil => rfl
  | cons v l ih => rw [List.foldl_cons, ih, admitVote_restartTime]

/-- **A fast-lock write is joined**: its call is not a restart, and the state before it is
joined at its time (the update's guard; the optimistic check's guard at a substep that keeps
`restart_time`). -/
theorem joined_of_fastLockAt (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i s : Nat} {D : Blk sp.n FGP} {CV : Set (Vote sp.n)}
    (h : FastLockAt tr x i s D CV) :
    joined sp (tr.state x i) (tr.time i) ∧
      ∃ ℓ, tr.CallAt x i ℓ ∧ ℓ.call ≠ .restart := by
  rcases h with ⟨ℓ, C, ⟨hc, htick, -, hj⟩, -⟩ | ⟨ℓ, A, ⟨hc, hA⟩, -, hsel, -⟩
  · exact ⟨hj, ℓ, hc, by rw [htick]; exact fun h => nomatch h⟩
  have hjA : joined sp A (tr.time i) := by
    unfold optimisticSelect at hsel
    dsimp only at hsel
    split_ifs at hsel with h1
    exact not_not.mp (not_or.mp h1).1
  have hrs : ∀ A' : SAState sp.n, A'.restartTime = (tr.state x i).restartTime →
      joined sp A' (tr.time i) → joined sp (tr.state x i) (tr.time i) := by
    intro A' h hj
    unfold joined at hj ⊢
    rwa [← h]
  rcases hA with ⟨m, hm, rfl⟩ | ⟨B, hB, rfl⟩ | ⟨e, he, rfl⟩
  · exact ⟨hrs _ (admitVote_restartTime _ _ _) hjA, ℓ, hc, by rw [hm]; exact fun h => nomatch h⟩
  · exact ⟨hrs _ (blockReceipt_restartTime _ _ _) hjA, ℓ, hc,
      by rw [hB]; exact fun h => nomatch h⟩
  · have hnr : ℓ.call ≠ .restart := by
      intro hres
      have hexec := hr.exec i ℓ hc.2 (hc.1 ▸ hx)
      rw [hres] at hexec
      obtain ⟨hΦ, -⟩ := frameIn_of_callAt hr hx hc
      have h0 := ((restart_state sp) FGP ro (tr.node i) (tr.state (tr.node i) i) ℓ.frame
        (tr.time i) hΦ (hr.time_nonneg i)).1
      rw [show ℓ.emits = [] from (congrArg Prod.snd hexec).symm.trans h0] at he
      exact absurd he List.not_mem_nil
    have hexec := hr.exec i ℓ hc.2 (hc.1 ▸ hx)
    rw [hc.1] at hexec
    have hpr : (tr.post i).restartTime = (tr.state x i).restartTime := by
      have h1 := congrArg Prod.fst hexec
      simp only at h1
      rw [← h1]
      exact step_restartTime x _ _ _ _ hnr
    have := restartTime_of_castAt hr hx ⟨hc, he⟩
    exact ⟨hrs _ ((admitVote_restartTime _ _ _).trans (this.symm.trans hpr)) hjA, ℓ, hc, hnr⟩

end Consensus.Goldilocks.Healing

end
