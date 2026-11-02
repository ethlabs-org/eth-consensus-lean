module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Statements.AC.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Tree
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain

public section

/-! # Goldilocks SA: where a node's fast locks come from

Every fast lock that an honest node holds sits below (inside `U`) the block of a fast lock of the
same slot that the node itself wrote at an earlier cut, by the fast test of an update
(`FastUpdateAt`) or by an optimistic confirmation (`OptimisticLockAt`): the SA's lock functions
only move locks back (A0.4 (c)), a restart keeps the locks (A0.7), and the only writers of fast
locks are those two events. A1.5 and A1.9 read this. Likewise every lock, fast or slow, sits below
a lock of its slot written by an optimistic confirmation or by the update of that slot
(`lock_provenance`, read by `Steps/Origin`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams}

/-! ## Locks that sit below others -/

/-- The block of `l'` is an ancestor (inside `U`) of the block of `l`, or `l' = l`. -/
private def SitsBelow (U : Set (Blk sp.n FGP)) (l' l : Lock) : Prop :=
  l' = l ∨ ∃ L₁ ∈ U, L₁.root = l'.block ∧ ∃ L₂ ∈ U, L₂.root = l.block ∧ Anc U L₁ L₂

/-- The block of `l` is in `U` and an ancestor of `B` there. -/
private def Below (U : Set (Blk sp.n FGP)) (l : Lock) (B : Blk sp.n FGP) : Prop :=
  ∃ L ∈ U, L.root = l.block ∧ Anc U L B

/-- Every lock of `L'` sits below a lock of `L` with its slot and fast bit, or below a block `B`
with `New l'.slot l'.fast B`. -/
private def FromP (U : Set (Blk sp.n FGP)) (L L' : Set Lock)
    (New : Nat → Bool → Blk sp.n FGP → Prop) : Prop :=
  ∀ l' ∈ L', (∃ l ∈ L, l.fast = l'.fast ∧ l'.slot = l.slot ∧ SitsBelow U l' l) ∨
    ∃ B, New l'.slot l'.fast B ∧ Below U l' B

private theorem FromP.of_eq {U : Set (Blk sp.n FGP)} {L L' : Set Lock}
    {New : Nat → Bool → Blk sp.n FGP → Prop} (h : L' = L) : FromP U L L' New := by
  subst h
  exact fun l hl => Or.inl ⟨l, hl, rfl, rfl, Or.inl rfl⟩

private theorem FromP.mono {U : Set (Blk sp.n FGP)} {L L' : Set Lock}
    {New New' : Nat → Bool → Blk sp.n FGP → Prop} (h : FromP U L L' New)
    (hN : ∀ s f B, New s f B → New' s f B) : FromP U L L' New' := fun l hl =>
  (h l hl).imp_right fun ⟨B, h1, h2⟩ => ⟨B, hN _ _ _ h1, h2⟩

private theorem FromP.trans {U : Set (Blk sp.n FGP)} (hU : Coherent U) {L₁ L₂ L₃ : Set Lock}
    {New : Nat → Bool → Blk sp.n FGP → Prop} (h₁ : FromP U L₁ L₂ New) (h₂ : FromP U L₂ L₃ New) :
    FromP U L₁ L₃ New := by
  intro l₃ hl₃
  rcases h₂ l₃ hl₃ with ⟨l₂, hl₂, hf₂, hs₂, hb₂⟩ | ⟨B, hN, hB⟩
  · rcases h₁ l₂ hl₂ with ⟨l₁, hl₁, hf₁, hs₁, hb₁⟩ | ⟨B, hN, L, hL, hLr, hLB⟩
    · refine Or.inl ⟨l₁, hl₁, hf₁.trans hf₂, hs₂.trans hs₁, ?_⟩
      rcases hb₂ with rfl | ⟨A₁, hA₁, hA₁r, A₂, hA₂, hA₂r, hA⟩
      · exact hb₁
      rcases hb₁ with rfl | ⟨C₁, hC₁, hC₁r, C₂, hC₂, hC₂r, hC⟩
      · exact Or.inr ⟨A₁, hA₁, hA₁r, A₂, hA₂, hA₂r, hA⟩
      have : A₂ = C₁ := hU.1 hA₂ hC₁ (hA₂r.trans hC₁r.symm)
      subst this
      exact Or.inr ⟨A₁, hA₁, hA₁r, C₂, hC₂, hC₂r, hA.trans hC⟩
    · refine Or.inr ⟨B, hs₂ ▸ hf₂ ▸ hN, ?_⟩
      rcases hb₂ with rfl | ⟨A₁, hA₁, hA₁r, A₂, hA₂, hA₂r, hA⟩
      · exact ⟨L, hL, hLr, hLB⟩
      have : A₂ = L := hU.1 hA₂ hL (hA₂r.trans hLr.symm)
      subst this
      exact ⟨A₁, hA₁, hA₁r, hA.trans hLB⟩
  · exact Or.inr ⟨B, hN, hB⟩

/-- Locks that move back in a frame inside `U` sit below the locks they come from. -/
private theorem FromP.of_movesBack {U : Set (Blk sp.n FGP)} {Φ : Frm sp.n FGP}
    (hΦ : Φ.tree ⊆ U) {L L' : Set Lock} {New : Nat → Bool → Blk sp.n FGP → Prop}
    (h : MovesBack sp Φ L L') : FromP U L L' New := by
  intro l' hl'
  obtain ⟨l, hl, hs, hfa, B, hB, hBr, B', hB', hB'r, hA⟩ := h l' hl'
  exact Or.inl ⟨l, hl, hfa.symm, hs, Or.inr ⟨B', hΦ hB', hB'r, B, hΦ hB, hBr,
    hA.mono hΦ⟩⟩

/-- `add_locks` with new locks: the new locks are on the blocks of `N`'s entries. -/
private theorem FromP.of_addLocks {U : Set (Blk sp.n FGP)} (hU : Coherent U) {Φ : Frm sp.n FGP}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {L : Set Lock} {t : Time} {s : Nat}
    {N : Set (Nat × Bool)} {New : Nat → Bool → Blk sp.n FGP → Prop} {L₀ : Set Lock} (hL : L₀ = L)
    (hN : ∀ r f, (r, f) ∈ N → ∃ B ∈ Φ.tree,
      B.root = r ∧ New s f (Φ.viableAncestor B)) :
    FromP U L (addLocks sp L₀ Φ t s N) New := by
  subst hL
  intro l' hl'
  obtain ⟨l, hl, B, hB, hBr, -, rfl⟩ := hl'
  rcases hl with hl | ⟨p, hp, rfl⟩
  · exact Or.inl ⟨l, hl, rfl, rfl, Or.inr ⟨Φ.viableAncestor B,
      hΦU (viableAncestor_anc hΦ hB).1, rfl, B, hΦU hB, hBr,
      Goldilocks.Anc.mono hΦU (viableAncestor_anc hΦ hB).2⟩⟩
  · obtain ⟨r, b⟩ := p
    simp only at hBr
    obtain ⟨D, hD, hDr, hND⟩ := hN r b hp
    have : B = D := hU.1 (hΦU hB) (hΦU hD) (hBr.trans hDr.symm)
    subst this
    exact Or.inr ⟨Φ.viableAncestor B, hND, Φ.viableAncestor B,
      hΦU (viableAncestor_anc hΦ hB).1, rfl, Relation.ReflTransGen.refl⟩

/-! ## What each SA function does to the locks -/

/-- Admitting a vote keeps the locks. -/
theorem admitVote_locks_eq (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).locks = A.locks := by
  unfold admitVote
  split_ifs <;> rfl

/-- The receipt of a block keeps the locks. -/
theorem blockReceipt_locks (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).locks = A.locks := by
  unfold blockReceipt
  generalize hA' : ({ A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) } :
    SAState sp.n) = A'
  have : A'.locks = A.locks := by rw [← hA']
  rw [← this]
  clear hA' this
  induction (blockVotes B) generalizing A' with
  | nil => rfl
  | cons v l ih => rw [List.foldl_cons, ih, admitVote_locks_eq]

/-- Updating the latest confirmed block keeps the locks. -/
theorem updateLatestConfirmed_locks_eq (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (C : Blk sp.n FGP) : (updateLatestConfirmed sp A Φ C).locks = A.locks := by
  unfold updateLatestConfirmed
  split_ifs <;> rfl

variable {U : Set (Blk sp.n FGP)} {Φ : Frm sp.n FGP}

private theorem FromP.of_optimistic (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    (A : SAState sp.n) (t : Time) :
    FromP U A.locks (optimisticConfirmation sp A Φ t).locks
      (fun s f B => ∃ D ∈ Φ.tree, B = Φ.viableAncestor D ∧
        f = true ∧ s = sp.slot t ∧ optimisticSelect sp A Φ t = some D) := by
  unfold optimisticConfirmation
  rcases h : optimisticSelect sp A Φ t with _ | B
  · exact FromP.of_eq rfl
  · rw [updateLatestConfirmed_locks_eq]
    refine FromP.of_addLocks hU hΦ hΦU rfl fun r f hr => ?_
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    have hB := h
    unfold optimisticSelect at hB
    dsimp only at hB
    split_ifs at hB
    exact ⟨B, (deepest_mem hB).1.1, rfl, B, (deepest_mem hB).1.1, rfl, rfl, rfl, rfl⟩

private theorem FromP.of_optimistic_admit (hU : Coherent U) (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {L : Set Lock} (A : SAState sp.n) (hL : A.locks = L) (t : Time)
    (v : Vote sp.n) :
    FromP U L (optimisticConfirmation sp (admitVote sp A t v) Φ t).locks
      (fun s f B => ∃ D ∈ Φ.tree, B = Φ.viableAncestor D ∧ f = true ∧ s = sp.slot t ∧
        optimisticSelect sp (admitVote sp A t v) Φ t = some D) :=
    by
  have := FromP.of_optimistic hU hΦ hΦU (admitVote sp A t v) t
  rwa [admitVote_locks_eq, hL] at this

private theorem FromP.of_tryVote (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    (x : Fin sp.n) (A : SAState sp.n) (t : Time) :
    FromP U A.locks (tryVote sp x A Φ t).1.locks
      (fun s f B => ∃ D ∈ Φ.tree, B = Φ.viableAncestor D ∧
        ∃ e ∈ (tryVote sp x A Φ t).2, f = true ∧ s = sp.slot t ∧
          optimisticSelect sp (admitVote sp e.readPoint t e.msg) Φ t = some D) := by
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
    · exact fun s f B ⟨D, hD, heq, h⟩ => ⟨D, hD, heq, _, List.mem_singleton_self _, h⟩
  · refine FromP.mono (FromP.of_optimistic_admit hU hΦ hΦU _ ?_ t _) ?_
    · rfl
    · exact fun s f B ⟨D, hD, heq, h⟩ => ⟨D, hD, heq, _, List.mem_singleton_self _, h⟩

private theorem FromP.of_updateConfirmation (hU : Coherent U) (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) (A : SAState sp.n) (t : Time) (s : Nat) :
    FromP U A.locks (updateConfirmation sp A Φ t s).locks
      (fun s' f B => ∃ D ∈ Φ.tree, B = Φ.viableAncestor D ∧
        s' = s ∧ (f = true → ∃ C, getConfirmation sp A Φ s = some C ∧
        ¬ conflictsWithLock sp A.locks Φ t C ∧ fastSelect sp A Φ s C = some D) ∧
        (f = false → ∃ C, getConfirmation sp A Φ s = some C ∧ Φ.Anc D C ∧
          ∀ m : Int, (s : Int) - sp.k < m → m < s →
            ∃ S ∈ Φ.tree, A.saved m = some S.root ∧ Φ.Anc D S)) := by
  unfold updateConfirmation
  dsimp only
  rcases hC : getConfirmation sp A Φ s with _ | C
  · exact FromP.of_eq rfl
  · dsimp only
    split_ifs with hconf
    · exact FromP.of_eq rfl
    · refine FromP.of_addLocks hU hΦ hΦU (updateLatestConfirmed_locks_eq _ _ _) fun r f hr => ?_
      rcases hr with ⟨D, hD, hr⟩ | ⟨hne, D, hD, hr⟩
      · simp only [Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ⟨D, (deepest_mem hD).1.1.1, rfl, D, (deepest_mem hD).1.1.1, rfl, rfl,
          (fun _ => ⟨C, rfl, hconf, hD⟩), (fun h => Bool.false_ne_true h.symm |>.elim)⟩
      · simp only [Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        have hDm := (deepest_mem hD).1
        have hslow : ∀ m : Int, (s : Int) - sp.k < m → m < s →
            ∃ S ∈ Φ.tree, A.saved m = some S.root ∧ Φ.Anc D S := by
          rcases hDm.2 with hf | hs
          · exfalso
            let T := {X | X ∈ confirmationPath sp Φ C ∧ FastTest sp A Φ s X}
            obtain ⟨E, hE⟩ := exists_deepest (S := T) hΦ (fun _ h => h.1.1) ⟨D, hDm.1, hf⟩
            have hDE := anc_deepest (S := T) hΦ (fun _ h => h.1.1)
              (fun X hX Y hY => anc_total hΦ.coherent hX.1.2.2 hY.1.2.2) hE D ⟨hDm.1, hf⟩
            have hED := anc_deepest (S := {X | X ∈ confirmationPath sp Φ C ∧
              (FastTest sp A Φ s X ∨ ∀ m : Int, (s : Int) - sp.k < m → m < s →
                ∃ S ∈ Φ.tree, (Function.update A.saved (s : Int) (some C.root)) m = some S.root ∧
                  Φ.Anc X S)}) hΦ (fun _ h => h.1.1)
              (fun X hX Y hY => anc_total hΦ.coherent hX.1.2.2 hY.1.2.2) hD E
              ⟨(deepest_mem hE).1.1, Or.inl (deepest_mem hE).1.2⟩
            have heq : E = D := Anc.antisymm hΦ.coherent hED hDE
            exact hne (hD.trans (by simpa only [fastSelect, heq] using hE.symm))
          · intro m hm hms
            obtain ⟨S, hS, hsave, hDS⟩ := hs m hm hms
            refine ⟨S, hS, ?_, hDS⟩
            simpa only [Function.update_of_ne (show m ≠ (s : Int) by omega)] using hsave
        exact ⟨D, hDm.1.1, rfl, D, hDm.1.1, rfl, rfl, Bool.false_ne_true.elim,
          fun _ => ⟨C, rfl, hDm.1.2.2, hslow⟩⟩

private theorem FromP.of_onTick (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    (x : Fin sp.n) (A : SAState sp.n) (t : Time) :
    FromP U A.locks (acOnTick sp x A Φ t).1.locks
      (fun s f B => ∃ D ∈ Φ.tree, B = Φ.viableAncestor D ∧
        ((∃ e ∈ (acOnTick sp x A Φ t).2, f = true ∧ s = sp.slot t ∧
        optimisticSelect sp (admitVote sp e.readPoint t e.msg) Φ t = some D) ∨
        (t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t ∧ joined sp A t ∧
          s = sp.slot t - 1 ∧ (f = true → ∃ C, getConfirmation sp A Φ s = some C ∧
          ¬ conflictsWithLock sp A.locks Φ t C ∧ fastSelect sp A Φ s C = some D) ∧
          (f = false → ∃ C, getConfirmation sp A Φ s = some C ∧ Φ.Anc D C ∧
            ∀ m : Int, (s : Int) - sp.k < m → m < s →
              ∃ S ∈ Φ.tree, A.saved m = some S.root ∧ Φ.Anc D S)))) := by
  unfold acOnTick
  dsimp only
  split_ifs with hj ht hu hu
  · exfalso
    have := sp.toParams.hΔ
    linarith [ht.1.symm.trans hu]
  · refine (FromP.of_updateConfirmation hU hΦ hΦU A t _).mono fun s f B h => ?_
    obtain ⟨D, hD, heq, rfl, h2⟩ := h
    exact ⟨D, hD, heq, Or.inr ⟨ht.1, ht.2, hj, rfl, h2⟩⟩
  · exact (FromP.of_tryVote hU hΦ hΦU x A t).mono
      fun s f B ⟨D, hD, heq, h⟩ => ⟨D, hD, heq, Or.inl h⟩
  · exact FromP.of_eq rfl
  · exact FromP.of_eq rfl

private theorem FromP.of_proposal (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) (A : SAState sp.n)
    (t : Time) {New : Nat → Bool → Blk sp.n FGP → Prop} :
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

/-- The frame of an honest node's call is well formed and inside `U`. -/
theorem frameIn_of_callAt (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
  rcases hr.frameLaw x hx i ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1

/-- A call of an honest node keeps its locks below earlier ones or writes locks of its own cut:
by an optimistic confirmation, or by the update of their slot (fast ones by its fast test). -/
private theorem call_candidate_fromP
    (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    FromP U (tr.state x i).locks (tr.post i).locks
      (fun s f B => ∃ D ∈ ℓ.frame.tree, B = ℓ.frame.viableAncestor D ∧
        (f = true → ∃ CV, FastLockAt tr x i s D CV) ∧
        ((∃ CV, OptimisticLockAt tr x i s D CV) ∨ ∃ ℓ', UpdateAt tr x i s ℓ') ∧
        (f = false → ∃ ℓ C CV, UpdateAt tr x i s ℓ ∧ ResultAt tr x i s C CV ∧
          D ∈ ℓ.frame.tree ∧ ℓ.frame.Anc D C ∧
          ∀ m : Int, (s : Int) - sp.k < m → m < s →
            ∃ S ∈ ℓ.frame.tree, (tr.state x i).saved m = some S.root ∧ ℓ.frame.Anc D S)) := by
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAt hr hx hc
  have hU := hr.coherent
  have opt : ∀ s (f : Bool) B, f = true → (∃ CV, OptimisticLockAt tr x i s B CV) →
      (f = true → ∃ CV, FastLockAt tr x i s B CV) ∧
        ((∃ CV, OptimisticLockAt tr x i s B CV) ∨ ∃ ℓ', UpdateAt tr x i s ℓ') ∧
        (f = false → ∃ ℓ C CV, UpdateAt tr x i s ℓ ∧ ResultAt tr x i s C CV ∧
          B ∈ ℓ.frame.tree ∧ ℓ.frame.Anc B C ∧
          ∀ m : Int, (s : Int) - sp.k < m → m < s →
            ∃ S ∈ ℓ.frame.tree, (tr.state x i).saved m = some S.root ∧ ℓ.frame.Anc B S) :=
    fun s f B hf h => ⟨fun _ => h.imp fun _ => Or.inr, Or.inl h,
      fun hf' => Bool.false_ne_true (hf'.symm.trans hf) |>.elim⟩
  have he := hr.exec i ℓ hc.2 (hc.1 ▸ hx)
  rw [hc.1] at he
  have hpost := congrArg Prod.fst he
  have hemits := congrArg Prod.snd he
  simp only at hpost hemits
  rw [← hpost]
  generalize hA : tr.state x i = A at hpost hemits opt
  cases hcall : ℓ.call with
  | tick =>
    rw [hcall] at hemits
    refine (FromP.of_onTick hU hΦ hΦU x A _).mono fun s f B h => ?_
    obtain ⟨D, hD, rfl, h⟩ := h
    refine ⟨D, hD, rfl, ?_⟩
    rcases h with ⟨e, he', hf, hs, hsel⟩ | ⟨ht, hs0, hj, hs, hC, hslow⟩
    · refine ⟨(opt _ _ _ hf
        ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr ⟨e, hemits ▸ he', rfl⟩)⟩, hs.symm, hsel, rfl⟩).1,
        Or.inl ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr ⟨e, hemits ▸ he', rfl⟩)⟩,
          hs.symm, hsel, rfl⟩, ?_⟩
      intro hf'
      exact Bool.false_ne_true (hf'.symm.trans hf) |>.elim
    · have hu : UpdateAt tr x i s ℓ := by
        refine ⟨hc, hcall, ?_, hA ▸ hj⟩
        rw [hs]
        conv_lhs => rw [ht]
        simp only [SAParams.ts]
        push_cast [Nat.cast_sub hs0]
        ring
      refine ⟨fun hf => ?_, Or.inr ⟨ℓ, hu⟩, fun hf => ?_⟩
      · obtain ⟨C, hC, hconf, hD⟩ := hC hf
        exact ⟨_, Or.inl ⟨ℓ, C, hu, hA ▸ hC, hA ▸ hconf, hA ▸ hD, rfl⟩⟩
      · obtain ⟨C, hC, hBC, hsave⟩ := hslow hf
        exact ⟨ℓ, C, _, hu, ⟨ℓ, hu, hA ▸ hC, rfl⟩,
          hD, hBC, hA ▸ hsave⟩
  | proposal => exact FromP.of_proposal hΦ hΦU A _
  | toFG => exact FromP.of_eq (toFG_locks A _)
  | message m =>
    rw [hcall] at hemits
    refine FromP.trans hU ((FromP.of_optimistic_admit hU hΦ hΦU A rfl _ m).mono
      fun s f B h => ?_) ((FromP.of_tryVote hU hΦ hΦU x _ _).mono fun s f B h => ?_)
    · obtain ⟨D, hD, rfl, hf, hs, hsel⟩ := h
      refine ⟨D, hD, rfl, ?_, ?_, ?_⟩
      · exact (opt _ _ _ hf ⟨_, ℓ, _, ⟨hc, Or.inl ⟨m, hcall, hA ▸ rfl⟩⟩,
          hs.symm, hsel, rfl⟩).1
      · exact Or.inl ⟨_, ℓ, _, ⟨hc, Or.inl ⟨m, hcall, hA ▸ rfl⟩⟩,
          hs.symm, hsel, rfl⟩
      · intro hf'; exact Bool.false_ne_true (hf'.symm.trans hf) |>.elim
    · obtain ⟨D, hD, rfl, e, he', hf, hs, hsel⟩ := h
      refine ⟨D, hD, rfl, ?_, ?_, ?_⟩
      · exact (opt _ _ _ hf ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr
          ⟨e, hemits ▸ he', rfl⟩)⟩, hs.symm, hsel, rfl⟩).1
      · exact Or.inl ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr
          ⟨e, hemits ▸ he', rfl⟩)⟩, hs.symm, hsel, rfl⟩
      · intro hf'; exact Bool.false_ne_true (hf'.symm.trans hf) |>.elim
  | block B =>
    rw [hcall] at hemits
    have h₁ := FromP.of_optimistic hU hΦ hΦU (blockReceipt sp A (tr.time i) B) (tr.time i)
    rw [blockReceipt_locks] at h₁
    refine FromP.trans hU (h₁.mono fun s f B' h => ?_)
      ((FromP.of_tryVote hU hΦ hΦU x _ _).mono fun s f B' h => ?_)
    · obtain ⟨D, hD, rfl, hf, hs, hsel⟩ := h
      refine ⟨D, hD, rfl, ?_, ?_, ?_⟩
      · exact (opt _ _ _ hf ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inl
          ⟨B, hcall, hA ▸ rfl⟩)⟩, hs.symm, hsel, rfl⟩).1
      · exact Or.inl ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inl
          ⟨B, hcall, hA ▸ rfl⟩)⟩, hs.symm, hsel, rfl⟩
      · intro hf'; exact Bool.false_ne_true (hf'.symm.trans hf) |>.elim
    · obtain ⟨D, hD, rfl, e, he', hf, hs, hsel⟩ := h
      refine ⟨D, hD, rfl, ?_, ?_, ?_⟩
      · exact (opt _ _ _ hf ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr
          ⟨e, hemits ▸ he', rfl⟩)⟩, hs.symm, hsel, rfl⟩).1
      · exact Or.inl ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr
          ⟨e, hemits ▸ he', rfl⟩)⟩, hs.symm, hsel, rfl⟩
      · intro hf'; exact Bool.false_ne_true (hf'.symm.trans hf) |>.elim
  | restart =>
    exact FromP.of_eq ((restart_state sp) FGP ro x A ℓ.frame (tr.time i) hΦ
      (hr.time_nonneg i)).2.1

private theorem call_fromP (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    FromP U (tr.state x i).locks (tr.post i).locks
      (fun s f B => (f = true → ∃ CV, FastLockAt tr x i s B CV) ∧
        ((∃ CV, OptimisticLockAt tr x i s B CV) ∨ ∃ ℓ', UpdateAt tr x i s ℓ') ∧
        (f = false → ∃ ℓ C CV, UpdateAt tr x i s ℓ ∧ ResultAt tr x i s C CV ∧
          B ∈ ℓ.frame.tree ∧ ℓ.frame.Anc B C ∧
          ∀ m : Int, (s : Int) - sp.k < m → m < s →
            ∃ S ∈ ℓ.frame.tree, (tr.state x i).saved m = some S.root ∧ ℓ.frame.Anc B S)) := by
  intro l hl
  rcases call_candidate_fromP hr hx hc l hl with h | ⟨A, ⟨D, hD, rfl, h⟩, L, hL, hLr, hLA⟩
  · exact Or.inl h
  · exact Or.inr ⟨D, h, L, hL, hLr,
      hLA.trans ((viableAncestor_anc (frameIn_of_callAt hr hx hc).1 hD).2.mono
        (frameIn_of_callAt hr hx hc).2)⟩

private theorem Below.of_sitsBelow (hU : Coherent U) {l' l : Lock} {B : Blk sp.n FGP}
    (h : SitsBelow U l' l) (hB : Below U l B) : Below U l' B := by
  rcases h with rfl | ⟨A₁, hA₁, hA₁r, A₂, hA₂, hA₂r, hA⟩
  · exact hB
  obtain ⟨L, hL, hLr, hLB⟩ := hB
  have : A₂ = L := hU.1 hA₂ hL (hA₂r.trans hLr.symm)
  subst this
  exact ⟨A₁, hA₁, hA₁r, hA.trans hLB⟩

/-- A stored lock lies below the actual candidate stored at its write, not merely
below the raw selected block. Labels and the optimistic/update origin are retained;
`liveLocks`, `unlock`, and restart calls are covered by the same step invariant. -/
theorem lock_candidate_provenance (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {x : Fin sp.n} (hx : x ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state x i).locks, ∃ j < i, ∃ ℓ D,
      tr.CallAt x j ℓ ∧ D ∈ ℓ.frame.tree ∧
      ((∃ CV, OptimisticLockAt tr x j l.slot D CV) ∨ ∃ ℓ', UpdateAt tr x j l.slot ℓ') ∧
      ∃ L ∈ U, L.root = l.block ∧ Anc U L (ℓ.frame.viableAncestor D) := by
  induction i with
  | zero =>
    intro l hl
    change l ∈ (tr.init x).locks at hl
    rw [hr.init x hx] at hl
    exact absurd hl (Set.notMem_empty l)
  | succ i ih =>
    intro l hl
    rw [Trace.state] at hl
    split_ifs at hl with hnode
    · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 hnode.2
      rcases call_candidate_fromP hr hx ⟨hnode.1, hℓ⟩ l hl with
        ⟨l₀, hl₀, -, hs, hb⟩ | ⟨A, ⟨D, hD, rfl, -, ho, -⟩, hA⟩
      · obtain ⟨j, hj, ℓ', D, hc, hD, ho, hA⟩ := ih l₀ hl₀
        exact ⟨j, hj.trans (Nat.lt_succ_self i), ℓ', D, hc, hD, hs ▸ ho,
          Below.of_sitsBelow hr.coherent hb hA⟩
      · exact ⟨i, Nat.lt_succ_self i, ℓ, D, ⟨hnode.1, hℓ⟩, hD, ho, hA⟩
    · obtain ⟨j, hj, h⟩ := ih l hl
      exact ⟨j, hj.trans (Nat.lt_succ_self i), h⟩

/-- OW's write-time alternative. The current lock is below a candidate at a genuine
write cut, and that candidate is either below the write root or has a viable witness
in the write frame. No viability of the raw selected block is assumed. -/
theorem lock_write_witness (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {x : Fin sp.n} (hx : x ∈ H) {i : Nat} {l : Lock} (hl : l ∈ (tr.state x i).locks) :
    ∃ j < i, ∃ ℓ D A,
      tr.CallAt x j ℓ ∧ D ∈ ℓ.frame.tree ∧ A = ℓ.frame.viableAncestor D ∧
      ((∃ CV, OptimisticLockAt tr x j l.slot D CV) ∨ ∃ ℓ', UpdateAt tr x j l.slot ℓ') ∧
      (∃ L ∈ U, L.root = l.block ∧ Anc U L A) ∧
      (ℓ.frame.Anc A ℓ.frame.fcRoot ∨
        ∃ Q ∈ ℓ.frame.tree, Q ∈ ℓ.frame.viableHeads ∧ ℓ.frame.Anc A Q) := by
  obtain ⟨j, hj, ℓ, D, hc, hD, ho, hA⟩ := lock_candidate_provenance hr hx i l hl
  refine ⟨j, hj, ℓ, D, ℓ.frame.viableAncestor D, hc, hD, rfl, ho, hA, ?_⟩
  rcases (viableAncestor_spec (frameIn_of_callAt hr hx hc).1 hD).2.1 with h | h
  · exact Or.inl h
  · exact Or.inr h.2.2

/-- Every lock that an honest node holds before cut `i` sits below the block of a lock of its
slot and fast bit that the node wrote at an earlier cut. -/
private theorem provenance (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state x i).locks, ∃ j < i, ∃ B,
      ((l.fast = true → ∃ CV, FastLockAt tr x j l.slot B CV) ∧
        ((∃ CV, OptimisticLockAt tr x j l.slot B CV) ∨ ∃ ℓ, UpdateAt tr x j l.slot ℓ) ∧
        (l.fast = false → ∃ ℓ C CV, UpdateAt tr x j l.slot ℓ ∧ ResultAt tr x j l.slot C CV ∧
          B ∈ ℓ.frame.tree ∧ ℓ.frame.Anc B C ∧
          ∀ m : Int, (l.slot : Int) - sp.k < m → m < l.slot →
            ∃ S ∈ ℓ.frame.tree, (tr.state x j).saved m = some S.root ∧ ℓ.frame.Anc B S)) ∧
      ∃ L ∈ U, L.root = l.block ∧ Anc U L B := by
  induction i with
  | zero =>
    intro l hl
    change l ∈ (tr.init x).locks at hl
    rw [hr.init x hx] at hl
    exact absurd hl (Set.notMem_empty l)
  | succ i ih =>
    intro l hl
    rw [Trace.state] at hl
    split_ifs at hl with hnode
    · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 hnode.2
      rcases call_fromP hr hx ⟨hnode.1, hℓ⟩ l hl with ⟨l₀, hl₀, hf₀, hs, hb⟩ | ⟨B, h, hB⟩
      · obtain ⟨j, hj, B, h, hB⟩ := ih l₀ hl₀
        refine ⟨j, hj.trans (Nat.lt_succ_self i), B, ?_, Below.of_sitsBelow hr.coherent hb hB⟩
        rwa [hs, ← hf₀]
      · exact ⟨i, Nat.lt_succ_self i, B, h, hB⟩
    · obtain ⟨j, hj, h⟩ := ih l hl
      exact ⟨j, hj.trans (Nat.lt_succ_self i), h⟩

/-- Between cuts `a ≤ b`, the locks of an honest node sit below locks of cut `a` or below locks
that the node wrote in `[a, b)`. -/
private theorem fromP_between (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {a b : Nat} (hab : a ≤ b) :
    FromP U (tr.state x a).locks (tr.state x b).locks fun s _ B => ∃ j, a ≤ j ∧ j < b ∧
      ((∃ CV, OptimisticLockAt tr x j s B CV) ∨ ∃ ℓ, UpdateAt tr x j s ℓ) := by
  induction b, hab using Nat.le_induction with
  | base => exact FromP.of_eq rfl
  | succ b hab ih =>
    refine FromP.trans hr.coherent (ih.mono fun s f B ⟨j, h1, h2, h⟩ =>
      ⟨j, h1, h2.trans (Nat.lt_succ_self b), h⟩) fun l hl => ?_
    rw [Trace.state] at hl
    split_ifs at hl with hnode
    · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 hnode.2
      exact (call_fromP hr hx ⟨hnode.1, hℓ⟩ l hl).imp_right fun ⟨B, h, hB⟩ =>
        ⟨B, ⟨b, hab, Nat.lt_succ_self b, h.2.1⟩, hB⟩
    · exact Or.inl ⟨l, hl, rfl, rfl, Or.inl rfl⟩

/-- **Lock provenance from a cut.** Every lock that an honest node holds at cut `b` sits below a
lock of its slot that it held at cut `a ≤ b`, or below the block of a lock of its slot that the
node wrote at a cut in `[a, b)`. -/
theorem lock_provenance_from (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {a b : Nat} (hab : a ≤ b) :
    ∀ l ∈ (tr.state x b).locks,
      (∃ l' ∈ (tr.state x a).locks, l'.slot = l.slot ∧
        (l' = l ∨ ∃ L ∈ U, L.root = l.block ∧ ∃ L' ∈ U, L'.root = l'.block ∧ Anc U L L')) ∨
      ∃ j, a ≤ j ∧ j < b ∧ ∃ B,
        ((∃ CV, OptimisticLockAt tr x j l.slot B CV) ∨ ∃ ℓ, UpdateAt tr x j l.slot ℓ) ∧
        ∃ L ∈ U, L.root = l.block ∧ Anc U L B := by
  intro l hl
  rcases fromP_between hr hx hab l hl with ⟨l', hl', -, hs, hb⟩ | ⟨B, ⟨j, h1, h2, h⟩, hB⟩
  · exact Or.inl ⟨l', hl', hs.symm, hb.imp Eq.symm id⟩
  · exact Or.inr ⟨j, h1, h2, B, h, hB⟩

/-- **Fast-lock provenance.** Every fast lock that an honest node holds before cut `i` sits below
the block of a fast lock of its slot that the node wrote at an earlier cut. -/
theorem fast_lock_provenance (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state x i).locks, l.fast = true →
      ∃ j < i, ∃ B CV, FastLockAt tr x j l.slot B CV ∧ ∃ L ∈ U, L.root = l.block ∧ Anc U L B := by
  intro l hl hf
  obtain ⟨j, hj, B, ⟨h, -⟩, hB⟩ := provenance hr hx i l hl
  obtain ⟨CV, h⟩ := h hf
  exact ⟨j, hj, B, CV, h, hB⟩

/-- **Lock provenance.** Every lock, fast or slow, that an honest node holds before cut `i` sits
below the block of a lock of its slot that the node wrote at an earlier cut: by an optimistic
confirmation, or by the update of that slot. -/
theorem lock_provenance (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state x i).locks, ∃ j < i, ∃ B,
      ((∃ CV, OptimisticLockAt tr x j l.slot B CV) ∨ ∃ ℓ, UpdateAt tr x j l.slot ℓ) ∧
      ∃ L ∈ U, L.root = l.block ∧ Anc U L B := by
  intro l hl
  obtain ⟨j, hj, B, ⟨-, h, -⟩, hB⟩ := provenance hr hx i l hl
  exact ⟨j, hj, B, h, hB⟩

/-- A slow lock lies below the block selected by an update, which lies below that update's
result and every saved result in its preceding slow window. -/
theorem slow_lock_saved (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state x i).locks, l.fast = false →
      ∃ c < i, ∃ ℓ C CV, UpdateAt tr x c l.slot ℓ ∧ ResultAt tr x c l.slot C CV ∧
        ∃ Lb ∈ ℓ.frame.tree, ℓ.frame.Anc Lb C ∧ (∃ L ∈ U, L.root = l.block ∧ Anc U L Lb) ∧
          ∀ m : Int, (l.slot : Int) - sp.k < m → m < l.slot →
            ∃ S ∈ ℓ.frame.tree, (tr.state x c).saved m = some S.root ∧ ℓ.frame.Anc Lb S := by
  intro l hl hf
  obtain ⟨c, hci, Lb, ⟨-, -, hs⟩, hLb⟩ := provenance hr hx i l hl
  obtain ⟨ℓ, C, CV, hu, hC, hmem, hanc, hsave⟩ := hs hf
  exact ⟨c, hci, ℓ, C, CV, hu, hC, Lb, hmem, hanc, hLb, hsave⟩

end Consensus.Goldilocks.SA

end
