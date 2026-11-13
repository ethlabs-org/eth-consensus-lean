module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.HandlerFields
public import ConsensusLean.Instances.Goldilocks.Milestones.Statements.AC.Steps
public import ConsensusLean.Instances.Goldilocks.Lemmas.Common.Tree
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockProvenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
import ConsensusLean.Lemmas.Tactic.Linarith

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

variable {wm : SA.WriteMode}

variable {FGP : Type} {sp : SAParams}

/-! ## Locks that sit below others -/

/-- `add_locks` with new locks: the new locks are on the blocks of `N`'s entries. -/
private theorem FromP.of_addLocks {U : Set (Blk sp.n FGP)} (hU : Coherent U) {Φ : Frm sp.n FGP}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {L : Set Lock} {t : Time} {s : Nat}
    {N : Set (Nat × Bool × Nat)} {New : Nat → Bool → Blk sp.n FGP → Prop} {L₀ : Set Lock}
      (hL : L₀ = L)
    (hN : ∀ r f e, (r, f, e) ∈ N → ∃ B ∈ Φ.tree,
      B.root = r ∧ New s f (Φ.viableAncestor B)) :
    FromP U L (addLocks sp L₀ Φ t s N) New := by
  subst hL
  rw [fromP_iff]
  intro l' hl'
  obtain ⟨l, hl, B, hB, hBr, -, rfl⟩ := hl'
  rcases hl with hl | ⟨p, hp, rfl⟩
  · exact Or.inl ⟨l, hl, rfl, rfl, sitsBelow_iff.2 (Or.inr ⟨Φ.viableAncestor B,
      hΦU (viableAncestor_anc hΦ hB).1, rfl, B, hΦU hB, hBr,
      Goldilocks.Anc.mono hΦU (viableAncestor_anc hΦ hB).2⟩)⟩
  · obtain ⟨r, b, e⟩ := p
    simp only at hBr
    obtain ⟨D, hD, hDr, hND⟩ := hN r b e hp
    have : B = D := hU.1 (hΦU hB) (hΦU hD) (hBr.trans hDr.symm)
    subst this
    exact Or.inr ⟨Φ.viableAncestor B, hND, below_iff.2 ⟨Φ.viableAncestor B,
      hΦU (viableAncestor_anc hΦ hB).1, rfl, Relation.ReflTransGen.refl⟩⟩

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

variable {U : Set (Blk sp.n FGP)} {Φ : Frm sp.n FGP}

private theorem FromP.of_optimistic (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    (A : SAState sp.n) (t : Time) :
    FromP U A.locks (optimisticConfirmationM sp wm A Φ t).locks
      (fun s f B => ∃ D ∈ Φ.tree, B = Φ.viableAncestor D ∧
        f = true ∧ s = sp.slot t ∧ optimisticSelect sp A Φ t = some D) := by
  rw [optimisticConfirmationM_eq]
  split_ifs
  swap
  · exact FromP.of_eq rfl
  unfold optimisticConfirmation
  rcases h : optimisticSelect sp A Φ t with _ | B
  · exact FromP.of_eq rfl
  · rw [updateLatestConfirmed_keeps_locks]
    refine FromP.of_addLocks hU hΦ hΦU rfl fun r f e hr => ?_
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, -⟩ := hr
    have hB := h
    unfold optimisticSelect at hB
    dsimp only at hB
    split_ifs at hB
    exact ⟨B, (deepest_mem hB).1.1, rfl, B, (deepest_mem hB).1.1, rfl, rfl, rfl, rfl⟩

private theorem FromP.of_optimistic_admit (hU : Coherent U) (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {L : Set Lock} (A : SAState sp.n) (hL : A.locks = L) (t : Time)
    (v : Vote sp.n) :
    FromP U L (optimisticConfirmationM sp wm (admitVote sp A t v) Φ t).locks
      (fun s f B => ∃ D ∈ Φ.tree, B = Φ.viableAncestor D ∧ f = true ∧ s = sp.slot t ∧
        optimisticSelect sp (admitVote sp A t v) Φ t = some D) :=
    by
  have := FromP.of_optimistic (wm := wm) hU hΦ hΦU (admitVote sp A t v) t
  rwa [admitVote_locks_eq, hL] at this

private theorem FromP.of_tryVote
    {L : Set Lock} (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    (x : Fin sp.n) (A : SAState sp.n) (t : Time)
    (hL : UnlockRel sp A.locks Φ t ((sp.slot t : Int) - 1) (mergedVoteView sp A Φ (sp.slot t)) L) :
    FromP U A.locks (tryVoteWithM sp wm x L A Φ t).1.locks
      (fun s f B => ∃ D ∈ Φ.tree, B = Φ.viableAncestor D ∧
        ∃ e ∈ (tryVoteWithM sp wm x L A Φ t).2, f = true ∧ s = sp.slot t ∧
          optimisticSelect sp (admitVote sp e.readPoint t e.msg) Φ t = some D) := by
  unfold tryVoteWithM
  dsimp only
  by_cases hp : A.mayVote (sp.slot t) = true
  swap
  · simp only [hp]
    split_ifs <;> first
      | contradiction
      | exact FromP.of_eq rfl
      | exact FromP.of_movesBack hΦU (hL.movesBack hΦ)
  simp only [hp, ↓reduceIte]
  by_cases h1 : ¬ joined sp A t ∨ A.votedSlot = sp.slot t ∨ sp.ts (sp.slot t) + sp.Δ < t
  · rw [ite_eq_left h1]
    exact FromP.of_eq rfl
  rw [ite_eq_right h1]
  by_cases h2 : t < sp.ts (sp.slot t) + sp.Δ ∧ (sp.slot t = 0 ∨ ¬ voteReady sp Φ (sp.slot t))
  · rw [ite_eq_left h2]
    exact FromP.of_eq rfl
  rw [ite_eq_right h2]
  by_cases h3 : 0 < sp.slot t
  · rw [ite_eq_left h3]
    refine FromP.trans hU (FromP.of_movesBack hΦU (hL.movesBack hΦ))
      (FromP.mono (FromP.of_optimistic_admit hU hΦ hΦU _ ?_ t _) ?_)
    · rfl
    · exact fun s f B ⟨D, hD, heq, h⟩ => ⟨D, hD, heq, _, List.mem_singleton_self _, h⟩
  · rw [ite_eq_right h3]
    refine FromP.mono (FromP.of_optimistic_admit hU hΦ hΦU _ ?_ t _) ?_
    · rfl
    · exact fun s f B ⟨D, hD, heq, h⟩ => ⟨D, hD, heq, _, List.mem_singleton_self _, h⟩

private theorem FromP.of_updateConfirmation (hU : Coherent U) (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) (A : SAState sp.n) (t : Time) (s : Nat) :
    FromP U A.locks (updateConfirmationM sp wm A Φ t s).locks
      (fun s' f B => ∃ D ∈ Φ.tree, B = Φ.viableAncestor D ∧
        s' = s ∧ (f = true → ∃ C, getConfirmation sp A Φ s = some C ∧
          deepest Φ {X | X ∈ confirmationPath sp Φ C ∧ ¬ conflictsWithLock sp A.locks Φ t X ∧
            FastTest sp A Φ s X} = some D) ∧
        (f = false → ∃ C, getConfirmation sp A Φ s = some C ∧ Φ.Anc D C ∧
          ∀ m : Int, (s : Int) - wm.width < m → m < s →
            ∃ S ∈ Φ.tree, A.saved m = some S.root ∧ Φ.Anc D S) ∧
        (f = false → ∃ C, getConfirmation sp A Φ s = some C ∧
          deepest Φ {X | X ∈ confirmationPath sp Φ C ∧ ¬ conflictsWithLock sp A.locks Φ t X ∧
            ∀ m : Int, (s : Int) - wm.width < m → m < s →
              ∃ S ∈ Φ.tree, A.saved m = some S.root ∧ Φ.Anc X S} = some D)) := by
  rcases hC : getConfirmation sp A Φ s with _ | C
  · exact FromP.of_eq (updateConfirmationM_locks_of_none hC)
  · rw [updateConfirmationM_locks_of_some hC]
    refine FromP.of_addLocks hU hΦ hΦU rfl fun r f e hr => ?_
    rcases mem_newLocksM.1 hr with ⟨-, D, hD, hr⟩ | ⟨D, hD, hr⟩
    · simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, -⟩ := hr
      refine ⟨D, (deepest_mem hD).1.1.1.1, rfl, D, (deepest_mem hD).1.1.1.1, rfl, rfl,
        fun _ => ⟨C, rfl, ?_⟩, fun h => Bool.false_ne_true h.symm |>.elim,
        fun h => Bool.false_ne_true h.symm |>.elim⟩
      rw [← hD]
      congr 1
      ext X
      simp only [Set.mem_ofPred_eq, and_assoc]
    · simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, -⟩ := hr
      have hDm := (deepest_mem hD).1
      have hslow : ∀ m : Int, (s : Int) - wm.width < m → m < s →
          ∃ S ∈ Φ.tree, A.saved m = some S.root ∧ Φ.Anc D S := by
        intro m hm hms
        obtain ⟨S, hS, hsave, hDS⟩ := hDm.2 m hm hms
        refine ⟨S, hS, ?_, hDS⟩
        simpa only [Function.update_of_ne (show m ≠ (s : Int) by omega)] using hsave
      refine ⟨D, hDm.1.1.1, rfl, D, hDm.1.1.1, rfl, rfl, Bool.false_ne_true.elim,
        fun _ => ⟨C, rfl, hDm.1.1.2.2, hslow⟩, fun _ => ⟨C, rfl, ?_⟩⟩
      rw [← hD]
      congr 1
      ext X
      simp only [Set.mem_ofPred_eq, and_assoc]
      refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun m =>
        imp_congr_right fun _ => imp_congr_right fun hm => ?_
      rw [Function.update_of_ne (ne_of_lt hm)]

private theorem FromP.of_onTick
    {L : Set Lock} (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
    (x : Fin sp.n) (A : SAState sp.n) (t : Time)
    (hL : UnlockRel sp A.locks Φ t ((sp.slot t : Int) - 1) (mergedVoteView sp A Φ (sp.slot t)) L) :
    FromP U A.locks (acOnTickWithM sp wm x L A Φ t).1.locks
      (fun s f B => ∃ D ∈ Φ.tree, B = Φ.viableAncestor D ∧
        ((∃ e ∈ (acOnTickWithM sp wm x L A Φ t).2, f = true ∧ s = sp.slot t ∧
        optimisticSelect sp (admitVote sp e.readPoint t e.msg) Φ t = some D) ∨
        (t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t ∧ joined sp A t ∧
          s = sp.slot t - 1 ∧ (f = true → ∃ C, getConfirmation sp A Φ s = some C ∧
            deepest Φ {X | X ∈ confirmationPath sp Φ C ∧ ¬ conflictsWithLock sp A.locks Φ t X ∧
              FastTest sp A Φ s X} = some D) ∧
          (f = false → ∃ C, getConfirmation sp A Φ s = some C ∧ Φ.Anc D C ∧
            ∀ m : Int, (s : Int) - wm.width < m → m < s →
              ∃ S ∈ Φ.tree, A.saved m = some S.root ∧ Φ.Anc D S) ∧
          (f = false → ∃ C, getConfirmation sp A Φ s = some C ∧
            deepest Φ {X | X ∈ confirmationPath sp Φ C ∧ ¬ conflictsWithLock sp A.locks Φ t X ∧
              ∀ m : Int, (s : Int) - wm.width < m → m < s →
                ∃ S ∈ Φ.tree, A.saved m = some S.root ∧ Φ.Anc X S} = some D)))) := by
  unfold acOnTickWithM
  dsimp only
  by_cases hj : joined sp A t
  · rw [ite_eq_right (not_not_intro hj)]
    by_cases hu : t = sp.ts (sp.slot t) + sp.Δ
    · rw [ite_eq_left hu]
      by_cases ht : t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t
      · exfalso
        have hΔ := sp.toParams.hΔ
        linarith only [ht.1.symm.trans hu, hΔ]
      · rw [ite_eq_right ht]
        exact (FromP.of_tryVote hU hΦ hΦU x A t hL).mono
          fun s f B ⟨D, hD, heq, h⟩ => ⟨D, hD, heq, Or.inl h⟩
    · rw [ite_eq_right hu]
      by_cases ht : t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t
      · rw [ite_eq_left ht]
        refine (FromP.of_updateConfirmation hU hΦ hΦU A t _).mono fun s f B h => ?_
        obtain ⟨D, hD, heq, rfl, h2⟩ := h
        exact ⟨D, hD, heq, Or.inr ⟨ht.1, ht.2, hj, rfl, h2⟩⟩
      · rw [ite_eq_right ht]
        exact FromP.of_eq rfl
  · rw [ite_eq_left hj]
    exact FromP.of_eq rfl

/-! ## Over an SA trace -/

variable {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)} {tr : SATrace sp FGP ro}

/-- `frameIn_of_callAt` with the unlock given. -/
theorem frameIn_of_callAtU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U := by
  rcases hr.frameLaw x hx i ℓ hc with ⟨-, Φ₀, -, -, h⟩ | ⟨j, ℓ', -, -, -, h⟩ <;> exact h.1

/-- The frame of an honest node's call is well formed and inside `U`. -/
theorem frameIn_of_callAt (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    FrameOK ℓ.frame ∧ ℓ.frame.tree ⊆ U :=
  frameIn_of_callAtU (hr := hr.toU) (x := x) (hx := hx) (i := i) (ℓ := ℓ) (hc := hc)

/-- A call of an honest node keeps its locks below earlier ones or writes locks of its own cut:
by an optimistic confirmation, or by the update of their slot (fast ones by its fast test). -/
private theorem call_candidate_fromPU
    {u : Nat → Set Lock}
    (hr : ACLocalRunU wm u H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    FromP U (tr.state x i).locks (tr.post i).locks
      (fun s f B => ∃ D ∈ ℓ.frame.tree, B = ℓ.frame.viableAncestor D ∧
        (f = true → ∃ CV, FastLockAt tr x i s D CV) ∧
        ((∃ CV, OptimisticLockAt tr x i s D CV) ∨ ∃ ℓ', UpdateAt tr x i s ℓ') ∧
        (f = false → (∃ ℓ C, UpdateAt tr x i s ℓ ∧
          getConfirmation sp (tr.state x i) ℓ.frame s = some C ∧
          deepest ℓ.frame {X | X ∈ confirmationPath sp ℓ.frame C ∧
            ¬ conflictsWithLock sp (tr.state x i).locks ℓ.frame (tr.time i) X ∧
            ∀ m : Int, (s : Int) - wm.width < m → m < s →
              ∃ S ∈ ℓ.frame.tree, (tr.state x i).saved m = some S.root ∧
                ℓ.frame.Anc X S} = some D) ∧ ∃ ℓ C CV,
          UpdateAt tr x i s ℓ ∧ ResultAt tr x i s C CV ∧
          D ∈ ℓ.frame.tree ∧ ℓ.frame.Anc D C ∧
          ∀ m : Int, (s : Int) - wm.width < m → m < s →
            ∃ S ∈ ℓ.frame.tree, (tr.state x i).saved m = some S.root ∧ ℓ.frame.Anc D S)) := by
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hx hc
  have hU := hr.coherent
  have opt : ∀ s (f : Bool) B, f = true → (∃ CV, OptimisticLockAt tr x i s B CV) →
      (f = true → ∃ CV, FastLockAt tr x i s B CV) ∧
        ((∃ CV, OptimisticLockAt tr x i s B CV) ∨ ∃ ℓ', UpdateAt tr x i s ℓ') ∧
        (f = false → (∃ ℓ C, UpdateAt tr x i s ℓ ∧
          getConfirmation sp (tr.state x i) ℓ.frame s = some C ∧
          deepest ℓ.frame {X | X ∈ confirmationPath sp ℓ.frame C ∧
            ¬ conflictsWithLock sp (tr.state x i).locks ℓ.frame (tr.time i) X ∧
            ∀ m : Int, (s : Int) - wm.width < m → m < s →
              ∃ S ∈ ℓ.frame.tree, (tr.state x i).saved m = some S.root ∧
                ℓ.frame.Anc X S} = some B) ∧ ∃ ℓ C CV,
          UpdateAt tr x i s ℓ ∧ ResultAt tr x i s C CV ∧
          B ∈ ℓ.frame.tree ∧ ℓ.frame.Anc B C ∧
          ∀ m : Int, (s : Int) - wm.width < m → m < s →
            ∃ S ∈ ℓ.frame.tree, (tr.state x i).saved m = some S.root ∧ ℓ.frame.Anc B S) :=
    fun s f B hf h => ⟨fun _ => h.imp fun _ => Or.inr, Or.inl h,
      fun hf' => Bool.false_ne_true (hf'.symm.trans hf) |>.elim⟩
  have he := hr.exec i ℓ hc.2 (hc.1 ▸ hx)
  rw [hc.1] at he
  have hpost := congrArg Prod.fst he
  have hemits := congrArg Prod.snd he
  simp only at hpost hemits
  rw [← hpost]
  have hlaw := hr.lawfulAt hx hc hΦ
  generalize hA : tr.state x i = A at hpost hemits opt hlaw
  cases hcall : ℓ.call with
  | tick =>
    rw [hcall] at hemits hlaw
    refine (FromP.of_onTick (L := u i) hU hΦ hΦU x A _ hlaw).mono fun s f B h => ?_
    obtain ⟨D, hD, rfl, h⟩ := h
    refine ⟨D, hD, rfl, ?_⟩
    rcases h with ⟨e, he', hf, hs, hsel⟩ | ⟨ht, hs0, hj, hs, hC, hslow, hsl⟩
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
      · obtain ⟨C, hC, hD⟩ := hC hf
        exact ⟨_, Or.inl ⟨ℓ, C, hu, hA ▸ hC, hA ▸ hD, rfl⟩⟩
      · obtain ⟨C, hC, hBC, hsave⟩ := hslow hf
        obtain ⟨C', hC', hdeep'⟩ := hsl hf
        exact ⟨⟨ℓ, C', hu, hA ▸ hC', hA ▸ hdeep'⟩,
          ℓ, C, _, hu, ⟨ℓ, hu, hA ▸ hC, rfl⟩, hD, hBC, hA ▸ hsave⟩
  | proposal => rw [hcall] at hlaw; exact FromP.of_proposalWith hΦ hΦU A _ hlaw
  | toFG => exact FromP.of_eq (toFG_locks A _)
  | message m =>
    rw [hcall] at hemits hlaw
    refine FromP.trans hU ((FromP.of_optimistic_admit hU hΦ hΦU A rfl _ m).mono
      fun s f B h => ?_) ((FromP.of_tryVote (L := u i) hU hΦ hΦU x _ _ hlaw).mono
          fun s f B h => ?_)
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
    rw [hcall] at hemits hlaw
    have h₁ := FromP.of_optimistic (wm := wm) hU hΦ hΦU (blockReceipt sp A (tr.time i) B)
      (tr.time i)
    rw [blockReceipt_locks] at h₁
    refine FromP.trans hU (h₁.mono fun s f B' h => ?_)
      ((FromP.of_tryVote (L := u i) hU hΦ hΦU x _ _ hlaw).mono
          fun s f B' h => ?_)
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


/-- A call of an honest node keeps its locks below earlier ones or writes locks of its own cut:
by an optimistic confirmation, or by the update of their slot (fast ones by its fast test). -/
private theorem call_candidate_fromP
    (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    FromP U (tr.state x i).locks (tr.post i).locks
      (fun s f B => ∃ D ∈ ℓ.frame.tree, B = ℓ.frame.viableAncestor D ∧
        (f = true → ∃ CV, FastLockAt tr x i s D CV) ∧
        ((∃ CV, OptimisticLockAt tr x i s D CV) ∨ ∃ ℓ', UpdateAt tr x i s ℓ') ∧
        (f = false → (∃ ℓ C, UpdateAt tr x i s ℓ ∧
          getConfirmation sp (tr.state x i) ℓ.frame s = some C ∧
          deepest ℓ.frame {X | X ∈ confirmationPath sp ℓ.frame C ∧
            ¬ conflictsWithLock sp (tr.state x i).locks ℓ.frame (tr.time i) X ∧
            ∀ m : Int, (s : Int) - sp.k < m → m < s →
              ∃ S ∈ ℓ.frame.tree, (tr.state x i).saved m = some S.root ∧
                ℓ.frame.Anc X S} = some D) ∧ ∃ ℓ C CV,
          UpdateAt tr x i s ℓ ∧ ResultAt tr x i s C CV ∧
          D ∈ ℓ.frame.tree ∧ ℓ.frame.Anc D C ∧
          ∀ m : Int, (s : Int) - sp.k < m → m < s →
            ∃ S ∈ ℓ.frame.tree, (tr.state x i).saved m = some S.root ∧ ℓ.frame.Anc D S)) :=
  call_candidate_fromPU (hr := hr.toU) (x := x) (hx := hx) (i := i) (ℓ := ℓ) (hc := hc)
private theorem call_fromPU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    FromP U (tr.state x i).locks (tr.post i).locks
      (fun s f B => (f = true → ∃ CV, FastLockAt tr x i s B CV) ∧
        ((∃ CV, OptimisticLockAt tr x i s B CV) ∨ ∃ ℓ', UpdateAt tr x i s ℓ') ∧
        (f = false → ∃ ℓ C CV, UpdateAt tr x i s ℓ ∧ ResultAt tr x i s C CV ∧
          B ∈ ℓ.frame.tree ∧ ℓ.frame.Anc B C ∧
          ∀ m : Int, (s : Int) - wm.width < m → m < s →
            ∃ S ∈ ℓ.frame.tree, (tr.state x i).saved m = some S.root ∧ ℓ.frame.Anc B S)) := by
  rw [fromP_iff]
  intro l hl
  rcases fromP_iff.1 (call_candidate_fromPU hr hx hc) l hl with h | ⟨A, ⟨D, hD, rfl, h⟩, hA⟩
  · exact Or.inl h
  obtain ⟨L, hL, hLr, hLA⟩ := below_iff.1 hA
  exact Or.inr ⟨D, ⟨h.1, h.2.1, fun hf => (h.2.2 hf).2⟩, below_iff.2 ⟨L, hL, hLr,
    hLA.trans ((viableAncestor_anc (frameIn_of_callAtU hr hx hc).1 hD).2.mono
      (frameIn_of_callAtU hr hx hc).2)⟩⟩

/-- Same-write provenance, retaining the selected raw block and the stored candidate
together with its actual fast or slow selection. A slow lock's block is the slow selection
of its update over the path blocks that no live lock vetoes, vetoed result or not (the
predicate of `SlowLockAt` in `Statements/Healing/AC`, written out here to keep the AC layer
independent of the Healing statement layer). In particular, two independent provenance
traversals must not be used to identify the candidate. -/
theorem lock_selection_candidate_provenance
    (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {x : Fin sp.n} (hx : x ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state x i).locks, ∃ j < i, ∃ ℓ D,
      tr.CallAt x j ℓ ∧ D ∈ ℓ.frame.tree ∧
      ((l.fast = true ∧ ∃ CV, FastLockAt tr x j l.slot D CV) ∨
        (l.fast = false ∧ ∃ ℓ' C, UpdateAt tr x j l.slot ℓ' ∧
          getConfirmation sp (tr.state x j) ℓ'.frame l.slot = some C ∧
          deepest ℓ'.frame {X | X ∈ confirmationPath sp ℓ'.frame C ∧
            ¬ conflictsWithLock sp (tr.state x j).locks ℓ'.frame (tr.time j) X ∧
            ∀ m : Int, (l.slot : Int) - sp.k < m → m < l.slot →
              ∃ S ∈ ℓ'.frame.tree, (tr.state x j).saved m = some S.root ∧
                ℓ'.frame.Anc X S} = some D)) ∧
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
      rcases fromP_iff.1 (call_candidate_fromP hr hx ⟨hnode.1, hℓ⟩) l hl with
        ⟨l₀, hl₀, hf, hs, hb⟩ | ⟨A, ⟨D, hD, rfl, hfast, -, hslow⟩, hA⟩
      · obtain ⟨j, hj, ℓ', D, hc, hD, ho, hA⟩ := ih l₀ hl₀
        refine ⟨j, hj.trans (Nat.lt_succ_self i), ℓ', D, hc, hD, ?_,
          below_iff.1 (Below.of_sitsBelow hr.coherent hb (below_iff.2 hA))⟩
        simpa only [hf, ← hs] using ho
      · refine ⟨i, Nat.lt_succ_self i, ℓ, D, ⟨hnode.1, hℓ⟩, hD, ?_, below_iff.1 hA⟩
        cases hf : l.fast with
        | false => exact Or.inr ⟨rfl, (hslow hf).1⟩
        | true => exact Or.inl ⟨rfl, hfast hf⟩
    · obtain ⟨j, hj, h⟩ := ih l hl
      exact ⟨j, hj.trans (Nat.lt_succ_self i), h⟩

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
      rcases fromP_iff.1 (call_candidate_fromP hr hx ⟨hnode.1, hℓ⟩) l hl with
        ⟨l₀, hl₀, -, hs, hb⟩ | ⟨A, ⟨D, hD, rfl, -, ho, -⟩, hA⟩
      · obtain ⟨j, hj, ℓ', D, hc, hD, ho, hA⟩ := ih l₀ hl₀
        exact ⟨j, hj.trans (Nat.lt_succ_self i), ℓ', D, hc, hD, hs ▸ ho,
          below_iff.1 (Below.of_sitsBelow hr.coherent hb (below_iff.2 hA))⟩
      · exact ⟨i, Nat.lt_succ_self i, ℓ, D, ⟨hnode.1, hℓ⟩, hD, ho, below_iff.1 hA⟩
    · obtain ⟨j, hj, h⟩ := ih l hl
      exact ⟨j, hj.trans (Nat.lt_succ_self i), h⟩

/-- The write-time alternative for a stored lock. The current lock is below a candidate at a genuine
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
private theorem provenanceU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {x : Fin sp.n}
    (hx : x ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state x i).locks, ∃ j < i, ∃ B,
      ((l.fast = true → ∃ CV, FastLockAt tr x j l.slot B CV) ∧
        ((∃ CV, OptimisticLockAt tr x j l.slot B CV) ∨ ∃ ℓ, UpdateAt tr x j l.slot ℓ) ∧
        (l.fast = false → ∃ ℓ C CV, UpdateAt tr x j l.slot ℓ ∧ ResultAt tr x j l.slot C CV ∧
          B ∈ ℓ.frame.tree ∧ ℓ.frame.Anc B C ∧
          ∀ m : Int, (l.slot : Int) - wm.width < m → m < l.slot →
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
      rcases fromP_iff.1 (call_fromPU hr hx ⟨hnode.1, hℓ⟩) l hl with
        ⟨l₀, hl₀, hf₀, hs, hb⟩ | ⟨B, h, hB⟩
      · obtain ⟨j, hj, B, h, hB⟩ := ih l₀ hl₀
        refine ⟨j, hj.trans (Nat.lt_succ_self i), B, ?_,
          below_iff.1 (Below.of_sitsBelow hr.coherent hb (below_iff.2 hB))⟩
        rwa [hs, ← hf₀]
      · exact ⟨i, Nat.lt_succ_self i, B, h, below_iff.1 hB⟩
    · obtain ⟨j, hj, h⟩ := ih l hl
      exact ⟨j, hj.trans (Nat.lt_succ_self i), h⟩


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
      ∃ L ∈ U, L.root = l.block ∧ Anc U L B :=
  provenanceU (hr := hr.toU) (x := x) (hx := hx) (i := i)
/-- Between cuts `a ≤ b`, the locks of an honest node sit below locks of cut `a` or below locks
that the node wrote in `[a, b)`. -/
private theorem fromP_betweenU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {a b : Nat} (hab : a ≤ b) :
    FromP U (tr.state x a).locks (tr.state x b).locks fun s _ B => ∃ j, a ≤ j ∧ j < b ∧
      ((∃ CV, OptimisticLockAt tr x j s B CV) ∨ ∃ ℓ, UpdateAt tr x j s ℓ) := by
  induction b, hab using Nat.le_induction with
  | base => exact FromP.of_eq rfl
  | succ b hab ih =>
    refine FromP.trans hr.coherent (ih.mono fun s f B ⟨j, h1, h2, h⟩ =>
      ⟨j, h1, h2.trans (Nat.lt_succ_self b), h⟩) (fromP_iff.2 fun l hl => ?_)
    rw [Trace.state] at hl
    split_ifs at hl with hnode
    · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 hnode.2
      exact (fromP_iff.1 (call_fromPU hr hx ⟨hnode.1, hℓ⟩) l hl).imp_right fun ⟨B, h, hB⟩ =>
        ⟨B, ⟨b, hab, Nat.lt_succ_self b, h.2.1⟩, hB⟩
    · exact Or.inl ⟨l, hl, rfl, rfl, sitsBelow_iff.2 (Or.inl rfl)⟩

/-- `lock_provenance_from` with the unlock given. -/
theorem lock_provenance_fromU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {a b : Nat} (hab : a ≤ b) :
    ∀ l ∈ (tr.state x b).locks,
      (∃ l' ∈ (tr.state x a).locks, l'.slot = l.slot ∧
        (l' = l ∨ ∃ L ∈ U, L.root = l.block ∧ ∃ L' ∈ U, L'.root = l'.block ∧ Anc U L L')) ∨
      ∃ j, a ≤ j ∧ j < b ∧ ∃ B,
        ((∃ CV, OptimisticLockAt tr x j l.slot B CV) ∨ ∃ ℓ, UpdateAt tr x j l.slot ℓ) ∧
        ∃ L ∈ U, L.root = l.block ∧ Anc U L B := by
  intro l hl
  rcases fromP_iff.1 (fromP_betweenU hr hx hab) l hl with
    ⟨l', hl', -, hs, hb⟩ | ⟨B, ⟨j, h1, h2, h⟩, hB⟩
  · exact Or.inl ⟨l', hl', hs.symm, (sitsBelow_iff.1 hb).imp Eq.symm id⟩
  · exact Or.inr ⟨j, h1, h2, B, h, below_iff.1 hB⟩

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
        ∃ L ∈ U, L.root = l.block ∧ Anc U L B :=
  lock_provenance_fromU (hr := hr.toU) (x := x) (hx := hx) (a := a) (b := b) (hab := hab)

/-- `fast_lock_provenance` with the unlock given. -/
theorem fast_lock_provenanceU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {x : Fin sp.n}
    (hx : x ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state x i).locks, l.fast = true →
      ∃ j < i, ∃ B CV, FastLockAt tr x j l.slot B CV ∧ ∃ L ∈ U, L.root = l.block ∧ Anc U L B := by
  intro l hl hf
  obtain ⟨j, hj, B, ⟨h, -⟩, hB⟩ := provenanceU hr hx i l hl
  obtain ⟨CV, h⟩ := h hf
  exact ⟨j, hj, B, CV, h, hB⟩

/-- **Fast-lock provenance.** Every fast lock that an honest node holds before cut `i` sits below
the block of a fast lock of its slot that the node wrote at an earlier cut. -/
theorem fast_lock_provenance (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state x i).locks, l.fast = true →
      ∃ j < i, ∃ B CV, FastLockAt tr x j l.slot B CV ∧ ∃ L ∈ U, L.root = l.block ∧ Anc U L B :=
  fast_lock_provenanceU (hr := hr.toU) (x := x) (hx := hx) (i := i)

/-- `lock_provenance` with the unlock given. -/
theorem lock_provenanceU
    {u : Nat → Set Lock} (hr : ACLocalRunU wm u H U tr) {x : Fin sp.n}
    (hx : x ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state x i).locks, ∃ j < i, ∃ B,
      ((∃ CV, OptimisticLockAt tr x j l.slot B CV) ∨ ∃ ℓ, UpdateAt tr x j l.slot ℓ) ∧
      ∃ L ∈ U, L.root = l.block ∧ Anc U L B := by
  intro l hl
  obtain ⟨j, hj, B, ⟨-, h, -⟩, hB⟩ := provenanceU hr hx i l hl
  exact ⟨j, hj, B, h, hB⟩

/-- **Lock provenance.** Every lock, fast or slow, that an honest node holds before cut `i` sits
below the block of a lock of its slot that the node wrote at an earlier cut: by an optimistic
confirmation, or by the update of that slot. -/
theorem lock_provenance (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) (i : Nat) :
    ∀ l ∈ (tr.state x i).locks, ∃ j < i, ∃ B,
      ((∃ CV, OptimisticLockAt tr x j l.slot B CV) ∨ ∃ ℓ, UpdateAt tr x j l.slot ℓ) ∧
      ∃ L ∈ U, L.root = l.block ∧ Anc U L B :=
  lock_provenanceU (hr := hr.toU) (x := x) (hx := hx) (i := i)

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
