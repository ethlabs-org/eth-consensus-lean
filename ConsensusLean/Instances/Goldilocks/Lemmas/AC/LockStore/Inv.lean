module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.HandlerFields

public section

/-! # Goldilocks SA: the stored locks sit below the record

The invariant behind A0.4 (a), (b), (f) and A0.5: at a reachable state with frame `Φ` inside
`U`, the stored record `latest_confirmed` names a block `E` of `U`, the block of every stored
lock is an ancestor of `E` inside `U`, and `E` is in the tree whenever it extends `Φ.F`. The lock
functions only move locks back; a new lock is on an ancestor of the block that the record then
names, and that block does not conflict with any live lock, so a live lock that the record
leaves behind would put the old record, and with it the new block, below it. Frame steps keep
the invariant, since a block that extends the new `Φ.F` stays in the tree. -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type}

/-- **The lock invariant** of a state `A` with frame `Φ` inside `U`. -/
def LockInv (U : Set (Blk sp.n FGP)) (A : SAState sp.n) (Φ : Frm sp.n FGP) : Prop :=
  ∃ E ∈ U, E.root = A.latestConfirmed ∧ (Anc U Φ.F E → E ∈ Φ.tree) ∧
    ∀ l ∈ A.locks, ∀ X ∈ U, X.root = l.block → Anc U X E

variable {U : Set (Blk sp.n FGP)}

theorem lockInv_iff {A : SAState sp.n} {Φ : Frm sp.n FGP} :
    LockInv U A Φ ↔ ∃ E ∈ U, E.root = A.latestConfirmed ∧ (Anc U Φ.F E → E ∈ Φ.tree) ∧
      ∀ l ∈ A.locks, ∀ X ∈ U, X.root = l.block → Anc U X E :=
  Iff.rfl

/-- Locks that move back stay below the record. -/
private theorem LockInv.movesBack (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦU : Φ.tree ⊆ U)
    {A A' : SAState sp.n} (h : LockInv U A Φ) (hm : MovesBack sp Φ A.locks A'.locks)
    (hl : A'.latestConfirmed = A.latestConfirmed) : LockInv U A' Φ := by
  obtain ⟨E, hE, hEr, hEt, hlE⟩ := h
  refine ⟨E, hE, hEr.trans hl.symm, hEt, fun l' hl' X hX hXr => ?_⟩
  obtain ⟨l, hl, -, -, -, B, hB, hBr, B', hB', hB'r, hA⟩ := hm l' hl'
  obtain rfl : X = B' := hU.1 hX (hΦU hB') (hXr.trans hB'r.symm)
  exact (Anc.mono hΦU hA).trans (hlE l hl B (hΦU hB) hBr)

open Classical in
/-- **New locks below a new record.** The record moves to `C` (unless `C` is below it), and the
stored locks become the live locks of the old ones with new ones on ancestors of `C`; when `C` is
in the tree and conflicts with no live lock, the invariant holds after. -/
theorem LockInv.addLocks (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {A A' : SAState sp.n} (h : LockInv U A Φ) {t : Time} {s : Nat}
    {N : Set (Nat × Bool × Nat)} {C : Blk sp.n FGP} (hC : C ∈ Φ.tree)
    (hconf : ¬ conflictsWithLock sp A.locks Φ t C)
    (hlocks : A'.locks = SA.addLocks sp A.locks Φ t s N)
    (hN : ∀ p ∈ N, ∃ Y ∈ Φ.tree, Y.root = p.1 ∧ Φ.Anc Y C)
    (hrec : A'.latestConfirmed =
      if AncR Φ C A.latestConfirmed then A.latestConfirmed else C.root) :
    LockInv U A' Φ := by
  obtain ⟨E, hE, hEr, hEt, hlE⟩ := h
  -- a lock of the new set: the live lock of an old one, or of a new one
  have key : ∀ l' ∈ A'.locks, ∀ X ∈ U, X.root = l'.block →
      X ∈ Φ.tree ∧ ((X ∈ liveLockBlocks sp A.locks Φ t ∧ Anc U X E) ∨ Φ.Anc X C) := by
    intro l' hl' X hX hXr
    rw [hlocks] at hl'
    obtain ⟨l, hl, B, hB, hBr, hlive, rfl⟩ := hl'
    obtain ⟨hvt, hva⟩ := viableAncestor_anc hΦ hB
    obtain rfl : X = Φ.viableAncestor B := hU.1 hX (hΦU hvt) hXr
    refine ⟨hvt, ?_⟩
    rcases hl with hl | ⟨p, hp, rfl⟩
    · exact Or.inl ⟨⟨hvt, _, ⟨l, hl, B, hB, hBr, hlive, rfl⟩, rfl⟩,
        (Anc.mono hΦU hva).trans (hlE l hl B (hΦU hB) hBr)⟩
    · obtain ⟨Y, hY, hYr, hYC⟩ := hN p hp
      obtain rfl : B = Y := hΦ.coherent.1 hB hY (hBr.trans hYr.symm)
      exact Or.inr (hva.trans hYC)
  by_cases hA : AncR Φ C A.latestConfirmed
  · simp only [hA, ↓reduceIte] at hrec
    obtain ⟨R, hR, hRr, hCR⟩ := hA
    obtain rfl : R = E := hU.1 (hΦU hR) hE (hRr.trans hEr.symm)
    refine ⟨R, hE, hEr.trans hrec.symm, hEt, fun l' hl' X hX hXr => ?_⟩
    obtain ⟨-, (⟨-, hYE⟩ | hYC)⟩ := key l' hl' X hX hXr
    · exact hYE
    · exact Anc.mono hΦU (hYC.trans hCR)
  · simp only [hA, ↓reduceIte] at hrec
    refine ⟨C, hΦU hC, hrec.symm, fun _ => hC, fun l' hl' X hX hXr => ?_⟩
    obtain ⟨hY, (⟨hYl, hYE⟩ | hYC)⟩ := key l' hl' X hX hXr
    · -- `C` is compatible with the live lock block `X`
      have hcomp : Compatible Φ.tree C X := by
        by_contra hnc
        exact hconf ⟨X, hYl, hnc⟩
      rcases hcomp with hCY | hYC
      · -- `C ⪯ X ⪯ E`: then `E` is in the tree and the record does not move
        exfalso
        have hEt' : E ∈ Φ.tree := hEt ((Anc.mono hΦU (hΦ.rooted.2 X hY)).trans hYE)
        exact hA ⟨E, hEt', hEr, hCY.trans (anc_tree_of_anc_U hU hΦ hΦU hY hYE hEt')⟩
      · exact Anc.mono hΦU hYC
    · exact Anc.mono hΦU hYC

/-- **New locks below a live lock, the record kept.** When every new lock is on a block below a
live lock block, and the record does not move, the invariant holds after: the live lock blocks are
below the record. -/
private theorem LockInv.addLocks_below (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {A A' : SAState sp.n} (h : LockInv U A Φ) {t : Time} {s : Nat}
    {N : Set (Nat × Bool × Nat)} (hlocks : A'.locks = SA.addLocks sp A.locks Φ t s N)
    (hN : ∀ p ∈ N, ∃ Y ∈ Φ.tree, Y.root = p.1 ∧
      ∃ L ∈ liveLockBlocks sp A.locks Φ t, Φ.Anc Y L)
    (hrec : A'.latestConfirmed = A.latestConfirmed) : LockInv U A' Φ := by
  obtain ⟨E, hE, hEr, hEt, hlE⟩ := h
  have hLE : ∀ L ∈ liveLockBlocks sp A.locks Φ t, Anc U L E := by
    rintro L ⟨hL, l', ⟨l, hl, B, hB, hBr, -, rfl⟩, hLr⟩
    obtain ⟨hvt, hva⟩ := viableAncestor_anc hΦ hB
    obtain rfl : L = Φ.viableAncestor B := hΦ.coherent.1 hL hvt hLr.symm
    exact (Anc.mono hΦU hva).trans (hlE l hl B (hΦU hB) hBr)
  refine ⟨E, hE, hEr.trans hrec.symm, hEt, fun l' hl' X hX hXr => ?_⟩
  rw [hlocks] at hl'
  obtain ⟨l, hl, B, hB, hBr, -, rfl⟩ := hl'
  obtain ⟨hvt, hva⟩ := viableAncestor_anc hΦ hB
  obtain rfl : X = Φ.viableAncestor B := hU.1 hX (hΦU hvt) hXr
  rcases hl with hl | ⟨p, hp, rfl⟩
  · exact (Anc.mono hΦU hva).trans (hlE l hl B (hΦU hB) hBr)
  · obtain ⟨Y, hY, hYr, L, hL, hYL⟩ := hN p hp
    obtain rfl : B = Y := hΦ.coherent.1 hB hY (hBr.trans hYr.symm)
    exact (Anc.mono hΦU (hva.trans hYL)).trans (hLE L hL)

/-! ### Each SA function keeps the invariant -/

private theorem LockInv.of_eq {Φ : Frm sp.n FGP} {A A' : SAState sp.n} (h : LockInv U A Φ)
    (hl : A'.locks = A.locks) (hr : A'.latestConfirmed = A.latestConfirmed) : LockInv U A' Φ := by
  obtain ⟨E, hE, hEr, hEt, hlE⟩ := h
  exact ⟨E, hE, hEr.trans hr.symm, hEt, hl ▸ hlE⟩

variable (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
include hU hΦ hΦU

theorem LockInv.unlock {A : SAState sp.n} (h : LockInv U A Φ) (t : Time) (s : Int)
    (V : View sp.n) : LockInv U { A with locks := SA.unlock sp A.locks Φ t s V } Φ :=
  h.movesBack hU hΦU (((locks_move_back sp) FGP Φ A.locks t hΦ).2.2 s V) rfl

open Classical in
private theorem LockInv.optimistic {A : SAState sp.n} (h : LockInv U A Φ) (t : Time) :
    LockInv U (optimisticConfirmation sp A Φ t) Φ := by
  unfold optimisticConfirmation
  rcases hsel : optimisticSelect sp A Φ t with _ | B
  · exact h
  · have hB := hsel
    unfold optimisticSelect at hB
    dsimp only at hB
    split_ifs at hB
    obtain ⟨⟨hBt, -, hconf⟩, -⟩ := deepest_mem hB
    refine h.addLocks hU hΦ hΦU hBt hconf
      (N := {(B.root, true, fastExpiry sp A.locks Φ t (sp.slot t))}) (s := sp.slot t) ?_
      (fun p hp => ⟨B, hBt, by rw [Set.mem_singleton_iff.1 hp], .refl⟩) ?_
    · dsimp only; unfold updateLatestConfirmed; split_ifs <;> rfl
    · dsimp only; unfold updateLatestConfirmed; split_ifs <;> rfl

open Classical in
private theorem LockInv.update {A : SAState sp.n} (h : LockInv U A Φ) (t : Time) (s : Nat) :
    LockInv U (updateConfirmation sp A Φ t s) Φ := by
  unfold updateConfirmation
  rcases hC : getConfirmation sp A Φ s with _ | C
  · exact h.of_eq rfl rfl
  · dsimp only
    have hCt := (deepest_mem hC).1.1
    -- every new lock is on a block of `C`'s path that conflicts with no live lock
    have hN : ∀ (N : Set (Nat × Bool × Nat)), (∀ p ∈ N, ∃ Y, (Y ∈ confirmationPath sp Φ C ∧
        ¬ conflictsWithLock sp A.locks Φ t Y) ∧ Y.root = p.1) →
        ∀ p ∈ N, ∃ Y ∈ Φ.tree, Y.root = p.1 ∧ Φ.Anc Y C ∧ ¬ conflictsWithLock sp A.locks Φ t Y :=
      fun N hN p hp => by
        obtain ⟨Y, ⟨⟨hYt, -, hYC⟩, hnc⟩, hYr⟩ := hN p hp
        exact ⟨Y, hYt, hYr, hYC, hnc⟩
    split_ifs with hconf
    · -- vetoed: the record stays; a written path block is below the live lock `C` conflicts with
      obtain ⟨L, hL, hCL⟩ := hconf
      refine (h.of_eq (A' := { A with saved := Function.update A.saved s (some C.root) }) rfl rfl
        ).addLocks_below hU hΦ hΦU rfl (fun p hp => ?_) rfl
      have hp' : ∃ Y, (Y ∈ confirmationPath sp Φ C ∧ ¬ conflictsWithLock sp A.locks Φ t Y) ∧
          Y.root = p.1 := by
        rcases hp with ⟨D, hD, rfl⟩ | ⟨D, hD, rfl⟩ <;> exact ⟨D, (deepest_mem hD).1.1, rfl⟩
      obtain ⟨Y, hYt, hYr, hYC, hnc⟩ :=
        hN {p} (fun q hq => (Set.mem_singleton_iff.1 hq) ▸ hp') p rfl
      refine ⟨Y, hYt, hYr, L, hL, ?_⟩
      rcases (show Compatible Φ.tree Y L by by_contra h'; exact hnc ⟨L, hL, h'⟩) with hYL | hLY
      · exact hYL
      · exact absurd (Or.inr (hLY.trans hYC)) hCL
    · have hconf' : ¬ conflictsWithLock sp A.locks Φ t C := hconf
      simp only [updateLatestConfirmed_keeps_locks]
      refine (h.of_eq (A' := { A with saved := Function.update A.saved s (some C.root) }) rfl rfl
        ).addLocks hU hΦ hΦU hCt hconf' rfl (fun p hp => ?_) ?_
      · have hp' : ∃ Y, (Y ∈ confirmationPath sp Φ C ∧ ¬ conflictsWithLock sp A.locks Φ t Y) ∧
            Y.root = p.1 := by
          rcases hp with ⟨D, hD, rfl⟩ | ⟨D, hD, rfl⟩ <;> exact ⟨D, (deepest_mem hD).1.1, rfl⟩
        obtain ⟨Y, hYt, hYr, hYC, -⟩ :=
          hN {p} (fun q hq => (Set.mem_singleton_iff.1 hq) ▸ hp') p rfl
        exact ⟨Y, hYt, hYr, hYC⟩
      · unfold updateLatestConfirmed; split_ifs <;> rfl

private theorem LockInv.tryVote {A : SAState sp.n} (h : LockInv U A Φ) (x : Fin sp.n)
    (t : Time) : LockInv U (SA.tryVote sp x A Φ t).1 Φ := by
  unfold SA.tryVote
  dsimp only
  split_ifs
  · exact h
  · exact h
  · refine LockInv.optimistic hU hΦ hΦU ?_ _
    refine LockInv.of_eq ?_ (admitVote_keeps_locks _ _ _).1 (admitVote_keeps_locks _ _ _).2
    exact LockInv.of_eq (h.unlock hU hΦ hΦU _ _ _) rfl rfl
  · refine LockInv.optimistic hU hΦ hΦU ?_ _
    refine LockInv.of_eq ?_ (admitVote_keeps_locks _ _ _).1 (admitVote_keeps_locks _ _ _).2
    exact LockInv.of_eq h rfl rfl
  · exact LockInv.of_eq (h.unlock hU hΦ hΦU _ _ _) rfl rfl
  · exact LockInv.of_eq h rfl rfl

private theorem LockInv.step {ro : ReplayOrder sp FGP} {A : SAState sp.n} (h : LockInv U A Φ)
    (x : Fin sp.n) (t : Time) (ht : 0 ≤ t) (c : (goldilocksSA sp FGP ro).Call) :
    LockInv U ((goldilocksSA sp FGP ro).step x A Φ t c).1 Φ := by
  cases c with
  | tick =>
    change LockInv U (acOnTick sp x A Φ t).1 Φ
    unfold acOnTick
    dsimp only
    split_ifs
    · exact (h.tryVote hU hΦ hΦU x t).update hU hΦ hΦU _ _
    · exact h.update hU hΦ hΦU _ _
    · exact h.tryVote hU hΦ hΦU x t
    · exact h
    · exact h
  | proposal =>
    change LockInv U (acProposal sp A Φ t).1 Φ
    unfold acProposal
    dsimp only
    split_ifs
    · exact h.unlock hU hΦ hΦU _ _ _
    · exact h
  | toFG =>
    change LockInv U (acToFG sp A Φ t).1 Φ
    unfold acToFG
    split_ifs
    · split
      · exact h
      · split_ifs
        · exact h
        · exact h.of_eq rfl rfl
    · exact h
  | message m =>
    exact LockInv.tryVote hU hΦ hΦU (LockInv.optimistic hU hΦ hΦU
      (h.of_eq (admitVote_keeps_locks _ _ _).1 (admitVote_keeps_locks _ _ _).2) _) _ _
  | block B =>
    exact LockInv.tryVote hU hΦ hΦU (LockInv.optimistic hU hΦ hΦU
      (h.of_eq (blockReceipt_keeps_locks _ _ _).1 (blockReceipt_keeps_locks _ _ _).2) _) _ _
  | restart =>
    obtain ⟨-, hl, hr, -⟩ := (restart_state sp) FGP ro x A Φ t hΦ ht
    exact h.of_eq hl hr

omit hU hΦ hΦU

/-- **The lock invariant at reachable states.** -/
theorem lockInv_of_reachable {ro : ReplayOrder sp FGP} {x : Fin sp.n} (hU : Coherent U)
    {A : (goldilocksSA sp FGP ro).State} {Φ : (goldilocksSA sp FGP ro).Frm} {t₀ : Time}
    (hr : (goldilocksSA sp FGP ro).ReachableAt x U A Φ t₀) :
    (goldilocksSA sp FGP ro).FrameIn U Φ ∧ 0 ≤ t₀ ∧ LockInv U A Φ := by
  induction hr with
  | init Φ hinit hin =>
    obtain ⟨htree, hroot, -⟩ := hinit
    have hF : Φ.F ∈ Φ.tree := htree ▸ rfl
    refine ⟨hin, le_rfl, Φ.F, hin.2 hF, hroot, fun _ => hF, fun l hl => ?_⟩
    exact absurd hl (Set.notMem_empty l)
  | step c _ ht hok ih =>
    obtain ⟨hin, ht₀, E, hE, hEr, hEt, hlE⟩ := ih
    obtain ⟨hF, hX⟩ := callOK_retains sp hU hin hok
    refine ⟨hok.1, ht₀.trans ht, LockInv.step hU hok.1.1 hok.1.2 ?_ x _ (ht₀.trans ht) c⟩
    exact ⟨E, hE, hEr, fun h => hX E (hEt (hF.trans h)) h, hlE⟩

private theorem optimistic_blockStamp (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).blockStamp = A.blockStamp := by
  unfold optimisticConfirmation updateLatestConfirmed
  split
  · rfl
  · split_ifs <;> rfl

private theorem update_blockStamp (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) :
    (updateConfirmation sp A Φ t s).blockStamp = A.blockStamp := by
  unfold updateConfirmation updateLatestConfirmed
  dsimp only
  split
  · rfl
  · split_ifs <;> rfl

/-- The duty head of a vote that `try_vote` emits: the walk over the viable vote domain from
the anchor of a state with the lock invariant, whose block stamps are those of the state
`try_vote` leaves. -/
private def EmitOK (U : Set (Blk sp.n FGP)) (Φ : Frm sp.n FGP) (t : Time) (post : SAState sp.n)
    (es : List (Em sp FGP)) : Prop :=
  ∀ e ∈ es, ∀ d, e.head = some d → ∃ (A₁ : SAState sp.n) (V : View sp.n) (σ : Int),
    LockInv U A₁ Φ ∧ A₁.blockStamp = post.blockStamp ∧
    d = ⟨getHead sp A₁ Φ t (Φ.viableTree (voteDomain sp A₁ Φ (sp.slot t))) V σ,
      getAnchor sp A₁ Φ t, voteDomain sp A₁ Φ (sp.slot t)⟩

include hU hΦ hΦU

private theorem LockInv.tryVote_emits {A : SAState sp.n} (h : LockInv U A Φ) (x : Fin sp.n)
    (t : Time) : EmitOK U Φ t (SA.tryVote sp x A Φ t).1 (SA.tryVote sp x A Φ t).2 := by
  unfold SA.tryVote
  dsimp only
  split_ifs with h1 h2 h3
  · simp [EmitOK]
  · simp [EmitOK]
  · simp only [EmitOK, List.mem_singleton, forall_eq, Option.some.injEq, forall_eq']
    exact ⟨_, _, _, h.unlock hU hΦ hΦU _ _ _, by
      rw [optimistic_blockStamp, admitVote_blockStamp], rfl⟩
  · simp only [EmitOK, List.mem_singleton, forall_eq, Option.some.injEq, forall_eq']
    exact ⟨_, _, _, h, by rw [optimistic_blockStamp, admitVote_blockStamp], rfl⟩
  all_goals simp [EmitOK]

/-- **The emitted duty heads of a call** from a state with the lock invariant at the call's
frame. -/
theorem LockInv.step_emits {ro : ReplayOrder sp FGP} {A : SAState sp.n} (h : LockInv U A Φ)
    (x : Fin sp.n) (t : Time) (ht : 0 ≤ t) (c : (goldilocksSA sp FGP ro).Call) :
    ∀ e ∈ ((goldilocksSA sp FGP ro).step x A Φ t c).2, ∀ d, e.head = some d →
      ∃ (A₁ : SAState sp.n) (V : View sp.n) (σ : Int), LockInv U A₁ Φ ∧
        A₁.blockStamp = ((goldilocksSA sp FGP ro).step x A Φ t c).1.blockStamp ∧
        d = ⟨getHead sp A₁ Φ t (Φ.viableTree (voteDomain sp A₁ Φ (sp.slot t))) V σ,
          getAnchor sp A₁ Φ t, voteDomain sp A₁ Φ (sp.slot t)⟩ := by
  cases c with
  | tick =>
    change EmitOK U Φ t (acOnTick sp x A Φ t).1 (acOnTick sp x A Φ t).2
    unfold acOnTick
    dsimp only
    split
    · simp only [EmitOK, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
    · split
      · split <;> dsimp only
        · intro e he d hd
          obtain ⟨A₁, V, σ, h1, h2, h3⟩ := h.tryVote_emits hU hΦ hΦU x t e he d hd
          exact ⟨A₁, V, σ, h1, h2.trans (update_blockStamp _ _ _ _).symm, h3⟩
        · simp only [EmitOK, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
      · split <;> dsimp only
        · exact h.tryVote_emits hU hΦ hΦU x t
        · simp only [EmitOK, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | proposal => simp [ACInterface.step]
  | toFG => simp [ACInterface.step]
  | message m =>
    exact LockInv.tryVote_emits hU hΦ hΦU (LockInv.optimistic hU hΦ hΦU
      (h.of_eq (admitVote_keeps_locks _ _ _).1 (admitVote_keeps_locks _ _ _).2) _) _ _
  | block B =>
    exact LockInv.tryVote_emits hU hΦ hΦU (LockInv.optimistic hU hΦ hΦU
      (h.of_eq (blockReceipt_keeps_locks _ _ _).1 (blockReceipt_keeps_locks _ _ _).2) _) _ _
  | restart =>
    intro e he
    change e ∈ (acRestart sp ro x A Φ t).2 at he
    rw [((restart_state sp) FGP ro x A Φ t hΦ ht).1] at he
    simp at he

private theorem LockInv.tryVote_readPoint {A : SAState sp.n} (h : LockInv U A Φ) (x : Fin sp.n)
    (t : Time) : ∀ e ∈ (SA.tryVote sp x A Φ t).2, LockInv U e.readPoint Φ := by
  unfold SA.tryVote
  dsimp only
  split_ifs
  · simp
  · simp
  · intro e he
    rw [List.mem_singleton] at he
    subst he
    exact (h.unlock hU hΦ hΦU _ _ _).of_eq rfl rfl
  · intro e he
    rw [List.mem_singleton] at he
    subst he
    exact h.of_eq rfl rfl
  all_goals simp

/-- **The read point of an emission keeps the lock invariant.** Every vote that a call emits from
a state with the lock invariant at the call's frame reads a state with the invariant: the
read point is the input of `try_vote`, after the optimistic check of a receipt and the
unlocking, with the same record. -/
theorem LockInv.step_readPoint {ro : ReplayOrder sp FGP} {A : SAState sp.n}
    (h : LockInv U A Φ) (x : Fin sp.n) (t : Time) (ht : 0 ≤ t)
    (c : (goldilocksSA sp FGP ro).Call) :
    ∀ e ∈ ((goldilocksSA sp FGP ro).step x A Φ t c).2, LockInv U e.readPoint Φ := by
  cases c with
  | tick =>
    change ∀ e ∈ (acOnTick sp x A Φ t).2, LockInv U e.readPoint Φ
    unfold acOnTick
    dsimp only
    split_ifs
    all_goals first
      | exact h.tryVote_readPoint hU hΦ hΦU x t
      | simp
  | proposal => simp [ACInterface.step]
  | toFG => simp [ACInterface.step]
  | message m =>
    exact LockInv.tryVote_readPoint hU hΦ hΦU (LockInv.optimistic hU hΦ hΦU
      (h.of_eq (admitVote_keeps_locks _ _ _).1 (admitVote_keeps_locks _ _ _).2) _) _ _
  | block B =>
    exact LockInv.tryVote_readPoint hU hΦ hΦU (LockInv.optimistic hU hΦ hΦU
      (h.of_eq (blockReceipt_keeps_locks _ _ _).1 (blockReceipt_keeps_locks _ _ _).2) _) _ _
  | restart =>
    intro e he
    change e ∈ (acRestart sp ro x A Φ t).2 at he
    rw [((restart_state sp) FGP ro x A Φ t hΦ ht).1] at he
    simp at he

omit hU hΦ hΦU

/-- The lock invariant passes to the frame of a lawful next call. -/
theorem LockInv.callOK {ro : ReplayOrder sp FGP} (hU : Coherent U) {A : SAState sp.n}
    {Φ Φ' : Frm sp.n FGP} {t : Time} {c : (goldilocksSA sp FGP ro).Call}
    (hin : (goldilocksSA sp FGP ro).FrameIn U Φ)
    (hok : (goldilocksSA sp FGP ro).CallOK U Φ t c Φ') (h : LockInv U A Φ) :
    LockInv U A Φ' := by
  obtain ⟨E, hE, hEr, hEt, hlE⟩ := h
  obtain ⟨hF, hX⟩ := callOK_retains sp hU hin hok
  exact ⟨E, hE, hEr, fun h => hX E (hEt (hF.trans h)) h, hlE⟩

end Consensus.Goldilocks.SA

end
