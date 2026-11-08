module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.HandlerFields

public section

/-! # The outage over AC traces, the lock rows: the lock invariant and the live-lock chain

The lock invariant `SA.LockInv` (the stored record names a block of `U` above every stored lock
block, in the tree once it extends `Φ.F`) at the states reachable with the unlock given at a
write mode (`ReachableAtU wm`), and its consequences at the honest calls of an AC trace with the
unlock given (`ACLocalRunU wm u`). The unlock is read only through the unlock relation: the
locks `L₁` a call executes at only move back from the call's unlock input
(`UnlockRel.movesBack`). The fast and optimistic writes of the mode are new locks on blocks of a
confirmation path or on the optimistic selection, which the record then names or extends, as at
the parent's mode; the slow lock at width `wm.width` is on a block of the path as well. So the
invariant holds at every mode, with no width condition:

* `lockInv_of_reachableU`: `SA.lockInv_of_reachable` at the states reachable with the unlock
  given;
* `lockInv_postAC`: the invariant after an honest call, in the call's frame;
* `lockInv_stateAC`: the invariant of the state before an honest call, in the call's frame
  (the composite `lockInv_state`, the node's frame read as the call's frame);
* `liveBlocks_chain_atAC`: the live lock blocks of the state before an honest call lie on one
  chain of the call's frame, at every time (the composite `liveBlocks_chain_at`). -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type} {U : Set (Blk sp.n FGP)} {wm : WriteMode}

/-! ### The lock functions at a mode keep the invariant

Public, so that a layer that runs these lock functions in its own handlers (with another head
walk) carries the invariant without restating them. -/

/-- Locks that move back stay below the record. -/
theorem lockInv_movesBackAC (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦU : Φ.tree ⊆ U)
    {A A' : SAState sp.n} (h : LockInv U A Φ) (hm : MovesBack sp Φ A.locks A'.locks)
    (hl : A'.latestConfirmed = A.latestConfirmed) : LockInv U A' Φ := by
  obtain ⟨E, hE, hEr, hEt, hlE⟩ := lockInv_iff.1 h
  refine lockInv_iff.2 ⟨E, hE, hEr.trans hl.symm, hEt, fun l' hl' X hX hXr => ?_⟩
  obtain ⟨l, hl, -, -, -, B, hB, hBr, B', hB', hB'r, hA⟩ := hm l' hl'
  obtain rfl : X = B' := hU.1 hX (hΦU hB') (hXr.trans hB'r.symm)
  exact (Anc.mono hΦU hA).trans (hlE l hl B (hΦU hB) hBr)

/-- The same locks and record keep the invariant. -/
theorem lockInv_of_eqAC {Φ : Frm sp.n FGP} {A A' : SAState sp.n} (h : LockInv U A Φ)
    (hl : A'.locks = A.locks) (hr : A'.latestConfirmed = A.latestConfirmed) :
    LockInv U A' Φ := by
  obtain ⟨E, hE, hEr, hEt, hlE⟩ := lockInv_iff.1 h
  exact lockInv_iff.2 ⟨E, hE, hEr.trans hr.symm, hEt, hl ▸ hlE⟩

open Classical in
/-- New locks below a new record: the record moves to `C` (unless `C` is below it), and the
stored locks become the live locks of the old ones with new ones on ancestors of `C`; when `C` is
in the tree and conflicts with no live lock, the invariant holds after. -/
theorem lockInv_addLocksAC (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {A A' : SAState sp.n} (h : LockInv U A Φ) {t : Time} {s : Nat}
    {N : Set (Nat × Bool × Nat)} {C : Blk sp.n FGP} (hC : C ∈ Φ.tree)
    (hconf : ¬ conflictsWithLock sp A.locks Φ t C)
    (hlocks : A'.locks = SA.addLocks sp A.locks Φ t s N)
    (hN : ∀ p ∈ N, ∃ Y ∈ Φ.tree, Y.root = p.1 ∧ Φ.Anc Y C)
    (hrec : A'.latestConfirmed =
      if AncR Φ C A.latestConfirmed then A.latestConfirmed else C.root) :
    LockInv U A' Φ := by
  obtain ⟨E, hE, hEr, hEt, hlE⟩ := lockInv_iff.1 h
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
    refine lockInv_iff.2 ⟨R, hE, hEr.trans hrec.symm, hEt, fun l' hl' X hX hXr => ?_⟩
    obtain ⟨-, (⟨-, hYE⟩ | hYC)⟩ := key l' hl' X hX hXr
    · exact hYE
    · exact Anc.mono hΦU (hYC.trans hCR)
  · simp only [hA, ↓reduceIte] at hrec
    refine lockInv_iff.2 ⟨C, hΦU hC, hrec.symm, fun _ => hC, fun l' hl' X hX hXr => ?_⟩
    obtain ⟨hY, (⟨hYl, hYE⟩ | hYC)⟩ := key l' hl' X hX hXr
    · have hcomp : Compatible Φ.tree C X := by
        by_contra hnc
        exact hconf ⟨X, hYl, hnc⟩
      rcases hcomp with hCY | hYC
      · exfalso
        have hEt' : E ∈ Φ.tree := hEt ((Anc.mono hΦU (hΦ.rooted.2 X hY)).trans hYE)
        exact hA ⟨E, hEt', hEr, hCY.trans (anc_tree_of_anc_U hU hΦ hΦU hY hYE hEt')⟩
      · exact Anc.mono hΦU hYC
    · exact Anc.mono hΦU hYC

/-- New locks below a live lock, the record kept. -/
theorem lockInv_addLocks_belowAC (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {A A' : SAState sp.n} (h : LockInv U A Φ) {t : Time} {s : Nat}
    {N : Set (Nat × Bool × Nat)} (hlocks : A'.locks = SA.addLocks sp A.locks Φ t s N)
    (hN : ∀ p ∈ N, ∃ Y ∈ Φ.tree, Y.root = p.1 ∧
      ∃ L ∈ liveLockBlocks sp A.locks Φ t, Φ.Anc Y L)
    (hrec : A'.latestConfirmed = A.latestConfirmed) : LockInv U A' Φ := by
  obtain ⟨E, hE, hEr, hEt, hlE⟩ := lockInv_iff.1 h
  have hLE : ∀ L ∈ liveLockBlocks sp A.locks Φ t, Anc U L E := by
    rintro L ⟨hL, l', ⟨l, hl, B, hB, hBr, -, rfl⟩, hLr⟩
    obtain ⟨hvt, hva⟩ := viableAncestor_anc hΦ hB
    obtain rfl : L = Φ.viableAncestor B := hΦ.coherent.1 hL hvt hLr.symm
    exact (Anc.mono hΦU hva).trans (hlE l hl B (hΦU hB) hBr)
  refine lockInv_iff.2 ⟨E, hE, hEr.trans hrec.symm, hEt, fun l' hl' X hX hXr => ?_⟩
  rw [hlocks] at hl'
  obtain ⟨l, hl, B, hB, hBr, -, rfl⟩ := hl'
  obtain ⟨hvt, hva⟩ := viableAncestor_anc hΦ hB
  obtain rfl : X = Φ.viableAncestor B := hU.1 hX (hΦU hvt) hXr
  rcases hl with hl | ⟨p, hp, rfl⟩
  · exact (Anc.mono hΦU hva).trans (hlE l hl B (hΦU hB) hBr)
  · obtain ⟨Y, hY, hYr, L, hL, hYL⟩ := hN p hp
    obtain rfl : B = Y := hΦ.coherent.1 hB hY (hBr.trans hYr.symm)
    exact (Anc.mono hΦU (hva.trans hYL)).trans (hLE L hL)

variable (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
include hU hΦ hΦU

open Classical in
/-- The optimistic confirmation at mode `wm`: its new lock is on the optimistic selection, which
conflicts with no live lock. -/
theorem lockInv_optimisticAC {A : SAState sp.n} (h : LockInv U A Φ) (t : Time) :
    LockInv U (optimisticConfirmationM sp wm A Φ t) Φ := by
  refine optimisticConfirmationM_of (P := fun X => LockInv U X Φ) ?_ h
  unfold optimisticConfirmation
  rcases hsel : optimisticSelect sp A Φ t with _ | B
  · exact h
  · have hB := hsel
    unfold optimisticSelect at hB
    dsimp only at hB
    split_ifs at hB
    obtain ⟨⟨hBt, -, hconf⟩, -⟩ := deepest_mem hB
    refine lockInv_addLocksAC hU hΦ hΦU h hBt hconf
      (N := {(B.root, true, fastExpiry sp A.locks Φ t (sp.slot t))}) (s := sp.slot t) ?_
      (fun p hp => ⟨B, hBt, by rw [Set.mem_singleton_iff.1 hp], .refl⟩) ?_
    · dsimp only; unfold updateLatestConfirmed; split_ifs <;> rfl
    · dsimp only; unfold updateLatestConfirmed; split_ifs <;> rfl

open Classical in
/-- The update at mode `wm`: every new lock (the fast arm's and the slow lock of width
`wm.width`) is on a block of the result's path that conflicts with no live lock. -/
theorem lockInv_updateAC {A : SAState sp.n} (h : LockInv U A Φ) (t : Time) (s : Nat) :
    LockInv U (updateConfirmationM sp wm A Φ t s) Φ := by
  unfold updateConfirmationM
  rcases hC : getConfirmation sp A Φ s with _ | C
  · exact lockInv_of_eqAC h rfl rfl
  · dsimp only
    have hCt := (deepest_mem hC).1.1
    have hN : ∀ (sv : Int → Option Nat) (L : Set Lock), ∀ p ∈ newLocksM sp wm A Φ t s C sv L,
        ∃ Y ∈ Φ.tree, Y.root = p.1 ∧ Φ.Anc Y C ∧ ¬ conflictsWithLock sp A.locks Φ t Y := by
      intro sv L p hp
      have hp' : ∃ Y, (Y ∈ confirmationPath sp Φ C ∧ ¬ conflictsWithLock sp A.locks Φ t Y) ∧
          Y.root = p.1 := by
        rcases mem_newLocksM.1 hp with ⟨-, B, hB, rfl⟩ | ⟨B, hB, rfl⟩ <;>
          exact ⟨B, (deepest_mem hB).1.1, rfl⟩
      obtain ⟨Y, ⟨⟨hYt, -, hYC⟩, hnc⟩, hYr⟩ := hp'
      exact ⟨Y, hYt, hYr, hYC, hnc⟩
    split_ifs with hconf
    · obtain ⟨L, hL, hCL⟩ := hconf
      refine lockInv_addLocks_belowAC hU hΦ hΦU
        (lockInv_of_eqAC (A' := { A with saved := Function.update A.saved s (some C.root) }) h
          rfl rfl) rfl (fun p hp => ?_) rfl
      obtain ⟨Y, hYt, hYr, hYC, hnc⟩ := hN _ _ p hp
      refine ⟨Y, hYt, hYr, L, hL, ?_⟩
      rcases (show Compatible Φ.tree Y L by by_contra h'; exact hnc ⟨L, hL, h'⟩) with hYL | hLY
      · exact hYL
      · exact absurd (Or.inr (hLY.trans hYC)) hCL
    · have hconf' : ¬ conflictsWithLock sp A.locks Φ t C := hconf
      simp only [updateLatestConfirmed_keeps_locks]
      refine lockInv_addLocksAC hU hΦ hΦU
        (lockInv_of_eqAC (A' := { A with saved := Function.update A.saved s (some C.root) }) h
          rfl rfl) hCt hconf' rfl (fun p hp => ?_) ?_
      · obtain ⟨Y, hYt, hYr, hYC, -⟩ := hN _ _ p hp
        exact ⟨Y, hYt, hYr, hYC⟩
      · unfold updateLatestConfirmed; split_ifs <;> rfl

/-- `try_vote` at mode `wm` with the locks `L₁` after its unlock, which move back from the
input's. -/
private theorem lockInv_tryVoteAC {A : SAState sp.n} (h : LockInv U A Φ) {L₁ : Set Lock}
    (hm : MovesBack sp Φ A.locks L₁) (x : Fin sp.n) (t : Time) :
    LockInv U (tryVoteWithM sp wm x L₁ A Φ t).1 Φ := by
  unfold tryVoteWithM
  dsimp only
  split_ifs
  · exact h
  · exact h
  all_goals
    refine lockInv_optimisticAC hU hΦ hΦU (lockInv_of_eqAC ?_ (admitVote_keeps_locks _ _ _).1
      (admitVote_keeps_locks _ _ _).2) _
    first
    | exact lockInv_of_eqAC (lockInv_movesBackAC (A' := { A with locks := L₁ }) hU hΦU h hm rfl)
        rfl rfl
    | exact lockInv_of_eqAC h rfl rfl

/-- A call at mode `wm` with the locks `L₁`, which move back from the call's unlock input. -/
private theorem lockInv_stepAC {ro : ReplayOrder sp FGP} {A : SAState sp.n} (h : LockInv U A Φ)
    (x : Fin sp.n) (t : Time) (ht : 0 ≤ t) (c : (goldilocksSA sp FGP ro).Call) {L₁ : Set Lock}
    (hm : MovesBack sp Φ (callInputM sp wm A Φ t c).locks L₁) :
    LockInv U (stepWithM sp ro wm x L₁ A Φ t c).1 Φ := by
  cases c with
  | tick =>
    change LockInv U (acOnTickWithM sp wm x L₁ A Φ t).1 Φ
    unfold acOnTickWithM
    dsimp only
    split_ifs
    · exact lockInv_updateAC hU hΦ hΦU (lockInv_tryVoteAC hU hΦ hΦU h hm x t) _ _
    · exact lockInv_updateAC hU hΦ hΦU h _ _
    · exact lockInv_tryVoteAC hU hΦ hΦU h hm x t
    · exact h
    · exact h
  | proposal =>
    change LockInv U (acProposalWith sp L₁ A Φ t).1 Φ
    unfold acProposalWith
    dsimp only
    split_ifs
    · exact lockInv_movesBackAC (A' := { A with locks := L₁ }) hU hΦU h hm rfl
    · exact h
  | toFG =>
    change LockInv U (acToFG sp A Φ t).1 Φ
    unfold acToFG
    split_ifs
    · split
      · exact h
      · split_ifs
        · exact h
        · exact lockInv_of_eqAC h rfl rfl
    · exact h
  | message m =>
    exact lockInv_tryVoteAC hU hΦ hΦU (lockInv_optimisticAC hU hΦ hΦU
      (lockInv_of_eqAC h (admitVote_keeps_locks _ _ _).1 (admitVote_keeps_locks _ _ _).2) _) hm _ _
  | block B =>
    exact lockInv_tryVoteAC hU hΦ hΦU (lockInv_optimisticAC hU hΦ hΦU
      (lockInv_of_eqAC h (blockReceipt_keeps_locks _ _ _).1 (blockReceipt_keeps_locks _ _ _).2)
      _) hm _ _
  | restart =>
    obtain ⟨-, hl, hr, -⟩ := (restart_state sp) FGP ro x A Φ t hΦ ht
    exact lockInv_of_eqAC h hl hr

omit hU hΦ hΦU

/-! ### Reachable states and honest calls -/

/-- **The lock invariant at the states reachable with the unlock given** (`lockInv_of_reachable`
over `ReachableAtU wm`): every call's locks move back from its unlock input, by the unlock
relation. -/
theorem lockInv_of_reachableU {ro : ReplayOrder sp FGP} {x : Fin sp.n} (hU : Coherent U)
    {A : SAState sp.n} {Φ : Frm sp.n FGP} {t₀ : Time}
    (hr : ReachableAtU (ro := ro) wm x U A Φ t₀) :
    (goldilocksSA sp FGP ro).FrameIn U Φ ∧ 0 ≤ t₀ ∧ LockInv U A Φ := by
  induction hr with
  | init Φ hinit hin =>
    obtain ⟨htree, hroot, -⟩ := hinit
    have hF : Φ.F ∈ Φ.tree := htree ▸ rfl
    refine ⟨hin, le_rfl, lockInv_iff.2 ⟨Φ.F, hin.2 hF, hroot, fun _ => hF, fun l hl => ?_⟩⟩
    exact absurd hl (Set.notMem_empty l)
  | step c L₁ _ ht hok hrel ih =>
    obtain ⟨hin, ht₀, hli⟩ := ih
    obtain ⟨E, hE, hEr, hEt, hlE⟩ := lockInv_iff.1 hli
    obtain ⟨hF, hX⟩ := callOK_retains sp hU hin hok
    refine ⟨hok.1, ht₀.trans ht, lockInv_stepAC hU hok.1.1 hok.1.2 ?_ x _ (ht₀.trans ht) c
      (hrel.movesBack hok.1.1)⟩
    exact lockInv_iff.2 ⟨E, hE, hEr, fun h => hX E (hEt (hF.trans h)) h, hlE⟩

variable {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)} {tr : SATrace sp FGP ro}
  {u : Nat → Set Lock}

/-- **The lock invariant after an honest call**, in the call's frame. -/
theorem lockInv_postAC (hr : ACLocalRunU wm u H U tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) :
    LockInv U (tr.post i) ℓ.frame :=
  (lockInv_of_reachableU hr.coherent (localRun_reachableU sp hr hy i ℓ hc)).2.2

/-- **The lock invariant before an honest call**, in the call's frame: the initial state with the
initial frame, or the state after the node's last call, passed to the call's frame by the call
law (`LockInv.callOK`). -/
theorem lockInv_stateAC (hr : ACLocalRunU wm u H U tr) {y : Fin sp.n} (hy : y ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) :
    LockInv U (tr.state y i) ℓ.frame := by
  have hU := hr.coherent
  rcases hr.frameLaw y hy i ℓ hc with ⟨hnone, Φ₀, hinit, hin, hok⟩ | ⟨j, ℓ', hj, hc', hnb, hok⟩
  · rw [tr.state_of_noCall hnone, hr.init y hy]
    exact LockInv.callOK hU hin hok
      (lockInv_of_reachableU (ro := ro) (wm := wm) (x := y) hU (.init Φ₀ hinit hin)).2.2
  · rw [tr.state_of_lastCall hc' hj hnb]
    have hreach := lockInv_of_reachableU hU (localRun_reachableU sp hr hy j ℓ' hc')
    exact LockInv.callOK hU hreach.1 hok hreach.2.2

/-- **The live lock blocks before an honest call lie on one chain** of the call's frame, at every
time (`lockInv_stateAC`). -/
theorem liveBlocks_chain_atAC (hr : ACLocalRunU wm u H U tr) {y : Fin sp.n} (hy : y ∈ H)
    {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ) (τ : Time) :
    ∀ X ∈ liveLockBlocks sp (tr.state y i).locks ℓ.frame τ,
      ∀ Y ∈ liveLockBlocks sp (tr.state y i).locks ℓ.frame τ, Compatible ℓ.frame.tree X Y := by
  obtain ⟨hΦ, hΦU⟩ := frameIn_of_callAtU hr hy hc
  exact (lockInv_stateAC hr hy hc).liveBlocks_chain hr.coherent hΦ hΦU

end Consensus.Goldilocks.SA

end
