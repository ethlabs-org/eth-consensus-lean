module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.EvidenceRelease.WeightInv
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.EvidenceRelease.Rule
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockRule

public section

/-! # Evidence-release: the release keeps a fast or optimistic lock against a minority

The parent's retention argument (the outage route's `unlockKeeps_of_voteCompat`) bounds the
opponents of a block `P` below half of the committee. Evidence-release's release then also needs
its own keep at `P` (`evidenceKeep`): the evidence against `P` lies in a set smaller than the lock's
weight at `P`. For a lock written fast or optimistic (`fast = true`) the weight carries the bound:

* **the invariant** `FastWeighted`: every stored lock with `fast = true` weighs at least half of
  the committee at its own block. A fast write weighs its update's count, which passes the fast
  test (`n ≤ 2·count`); an optimistic write weighs its optimistic voters (`3n ≤ 4·voters`). A move
  goes to an ancestor in the tree, where the weight is at least as large (the weights are antitone,
  `WeightInv`), so every handler keeps it, for every stage whose unlock moves locks back
  (`fastWeighted_tryVoteE`, …, `fastWeighted_acRestartE`), and it holds at every reachable state
  of the evidence-release SA (`fastWeighted_of_reachable`);
* **the keep** (`unlockW_keeps_fast`): a stored fast lock on `B ⪰ P`, whose parent unlock target is
  at or above `P`, stays at or above `P` in `unlockW` when the evidence against `P` lies in a set
  `O` with `2·|O| < n`; at a reachable state from its weights (`unlockW_keeps_fast_of_reachable`).

What is left of the outage keep for these locks is the evidence bound itself: the evidence against
`P` lies in the faulty validators and the late wakers when every other honest vote of the view's
slot *extends* `P` (not only compatible with it). That is the vote-extension half of the outage
route's argument, shared with the slow locks. -/

namespace Consensus.Goldilocks.EvidenceRelease

open SA

variable {sp : SAParams} {FGP : Type} {U : Set (Blk sp.n FGP)}

variable (sp) in
/-- Every stored lock with `fast = true` weighs at least half of the committee at its block. -/
def FastWeighted (W : Set WLock) : Prop :=
  ∀ w ∈ W, w.lock.fast = true → sp.n ≤ 2 * w.weight w.lock.block

theorem fastWeighted_iff (W : Set WLock) :
    FastWeighted sp W ↔ ∀ w ∈ W, w.lock.fast = true → sp.n ≤ 2 * w.weight w.lock.block :=
  Iff.rfl

/-- `w'` is a lock of `W` moved to an ancestor of its block in the tree, with its weight and its
fast bit. -/
abbrev MovedBack (Φ : Frm sp.n FGP) (W : Set WLock) (w' : WLock) : Prop :=
  ∃ w ∈ W, w'.weight = w.weight ∧ w'.lock.fast = w.lock.fast ∧
    ∃ B ∈ Φ.tree, B.root = w.lock.block ∧ ∃ Y ∈ Φ.tree, Y.root = w'.lock.block ∧ Φ.Anc Y B

/-! ### Moves and writes -/

/-- Moves to ancestors keep `FastWeighted`, for weights antitone along the tree. -/
theorem FastWeighted.of_movedBack {Φ : Frm sp.n FGP} {W W' : Set WLock} (h : FastWeighted sp W)
    (hA : ∀ w ∈ W, TreeAntitone sp Φ fun Y => w.weight Y.root)
    (hmv : ∀ w' ∈ W', MovedBack Φ W w') : FastWeighted sp W' := by
  intro w' hw' hf
  obtain ⟨w, hw, hwt, hfe, B, hB, hBr, Y, hY, hYr, hYB⟩ := hmv w' hw'
  have hle : w.weight B.root ≤ w.weight Y.root := (treeAntitone_iff _ _).1 (hA w hw) Y hY B hB hYB
  have h0 := h w hw (hfe ▸ hf)
  rw [hwt, ← hYr]
  rw [← hBr] at h0
  omega

theorem liveLocks_movedBack {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (W : Set WLock) (t : Time) :
    ∀ w' ∈ wlockStore.liveLocks sp W Φ t, MovedBack Φ W w' := by
  rintro _ ⟨w, hw, B, hB, hBr, -, rfl⟩
  obtain ⟨hva, hvaB⟩ := viableAncestor_anc hΦ hB
  exact ⟨w, hw, rfl, rfl, B, hB, hBr, _, hva, rfl, hvaB⟩

/-- The unlock of a lawful stage moves locks back. -/
theorem unlockWith_movedBack {σ : Type} {E : UnlockStage sp wlockStore σ}
    {K : UnlockStage.Keep sp wlockStore σ} (hE : E.Lawful K) (c : σ) {Φ : Frm sp.n FGP}
    (hΦ : FrameOK Φ) (W : Set WLock) (t : Time) (s : Int) (V : View sp.n) :
    ∀ w' ∈ wlockStore.unlockWith sp E c W Φ t s V, MovedBack Φ W w' := by
  intro w' hw'
  obtain ⟨w, hw, B, hB, hBr, -, rfl⟩ := LockStore.mem_unlockWith_stored wlockStore_lawful hE hΦ hw'
  obtain ⟨hva, hvaB⟩ := viableAncestor_anc hΦ hB
  split_ifs
  · obtain ⟨hTt, hTB⟩ := unlockTarget_anc sp hΦ V s hva
    obtain ⟨hYt, hYT⟩ := hE.target_anc c V s w hΦ hTt
    exact ⟨w, hw, rfl, rfl, B, hB, hBr, _, hYt, rfl, hYT.trans (hTB.trans hvaB)⟩
  · exact ⟨w, hw, rfl, rfl, B, hB, hBr, _, hva, rfl, hvaB⟩

theorem FastWeighted.union {W N : Set WLock} (hW : FastWeighted sp W) (hN : FastWeighted sp N) :
    FastWeighted sp (W ∪ N) :=
  fun w hw => hw.elim (hW w) (hN w)

/-- Adding locks keeps `FastWeighted`, for weights written before the frame. -/
theorem FastWeighted.addLocksWith (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    (hΦU : Φ.tree ⊆ U) {W N : Set WLock} (hW : FastWeighted sp W) (hN : FastWeighted sp N)
    (hwr : ∀ w ∈ W ∪ N, WrittenBefore sp U Φ w.weight) (t : Time) :
    FastWeighted sp (wlockStore.addLocksWith sp W N Φ t) := by
  rw [LockStore.addLocksWith_eq]
  exact (hW.union hN).of_movedBack (fun w hw => (hwr w hw).antitone hU hΦ hΦU)
    (liveLocks_movedBack hΦ _ t)

theorem fastWeighted_optimisticWrite {A : SAState sp.n} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    {t : Time} {B : Blk sp.n FGP} (hsel : optimisticSelect sp A Φ t = some B) :
    FastWeighted sp {optimisticWrite sp A Φ t B} := by
  rintro _ rfl -
  have hsel' := hsel
  unfold optimisticSelect at hsel'
  dsimp only at hsel'
  split_ifs at hsel'
  obtain ⟨hBt, h34, -⟩ := (deepest_mem hsel').1
  change sp.n ≤ 2 * optimisticWeight sp A Φ (sp.slot t) B.root B.root
  rw [optimisticWeight, weightBelow_of_anc hΦ _ hBt ⟨B, hBt, rfl, .refl⟩]
  omega

theorem fastWeighted_updateWrites {A : SAState sp.n} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ)
    {t : Time} {s : Nat} {N : Set (Nat × Bool × Nat)} (h : updateNewLocks sp A Φ t s = some N)
    (C : Int → Nat → Nat) : FastWeighted sp (updateWrites sp A Φ C s N) := by
  rintro _ ⟨p, hp, rfl⟩ hf
  unfold updateNewLocks at h
  obtain ⟨Cf, -, rfl⟩ := Option.map_eq_some_iff.1 h
  rcases hp with ⟨D, hD, rfl⟩ | ⟨X, -, rfl⟩
  · obtain ⟨⟨⟨hDt, -, -⟩, -⟩, hfast⟩ := (deepest_mem hD).1
    change sp.n ≤ 2 * fastWeight sp A Φ s D.root D.root
    rw [fastWeight, weightBelow_of_anc hΦ _ hDt ⟨D, hDt, rfl, .refl⟩]
    exact hfast
  · exact absurd hf (by simp)

/-! ### The handlers -/

theorem fastWeighted_optimisticConfirmationW (hU : Coherent U) {Φ : Frm sp.n FGP}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {X : WState sp.n} (hi : WeightInv sp U Φ X)
    (h : FastWeighted sp X.wlocks) (t : Time) :
    FastWeighted sp (optimisticConfirmationW sp X Φ t).wlocks := by
  change FastWeighted sp (optimisticLocksW sp X.wlocks X.ac Φ t)
  unfold optimisticLocksW
  split
  · exact h
  · rename_i B hsel
    refine h.addLocksWith hU hΦ hΦU (fastWeighted_optimisticWrite hΦ hsel) ?_ t
    rintro w (hw | rfl)
    · exact ((weightInv_iff _ _ _).1 hi).1 w hw
    · rw [optimisticWrite_weight]
      exact writtenBefore_optimisticWeight hΦ hΦU _ _ _

theorem fastWeighted_updateConfirmationW (hU : Coherent U) {Φ : Frm sp.n FGP}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {X : WState sp.n} (hi : WeightInv sp U Φ X)
    (h : FastWeighted sp X.wlocks) (t : Time) (s : Nat) :
    FastWeighted sp (updateConfirmationW sp X Φ t s).wlocks := by
  change FastWeighted sp (updateLocksW sp X.wlocks X.ac X.counts Φ t s)
  unfold updateLocksW
  split
  · exact h
  · rename_i N hN
    refine h.addLocksWith hU hΦ hΦU (fastWeighted_updateWrites hΦ hN _) ?_ t
    rintro w (hw | ⟨p, -, rfl⟩)
    · exact ((weightInv_iff _ _ _).1 hi).1 w hw
    · dsimp only
      split
      · exact writtenBefore_fastWeight hΦ hΦU _ _ _
      · exact writtenBefore_slowWeight hU hΦ hΦU (savedBefore_saveCount hΦ hΦU ((weightInv_iff _ _
          _).1 hi).2 X.ac s) _ _

section Generic

variable {σ : Type} (E : UnlockStage sp wlockStore σ) (c : σ)

/-- The stage's unlock moves locks back, at every well-formed frame. -/
abbrev StageMovesBack (Φ : Frm sp.n FGP) : Prop :=
  ∀ (W : Set WLock) (t : Time) (s : Int) (V : View sp.n),
    ∀ w' ∈ wlockStore.unlockWith sp E c W Φ t s V, MovedBack Φ W w'

variable {E c}

theorem fastWeighted_unlockStateE {Φ : Frm sp.n FGP} (hmv : StageMovesBack E c Φ) (hU : Coherent U)
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {X : WState sp.n} (hi : WeightInv sp U Φ X)
    (h : FastWeighted sp X.wlocks) (t : Time) (s : Int) (V : View sp.n) :
    FastWeighted sp (unlockStateE sp E c X Φ t s V).wlocks :=
  h.of_movedBack (fun w hw => (((weightInv_iff _ _ _).1 hi).1 w hw).antitone hU hΦ hΦU)
    (hmv _ t s V)

theorem fastWeighted_tryVoteE {Φ : Frm sp.n FGP} (hmv : StageMovesBack E c Φ) (hU : Coherent U)
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {X : WState sp.n} (hi : WeightInv sp U Φ X)
    (h : FastWeighted sp X.wlocks) (self : Fin sp.n) (t : Time) :
    FastWeighted sp (tryVoteE sp E c self X Φ t).1.wlocks := by
  unfold tryVoteE
  dsimp only
  split_ifs
  · exact h
  · exact h
  · refine fastWeighted_optimisticConfirmationW hU hΦ hΦU ?_ ?_ t
    · exact weightInv_ac (weightInv_ac (weightInv_unlockStateE E c hi t _ _) _) _
    · exact fastWeighted_unlockStateE hmv hU hΦ hΦU hi h t _ _
  · refine fastWeighted_optimisticConfirmationW hU hΦ hΦU ?_ ?_ t
    · exact weightInv_ac (weightInv_ac hi _) _
    · exact h

theorem fastWeighted_acOnMessageE {Φ : Frm sp.n FGP} (hmv : StageMovesBack E c Φ)
    (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {X : WState sp.n}
    (hi : WeightInv sp U Φ X) (h : FastWeighted sp X.wlocks) (self : Fin sp.n) (t : Time)
    (v : Vote sp.n) : FastWeighted sp (acOnMessageE sp E c self X Φ t v).1.wlocks := by
  unfold acOnMessageE
  exact fastWeighted_tryVoteE hmv hU hΦ hΦU
    (weightInv_optimisticConfirmationW hΦ hΦU (weightInv_ac hi (admitVote sp X.ac t v)) t)
    (fastWeighted_optimisticConfirmationW hU hΦ hΦU (weightInv_ac hi (admitVote sp X.ac t v)) h t)
        self t

theorem fastWeighted_acOnBlockE {Φ : Frm sp.n FGP} (hmv : StageMovesBack E c Φ)
    (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {X : WState sp.n}
    (hi : WeightInv sp U Φ X) (h : FastWeighted sp X.wlocks) (self : Fin sp.n) (t : Time)
    (B : Blk sp.n FGP) : FastWeighted sp (acOnBlockE sp E c self X Φ t B).1.wlocks := by
  unfold acOnBlockE
  exact fastWeighted_tryVoteE hmv hU hΦ hΦU
    (weightInv_optimisticConfirmationW hΦ hΦU (weightInv_ac hi (blockReceipt sp X.ac t B)) t)
    (fastWeighted_optimisticConfirmationW hU hΦ hΦU (weightInv_ac hi (blockReceipt sp X.ac t B)) h
        t) self t

theorem fastWeighted_acOnTickE {Φ : Frm sp.n FGP} (hmv : StageMovesBack E c Φ)
    (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {X : WState sp.n}
    (hi : WeightInv sp U Φ X) (h : FastWeighted sp X.wlocks) (self : Fin sp.n) (t : Time) :
    FastWeighted sp (acOnTickE sp E c self X Φ t).1.wlocks := by
  have hv := fastWeighted_tryVoteE hmv hU hΦ hΦU hi h self t
  have hvi := weightInv_tryVoteE E c hΦ hΦU hi self t
  unfold acOnTickE
  dsimp only
  split_ifs
  · exact fastWeighted_updateConfirmationW hU hΦ hΦU hvi hv t _
  · exact fastWeighted_updateConfirmationW hU hΦ hΦU hi h t _
  · exact hv
  · exact h
  · exact h

theorem fastWeighted_acProposalE {Φ : Frm sp.n FGP} (hmv : StageMovesBack E c Φ)
    (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {X : WState sp.n}
    (hi : WeightInv sp U Φ X) (h : FastWeighted sp X.wlocks) (t : Time) :
    FastWeighted sp (acProposalE sp E c X Φ t).1.wlocks := by
  unfold acProposalE
  dsimp only
  split_ifs
  · exact fastWeighted_unlockStateE hmv hU hΦ hΦU hi h t _ _
  · exact h

theorem fastWeighted_acRestartE {Φ : Frm sp.n FGP} (hmv : StageMovesBack E c Φ)
    (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) {X : WState sp.n}
    (hi : WeightInv sp U Φ X) (h : FastWeighted sp X.wlocks) (ro : ReplayOrder sp FGP)
    (self : Fin sp.n) (t : Time) : FastWeighted sp (acRestartE sp E c ro self X Φ t).1.wlocks := by
  unfold acRestartE
  dsimp only
  have key : ∀ (l : List (Blk sp.n FGP)) (acc : WState sp.n × List (EmW sp FGP)),
      WeightInv sp U Φ acc.1 → FastWeighted sp acc.1.wlocks →
      FastWeighted sp (l.foldl (fun acc B => let r := acOnBlockE sp E c self acc.1 Φ t B;
        (r.1, acc.2 ++ r.2)) acc).1.wlocks := by
    intro l
    induction l with
    | nil => intro acc _ h; exact h
    | cons B l ih =>
      intro acc hacc hf
      simp only [List.foldl_cons]
      exact ih _ (weightInv_acOnBlockE E c hΦ hΦU hacc self t B)
        (fastWeighted_acOnBlockE hmv hU hΦ hΦU hacc hf self t B)
  exact key _ _ ((weightInv_iff _ _ _).2 ⟨((weightInv_iff _ _ _).1 hi).1, fun _ =>
      savedBefore_zero _ _⟩) h

end Generic

/-! ### Reachable states -/

/-- **Every stored fast lock of a reachable state weighs at least half of the committee** at its
block. -/
theorem fastWeighted_of_reachable (hU : Coherent U) {ro : ReplayOrder sp FGP} {self : Fin sp.n}
    {X : (evidenceReleaseSA sp FGP ro).State} {Φ : (evidenceReleaseSA sp FGP ro).Frm} {t : Time}
    (h : (evidenceReleaseSA sp FGP ro).ReachableAt self U X Φ t) : FastWeighted sp X.wlocks := by
  induction h with
  | init => exact fun w hw => absurd hw (Set.notMem_empty w)
  | @step X Φ Φ' t t' c hr _ hc ih =>
    obtain ⟨⟨hΦ, hΦU⟩, hinv⟩ := weightInv_of_reachable hU hr
    have hF := callOK_F_anc hΦU hc
    obtain ⟨⟨hΦ', hΦ'U⟩, -⟩ := hc
    have h' := hinv.later hF
    have hmv : StageMovesBack (evidenceStage sp) () Φ' :=
      unlockWith_movedBack (evidenceStage_lawful sp) () hΦ'
    cases c with
    | tick => exact fastWeighted_acOnTickE hmv hU hΦ' hΦ'U h' ih self t'
    | proposal => exact fastWeighted_acProposalE hmv hU hΦ' hΦ'U h' ih t'
    | toFG => exact ih
    | message m => exact fastWeighted_acOnMessageE hmv hU hΦ' hΦ'U h' ih self t' m
    | block B => exact fastWeighted_acOnBlockE hmv hU hΦ' hΦ'U h' ih self t' B
    | restart => exact fastWeighted_acRestartE hmv hU hΦ' hΦ'U h' ih ro self t'

/-! ### The keep -/

/-- **The release keeps a fast lock against a minority**: a stored lock `w` on `B` of weight at
least half of the committee at its block, antitone along the tree, whose parent unlock target is
at or above `P ⪯ B`, stays on a block at or above `P` in `unlockW` when the evidence against `P`
lies in a set `O` with `2·|O| < n`. -/
theorem unlockW_keeps_fast {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {L : Set WLock} {w : WLock}
    (hw : w ∈ L) (hFW : sp.n ≤ 2 * w.weight w.lock.block)
    (hanti : TreeAntitone sp Φ fun Y => w.weight Y.root) {B : Blk sp.n FGP} (hB : B ∈ Φ.tree)
    (hBr : B.root = w.lock.block) {t : Time} (hlive : w.lock.LiveAt sp t) {s : Int}
    {V : View sp.n} {P : Blk sp.n FGP} (hP : P ∈ Φ.tree) (hPB : Φ.Anc P B)
    (hpar : Φ.Anc P (unlockTarget sp Φ V s (Φ.viableAncestor B))) {O : Set (Fin sp.n)}
    (hO : evidence sp Φ V s P ⊆ O) (hOn : 2 * O.ncard < sp.n) :
    ∃ Z ∈ Φ.tree, Φ.Anc P Z ∧ wlockStore.withBlock w Z.root ∈ unlockW sp L Φ t s V := by
  have hle : w.weight B.root ≤ w.weight P.root := (treeAntitone_iff _ _).1 hanti P hP B hB hPB
  rw [hBr] at hle
  rw [unlockW_eq_unlockWith]
  exact LockStore.unlockWith_keeps wlockStore_lawful (evidenceStage_lawful sp) () hΦ hw hB hBr
    hlive hP hpar ((evidenceKeep_iff _ _ _ _ _ _).2 ⟨O, hO, by omega⟩)

/-- **The keep at a reachable state**: a stored fast lock of a reachable state of the
evidence-release SA, read at a later frame, stays at or above `P` in `unlockW` under the parent's
target and the minority evidence bound. -/
theorem unlockW_keeps_fast_of_reachable (hU : Coherent U) {ro : ReplayOrder sp FGP}
    {self : Fin sp.n} {X : (evidenceReleaseSA sp FGP ro).State}
    {Φ₀ : (evidenceReleaseSA sp FGP ro).Frm} {t₀ : Time}
    (h : (evidenceReleaseSA sp FGP ro).ReachableAt self U X Φ₀ t₀) {Φ : Frm sp.n FGP}
    (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) (hF : Anc U Φ₀.F Φ.F) {w : WLock} (hw : w ∈ X.wlocks)
    (hfast : w.lock.fast = true) {B : Blk sp.n FGP} (hB : B ∈ Φ.tree)
    (hBr : B.root = w.lock.block) {t : Time} (hlive : w.lock.LiveAt sp t) {s : Int}
    {V : View sp.n} {P : Blk sp.n FGP} (hP : P ∈ Φ.tree) (hPB : Φ.Anc P B)
    (hpar : Φ.Anc P (unlockTarget sp Φ V s (Φ.viableAncestor B))) {O : Set (Fin sp.n)}
    (hO : evidence sp Φ V s P ⊆ O) (hOn : 2 * O.ncard < sp.n) :
    ∃ Z ∈ Φ.tree, Φ.Anc P Z ∧ wlockStore.withBlock w Z.root ∈ unlockW sp X.wlocks Φ t s V :=
  unlockW_keeps_fast hΦ hw (fastWeighted_of_reachable hU h w hw hfast)
    (weightAntitone_of_reachable hU h hΦ hΦU hF w hw) hB hBr hlive hP hPB hpar hO hOn

end Consensus.Goldilocks.EvidenceRelease

end
