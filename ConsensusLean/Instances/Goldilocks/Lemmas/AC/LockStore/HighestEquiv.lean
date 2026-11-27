module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.Chain
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockStore.ExpiryEquiv
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.RelTrace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Restart

public section

/-! # The highest-live-lock and fast-expiry rules agree with the previous rules on lawful runs

The old handlers use the old reads and expiry rule at each site. Restart is held fixed
to the production bulk stamp on both sides, so the comparison concerns the lock and expiry rules.
The relational run uses the same unlock choices on both sides. The stock run makes those
choices itself; its unlock sees identical inputs on both sides. `LockInv` carries the live
lock chain across frame advances and between reads within a call. `LocksWF` supplies the
expiry cap, including on the locks after a receipt, an optimistic write, or an unlock.

`ReachableAtUFrom` does not constrain `s₀`, and `ACLocalRunU` does not constrain `ini`.
Even if all their locks visible in the initial frame lie on a chain, stored locks can be
revealed on different branches by later frames. `ACLocalRunStep` additionally accepts an
arbitrary replacement step: its `lawful` field constrains the supplied unlock, not the
replacement's output locks. The equivalence below is for the specified handlers and starts
with both invariants; `ACRunU`'s `VoteStart` gives both without extra hypotheses.
In particular, the raw update helpers need not agree for uncapped stored expiries or
write slots later than the call's slot.
-/

namespace Consensus.Goldilocks.AC

namespace BeforeHighest

variable {sp : ACParams} {FGP : Type} {U : Set (Blk sp.n FGP)}

def conflicts (L : Set Lock) (Φ : Frm sp.n FGP) (t : Time) (C : Blk sp.n FGP) : Prop :=
  ∃ B ∈ liveLockBlocks sp L Φ t, ¬ Compatible Φ.tree C B

noncomputable def anchor (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) : Blk sp.n FGP :=
  (deepest Φ (liveLockBlocks sp A.locks Φ t ∪ {Φ.fcRoot})).getD Φ.fcRoot

noncomputable def deep (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) : Option (Blk sp.n FGP) :=
  deepest Φ (liveLockBlocks sp A.locks Φ t)

noncomputable def source (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) : Option (Blk sp.n FGP) :=
  match sp.deepDepth with
  | none => deepest Φ (toFGCandidates sp A Φ t)
  | some D => (deepest Φ (toFGCandidates sp A Φ t)).orElse fun _ =>
      (deep A Φ t).bind fun a => deepest Φ (toFGDeepCandidates sp D a A Φ t)

noncomputable def walk (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (tree : Set (Blk sp.n FGP)) (V : View sp.n) (s : Int) : Blk sp.n FGP :=
  ghost sp tree (headScore sp Φ V s) (headEligible sp Φ t V s) Φ.tree.ncard (anchor A Φ t)

noncomputable def head (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) : Blk sp.n FGP :=
  walk A Φ t (Φ.viableTree Φ.tree) (latestView sp A Φ t).1 (latestView sp A Φ t).2

noncomputable def confirmed (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) : Blk sp.n FGP :=
  let C := (lookup Φ A.latestConfirmed).getD Φ.F
  let H := head A Φ t
  (deepest Φ {X | X ∈ Φ.tree ∧ Φ.Anc X C ∧ Φ.Anc X H}).getD Φ.F

open Classical in
private noncomputable def select (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    Option (Blk sp.n FGP) :=
  let s := sp.slot t
  if ¬ joined sp A t ∨ s = 0 ∨ sp.ts s + 2 * sp.Δ ≤ t ∨ sp.optimistic = false then none
  else deepest Φ {B | B ∈ Φ.tree ∧ 3 * sp.committeeSize ≤ 4 * (optimisticVoters sp A Φ s B).ncard ∧
    ¬ conflicts A.locks Φ t B}

private noncomputable def optimistic (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    ACState sp.n :=
  match select A Φ t with
  | none => A
  | some B =>
    updateLatestConfirmed sp
      { A with locks := addLocks sp A.locks Φ t (sp.slot t)
                  {(B.root, true, expiry A.locks Φ t (sp.slot t))} } Φ B

private noncomputable def newLocks (m : WriteMode) (A : ACState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (s : Nat) (C : Blk sp.n FGP) (sv : Int → Option Nat) (L : Set Lock) :
    Set (Nat × Bool × Nat) :=
  let path := {B | B ∈ confirmationPath sp Φ C ∧ ¬ conflicts A.locks Φ t B}
  let slow := fun B : Blk sp.n FGP => ∀ j : Int, (s : Int) - m.width < j → j < s →
    ∃ S ∈ Φ.tree, sv j = some S.root ∧ Φ.Anc B S
  let D := match m.fastArm with
    | true => deepest Φ {B | B ∈ path ∧ FastTest sp A Φ s B}
    | false => none
  let X := deepest Φ {B | B ∈ path ∧ slow B}
  {p | (∃ B, D = some B ∧ p = (B.root, true, expiry L Φ t s)) ∨
    (∃ B, X = some B ∧ p = (B.root, false, s + sp.k))}

open Classical in
private noncomputable def update (m : WriteMode) (A : ACState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (s : Nat) : ACState sp.n :=
  let C := getConfirmation sp A Φ s
  let A₁ := { A with saved := Function.update A.saved s (C.map Block.root) }
  match C with
  | none => A₁
  | some C =>
    let A₂ := if conflicts A₁.locks Φ t C then A₁ else updateLatestConfirmed sp A₁ Φ C
    { A₂ with locks := addLocks sp A₂.locks Φ t s (newLocks m A Φ t s C A₁.saved A₂.locks) }

open Classical in
private noncomputable def tryVote (self : Fin sp.n) (L : Set Lock) (A : ACState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : ACState sp.n × List (Em sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp A t ∨ A.votedSlot = s ∨ sp.ts s + sp.Δ < t then (A, [])
  else if t < sp.ts s + sp.Δ ∧ (s = 0 ∨ ¬ voteReady sp A Φ s) then (A, [])
  else
    let V := mergedVoteView sp A Φ s
    let A₁ := if 0 < s then { A with locks := L } else A
    let dom := voteDomain sp A₁ Φ s
    let H := walk A₁ Φ t (Φ.viableTree dom) V ((s : Int) - 1)
    let A₂ := { A₁ with votedSlot := s }
    let vote : Vote sp.n := { val := self, slot := s, head := H.root }
    let A₃ := if A.mayVote s then optimistic (admitVote sp A₂ t vote) Φ t else A₂
    (A₃, if A.mayVote s then
      [{ msg := vote, readPoint := A₂,
         head := some { head := H, start := anchor A₁ Φ t, dom := dom } }] else [])

open Classical in
private noncomputable def tick (m : WriteMode) (self : Fin sp.n) (L : Set Lock) (A : ACState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : ACState sp.n × List (Em sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp A t then (A, [])
  else
    let r := if t = sp.ts s + sp.Δ then tryVote self L A Φ t else (A, [])
    let A₂ := if t = sp.ts s + 2 * sp.Δ ∧ 0 < s then update m r.1 Φ t (s - 1) else r.1
    (A₂, r.2)

open Classical in
noncomputable def proposal (L : Set Lock) (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    ACState sp.n × Option (DutyHead sp.n FGP (Payload sp.n) × Payload sp.n) :=
  if ¬ joined sp A t then (A, none)
  else
    let s : Int := sp.slot t
    let p := voteViewList A Φ (s - 1) ⊤
    let V := View.ofLists p
    let A₁ := { A with locks := L }
    let H := walk A₁ Φ t (Φ.viableTree Φ.tree) V (s - 1)
    (A, some (⟨H, anchor A₁ Φ t, Φ.tree⟩, p))

open Classical in
noncomputable def toFG (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    ACState sp.n × Option (Blk sp.n FGP) :=
  if ¬ joined sp A t then (A, none)
  else (A, source A Φ t)

noncomputable def input (A : ACState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : (goldilocksAC sp FGP).Call → ACState sp.n
  | .message v => optimistic (admitVote sp A t v) Φ t
  | .block B => optimistic (blockReceipt sp A t B) Φ t
  | _ => A

noncomputable def view (A : ACState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (c : (goldilocksAC sp FGP).Call) : View sp.n :=
  match c with
  | .proposal => View.ofLists (voteViewList A Φ ((sp.slot t : Int) - 1) ⊤)
  | _ => mergedVoteView sp (input A Φ t c) Φ (sp.slot t)

noncomputable def unlockFor (A : ACState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (c : (goldilocksAC sp FGP).Call) : Set Lock :=
  unlock sp (input A Φ t c).locks Φ t ((sp.slot t : Int) - 1) (view A Φ t c)

noncomputable def stepWith (m : WriteMode) (self : Fin sp.n)
    (L : Set Lock) (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (goldilocksAC sp FGP).Call → ACState sp.n × List (Em sp FGP)
  | .tick => tick m self L A Φ t
  | .proposal => (A, [])
  | .toFG => ((toFG A Φ t).1, [])
  | .message v => tryVote self L (optimistic (admitVote sp A t v) Φ t) Φ t
  | .block B => tryVote self L (optimistic (blockReceipt sp A t B) Φ t) Φ t
  | .restart => acRestart sp self A Φ t

noncomputable def step (self : Fin sp.n) (A : ACState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (c : (goldilocksAC sp FGP).Call) :
    ACState sp.n × List (Em sp FGP) :=
  stepWith (WriteMode.parent sp) self (unlockFor A Φ t c) A Φ t c

theorem conflicts_iff {A : ACState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    (hU : Coherent U) (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U) (h : LockInv U A Φ)
    (C : Blk sp.n FGP) : conflicts A.locks Φ t C ↔ conflictsWithLock sp A.locks Φ t C := by
  constructor
  · rintro ⟨B, hB, hCB⟩
    obtain ⟨H, hH⟩ := exists_deepest hΦ (fun _ hX => hX.1) ⟨B, hB⟩
    have hBH := anc_deepest hΦ (fun _ hX => hX.1) (h.liveBlocks_chain hU hΦ hΦU) hH B hB
    refine ⟨H, hH, fun hCH => hCB ?_⟩
    rcases hCH with hCH | hHC
    · exact anc_total hΦ.coherent hCH hBH
    · exact Or.inr (hBH.trans hHC)
  · exact exists_of_conflictsWithLock

theorem anchor_eq {A : ACState sp.n} {Φ : Frm sp.n FGP} {t : Time} (hΦ : FrameOK Φ) :
    anchor A Φ t = getAnchor sp A Φ t := (getAnchor_eq_deepest_union hΦ A t).symm

theorem deep_eq (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    deep A Φ t = deepAnchor sp A Φ t := by rfl

theorem source_eq (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    source A Φ t = fgSource sp A Φ t := by rfl

theorem walk_eq {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (A : ACState sp.n) (t : Time)
    (tree : Set (Blk sp.n FGP)) (V : View sp.n) (s : Int) :
    walk A Φ t tree V s = getHead sp A Φ t tree V s := by
  simp only [walk, getHead, anchor_eq hΦ]

theorem head_eq {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (A : ACState sp.n) (t : Time) :
    head A Φ t = acHead sp A Φ t := by
  simp only [head, acHead, walk_eq hΦ]

theorem confirmed_eq {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (A : ACState sp.n) (t : Time) :
    confirmed A Φ t = acConfirmed sp A Φ t := by
  simp only [confirmed, acConfirmed, head_eq hΦ]

theorem proposal_eq {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (L : Set Lock)
    (A : ACState sp.n) (t : Time) : proposal L A Φ t = acProposalWith sp L A Φ t := by
  simp only [proposal, acProposalWith, walk_eq hΦ, anchor_eq hΦ]

theorem toFG_eq (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    toFG A Φ t = acToFG sp A Φ t := by
  simp only [toFG, acToFG, source_eq]

variable (hU : Coherent U) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (hΦU : Φ.tree ⊆ U)
include hU hΦ hΦU

private theorem optimistic_eq {A : ACState sp.n} (h : LockInv U A Φ)
    (hw : LocksWF sp A.locks) (t : Time) :
    optimistic A Φ t = optimisticConfirmation sp A Φ t := by
  have he : select A Φ t = optimisticSelect sp A Φ t := by
    simp only [select, optimisticSelect, conflicts_iff hU hΦ hΦU h]
  rw [optimistic, optimisticConfirmation, he]
  cases optimisticSelect sp A Φ t with
  | none => rfl
  | some B => rw [expiry_eq (fun _ hl => hw.cap hl) (le_rfl : sp.slot t ≤ sp.slot t)]

private theorem update_eq (m : WriteMode) {A : ACState sp.n} (h : LockInv U A Φ) (t : Time)
    (s : Nat) (hw : LocksWF sp A.locks) (hs : s ≤ sp.slot t) :
    update m A Φ t s = updateConfirmationM sp m A Φ t s := by
  -- The expiry reads the record-update state's locks, before `addLocks` inserts the triples.
  have hN (C : Blk sp.n FGP) (sv : Int → Option Nat) (L : Set Lock) (hwL : LocksWF sp L) :
      newLocks m A Φ t s C sv L = newLocksM sp m A Φ t s C sv L := by
    cases hm : m.fastArm <;>
      simp only [newLocks, newLocksM, hm, conflicts_iff hU hΦ hΦU h,
        expiry_eq (fun _ hl => hwL.cap hl) hs]
  unfold update updateConfirmationM
  cases getConfirmation sp A Φ s with
  | none => rfl
  | some C =>
    dsimp only
    by_cases hc : conflicts A.locks Φ t C
    · simp only [ite_eq_left hc, ite_eq_left ((conflicts_iff hU hΦ hΦU h C).mp hc)]
      rw [hN _ _ _ hw]
    · simp only [ite_eq_right hc, ite_eq_right (mt (conflicts_iff hU hΦ hΦU h C).mpr hc)]
      rw [hN _ _ _ (by rwa [updateLatestConfirmed_keeps_locks])]

private theorem update_inv (m : WriteMode) {A : ACState sp.n} (h : LockInv U A Φ)
    (t : Time) (s : Nat) : LockInv U (updateConfirmationM sp m A Φ t s) Φ := by
  classical
  unfold updateConfirmationM
  cases hC : getConfirmation sp A Φ s with
  | none => exact h.of_eq rfl rfl
  | some C =>
    dsimp only
    have hCt := (deepest_mem hC).1.1
    have hN : ∀ {sv L p}, p ∈ newLocksM sp m A Φ t s C sv L →
        ∃ Y ∈ Φ.tree, Y.root = p.1 ∧ Φ.Anc Y C ∧ ¬ conflictsWithLock sp A.locks Φ t Y := by
      intro sv L p hp
      rcases mem_newLocksM.mp hp with ⟨_, Y, hY, rfl⟩ | ⟨Y, hY, rfl⟩ <;>
        obtain ⟨⟨⟨hYt, -, hYC⟩, hnc⟩, -⟩ := (deepest_mem hY).1 <;>
        exact ⟨Y, hYt, rfl, hYC, hnc⟩
    have hs : LockInv U { A with saved := Function.update A.saved s (some C.root) } Φ :=
      h.of_eq rfl rfl
    split_ifs with hc
    · obtain ⟨B, hB, hCB⟩ := (conflicts_iff hU hΦ hΦU h C).mpr hc
      refine hs.addLocks_below hU hΦ hΦU rfl (fun p hp => ?_) rfl
      obtain ⟨Y, hYt, hYr, hYC, hYnc⟩ := hN hp
      have hYB : Compatible Φ.tree Y B := by
        by_contra hnot
        exact hYnc ((conflicts_iff hU hΦ hΦU h Y).mp ⟨B, hB, hnot⟩)
      refine ⟨Y, hYt, hYr, B, hB, hYB.elim id fun hBY => ?_⟩
      exact (hCB (Or.inr (hBY.trans hYC))).elim
    · simp only [updateLatestConfirmed_keeps_locks]
      refine hs.addLocks hU hΦ hΦU hCt hc rfl (fun p hp => ?_) ?_
      · obtain ⟨Y, hYt, hYr, hYC, -⟩ := hN hp
        exact ⟨Y, hYt, hYr, hYC⟩
      · unfold updateLatestConfirmed
        split_ifs <;> rfl

private theorem tryVote_eq_inv (m : WriteMode) {A : ACState sp.n} {L : Set Lock} (h : LockInv U A Φ)
    (hL : LockInv U { A with locks := L } Φ) (hw : LocksWF sp A.locks) (hwL : LocksWF sp L)
    (self : Fin sp.n) (t : Time) :
    tryVote self L A Φ t = tryVoteWithM sp m self L A Φ t ∧
      LockInv U (tryVoteWithM sp m self L A Φ t).1 Φ := by
  unfold tryVote tryVoteWithM
  dsimp only
  simp only [walk_eq hΦ, anchor_eq hΦ]
  split_ifs
  all_goals try (solve
    | exact ⟨rfl, h⟩
    | exact ⟨rfl, h.of_eq rfl rfl⟩
    | exact ⟨rfl, hL.of_eq rfl rfl⟩)
  all_goals
    have hadmit {X : ACState sp.n} (v : Vote sp.n) (hx : LockInv U X Φ) :
        LockInv U (admitVote sp X t v) Φ :=
      hx.of_eq (admitVote_keeps_locks _ _ _).1 (admitVote_keeps_locks _ _ _).2
    refine ⟨?_, ?_⟩
    · congr 1
      apply optimistic_eq hU hΦ hΦU
      · apply hadmit
        first | exact hL.of_eq rfl rfl | exact h.of_eq rfl rfl
      · rw [admitVote_locks_eq]
        first | exact hwL | exact hw
    · apply LockInv.optimistic hU hΦ hΦU
      apply hadmit
      first | exact hL.of_eq rfl rfl | exact h.of_eq rfl rfl

private theorem tick_eq_inv (m : WriteMode) {A : ACState sp.n} {L : Set Lock} (h : LockInv U A Φ)
    (hL : LockInv U { A with locks := L } Φ) (hw : LocksWF sp A.locks) (t : Time)
    (hu : UnlockRel sp A.locks Φ t ((sp.slot t : Int) - 1) (mergedVoteView sp A Φ (sp.slot t)) L)
    (self : Fin sp.n) :
    tick m self L A Φ t = acOnTickWithM sp m self L A Φ t ∧
      LockInv U (acOnTickWithM sp m self L A Φ t).1 Φ := by
  obtain ⟨he, hi⟩ := tryVote_eq_inv hU hΦ hΦU m h hL hw (hw.unlockRel hu) self t
  unfold tick acOnTickWithM
  rw [he]
  dsimp only
  by_cases hj : ¬ joined sp A t
  · simp only [ite_eq_left hj, true_and]
    exact h
  simp only [ite_eq_right hj]
  generalize hr : (if t = sp.ts (sp.slot t) + sp.Δ then tryVoteWithM sp m self L A Φ t
    else (A, [])) = r
  have hir : LockInv U r.1 Φ := by
    rw [← hr]
    split
    · exact hi
    · exact h
  have hwr : LocksWF sp r.1.locks := by
    rw [← hr]
    split
    · exact (hw.tryVoteWith (wm := m) self Φ t hu).1
    · exact hw
  split_ifs
  · exact ⟨congrArg (fun X => (X, r.2)) (update_eq hU hΦ hΦU m hir t _ hwr (Nat.sub_le ..)),
      update_inv hU hΦ hΦU m hir _ _⟩
  · exact ⟨rfl, hir⟩

private theorem input_eq_inv {A : ACState sp.n} (h : LockInv U A Φ)
    (hw : LocksWF sp A.locks) (t : Time) (c : (goldilocksAC sp FGP).Call) :
    input A Φ t c = callInput sp A Φ t c ∧ LockInv U (callInput sp A Φ t c) Φ ∧
      LocksWF sp (callInput sp A Φ t c).locks := by
  cases c with
  | message v =>
    have hv : LockInv U (admitVote sp A t v) Φ :=
      h.of_eq (admitVote_keeps_locks _ _ _).1 (admitVote_keeps_locks _ _ _).2
    have hwv : LocksWF sp (admitVote sp A t v).locks := by rwa [admitVote_locks_eq]
    exact ⟨optimistic_eq hU hΦ hΦU hv hwv t, hv.optimistic hU hΦ hΦU t,
      hwv.optimisticConfirmation Φ t⟩
  | block B =>
    have hv : LockInv U (blockReceipt sp A t B) Φ := h.of_eq rfl rfl
    exact ⟨optimistic_eq hU hΦ hΦU hv hw t, hv.optimistic hU hΦ hΦU t,
      LocksWF.optimisticConfirmation (A := blockReceipt sp A t B) hw Φ t⟩
  | _ => exact ⟨rfl, h, hw⟩

theorem view_eq {A : ACState sp.n} (h : LockInv U A Φ)
    (hw : LocksWF sp A.locks) (t : Time) (c : (goldilocksAC sp FGP).Call) :
    view A Φ t c = callView sp A Φ t c := by
  have he := (input_eq_inv hU hΦ hΦU h hw t c).1
  cases c <;> first | rfl | exact congrArg (fun S => mergedVoteView sp S Φ (sp.slot t)) he

private theorem unlockFor_eq {A : ACState sp.n} (h : LockInv U A Φ)
    (hw : LocksWF sp A.locks) (t : Time) (c : (goldilocksAC sp FGP).Call) :
    unlockFor A Φ t c = parentUnlock sp A Φ t c := by
  unfold unlockFor parentUnlock
  rw [(input_eq_inv hU hΦ hΦU h hw t c).1, view_eq hU hΦ hΦU h hw t c]

omit hU hΦU in
/-- The proposal result includes the duty head and payload, not just the state in `step`. -/
theorem stockProposal_eq {A : ACState sp.n}
    (t : Time) : proposal (unlockFor A Φ t (.proposal : (goldilocksAC sp FGP).Call)) A Φ t =
      acProposal sp A Φ t := by
  rw [proposal_eq hΦ, acProposal_eq_acProposalWith]
  rfl

/-- A call in any write mode gives equal post-states and emissions for the same lawful unlock,
and preserves the invariant needed for the next call. -/
theorem stepWith_eq_inv (m : WriteMode) (self : Fin sp.n)
    {A : ACState sp.n} (h : LockInv U A Φ) (hw : LocksWF sp A.locks) {t : Time} (ht : 0 ≤ t)
    (c : (goldilocksAC sp FGP).Call) {L : Set Lock}
    (hu : UnlockRel sp (callInputM sp m A Φ t c).locks Φ t ((sp.slot t : Int) - 1)
      (callViewM sp m A Φ t c) L) :
    stepWith m self L A Φ t c = stepWithM sp m self L A Φ t c ∧
      LockInv U (stepWithM sp m self L A Φ t c).1 Φ := by
  change UnlockRel sp (callInput sp A Φ t c).locks Φ t ((sp.slot t : Int) - 1)
    (callView sp A Φ t c) L at hu
  obtain ⟨he, hi, hwi⟩ := input_eq_inv hU hΦ hΦU h hw t c
  have hL : LockInv U { callInput sp A Φ t c with locks := L } Φ :=
    hi.movesBack hU hΦU (hu.movesBack hΦ) rfl
  cases c with
  | tick => exact tick_eq_inv hU hΦ hΦU m h hL hw t hu self
  | proposal =>
    exact ⟨rfl, h⟩
  | toFG =>
    refine ⟨congrArg (fun r => (r.1, [])) (toFG_eq A Φ t), ?_⟩
    change LockInv U (acToFG sp A Φ t).1 Φ
    unfold acToFG
    split <;> exact h
  | message v =>
    simp only [stepWith, stepWithM, acOnMessageWithM]
    rw [show optimistic (admitVote sp A t v) Φ t = _ from he]
    exact tryVote_eq_inv hU hΦ hΦU m hi hL hwi (hwi.unlockRel hu) self t
  | block B =>
    simp only [stepWith, stepWithM, acOnBlockWithM]
    rw [show optimistic (blockReceipt sp A t B) Φ t = _ from he]
    exact tryVote_eq_inv hU hΦ hΦU m hi hL hwi (hwi.unlockRel hu) self t
  | restart =>
    obtain ⟨-, hl, hr, -⟩ := (restart_state sp) FGP self A Φ t hΦ ht
    exact ⟨rfl, h.of_eq hl hr⟩

theorem step_eq (self : Fin sp.n) {A : ACState sp.n}
    (h : LockInv U A Φ) (hw : LocksWF sp A.locks) {t : Time} (ht : 0 ≤ t)
    (c : (goldilocksAC sp FGP).Call) :
    step self A Φ t c = (goldilocksAC sp FGP).step self A Φ t c := by
  rw [step, unlockFor_eq hU hΦ hΦU h hw, step_eq_stepWith, ← stepWithM_parent]
  refine (stepWith_eq_inv hU hΦ hΦU _ self h hw ht c ?_).1
  rw [callInputM_parent, callViewM_parent]
  exact unlockRel_unlock hΦ _ _ _ _

omit hU hΦ hΦU

/-- The invariant required of a custom start is at the initial frame, not just a chain of the
locks currently visible there. Stored locks may become visible when a later call grows the tree. -/
theorem voteStart_lockInv {A : ACState sp.n}
    (h : VoteStart sp.genesisRoot A) {Φ : Frm sp.n FGP}
    (hi : (goldilocksAC sp FGP).InitialFrame Φ) (hf : (goldilocksAC sp FGP).FrameIn U Φ) :
    LockInv U A Φ := by
  obtain ⟨m, rfl⟩ := voteStart_iff.1 h
  have hF : Φ.F ∈ Φ.tree := hi.1 ▸ rfl
  exact lockInv_iff.2 ⟨Φ.F, hf.2 hF, hi.2.1, fun _ => hF,
    fun l hl => (Set.notMem_empty l hl).elim⟩

/-- The lock invariant holds after any prefix of calls with lawful unlock choices. -/
theorem reachable_lockInv {m : WriteMode} {s₀ : ACState sp.n}
    {self : Fin sp.n} (hU : Coherent U)
    (h₀ : ∀ Φ, (goldilocksAC sp FGP).InitialFrame Φ →
      (goldilocksAC sp FGP).FrameIn U Φ → LockInv U s₀ Φ)
    (hw₀ : LocksWF sp s₀.locks)
    {A : ACState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    (h : ReachableAtUFrom m s₀ self U A Φ t) :
    (goldilocksAC sp FGP).FrameIn U Φ ∧ 0 ≤ t ∧ LockInv U A Φ ∧ LocksWF sp A.locks := by
  induction h with
  | init Ψ hi hf => exact ⟨hf, le_rfl, h₀ Ψ hi hf, hw₀⟩
  | step c L _ ht hok hl ih =>
    obtain ⟨hf, htime, hx, hw⟩ := ih
    have ht' := htime.trans ht
    have hi := (stepWith_eq_inv hU hok.1.1 hok.1.2 m self (hx.callOK hU hf hok) hw ht' c hl).2
    exact ⟨hok.1, ht', hi, (hw.stepWith self hok.1.1 ht' c hl).1⟩

/-- The invariant in the actual call frame, before the handler performs any reads. -/
theorem localRunU_call_lockInv {m : WriteMode} {u : Nat → Set Lock}
    {H : Set (Fin sp.n)} {tr : GTrace sp FGP} {ini : Fin sp.n → ACState sp.n}
    (h : ACLocalRunU m u H U tr ini)
    (h₀ : ∀ y ∈ H, ∀ Φ, (goldilocksAC sp FGP).InitialFrame Φ →
      (goldilocksAC sp FGP).FrameIn U Φ → LockInv U (ini y) Φ)
    (hw₀ : ∀ y ∈ H, LocksWF sp (ini y).locks)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksAC sp FGP)}
    (hc : tr.CallAt y i ℓ) :
    (goldilocksAC sp FGP).FrameIn U ℓ.frame ∧ LockInv U (tr.state y i) ℓ.frame ∧
      LocksWF sp (tr.state y i).locks := by
  rcases h.frameLaw y hy i ℓ hc with ⟨hn, Ψ, hi, hf, hok⟩ | ⟨j, ℓ', hj, hc', hn, hok⟩
  · rw [tr.state_of_noCall hn, h.init y hy]
    exact ⟨hok.1, (h₀ y hy Ψ hi hf).callOK h.coherent hf hok, hw₀ y hy⟩
  · rw [tr.state_of_lastCall hc' hj hn]
    obtain ⟨hf, -, hx, hw⟩ := reachable_lockInv h.coherent (h₀ y hy) (hw₀ y hy)
      (localRun_reachableU sp h hy j ℓ' hc')
    exact ⟨hok.1, hx.callOK h.coherent hf hok, hw⟩

/-- The same relational trace is executable by the old handlers, with all its states and
emissions unchanged. Both sides use the same lawful unlock oracle. -/
theorem localRunU_beforeHighest {m : WriteMode} {u : Nat → Set Lock}
    {H : Set (Fin sp.n)} {tr : GTrace sp FGP} {ini : Fin sp.n → ACState sp.n}
    (h : ACLocalRunU m u H U tr ini)
    (h₀ : ∀ y ∈ H, ∀ Φ, (goldilocksAC sp FGP).InitialFrame Φ →
      (goldilocksAC sp FGP).FrameIn U Φ → LockInv U (ini y) Φ)
    (hw₀ : ∀ y ∈ H, LocksWF sp (ini y).locks) :
    ACLocalRunStep m u (fun _ => stepWith m) H U tr ini := by
  refine { h with exec := ?_ }
  intro i ℓ hl hy
  obtain ⟨hf, hx, hw⟩ := localRunU_call_lockInv h h₀ hw₀ hy ⟨rfl, hl⟩
  have he := (stepWith_eq_inv h.coherent hf.1 hf.2 m (tr.node i) hx hw (h.time_nonneg i) ℓ.call
    (h.lawful i ℓ hl hy hf.1)).1
  exact he.trans (h.exec i ℓ hl hy)

/-- In particular all the vote-permission starts of `ACRunU` are supported. -/
theorem runU_beforeHighest {m : WriteMode} {u : Nat → Set Lock}
    {proposer : Nat → Fin sp.n} {H : Set (Fin sp.n)} {tr : GTrace sp FGP}
    {ini : Fin sp.n → ACState sp.n} (h : ACRunU m u proposer tr H U ini) :
    ACLocalRunStep m u (fun _ => stepWith m) H U tr ini :=
  localRunU_beforeHighest h.localRun (fun y _ _ => voteStart_lockInv (h.vstart y))
    (fun y _ => VoteStart.locksWF (h.vstart y))

/-- Conversely, an old execution on the same lawful unlocks is a new execution. Inductively
replaying its prefix establishes the invariant before reusing the old label's outputs. -/
theorem localRunU_iff {m : WriteMode} {u : Nat → Set Lock}
    {H : Set (Fin sp.n)} {tr : GTrace sp FGP} {ini : Fin sp.n → ACState sp.n}
    (h₀ : ∀ y ∈ H, ∀ Φ, (goldilocksAC sp FGP).InitialFrame Φ →
      (goldilocksAC sp FGP).FrameIn U Φ → LockInv U (ini y) Φ)
    (hw₀ : ∀ y ∈ H, LocksWF sp (ini y).locks) :
    ACLocalRunStep m u (fun _ => stepWith m) H U tr ini ↔ ACLocalRunU m u H U tr ini := by
  refine ⟨fun h => { h with exec := ?_ }, fun h => localRunU_beforeHighest h h₀ hw₀⟩
  have replay (y : Fin sp.n) (hy : y ∈ H) (i : Nat) : ∀ ℓ, tr.CallAt y i ℓ →
      stepWithM sp m y (u i) (tr.state y i) ℓ.frame (tr.time i) ℓ.call = (tr.post i, ℓ.emits) ∧
      ReachableAtUFrom m (ini y) y U (tr.post i) ℓ.frame (tr.time i) := by
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro ℓ hc
      have hpre : ∃ Ψ t, ReachableAtUFrom m (ini y) y U (tr.state y i) Ψ t ∧
          t ≤ tr.time i ∧ (goldilocksAC sp FGP).CallOK U Ψ (tr.time i) ℓ.call ℓ.frame := by
        rcases h.frameLaw y hy i ℓ hc with ⟨hn, Ψ, hi, hf, hok⟩ | ⟨j, ℓ', hj, hc', hn, hok⟩
        · rw [tr.state_of_noCall hn, h.init y hy]
          exact ⟨Ψ, 0, .init Ψ hi hf, h.time_nonneg _, hok⟩
        · rw [tr.state_of_lastCall hc' hj hn]
          exact ⟨ℓ'.frame, tr.time j, (ih j hj ℓ' hc').2, h.time_mono hj.le, hok⟩
      obtain ⟨Ψ, t, hp, ht, hok⟩ := hpre
      have hl := h.lawful i ℓ hc.2 (hc.1 ▸ hy) hok.1.1
      have he := h.exec i ℓ hc.2 (hc.1 ▸ hy)
      rw [hc.1] at hl he
      obtain ⟨hf, hu, hx, hw⟩ := reachable_lockInv h.coherent (h₀ y hy) (hw₀ y hy) hp
      have he' := (stepWith_eq_inv h.coherent hok.1.1 hok.1.2 m y
        (hx.callOK h.coherent hf hok) hw (hu.trans ht) ℓ.call hl).1.symm.trans he
      have hs : (stepWithM sp m y (u i) (tr.state y i) ℓ.frame (tr.time i) ℓ.call).1 =
          tr.post i := congrArg Prod.fst he'
      exact ⟨he', hs ▸ ReachableAtUFrom.step ℓ.call (u i) hp ht hok hl⟩
  exact fun i ℓ hl hy => (replay _ hy i ℓ ⟨rfl, hl⟩).1

/-- The stock AC, without any unlock oracle, agrees at each lawful next call. The actual
committee start is `voteStart_initial`; the same statement allows custom vote permissions. -/
theorem reachable_stock_step_eq {self : Fin sp.n} {s₀ : ACState sp.n}
    {A : ACState sp.n} {Φ Φ' : Frm sp.n FGP} {t t' : Time} (hU : Coherent U)
    (h₀ : VoteStart sp.genesisRoot s₀)
    (h : (goldilocksAC sp FGP).ReachableAtFrom s₀ self U A Φ t)
    (ht : t ≤ t') (c : (goldilocksAC sp FGP).Call)
    (hok : (goldilocksAC sp FGP).CallOK U Φ t' c Φ') :
    step self A Φ' t' c = (goldilocksAC sp FGP).step self A Φ' t' c := by
  obtain ⟨hf, hu, hx, hw⟩ := reachable_lockInv hU (fun _ => voteStart_lockInv h₀)
    (VoteStart.locksWF h₀) h.toU
  exact step_eq hU hok.1.1 hok.1.2 self (hx.callOK hU hf hok) hw (hu.trans ht) c

/-- Every honest call on a stock trace has the same post-state and emissions when the old
handler computes its own unlock. -/
theorem stockRun_exec {H : Set (Fin sp.n)}
    {tr : GTrace sp FGP} {ini : Fin sp.n → ACState sp.n}
    (h : ACLocalRun (goldilocksAC sp FGP) H U tr ini)
    (h₀ : ∀ y ∈ H, ∀ Φ, (goldilocksAC sp FGP).InitialFrame Φ →
      (goldilocksAC sp FGP).FrameIn U Φ → LockInv U (ini y) Φ)
    (hw₀ : ∀ y ∈ H, LocksWF sp (ini y).locks)
    {i : Nat} {ℓ : ACLabel (goldilocksAC sp FGP)}
    (hl : tr.label i = some ℓ) (hy : tr.node i ∈ H) :
    step (tr.node i) (tr.state (tr.node i) i) ℓ.frame (tr.time i) ℓ.call =
      (tr.post i, ℓ.emits) := by
  obtain ⟨hf, hx, hw⟩ := localRunU_call_lockInv h.toU h₀ hw₀ hy ⟨rfl, hl⟩
  exact (step_eq h.coherent hf.1 hf.2 _ hx hw (h.time_nonneg i) ℓ.call).trans (h.exec i ℓ hl hy)

end BeforeHighest
end Consensus.Goldilocks.AC

end
