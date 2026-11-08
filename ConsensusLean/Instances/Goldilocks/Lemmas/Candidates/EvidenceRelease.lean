module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Candidates.Projection
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Candidates.EvidenceRelease
public import ConsensusLean.Instances.Goldilocks.Lemmas.Candidates.WeightedWrites
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.EvidenceRelease.RelTrace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace

public section

/-! # The evidence-release SA at a write mode projects to the SA's step at the same mode

The evidence-release SA at a write mode `m` (`Milestones/Spec/Candidates/EvidenceRelease`),
forgotten to the parent's state, is the SA's step at mode `m` (`stepWithM m`) with the locks after
the unlock given, as at the parent's mode (`Lemmas/AC/Candidates/EvidenceRelease/Projection`,
`RelTrace`):

* at the parent's mode it is evidence-release's SA (`optimisticConfirmationWM_parent`,
  `updateConfirmationWM_parent`, `evidenceReleaseSAM_parent`), which certifies the parent's mode
  only;
* proposals: `acProposalWith_erOracleM` reads the oracle's proposal as the SA's;
* the invariant `LocksForget` holds through every handler at mode `m`, and the forgotten writes
  are the writes at mode `m` (`optimisticConfirmationWM_ac`, `updateConfirmationWM_ac`);
* the forgotten handlers are `tryVoteWithM m` and `acOnTickWithM m` of the forgotten stage unlock
  (`tryVoteEM_proj`, `acOnMessageEM_proj`, `acOnBlockEM_proj`, `acOnTickEM_proj`), and the
  restart, whose replay runs unjoined (so its optimistic confirmation selects nothing, at every
  mode), is the parent's restart, which `stepWithM` takes at every mode
  (`acOnBlockEM_of_not_joined`, `acRestartEM_proj`);
* lifted to traces: a run of the evidence-release SA at mode `m`, forgotten, is a run at mode `m`
  with the unlock given by `erOracleM` (`localRunU_projTraceM`).

The parent's forms (`Lemmas/AC/Candidates/EvidenceRelease/Projection`, `RelTrace`) are kept as
separate proofs, not corollaries at `WriteMode.parent sp`: the healing lemmas import them, and
only leaf layers may import the Candidates layers, which hold the weighted locks. -/

namespace Consensus.Goldilocks.EvidenceRelease

open SA

section Parent

variable {sp : SAParams} {FGP : Type}

/-- At the parent's mode, the weighted optimistic confirmation is evidence-release's. -/
theorem optimisticConfirmationWM_parent :
    optimisticConfirmationWM (FGP := FGP) sp (WriteMode.parent sp) = optimisticConfirmationW sp :=
  rfl

/-- At the parent's mode, the weighted update is evidence-release's. -/
theorem updateConfirmationWM_parent :
    updateConfirmationWM (FGP := FGP) sp (WriteMode.parent sp) = updateConfirmationW sp := by
  funext X Φ t s
  simp only [updateConfirmationWM, updateConfirmationW, updateLocksWM_parent]
  rfl

/-- At the parent's mode, `ac_on_tick` is evidence-release's, at every unlock stage. -/
theorem acOnTickEM_parent {σ : Type} (E : UnlockStage sp wlockStore σ) (c : σ) :
    acOnTickEM (FGP := FGP) sp E c (WriteMode.parent sp) = acOnTickE sp E c := by
  funext self X Φ t
  simp only [acOnTickEM, acOnTickE, updateConfirmationWM_parent]
  rfl

/-- **At the parent's mode, the SA is evidence-release's.** -/
theorem evidenceReleaseSAM_parent (ro : ReplayOrder sp FGP) :
    evidenceReleaseSAM sp (WriteMode.parent sp) FGP ro = evidenceReleaseSA sp FGP ro := by
  unfold evidenceReleaseSAM
  rw [acOnTickEM_parent]
  rfl

end Parent

open SA

section Handlers

variable {sp : SAParams} {FGP : Type} {σ : Type} (E : UnlockStage sp wlockStore σ) (c : σ)
  (m : WriteMode)

/-! ### The writes -/

theorem optimisticConfirmationWM_ac {X : WState sp.n} (hX : LocksForget X) (Φ : Frm sp.n FGP)
    (t : Time) :
    (optimisticConfirmationWM sp m X Φ t).ac = optimisticConfirmationM sp m X.ac Φ t := by
  have h := lock_image_optimisticLocksWM m (W := X.wlocks) (A := X.ac)
    ((locksForget_iff X).1 hX).symm Φ t
  change { optimisticConfirmationM sp m X.ac Φ t with
    locks := WLock.lock '' optimisticLocksWM sp m X.wlocks X.ac Φ t } = _
  rw [h]

theorem updateConfirmationWM_ac {X : WState sp.n} (hX : LocksForget X) (Φ : Frm sp.n FGP)
    (t : Time) (s : Nat) :
    (updateConfirmationWM sp m X Φ t s).ac = updateConfirmationM sp m X.ac Φ t s := by
  have h := lock_image_updateLocksWM m (W := X.wlocks) (A := X.ac)
    ((locksForget_iff X).1 hX).symm X.counts Φ t s
  change { updateConfirmationM sp m X.ac Φ t s with
    locks := WLock.lock '' updateLocksWM sp m X.wlocks X.ac X.counts Φ t s } = _
  rw [h]

/-! ### The parent's handlers with the locks after the unlock given -/

/-- **`try_vote` at mode `m`, forgotten**, is `tryVoteWithM m` of the forgotten stage unlock. -/
theorem tryVoteEM_proj {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    ((tryVoteEM sp E c m self X Φ t).1.ac, (tryVoteEM sp E c m self X Φ t).2.map projEm) =
      tryVoteWithM sp m self (WLock.lock '' wlockStore.unlockWith sp E c
        X.wlocks Φ t ((sp.slot t : Int) - 1)
        (mergedVoteView sp X.ac Φ (sp.slot t))) X.ac Φ t := by
  unfold tryVoteEM tryVoteWithM
  dsimp only
  split_ifs with h₁ h₂ h₃
  · rfl
  · rfl
  · rw [optimisticConfirmationWM_ac m (locksForget_admitVote
      (Y := { (unlockStateE sp E c X Φ t ((sp.slot t : Int) - 1)
          (mergedVoteView sp X.ac Φ (sp.slot t)))
        with ac := { (unlockStateE sp E c X Φ t _ _).ac with votedSlot := sp.slot t } })
      ((locksForget_iff _).2 rfl) t _)]
    simp only [List.map_cons, List.map_nil, projEm_eq]
    rfl
  · rw [optimisticConfirmationWM_ac m (locksForget_admitVote
      (Y := { X with ac := { X.ac with votedSlot := sp.slot t } })
      ((locksForget_iff _).2 ((locksForget_iff X).1 hX)) t _)]
    simp only [List.map_cons, List.map_nil, projEm_eq]

/-! ### The invariant through every handler -/

theorem locksForget_optimisticConfirmationWM (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    LocksForget (optimisticConfirmationWM sp m X Φ t) :=
  locksForget_withLocks _ _ _

theorem locksForget_updateConfirmationWM (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (s : Nat) : LocksForget (updateConfirmationWM sp m X Φ t s) :=
  (locksForget_iff _).2 rfl

/-- `try_vote` at mode `m` keeps the invariant, also at the read point of its emission. -/
theorem locksForget_tryVoteEM {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    LocksForget (tryVoteEM sp E c m self X Φ t).1 ∧
      ∀ e ∈ (tryVoteEM sp E c m self X Φ t).2, LocksForget e.readPoint := by
  unfold tryVoteEM
  dsimp only
  split_ifs with h₁ h₂ h₃
  · exact ⟨hX, fun _ h => absurd h List.not_mem_nil⟩
  · exact ⟨hX, fun _ h => absurd h List.not_mem_nil⟩
  · refine ⟨locksForget_optimisticConfirmationWM m _ _ _, fun e he => ?_⟩
    rw [List.mem_singleton] at he
    subst he
    exact (locksForget_iff _).2 rfl
  · refine ⟨locksForget_optimisticConfirmationWM m _ _ _, fun e he => ?_⟩
    rw [List.mem_singleton] at he
    subst he
    exact (locksForget_iff _).2 ((locksForget_iff X).1 hX)

/-- `ac_on_message` at mode `m` establishes the invariant, also at its emissions. -/
theorem locksForget_acOnMessageEM (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (v : Vote sp.n) :
    LocksForget (acOnMessageEM sp E c m self X Φ t v).1 ∧
      ∀ e ∈ (acOnMessageEM sp E c m self X Φ t v).2, LocksForget e.readPoint :=
  locksForget_tryVoteEM E c m (locksForget_optimisticConfirmationWM m _ _ _) self Φ t

/-- `ac_on_block` at mode `m` establishes the invariant, also at its emissions. -/
theorem locksForget_acOnBlockEM (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (B : Blk sp.n FGP) :
    LocksForget (acOnBlockEM sp E c m self X Φ t B).1 ∧
      ∀ e ∈ (acOnBlockEM sp E c m self X Φ t B).2, LocksForget e.readPoint :=
  locksForget_tryVoteEM E c m (locksForget_optimisticConfirmationWM m _ _ _) self Φ t

/-- `ac_on_tick` at mode `m` keeps the invariant, also at its emissions. -/
theorem locksForget_acOnTickEM {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    LocksForget (acOnTickEM sp E c m self X Φ t).1 ∧
      ∀ e ∈ (acOnTickEM sp E c m self X Φ t).2, LocksForget e.readPoint := by
  have hv := locksForget_tryVoteEM E c m hX self Φ t
  unfold acOnTickEM
  dsimp only
  split_ifs <;>
    first
    | exact ⟨hX, fun _ h => absurd h List.not_mem_nil⟩
    | exact ⟨locksForget_updateConfirmationWM m _ _ _ _, hv.2⟩
    | exact hv
    | exact ⟨locksForget_updateConfirmationWM m _ _ _ _, fun _ h => absurd h List.not_mem_nil⟩

/-! ### `ac_on_message`, `ac_on_block`, `ac_on_tick` -/

/-- **`ac_on_message` at mode `m`, forgotten**: the admission and the optimistic confirmation at
mode `m`, then `tryVoteWithM m` of the forgotten stage unlock of the state after them. -/
theorem acOnMessageEM_proj {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (v : Vote sp.n) :
    let Y := optimisticConfirmationWM sp m { X with ac := admitVote sp X.ac t v } Φ t
    ((acOnMessageEM sp E c m self X Φ t v).1.ac,
        (acOnMessageEM sp E c m self X Φ t v).2.map projEm) =
      tryVoteWithM sp m self (WLock.lock '' wlockStore.unlockWith sp E c
        Y.wlocks Φ t ((sp.slot t : Int) - 1)
        (mergedVoteView sp Y.ac Φ (sp.slot t)))
        (optimisticConfirmationM sp m (admitVote sp X.ac t v) Φ t) Φ t := by
  intro Y
  have hY : Y.ac = optimisticConfirmationM sp m (admitVote sp X.ac t v) Φ t :=
    optimisticConfirmationWM_ac m (locksForget_admitVote hX t v) Φ t
  rw [← hY]
  exact tryVoteEM_proj E c m (locksForget_optimisticConfirmationWM m _ _ _) self Φ t

/-- **`ac_on_block` at mode `m`, forgotten**: the receipt and the optimistic confirmation at mode
`m`, then `tryVoteWithM m` of the forgotten stage unlock of the state after them. -/
theorem acOnBlockEM_proj {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (B : Blk sp.n FGP) :
    let Y := optimisticConfirmationWM sp m { X with ac := blockReceipt sp X.ac t B } Φ t
    ((acOnBlockEM sp E c m self X Φ t B).1.ac, (acOnBlockEM sp E c m self X Φ t B).2.map projEm) =
      tryVoteWithM sp m self (WLock.lock '' wlockStore.unlockWith sp E c
        Y.wlocks Φ t ((sp.slot t : Int) - 1)
        (mergedVoteView sp Y.ac Φ (sp.slot t)))
        (optimisticConfirmationM sp m (blockReceipt sp X.ac t B) Φ t) Φ t := by
  intro Y
  have hR : LocksForget { X with ac := blockReceipt sp X.ac t B } :=
    (locksForget_iff _).2 ((blockReceipt_keeps_locks X.ac t B).1.trans ((locksForget_iff X).1 hX))
  have hY : Y.ac = optimisticConfirmationM sp m (blockReceipt sp X.ac t B) Φ t :=
    optimisticConfirmationWM_ac m hR Φ t
  rw [← hY]
  exact tryVoteEM_proj E c m (locksForget_optimisticConfirmationWM m _ _ _) self Φ t

/-- **`ac_on_tick` at mode `m`, forgotten**: `acOnTickWithM m` of the forgotten stage unlock. -/
theorem acOnTickEM_proj {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    ((acOnTickEM sp E c m self X Φ t).1.ac, (acOnTickEM sp E c m self X Φ t).2.map projEm) =
      acOnTickWithM sp m self (WLock.lock '' wlockStore.unlockWith sp E c
        X.wlocks Φ t ((sp.slot t : Int) - 1)
        (mergedVoteView sp X.ac Φ (sp.slot t))) X.ac Φ t := by
  have hv := tryVoteEM_proj E c m hX self Φ t
  have hf := (locksForget_tryVoteEM E c m hX self Φ t).1
  unfold acOnTickEM acOnTickWithM
  dsimp only
  split_ifs <;>
    first
    | rfl
    | exact hv
    | (rw [updateConfirmationWM_ac m hf, ← hv])
    | (rw [updateConfirmationWM_ac m hX]; rfl)

/-! ### The restart -/

/-- At a state whose receipt is not joined, `ac_on_block` at mode `m` is the receipt and emits
nothing: the optimistic confirmation selects nothing unjoined, at every mode. -/
theorem acOnBlockEM_of_not_joined {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (B : Blk sp.n FGP)
    (hnj : ¬ joined sp (blockReceipt sp X.ac t B) t) :
    acOnBlockEM sp E c m self X Φ t B = ({ X with ac := blockReceipt sp X.ac t B }, []) := by
  have hsel : optimisticSelect sp (blockReceipt sp X.ac t B) Φ t = none := by
    simp only [optimisticSelect, hnj, not_false_eq_true, true_or, ite_true]
  have hopt : optimisticConfirmationWM sp m { X with ac := blockReceipt sp X.ac t B } Φ t =
      { X with ac := blockReceipt sp X.ac t B } := by
    have hl : WLock.lock '' X.wlocks = (blockReceipt sp X.ac t B).locks :=
      ((locksForget_iff X).1 hX).symm.trans (blockReceipt_keeps_locks X.ac t B).1.symm
    cases hm : m.optimistic
    · simp only [optimisticConfirmationWM, withLocks, optimisticLocksWM, optimisticConfirmationM,
        hm, hl]
    · simp only [optimisticConfirmationWM, withLocks, optimisticLocksWM, optimisticConfirmationM,
        hm, optimisticLocksW, hsel, hl]
  simp only [acOnBlockEM, hopt, tryVoteEM, hnj, not_false_eq_true, true_or, ite_true]

/-- **The restart at mode `m`, forgotten**: in a well-formed frame at `t ≥ 0`, it is the parent's
restart (which `stepWithM` takes at every mode), and neither emits; its replay runs unjoined. -/
theorem acRestartEM_proj {X : WState sp.n} (hX : LocksForget X) (ro : ReplayOrder sp FGP)
    (self : Fin sp.n) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} (ht : 0 ≤ t) :
    (acRestartEM sp E c m ro self X Φ t).1.ac = (acRestart sp ro self X.ac Φ t).1 ∧
      (acRestartEM sp E c m ro self X Φ t).2 = [] ∧ LocksForget (acRestartEM sp E c m ro self X Φ
          t).1 := by
  have hl := ro.parentOrder t Φ (parentOrder_exists sp hΦ)
  let A' : SAState sp.n := { SAState.initial sp.genesisRoot with
    locks := X.ac.locks, latestConfirmed := X.ac.latestConfirmed,
    restartTime := (t : WithBot Time) }
  have h₀ : RestartInv sp X.ac Φ t A' :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun σ x hx => by simp [A', SAState.initial] at hx,
      fun x => Or.inl rfl, fun q => Or.inl rfl⟩
  have key : ∀ l : List (Blk sp.n FGP), (∀ B ∈ l, B ∈ Φ.tree ∧ B.root ≠ sp.genesisRoot) →
      ∀ (acc : WState sp.n × List (EmW sp FGP)) (pacc : SAState sp.n × List (Em sp FGP)),
      acc.1.ac = pacc.1 → acc.2 = [] → pacc.2 = [] → LocksForget acc.1 →
      RestartInv sp X.ac Φ t pacc.1 →
      let r := l.foldl (fun acc B => let r := acOnBlockEM sp E c m self acc.1 Φ t B;
        (r.1, acc.2 ++ r.2)) acc
      let q := l.foldl (fun acc B => let r := SA.acOnBlock sp self acc.1 Φ t B;
        (r.1, acc.2 ++ r.2)) pacc
      r.1.ac = q.1 ∧ r.2 = [] ∧ q.2 = [] ∧ LocksForget r.1 := by
    intro l
    induction l with
    | nil => intro _ acc pacc he h₂ h₂' hf _; exact ⟨he, h₂, h₂', hf⟩
    | cons B l ih =>
      intro hl acc pacc he h₂ h₂' hf h₁
      obtain ⟨hB, hg⟩ := hl B List.mem_cons_self
      have hR := h₁.blockReceipt sp hB hg
      have hnj := not_joined_of_restartTime sp ht hR.restartTime
      rw [← he] at hnj
      have hw := acOnBlockEM_of_not_joined E c m hf self Φ t B hnj
      have hp := h₁.acOnBlock sp ht hB hg self
      simp only [List.foldl_cons]
      apply ih (fun C hC => hl C (List.mem_cons_of_mem _ hC))
      · simp only [hw, hp, he]
      · simp only [hw, h₂, List.append_nil]
      · simp only [hp, h₂', List.append_nil]
      · simp only [hw]
        exact (locksForget_iff _).2
          ((blockReceipt_keeps_locks acc.1.ac t B).1.trans ((locksForget_iff acc.1).1 hf))
      · simp only [hp]
        exact hR
  obtain ⟨h1, h2, -, h4⟩ := key (ro.order t Φ) (fun B hB => (hl.2.1 B).mp hB)
    ({ ac := A', wlocks := X.wlocks, counts := fun _ _ => 0 }, []) (A', []) rfl rfl rfl
    ((locksForget_iff _).2 ((locksForget_iff X).1 hX)) h₀
  exact ⟨h1, h2, h4⟩

open SA

end Handlers

section Traces

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}

/-! ### A call at a stage -/

section Stage

variable {σ : Type} (E : UnlockStage sp wlockStore σ) (c : σ) (m : WriteMode)

variable (sp ro) in
/-- A call of the weighted SA at the stage `E` with context `c`, at mode `m`. -/
noncomputable abbrev stepEM (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (goldilocksSA sp FGP ro).Call → WState sp.n × List (EmW sp FGP)
  | .tick => acOnTickEM sp E c m self X Φ t
  | .proposal => ((acProposalE sp E c X Φ t).1, [])
  | .toFG => ((acToFGW sp X Φ t).1, [])
  | .message v => acOnMessageEM sp E c m self X Φ t v
  | .block B => acOnBlockEM sp E c m self X Φ t B
  | .restart => acRestartEM sp E c m ro self X Φ t

theorem callInputWM_spec {X : WState sp.n} (hX : LocksForget X) (Φ : Frm sp.n FGP) (t : Time)
    (k : (goldilocksSA sp FGP ro).Call) :
    LocksForget (callInputWM sp m X Φ t k) ∧
      (callInputWM sp m X Φ t k).ac = callInputM sp m X.ac Φ t k := by
  cases k with
  | message v =>
    exact ⟨locksForget_optimisticConfirmationWM m _ _ _,
      optimisticConfirmationWM_ac m (locksForget_admitVote hX t v) Φ t⟩
  | block B =>
    exact ⟨locksForget_optimisticConfirmationWM m _ _ _, optimisticConfirmationWM_ac m
      ((locksForget_iff _).2 ((blockReceipt_keeps_locks X.ac t B).1.trans ((locksForget_iff _).1
          hX))) Φ t⟩
  | _ => exact ⟨hX, rfl⟩

/-- **The stage's unlock is related to the call's unlock input**, for every stage whose
forgotten unlock satisfies the unlock relation at the frame. -/
theorem unlockAtEM_rel {Φ : Frm sp.n FGP}
    (hrel : ∀ (L : Set WLock) (t : Time) (s : Int) (V : View sp.n),
      UnlockRel sp (WLock.lock '' L) Φ t s V (WLock.lock '' wlockStore.unlockWith sp E c L Φ t s V))
    {X : WState sp.n} (hX : LocksForget X) (t : Time) (k : (goldilocksSA sp FGP ro).Call) :
    UnlockRel sp (callInputM sp m X.ac Φ t k).locks Φ t ((sp.slot t : Int) - 1)
      (callViewM sp m X.ac Φ t k) (unlockAtEM sp E c m X Φ t k) := by
  obtain ⟨hf, he⟩ := callInputWM_spec m hX Φ t k
  rw [← he, (locksForget_iff _).1 hf]
  exact hrel _ t _ _

/-- **A call at a stage and mode `m`, forgotten, is `stepWithM m` of the stage's unlock.** -/
theorem stepWithM_stepEM {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} (ht : 0 ≤ t)
    (k : (goldilocksSA sp FGP ro).Call) :
    stepWithM sp ro m self (unlockAtEM sp E c m X Φ t k) X.ac Φ t k =
      ((stepEM sp ro E c m self X Φ t k).1.ac,
        (stepEM sp ro E c m self X Φ t k).2.map projEm) := by
  cases k with
  | tick => exact (acOnTickEM_proj E c m hX self Φ t).symm
  | proposal =>
    have h := congrArg Prod.fst (acProposalE_proj E c X Φ t)
    exact Prod.ext h.symm rfl
  | toFG => rfl
  | message v =>
    have h := acOnMessageEM_proj E c m hX self Φ t v
    dsimp only at h
    rw [optimisticConfirmationWM_ac m (locksForget_admitVote hX t v) Φ t] at h
    exact h.symm
  | block B =>
    have h := acOnBlockEM_proj E c m hX self Φ t B
    dsimp only at h
    rw [optimisticConfirmationWM_ac m ((locksForget_iff _).2
      ((blockReceipt_keeps_locks X.ac t B).1.trans ((locksForget_iff X).1 hX))) Φ t] at h
    exact h.symm
  | restart =>
    obtain ⟨h1, h2, -⟩ := acRestartEM_proj E c m hX ro self hΦ ht
    refine Prod.ext h1.symm ?_
    change (acRestart sp ro self X.ac Φ t).2 = (acRestartEM sp E c m ro self X Φ t).2.map projEm
    rw [h2, (restart_state sp FGP ro self X.ac Φ t hΦ ht).1]
    rfl

/-- Every call at a stage keeps `LocksForget`. -/
theorem locksForget_stepEM {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} (ht : 0 ≤ t)
    (k : (goldilocksSA sp FGP ro).Call) : LocksForget (stepEM sp ro E c m self X Φ t k).1 := by
  cases k with
  | tick => exact (locksForget_acOnTickEM E c m hX self Φ t).1
  | proposal => exact locksForget_acProposalE E c hX Φ t
  | toFG => exact locksForget_acToFGW hX Φ t
  | message v => exact (locksForget_acOnMessageEM E c m self X Φ t v).1
  | block B => exact (locksForget_acOnBlockEM E c m self X Φ t B).1
  | restart => exact (acRestartEM_proj E c m hX ro self hΦ ht).2.2

end Stage

variable {m : WriteMode}

/-! ### Evidence-release's traces -/

theorem step_eq_stepEM (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (k : (evidenceReleaseSAM sp m FGP ro).Call) :
    (evidenceReleaseSAM sp m FGP ro).step self X Φ t k =
      stepEM sp ro (evidenceStage sp) () m self X Φ t (projCallM ro k) := by
  cases k <;> rfl

theorem projCallM_eq_restart {k : (evidenceReleaseSAM sp m FGP ro).Call} :
    projCallM ro k = .restart ↔ k = .restart := by
  cases k <;> simp

theorem callOK_projCallM {U : Set (Blk sp.n FGP)} {Φ Φ' : Frm sp.n FGP} {t : Time}
    {k : (evidenceReleaseSAM sp m FGP ro).Call}
    (h : (evidenceReleaseSAM sp m FGP ro).CallOK U Φ t k Φ') :
    (goldilocksSA sp FGP ro).CallOK U Φ t (projCallM ro k) Φ' := by
  cases k <;> exact h

variable {tr : ACTrace (evidenceReleaseSAM sp m FGP ro)}

theorem projTraceM_state (y : Fin sp.n)
    (i : Nat) : (projTraceM tr).state y i = (tr.state y i).ac := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [Trace.state]
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact absurd ⟨h₁.1, by simpa using h₁.2⟩ h₂
    · exact absurd ⟨h₂.1, by simpa using h₂.2⟩ h₁
    · exact ih

theorem projTraceM_callAt {y : Fin sp.n} {i : Nat} {ℓP : ACLabel (goldilocksSA sp FGP ro)} :
    (projTraceM tr).CallAt y i ℓP ↔ ∃ ℓ, tr.CallAt y i ℓ ∧ projLabelM ℓ = ℓP := by
  simp only [Trace.CallAt, Option.map_eq_some_iff]
  constructor
  · rintro ⟨h1, ℓ, h2, rfl⟩
    exact ⟨ℓ, ⟨h1, h2⟩, rfl⟩
  · rintro ⟨ℓ, ⟨h1, h2⟩, rfl⟩
    exact ⟨h1, ℓ, h2, rfl⟩

theorem projTraceM_noCallBetween {y : Fin sp.n} {j i : Nat} :
    (projTraceM tr).NoCallBetween y j i ↔ tr.NoCallBetween y j i :=
  ⟨fun h k hj hi ℓ hc => h k hj hi _ (projTraceM_callAt.2 ⟨ℓ, hc, rfl⟩),
    fun h k hj hi _ hc => by
      obtain ⟨ℓ, hc, -⟩ := projTraceM_callAt.1 hc
      exact h k hj hi ℓ hc⟩

theorem projTraceM_restartAt {y : Fin sp.n} {k : Nat} :
    (projTraceM tr).RestartAt y k ↔ tr.RestartAt y k := by
  constructor
  · rintro ⟨_, hc, hr⟩
    obtain ⟨ℓ, hc₀, rfl⟩ := projTraceM_callAt.1 hc
    exact ⟨ℓ, hc₀, projCallM_eq_restart.1 hr⟩
  · rintro ⟨ℓ, hc, hr⟩
    exact ⟨_, projTraceM_callAt.2 ⟨ℓ, hc, rfl⟩, projCallM_eq_restart.2 hr⟩

variable {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}

/-- At a proposal call, the oracle's `ac_proposal` is evidence-release's, forgotten, at every
mode (the proposal writes nothing): the honest proposals with the unlock given (`HonestProposalU`,
`DrivenU`) are the SA's at mode `m`. -/
theorem acProposalWith_erOracleM {x : Fin sp.n} {k : Nat}
    {ℓ : ACLabel (evidenceReleaseSAM sp m FGP ro)} (hc : tr.CallAt x k ℓ)
    (hcall : ℓ.call = .proposal) :
    acProposalWith sp (erOracleM tr k) ((projTraceM tr).state x k) ℓ.frame (tr.time k) =
      ((acProposalW sp (tr.state x k) ℓ.frame (tr.time k)).1.ac,
        (acProposalW sp (tr.state x k) ℓ.frame (tr.time k)).2) := by
  rw [projTraceM_state, acProposalW_proj]
  simp only [erOracleM, hc.2, hc.1, hcall]
  rfl

/-- Reachable states of the evidence-release SA at mode `m` keep `LocksForget`, at times from
`0`. -/
theorem locksForget_of_reachableM {self : Fin sp.n} {X : (evidenceReleaseSAM sp m FGP ro).State}
    {Φ : (evidenceReleaseSAM sp m FGP ro).Frm} {t : Time}
        (h : (evidenceReleaseSAM sp m FGP ro).ReachableAt self U X Φ t) :
    LocksForget X ∧ 0 ≤ t := by
  induction h with
  | init => exact ⟨locksForget_initial _, le_rfl⟩
  | step k _ ht hc ih =>
    refine ⟨?_, ih.2.trans ht⟩
    rw [step_eq_stepEM]
    exact locksForget_stepEM _ _ _ ih.1 _ hc.1.1 (ih.2.trans ht) _

/-- The honest states of a run of the evidence-release SA at mode `m` keep `LocksForget`. -/
theorem locksForget_stateM (h : ACLocalRun (evidenceReleaseSAM sp m FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) : LocksForget (tr.state y i) := by
  rcases tr.noCall_or_lastCall y i with hnone | ⟨j, hj, ℓ, hc, hnb⟩
  · rw [tr.state_of_noCall hnone, h.init y hy]
    exact locksForget_initial _
  · rw [tr.state_of_lastCall hc hj hnb]
    exact (locksForget_of_reachableM (localRun_reachable _ _ _ _ _ tr h y hy j ℓ hc)).1

private theorem frameOK_of_callM (h : ACLocalRun (evidenceReleaseSAM sp m FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (evidenceReleaseSAM sp m FGP ro)}
    (hc : tr.CallAt y i ℓ) : FrameOK ℓ.frame := by
  rcases h.frameLaw y hy i ℓ hc with ⟨-, Φ₀, -, -, hk⟩ | ⟨-, ℓ₀, -, -, -, hk⟩ <;> exact hk.1.1

/-- **A run of the evidence-release SA at mode `m`, forgotten, is a run at mode `m` with the unlock
given by `erOracleM`.** -/
theorem localRunU_projTraceM (h : ACLocalRun (evidenceReleaseSAM sp m FGP ro) H U tr) :
    ACLocalRunU m (erOracleM tr) H U (projTraceM tr) where
  coherent := h.coherent
  init y hy := by
    change (tr.init y).ac = _
    rw [h.init y hy]
    rfl
  exec i ℓP hl hH := by
    obtain ⟨ℓ, hl', rfl⟩ := Option.map_eq_some_iff.1 hl
    have hc : tr.CallAt (tr.node i) i ℓ := ⟨rfl, hl'⟩
    rw [projTraceM_state]
    simp only [erOracleM, hl']
    rw [stepWithM_stepEM _ _ _ (locksForget_stateM h hH i) _ (frameOK_of_callM h hH hc)
      (h.time_nonneg i), ← step_eq_stepEM, h.exec i ℓ hl' hH]
  lawful i ℓP hl hH hΦ := by
    obtain ⟨ℓ, hl', rfl⟩ := Option.map_eq_some_iff.1 hl
    rw [projTraceM_state]
    simp only [erOracleM, hl']
    exact unlockAtEM_rel _ _ _
      (unlockRel_unlockWith wlockStore_lawful (evidenceStage_lawful sp) () hΦ)
      (locksForget_stateM h hH i) _ _
  frameLaw y hy i ℓP hc := by
    obtain ⟨ℓ, hc₀, rfl⟩ := projTraceM_callAt.1 hc
    rcases h.frameLaw y hy i ℓ hc₀ with ⟨hn, Φ₀, h1, h2, h3⟩ | ⟨j, ℓ', hj, hc', hn, h3⟩
    · exact Or.inl ⟨projTraceM_noCallBetween.2 hn, Φ₀, h1, h2, callOK_projCallM h3⟩
    · exact Or.inr ⟨j, projLabelM ℓ', hj, projTraceM_callAt.2 ⟨ℓ', hc', rfl⟩,
        projTraceM_noCallBetween.2 hn, callOK_projCallM h3⟩
  time_nonneg := h.time_nonneg
  time_mono := h.time_mono
  awake_of_call y hy i ℓP hc := by
    obtain ⟨ℓ, hc₀, rfl⟩ := projTraceM_callAt.1 hc
    exact h.awake_of_call y hy i ℓ hc₀
  restart_of_sleep y hy i ℓP u hc h0 hu hna hb := by
    obtain ⟨ℓ, hc₀, rfl⟩ := projTraceM_callAt.1 hc
    exact projCallM_eq_restart.2 (h.restart_of_sleep y hy i ℓ u hc₀ h0 hu hna
      fun j hj ℓ' hc' => hb j hj _ (projTraceM_callAt.2 ⟨ℓ', hc', rfl⟩))
  restart_at_wake y hy u v h0 huv hna hv := by
    obtain ⟨k, hk, h1, h2⟩ := h.restart_at_wake y hy u v h0 huv hna hv
    exact ⟨k, projTraceM_restartAt.2 hk, h1, h2⟩
  sleep_of_restart y hy i ℓP hc hr := by
    obtain ⟨ℓ, hc₀, rfl⟩ := projTraceM_callAt.1 hc
    obtain ⟨u, h0, hu, hna, hb⟩ := h.sleep_of_restart y hy i ℓ hc₀ (projCallM_eq_restart.1 hr)
    exact ⟨u, h0, hu, hna, fun j hj ℓ' hc' => by
      obtain ⟨ℓ'', hc'', -⟩ := projTraceM_callAt.1 hc'
      exact hb j hj ℓ'' hc''⟩

end Traces

end Consensus.Goldilocks.EvidenceRelease

end
