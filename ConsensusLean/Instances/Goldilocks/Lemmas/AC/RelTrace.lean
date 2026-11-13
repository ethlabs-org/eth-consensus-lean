module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Locks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Events
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WriteMode
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.RelTrace
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.HandlerFields

public section

/-! # SA traces with the unlock given per call: the laws

The vocabulary (the handlers with the locks after the unlock given and at a write mode, the
unlock input of a call, the unlock relation `UnlockRel`, the parent's oracle and the trace law
`ACLocalRunU m u`) is in `Milestones/Spec/SA/RelTrace`. This module proves its laws: the parent's
calls are `stepWith` of their own unlock (`step_eq_stepWith`), the handlers at the parent's mode
are the parent's (`stepWithM_parent` and the others, by `rfl`), so are the call and the trace law
from the parent's start (`stepWithMS_parentWalkStartFn`, `acLocalRunUS_parentWalkStartFn`, by
`rfl`), the parent's `unlock` satisfies the relation (`unlockRel_unlock`) and related locks only
move back (`UnlockRel.movesBack`), and the parent's runs and reachable states are such runs at
the parent's mode and unlock (`ACLocalRun.toU`, `ACInterface.ReachableAtFrom.toU`, `ACRun.toU`). -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type}
  {ini : Fin sp.n → SAState sp.n}

/-- `optimistic_confirmation` at any write mode keeps the permission `mayVote`. -/
theorem optimisticM_mayVote (m : WriteMode) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmationM sp m A Φ t).mayVote = A.mayVote :=
  optimisticConfirmationM_keep _ optimisticConfirmation_mayVote m A Φ t

/-- `update_confirmation` at any write mode keeps the permission `mayVote`. -/
private theorem updateM_mayVote (m : WriteMode) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (s : Nat) : (updateConfirmationM sp m A Φ t s).mayVote = A.mayVote := by
  rw [updateConfirmationM_field SAState.mayVote (fun _ _ => rfl)]
  exact updateConfirmation_mayVote A Φ t s

/-- `try_vote` with the locks after a given unlock, at any write mode, keeps the permission
`mayVote`. -/
private theorem tryVoteWithM_mayVote (m : WriteMode) (self : Fin sp.n) (L : Set Lock)
    (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (tryVoteWithM sp m self L A Φ t).1.mayVote = A.mayVote := by
  unfold tryVoteWithM
  dsimp only
  split_ifs <;> simp only [optimisticM_mayVote, admitVote_mayVote]

/-- Every call with the locks after a given unlock, at any write mode, keeps the permission
`mayVote`. -/
theorem stepWithM_mayVote (ro : ReplayOrder sp FGP) (m : WriteMode) (self : Fin sp.n)
    (L : Set Lock) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (c : (goldilocksSA sp FGP ro).Call) :
    (stepWithM sp ro m self L A Φ t c).1.mayVote = A.mayVote := by
  cases c with
  | tick =>
    change (acOnTickWithM sp m self L A Φ t).1.mayVote = _
    unfold acOnTickWithM
    dsimp only
    split_ifs <;> simp only [tryVoteWithM_mayVote, updateM_mayVote]
  | proposal =>
    change (acProposalWith sp L A Φ t).1.mayVote = _
    unfold acProposalWith
    split_ifs <;> rfl
  | toFG => exact acToFG_mayVote A Φ t
  | message v =>
    simp only [stepWithM, acOnMessageWithM, tryVoteWithM_mayVote, optimisticM_mayVote,
      admitVote_mayVote]
  | block B =>
    simp only [stepWithM, acOnBlockWithM, tryVoteWithM_mayVote, optimisticM_mayVote,
      blockReceipt_mayVote]
  | restart => exact acRestart_mayVote ro self A Φ t

/-- On a trace with the unlock given per call, which starts every honest node at the initial
state, every honest node may vote in every slot at every cut. -/
theorem traceWithM_mayVote {ro : ReplayOrder sp FGP} {m : WriteMode} {u : Nat → Set Lock}
    {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (hr : ACLocalRunU m u H U tr) {y : Fin sp.n} (hy : y ∈ H) (i s : Nat) :
    (tr.state y i).mayVote s = true := by
  induction i with
  | zero => change (tr.init y).mayVote s = true; rw [hr.init y hy]; rfl
  | succ i ih =>
    by_cases hc : ∃ ℓ, tr.CallAt y i ℓ
    · obtain ⟨ℓ, hc⟩ := hc
      have he := hr.exec i ℓ hc.2 (hc.1 ▸ hy)
      rw [hc.1] at he
      have hp := stepWithM_mayVote ro m y (u i) (tr.state y i) ℓ.frame (tr.time i) ℓ.call
      rw [he] at hp
      have hs : tr.state y (i + 1) = tr.post i := by simp [Trace.state, hc.1, hc.2]
      rw [hs, hp]
      exact ih
    · have hs : tr.state y (i + 1) = tr.state y i := by
        rw [Trace.state]
        split_ifs with h
        · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp h.2
          exact False.elim (hc ⟨ℓ, h.1, hℓ⟩)
        · rfl
      rw [hs]
      exact ih

/-! ### The handlers with the locks after the unlock given -/

/-- `ac_proposal` with the locks after the unlock given keeps `voted_slot` and
`restart_time`. -/
theorem acProposalWith_keeps (L : Set Lock) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acProposalWith sp L A Φ t).1.votedSlot = A.votedSlot ∧
      (acProposalWith sp L A Φ t).1.restartTime = A.restartTime := by
  unfold acProposalWith
  split_ifs <;> exact ⟨rfl, rfl⟩

/-! ### The unlock input of a call -/

/-- **The parent's call is `stepWith` of its own unlock.** -/
theorem step_eq_stepWith (ro : ReplayOrder sp FGP) (self : Fin sp.n) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (c : (goldilocksSA sp FGP ro).Call) :
    (goldilocksSA sp FGP ro).step self A Φ t c =
      stepWith sp ro self (parentUnlock sp A Φ t c) A Φ t c := by
  cases c <;> rfl

theorem tryVote_eq_tryVoteWith (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) :
    tryVote sp self A Φ t = tryVoteWith sp self
      (unlock sp A.locks Φ t ((sp.slot t : Int) - 1) (mergedVoteView sp A Φ (sp.slot t)))
      A Φ t := by
  rfl

theorem acProposal_eq_acProposalWith (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    acProposal sp A Φ t = acProposalWith sp
      (unlock sp A.locks Φ t ((sp.slot t : Int) - 1)
        (View.ofLists (voteViewList A Φ ((sp.slot t : Int) - 1) ⊤))) A Φ t := by
  rfl

/-- The payload of `ac_proposal` does not depend on the locks after its unlock. -/
theorem acProposal_payload_of_with {L : Set Lock} {A : SAState sp.n} {Φ : Frm sp.n FGP}
    {t : Time} {d : DutyHead sp.n FGP (Payload sp.n)} {pay : Payload sp.n}
    (h : (acProposalWith sp L A Φ t).2 = some (d, pay)) :
    ∃ d', (acProposal sp A Φ t).2 = some (d', pay) := by
  rw [acProposal_eq_acProposalWith]
  unfold acProposalWith at h ⊢
  split_ifs at h ⊢ with hj
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨_, by rw [← h.2]⟩

theorem acOnTick_eq_acOnTickWith (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) :
    acOnTick sp self A Φ t = acOnTickWith sp self
      (unlock sp A.locks Φ t ((sp.slot t : Int) - 1) (mergedVoteView sp A Φ (sp.slot t)))
      A Φ t := by
  rfl

/-! ### The handlers at the parent's mode -/

theorem tryVoteWithM_parent :
    tryVoteWithM (FGP := FGP) sp (WriteMode.parent sp) = tryVoteWith sp :=
  rfl

theorem acOnTickWithM_parent :
    acOnTickWithM (FGP := FGP) sp (WriteMode.parent sp) = acOnTickWith sp :=
  rfl

theorem acOnMessageWithM_parent :
    acOnMessageWithM (FGP := FGP) sp (WriteMode.parent sp) = acOnMessageWith sp :=
  rfl

theorem acOnBlockWithM_parent :
    acOnBlockWithM (FGP := FGP) sp (WriteMode.parent sp) = acOnBlockWith sp :=
  rfl

theorem stepWithM_parent (ro : ReplayOrder sp FGP) :
    stepWithM sp ro (WriteMode.parent sp) = stepWith sp ro :=
  rfl

theorem callInputM_parent {ro : ReplayOrder sp FGP} :
    callInputM (ro := ro) sp (WriteMode.parent sp) = callInput sp :=
  rfl

theorem callViewM_parent {ro : ReplayOrder sp FGP} :
    callViewM (ro := ro) sp (WriteMode.parent sp) = callView sp :=
  rfl

/-! ### The unlock relation -/

theorem unlockRel_iff (L : Set Lock) (Φ : Frm sp.n FGP) (t : Time) (s : Int) (V : View sp.n)
    (L' : Set Lock) :
    UnlockRel sp L Φ t s V L' ↔ ∀ l' ∈ L', ∃ l ∈ L, ∃ B ∈ Φ.tree, B.root = l.block ∧
      l.LiveAt sp t ∧ l'.slot = l.slot ∧ l'.fast = l.fast ∧ l'.expiry = l.expiry ∧
      ((l.slot : Int) < s → ∃ Y ∈ Φ.tree, Y.root = l'.block ∧
        Φ.Anc Y (unlockTarget sp Φ V s (Φ.viableAncestor B))) ∧
      (s ≤ (l.slot : Int) → l'.block = (Φ.viableAncestor B).root) :=
  Iff.rfl

/-- **The parent's unlock satisfies the relation.** -/
theorem unlockRel_unlock {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (L : Set Lock) (t : Time) (s : Int)
    (V : View sp.n) : UnlockRel sp L Φ t s V (unlock sp L Φ t s V) := by
  rintro _ ⟨l₁, ⟨l, hl, B, hB, hBr, hlive, rfl⟩, B₁, hB₁, hB₁r, rfl⟩
  obtain rfl : B₁ = Φ.viableAncestor B := hΦ.coherent.1 hB₁ (viableAncestor_anc hΦ hB).1 hB₁r
  refine ⟨l, hl, B, hB, hBr, hlive, ?_⟩
  split_ifs with h
  · refine ⟨rfl, rfl, rfl, fun _ => ⟨_, (unlockTarget_anc sp hΦ V s hB₁).1, rfl, .refl⟩,
      fun h' => absurd h (not_lt.2 h')⟩
  · exact ⟨rfl, rfl, rfl, fun h' => absurd h' h, fun _ => rfl⟩

/-- Locks related by the unlock relation only move back (A0.4 (c)). -/
theorem UnlockRel.movesBack {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {L L' : Set Lock} {t : Time}
    {s : Int} {V : View sp.n} (h : UnlockRel sp L Φ t s V L') : MovesBack sp Φ L L' := by
  intro l' hl'
  obtain ⟨l, hl, B, hB, hBr, -, hs, hf, he, hlt, hge⟩ := h l' hl'
  obtain ⟨hva, hvaB⟩ := viableAncestor_anc hΦ hB
  refine ⟨l, hl, hs, hf, he, B, hB, hBr, ?_⟩
  by_cases hsl : (l.slot : Int) < s
  · obtain ⟨Y, hY, hYr, hYT⟩ := hlt hsl
    exact ⟨Y, hY, hYr, hYT.trans ((unlockTarget_anc sp hΦ V s hva).2.trans hvaB)⟩
  · exact ⟨_, hva, (hge (not_lt.1 hsl)).symm, hvaB⟩

/-! ### The trace law -/

/-- The unlock relation at an honest call with a well-formed frame. -/
theorem ACLocalRunU.lawfulAt {ro : ReplayOrder sp FGP} {m : WriteMode} {u : Nat → Set Lock}
    {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (h : ACLocalRunU m u H U tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ)
    (hΦ : FrameOK ℓ.frame) :
    UnlockRel sp (callInputM sp m (tr.state y i) ℓ.frame (tr.time i) ℓ.call).locks ℓ.frame
      (tr.time i) ((sp.slot (tr.time i) : Int) - 1)
      (callViewM sp m (tr.state y i) ℓ.frame (tr.time i) ℓ.call) (u i) := by
  have := h.lawful i ℓ hc.2 (hc.1 ▸ hy) hΦ
  rwa [hc.1] at this

/-- At the parent's start, the call from a start is the parent's call. -/
theorem stepWithMS_parentWalkStartFn (ro : ReplayOrder sp FGP) (m : WriteMode) :
    stepWithMS sp ro m (parentWalkStartFn sp) = stepWithM sp ro m := rfl

/-- At the parent's start at every call, the trace law from the starts is the parent's. -/
theorem acLocalRunUS_parentWalkStartFn {ro : ReplayOrder sp FGP} (m : WriteMode)
    (u : Nat → Set Lock) (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) (tr : SATrace sp FGP ro) :
    ACLocalRunUS m u (fun _ => parentWalkStartFn sp) H U tr = ACLocalRunU m u H U tr := rfl

/-- **The parent's runs are runs with the unlock given**, at the parent's own unlock. -/
theorem _root_.Consensus.Goldilocks.ACLocalRun.toU {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)} {ini : Fin sp.n → SAState sp.n}
    {tr : SATrace sp FGP ro} (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr ini) :
    ACLocalRunU (WriteMode.parent sp) (parentOracle sp tr) H U tr ini where
  coherent := h.coherent
  init := h.init
  exec i ℓ hl hy := by
    have := h.exec i ℓ hl hy
    rw [step_eq_stepWith] at this
    rw [stepWithM_parent]
    simpa only [parentOracle, hl] using this
  lawful i ℓ hl _ hΦ := by
    rw [callInputM_parent, callViewM_parent]
    simp only [parentOracle, hl]
    exact unlockRel_unlock hΦ _ _ _ _
  frameLaw := h.frameLaw
  time_nonneg := h.time_nonneg
  time_mono := h.time_mono
  awake_of_call := h.awake_of_call
  restart_of_sleep := h.restart_of_sleep
  restart_at_wake := h.restart_at_wake
  sleep_of_restart := h.sleep_of_restart

/-! ### Reachable states -/

/-- **The parent's reachable states are reachable with the unlock given**, from the same start. -/
theorem _root_.Consensus.Goldilocks.ACInterface.ReachableAtFrom.toU {ro : ReplayOrder sp FGP}
    {self : Fin sp.n} {U : Set (Blk sp.n FGP)} {s₀ : SAState sp.n}
    {A : (goldilocksSA sp FGP ro).State} {Φ : (goldilocksSA sp FGP ro).Frm} {t : Time}
    (h : (goldilocksSA sp FGP ro).ReachableAtFrom s₀ self U A Φ t) :
    ReachableAtUFrom (ro := ro) (WriteMode.parent sp) s₀ self U A Φ t := by
  induction h with
  | init Φ hi hf => exact .init Φ hi hf
  | @step A Φ Φ' t t' c _ ht hc ih =>
    rw [step_eq_stepWith, ← stepWithM_parent]
    exact .step c _ ih ht hc (by
      rw [callInputM_parent, callViewM_parent]; exact unlockRel_unlock hc.1.1 _ _ _ _)

/-- The parent's runs are runs with the unlock given. -/
theorem ACRun.toU {ro : ReplayOrder sp FGP} {selectedProposer : Nat → Fin sp.n}
    {tr : SATrace sp FGP ro} {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}
    (h : ACRun selectedProposer tr H U ini) :
    ACRunU (WriteMode.parent sp) (parentOracle sp tr) selectedProposer tr H U ini :=
  ⟨h.stock, h.localRun.toU, h.honest, h.vstart⟩

end Consensus.Goldilocks.SA

end
