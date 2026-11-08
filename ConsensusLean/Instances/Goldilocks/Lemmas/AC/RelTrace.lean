module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Locks
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.SA.Events
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.WriteMode

public section

/-! # SA traces with the unlock given per call

A lock rule that replaces the SA's `unlock` (the lock-rule interface, `LockRule`) runs the
parent's handlers with other locks after the unlock. This module states the SA's handlers with
the locks after the unlock given as an argument (`tryVoteWith`, `acProposalWith`, `acOnTickWith`,
`acOnMessageWith`, `acOnBlockWith`, and the call `stepWith`), and an AC trace law over them:

* the **unlock input** of a call (`callInput`, `callView`): the state whose locks the call's
  unlock reads, and the view it reads them against (the merged vote view of the state `try_vote`
  receives; the slot-`(s − 1)` pool view in `ac_proposal`);
* **the unlock relation** (`UnlockRel`): every lock after the unlock is a live lock before it on a
  block of the tree, with its slot, fast bit and expiry; a lock of a slot below `s` is on an
  ancestor of its parent unlock target, any other on its viable ancestor. The parent's `unlock`
  satisfies it (`unlockRel_unlock`), and so does every lawful unlock stage (`LockRule`);
* **the trace law** (`ACLocalRunU u`): the AC trace contract with each honest call executing
  `stepWith` at the locks `u i` of an oracle `u`, related to the call's unlock input by
  `UnlockRel`. The parent's runs are such runs at the parent's own unlock (`ACLocalRun.toU`,
  `step_eq_stepWith`).

The other handlers (`ac_to_fg`, the restart, whose replay does not unlock) are the parent's. -/

namespace Consensus.Goldilocks.SA

variable {sp : SAParams} {FGP : Type}

/-! ### The handlers with the locks after the unlock given -/

variable (sp) in
open Classical in
/-- The parent's `try_vote` at `self`, with `L₁` as the locks after its unlock (for `s > 0`). -/
noncomputable abbrev tryVoteWith (self : Fin sp.n) (L₁ : Set Lock) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : SAState sp.n × List (Em sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp A t ∨ A.votedSlot = s ∨ sp.ts s + sp.Δ < t then (A, [])
  else if t < sp.ts s + sp.Δ ∧ (s = 0 ∨ ¬ voteReady sp Φ s) then (A, [])
  else
    let V := mergedVoteView sp A Φ s
    let A₁ := if 0 < s then { A with locks := L₁ } else A
    let dom := voteDomain sp A₁ Φ s
    let H := getHead sp A₁ Φ t (Φ.viableTree dom) V ((s : Int) - 1)
    let A₂ := { A₁ with votedSlot := s }
    let vote : Vote sp.n := { val := self, slot := s, head := H.root }
    let A₃ := optimisticConfirmation sp (admitVote sp A₂ t vote) Φ t
    (A₃, [{ msg := vote, readPoint := A₂,
            head := some { head := H, start := getAnchor sp A₁ Φ t, dom := dom } }])

variable (sp) in
open Classical in
/-- The parent's `ac_proposal`, with `L₁` as the locks after its unlock. -/
noncomputable abbrev acProposalWith (L₁ : Set Lock) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : SAState sp.n × Option (DutyHead sp.n FGP (Payload sp.n) × Payload sp.n) :=
  if ¬ joined sp A t then (A, none)
  else
    let s : Int := sp.slot t
    let p := voteViewList A Φ (s - 1) ⊤
    let V := View.ofLists p
    let A₁ := { A with locks := L₁ }
    let H := getHead sp A₁ Φ t (Φ.viableTree Φ.tree) V (s - 1)
    (A₁, some (⟨H, getAnchor sp A₁ Φ t, Φ.tree⟩, p))

variable (sp) in
open Classical in
/-- The parent's `ac_on_tick` at `self`, with `L₁` as the locks after the unlock of its vote. -/
noncomputable abbrev acOnTickWith (self : Fin sp.n) (L₁ : Set Lock) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : SAState sp.n × List (Em sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp A t then (A, [])
  else
    let r := if t = sp.ts s + sp.Δ then tryVoteWith sp self L₁ A Φ t else (A, [])
    let A₂ := if t = sp.ts s + 2 * sp.Δ ∧ 0 < s then updateConfirmation sp r.1 Φ t (s - 1)
      else r.1
    (A₂, r.2)

variable (sp) in
/-- The parent's `ac_on_message` at `self`, with `L₁` as the locks after the unlock. -/
noncomputable abbrev acOnMessageWith (self : Fin sp.n) (L₁ : Set Lock) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (v : Vote sp.n) : SAState sp.n × List (Em sp FGP) :=
  tryVoteWith sp self L₁ (optimisticConfirmation sp (admitVote sp A t v) Φ t) Φ t

variable (sp) in
/-- The parent's `ac_on_block` at `self`, with `L₁` as the locks after the unlock. -/
noncomputable abbrev acOnBlockWith (self : Fin sp.n) (L₁ : Set Lock) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (B : Blk sp.n FGP) : SAState sp.n × List (Em sp FGP) :=
  tryVoteWith sp self L₁ (optimisticConfirmation sp (blockReceipt sp A t B) Φ t) Φ t

variable (sp) in
/-- A call of the SA at `self` with `L₁` as the locks after its unlock (`ac_to_fg` and the
restart are the parent's: neither unlocks). -/
noncomputable abbrev stepWith (ro : ReplayOrder sp FGP) (self : Fin sp.n) (L₁ : Set Lock)
    (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (goldilocksSA sp FGP ro).Call → SAState sp.n × List (Em sp FGP)
  | .tick => acOnTickWith sp self L₁ A Φ t
  | .proposal => ((acProposalWith sp L₁ A Φ t).1, [])
  | .toFG => ((acToFG sp A Φ t).1, [])
  | .message m => acOnMessageWith sp self L₁ A Φ t m
  | .block B => acOnBlockWith sp self L₁ A Φ t B
  | .restart => acRestart sp ro self A Φ t

/-- `ac_proposal` with the locks after the unlock given keeps `voted_slot` and
`restart_time`. -/
theorem acProposalWith_keeps (L : Set Lock) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acProposalWith sp L A Φ t).1.votedSlot = A.votedSlot ∧
      (acProposalWith sp L A Φ t).1.restartTime = A.restartTime := by
  unfold acProposalWith
  split_ifs <;> exact ⟨rfl, rfl⟩

/-! ### The unlock input of a call -/

variable (sp) in
/-- The state whose locks the unlock of the call `c` reads: the state `try_vote` receives (after
the receipt and the optimistic confirmation of a message or a block), else the state itself. -/
noncomputable abbrev callInput {ro : ReplayOrder sp FGP} (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : (goldilocksSA sp FGP ro).Call → SAState sp.n
  | .message v => optimisticConfirmation sp (admitVote sp A t v) Φ t
  | .block C => optimisticConfirmation sp (blockReceipt sp A t C) Φ t
  | _ => A

variable (sp) in
/-- The view the unlock of the call `c` reads (the pool view in `ac_proposal`, else the merged
vote view of the call's input). -/
noncomputable abbrev callView {ro : ReplayOrder sp FGP} (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (c : (goldilocksSA sp FGP ro).Call) : View sp.n :=
  match c with
  | .proposal => View.ofLists (voteViewList A Φ ((sp.slot t : Int) - 1) ⊤)
  | _ => mergedVoteView sp (callInput sp A Φ t c) Φ (sp.slot t)

variable (sp) in
/-- The parent's locks after the unlock of the call `c`. -/
noncomputable abbrev parentUnlock {ro : ReplayOrder sp FGP} (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (c : (goldilocksSA sp FGP ro).Call) : Set Lock :=
  unlock sp (callInput sp A Φ t c).locks Φ t ((sp.slot t : Int) - 1) (callView sp A Φ t c)

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

/-! ### The handlers at a write mode -/

variable (sp) in
open Classical in
/-- `tryVoteWith` with the optimistic confirmation of mode `m`. -/
noncomputable abbrev tryVoteWithM (m : WriteMode) (self : Fin sp.n) (L₁ : Set Lock)
    (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) : SAState sp.n × List (Em sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp A t ∨ A.votedSlot = s ∨ sp.ts s + sp.Δ < t then (A, [])
  else if t < sp.ts s + sp.Δ ∧ (s = 0 ∨ ¬ voteReady sp Φ s) then (A, [])
  else
    let V := mergedVoteView sp A Φ s
    let A₁ := if 0 < s then { A with locks := L₁ } else A
    let dom := voteDomain sp A₁ Φ s
    let H := getHead sp A₁ Φ t (Φ.viableTree dom) V ((s : Int) - 1)
    let A₂ := { A₁ with votedSlot := s }
    let vote : Vote sp.n := { val := self, slot := s, head := H.root }
    let A₃ := optimisticConfirmationM sp m (admitVote sp A₂ t vote) Φ t
    (A₃, [{ msg := vote, readPoint := A₂,
            head := some { head := H, start := getAnchor sp A₁ Φ t, dom := dom } }])

variable (sp) in
open Classical in
/-- `acOnTickWith` with the writes of mode `m`. -/
noncomputable abbrev acOnTickWithM (m : WriteMode) (self : Fin sp.n) (L₁ : Set Lock)
    (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) : SAState sp.n × List (Em sp FGP) :=
  let s := sp.slot t
  if ¬ joined sp A t then (A, [])
  else
    let r := if t = sp.ts s + sp.Δ then tryVoteWithM sp m self L₁ A Φ t else (A, [])
    let A₂ := if t = sp.ts s + 2 * sp.Δ ∧ 0 < s then updateConfirmationM sp m r.1 Φ t (s - 1)
      else r.1
    (A₂, r.2)

variable (sp) in
/-- `acOnMessageWith` with the writes of mode `m`. -/
noncomputable abbrev acOnMessageWithM (m : WriteMode) (self : Fin sp.n) (L₁ : Set Lock)
    (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (v : Vote sp.n) :
    SAState sp.n × List (Em sp FGP) :=
  tryVoteWithM sp m self L₁ (optimisticConfirmationM sp m (admitVote sp A t v) Φ t) Φ t

variable (sp) in
/-- `acOnBlockWith` with the writes of mode `m`. -/
noncomputable abbrev acOnBlockWithM (m : WriteMode) (self : Fin sp.n) (L₁ : Set Lock)
    (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (B : Blk sp.n FGP) :
    SAState sp.n × List (Em sp FGP) :=
  tryVoteWithM sp m self L₁ (optimisticConfirmationM sp m (blockReceipt sp A t B) Φ t) Φ t

variable (sp) in
/-- A call of the SA at `self` with `L₁` as the locks after its unlock and the writes of mode `m`
(`ac_to_fg` and the restart are the parent's). -/
noncomputable abbrev stepWithM (ro : ReplayOrder sp FGP) (m : WriteMode) (self : Fin sp.n)
    (L₁ : Set Lock) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (goldilocksSA sp FGP ro).Call → SAState sp.n × List (Em sp FGP)
  | .tick => acOnTickWithM sp m self L₁ A Φ t
  | .proposal => ((acProposalWith sp L₁ A Φ t).1, [])
  | .toFG => ((acToFG sp A Φ t).1, [])
  | .message v => acOnMessageWithM sp m self L₁ A Φ t v
  | .block B => acOnBlockWithM sp m self L₁ A Φ t B
  | .restart => acRestart sp ro self A Φ t

variable (sp) in
/-- The state whose locks the unlock of the call `c` reads at mode `m` (`callInput`). -/
noncomputable abbrev callInputM {ro : ReplayOrder sp FGP} (m : WriteMode) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : (goldilocksSA sp FGP ro).Call → SAState sp.n
  | .message v => optimisticConfirmationM sp m (admitVote sp A t v) Φ t
  | .block C => optimisticConfirmationM sp m (blockReceipt sp A t C) Φ t
  | _ => A

variable (sp) in
/-- The view the unlock of the call `c` reads at mode `m` (`callView`). -/
noncomputable abbrev callViewM {ro : ReplayOrder sp FGP} (m : WriteMode) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (c : (goldilocksSA sp FGP ro).Call) : View sp.n :=
  match c with
  | .proposal => View.ofLists (voteViewList A Φ ((sp.slot t : Int) - 1) ⊤)
  | _ => mergedVoteView sp (callInputM sp m A Φ t c) Φ (sp.slot t)

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

variable (sp) in
/-- **The unlock relation**: every lock of `L'` is a live lock of `L` on a block `B` of the tree,
with its slot, fast bit and expiry, on an ancestor (in the tree) of the unlock target of
`B`'s viable ancestor when its slot is below `s`, and on that viable ancestor otherwise. -/
abbrev UnlockRel (L : Set Lock) (Φ : Frm sp.n FGP) (t : Time) (s : Int) (V : View sp.n)
    (L' : Set Lock) : Prop :=
  ∀ l' ∈ L', ∃ l ∈ L, ∃ B ∈ Φ.tree, B.root = l.block ∧ l.LiveAt sp t ∧ l'.slot = l.slot ∧
    l'.fast = l.fast ∧ l'.expiry = l.expiry ∧
    ((l.slot : Int) < s → ∃ Y ∈ Φ.tree, Y.root = l'.block ∧
      Φ.Anc Y (unlockTarget sp Φ V s (Φ.viableAncestor B))) ∧
    (s ≤ (l.slot : Int) → l'.block = (Φ.viableAncestor B).root)

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

variable (sp) in
/-- The parent's unlock oracle of a trace: at each labelled cut, the parent's locks after the
unlock of the call at the pre-state. -/
noncomputable abbrev parentOracle {ro : ReplayOrder sp FGP} (tr : SATrace sp FGP ro) (i : Nat) :
    Set Lock :=
  match tr.label i with
  | some ℓ => parentUnlock sp (tr.state (tr.node i) i) ℓ.frame (tr.time i) ℓ.call
  | none => ∅

/-- **The AC trace contract with the unlock given by `u` and the writes of mode `m`**:
`ACLocalRun` of the SA, except that each honest call executes `stepWithM m` at the locks `u i`,
which the unlock relation ties to the call's unlock input. -/
structure ACLocalRunU {ro : ReplayOrder sp FGP} (m : WriteMode) (u : Nat → Set Lock)
    (H : Set (Fin sp.n)) (U : Set (Blk sp.n FGP)) (tr : SATrace sp FGP ro) : Prop where
  /-- `U` is coherent: roots injective, slots increasing along parent edges. -/
  coherent : Coherent U
  /-- Each honest node starts from the initial AC state. -/
  init : ∀ y ∈ H, tr.init y = (goldilocksSA sp FGP ro).initial
  /-- Each call of an honest node executes `stepWithM m` at the locks `u i`. -/
  exec : ∀ i ℓ, tr.label i = some ℓ → tr.node i ∈ H →
    stepWithM sp ro m (tr.node i) (u i) (tr.state (tr.node i) i) ℓ.frame (tr.time i) ℓ.call =
      (tr.post i, ℓ.emits)
  /-- The locks `u i` are related to the call's unlock input. -/
  lawful : ∀ i ℓ, tr.label i = some ℓ → tr.node i ∈ H → FrameOK ℓ.frame →
    UnlockRel sp (callInputM sp m (tr.state (tr.node i) i) ℓ.frame (tr.time i) ℓ.call).locks
      ℓ.frame (tr.time i) ((sp.slot (tr.time i) : Int) - 1)
      (callViewM sp m (tr.state (tr.node i) i) ℓ.frame (tr.time i) ℓ.call) (u i)
  /-- The frame law and the input contract (`ACLocalRun.frameLaw`). -/
  frameLaw : ∀ y ∈ H, ∀ i ℓ, tr.CallAt y i ℓ →
    (tr.NoCallBetween y 0 i ∧ ∃ Φ₀, (goldilocksSA sp FGP ro).InitialFrame Φ₀ ∧
      (goldilocksSA sp FGP ro).FrameIn U Φ₀ ∧
      (goldilocksSA sp FGP ro).CallOK U Φ₀ (tr.time i) ℓ.call ℓ.frame) ∨
    (∃ j ℓ', j < i ∧ tr.CallAt y j ℓ' ∧ tr.NoCallBetween y (j + 1) i ∧
      (goldilocksSA sp FGP ro).CallOK U ℓ'.frame (tr.time i) ℓ.call ℓ.frame)
  /-- Cuts are at times from `0` on. -/
  time_nonneg : ∀ i, 0 ≤ tr.time i
  /-- The cut order is by time. -/
  time_mono : Monotone tr.time
  /-- An honest node is called only while awake. -/
  awake_of_call : ∀ y ∈ H, ∀ i ℓ, tr.CallAt y i ℓ → tr.awake y (tr.time i)
  /-- The first call of an honest node after it was asleep is a restart. -/
  restart_of_sleep : ∀ y ∈ H, ∀ i ℓ (u : Time), tr.CallAt y i ℓ → 0 ≤ u → u < tr.time i →
    ¬ tr.awake y u → (∀ j < i, ∀ ℓ', tr.CallAt y j ℓ' → tr.time j < u) → ℓ.call = .restart
  /-- A wake is a restart. -/
  restart_at_wake : ∀ y ∈ H, ∀ u v : Time, 0 ≤ u → u < v → ¬ tr.awake y u → tr.awake y v →
    ∃ k, tr.RestartAt y k ∧ u < tr.time k ∧ tr.time k ≤ v
  /-- A restart is a wake. -/
  sleep_of_restart : ∀ y ∈ H, ∀ i ℓ, tr.CallAt y i ℓ → ℓ.call = .restart →
    ∃ u : Time, 0 ≤ u ∧ u < tr.time i ∧ ¬ tr.awake y u ∧
      ∀ j < i, ∀ ℓ', tr.CallAt y j ℓ' → tr.time j < u

/-- The unlock relation at an honest call with a well-formed frame. -/
theorem ACLocalRunU.lawfulAt {ro : ReplayOrder sp FGP} {m : WriteMode} {u : Nat → Set Lock}
    {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}
    (h : ACLocalRunU m u H U tr) {y : Fin sp.n}
    (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt y i ℓ)
    (hΦ : FrameOK ℓ.frame) :
    UnlockRel sp (callInputM sp m (tr.state y i) ℓ.frame (tr.time i) ℓ.call).locks ℓ.frame
      (tr.time i) ((sp.slot (tr.time i) : Int) - 1)
      (callViewM sp m (tr.state y i) ℓ.frame (tr.time i) ℓ.call) (u i) := by
  have := h.lawful i ℓ hc.2 (hc.1 ▸ hy) hΦ
  rwa [hc.1] at this

/-- **The parent's runs are runs with the unlock given**, at the parent's own unlock. -/
theorem _root_.Consensus.Goldilocks.ACLocalRun.toU {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
    {U : Set (Blk sp.n FGP)}
    {tr : SATrace sp FGP ro} (h : ACLocalRun (goldilocksSA sp FGP ro) H U tr) :
    ACLocalRunU (WriteMode.parent sp) (parentOracle sp tr) H U tr where
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

/-- The states reached at validator `self` inside `U` by calls under the call law, each executing
`stepWith` at locks related to its unlock input (`ACInterface.ReachableAt`, with the unlock
given). -/
inductive ReachableAtU {ro : ReplayOrder sp FGP} (m : WriteMode) (self : Fin sp.n)
    (U : Set (Blk sp.n FGP)) :
    SAState sp.n → Frm sp.n FGP → Time → Prop
  /-- The initial state, with the initial frame, at time `0`. -/
  | init (Φ : Frm sp.n FGP) : (goldilocksSA sp FGP ro).InitialFrame Φ →
      (goldilocksSA sp FGP ro).FrameIn U Φ →
      ReachableAtU m self U (SAState.initial sp.genesisRoot) Φ 0
  /-- One more call at locks `L₁` related to its unlock input. -/
  | step {A : SAState sp.n} {Φ Φ' : Frm sp.n FGP} {t t' : Time}
      (c : (goldilocksSA sp FGP ro).Call) (L₁ : Set Lock) : ReachableAtU m self U A Φ t → t ≤ t' →
      (goldilocksSA sp FGP ro).CallOK U Φ t' c Φ' →
      UnlockRel sp (callInputM sp m A Φ' t' c).locks Φ' t' ((sp.slot t' : Int) - 1)
        (callViewM sp m A Φ' t' c) L₁ →
      ReachableAtU m self U (stepWithM sp ro m self L₁ A Φ' t' c).1 Φ' t'

/-- **The parent's reachable states are reachable with the unlock given.** -/
theorem _root_.Consensus.Goldilocks.ACInterface.ReachableAt.toU {ro : ReplayOrder sp FGP}
    {self : Fin sp.n} {U : Set (Blk sp.n FGP)}
    {A : (goldilocksSA sp FGP ro).State} {Φ : (goldilocksSA sp FGP ro).Frm} {t : Time}
    (h : (goldilocksSA sp FGP ro).ReachableAt self U A Φ t) :
    ReachableAtU (ro := ro) (WriteMode.parent sp) self U A Φ t := by
  induction h with
  | init Φ hi hf => exact .init Φ hi hf
  | @step A Φ Φ' t t' c _ ht hc ih =>
    rw [step_eq_stepWith, ← stepWithM_parent]
    exact .step c _ ih ht hc (by
      rw [callInputM_parent, callViewM_parent]; exact unlockRel_unlock hc.1.1 _ _ _ _)

/-- An AC trace of the SA with the unlock given, its contract and the honest-object facts
(`ACRun` with the unlock given). -/
structure ACRunU (m : WriteMode) (u : Nat → Set Lock) {ro : ReplayOrder sp FGP}
    (selectedProposer : Nat → Fin sp.n) (tr : SATrace sp FGP ro) (H : Set (Fin sp.n))
    (U : Set (Blk sp.n FGP)) : Prop where
  /-- The AC trace contract with the unlock given. -/
  localRun : ACLocalRunU m u H U tr
  /-- The honest-object facts. -/
  honest : HonestObjects selectedProposer tr H

/-- The parent's runs are runs with the unlock given. -/
theorem ACRun.toU {ro : ReplayOrder sp FGP} {selectedProposer : Nat → Fin sp.n}
    {tr : SATrace sp FGP ro} {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}
    (h : ACRun selectedProposer tr H U) :
    ACRunU (WriteMode.parent sp) (parentOracle sp tr) selectedProposer tr H U :=
  ⟨h.localRun.toU, h.honest⟩

end Consensus.Goldilocks.SA

end
