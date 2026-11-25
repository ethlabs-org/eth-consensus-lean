module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Invariant
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.RelTrace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.HandlerFields
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks AC: the vote branch of `try_vote`

Past its guard (joined, `voted_slot ≠ slot(t)`, by the slot's vote deadline `t_s + Δ`, and at the
deadline or with a ready slot `s > 0`), `try_vote` takes its vote branch whether or not the node
may vote in `s`: it unlocks (for `s > 0`; at `s = 0` it keeps the locks) and sets
`voted_slot ← s`, which is its read point. Only the emission and the own vote's admission and
optimistic check are gated by the vote permission (`tryVoteWithM_branch`). A call reaches
`try_vote` from its unlock input (`callInputM`): a tick at `t_s + Δ`, a message or a block.

* `VoteBranchAt tr y j ℓ R`: call `j` of `y` reaches `try_vote`, passes its guard, and emits a
  vote read at `R` or leaves `R`;
* the step-level lift (`stepWithM_voteBranch`) and the characterisation of an honest vote branch
  (`voteBranchAt_inputU`, `voteBranchAt_input`, `voteBranchAt_specU`, `post_of_voteBranchAtU`);
* a cast is a vote branch (`voteBranchAt_of_castAtU`), and a vote branch of a node that may vote
  in the slot is a cast (`castAt_of_voteBranchAtU`);
* where vote branches come from: a tick at the vote deadline (`voteBranchAt_of_tickU`) and
  `voted_slot` (`voteBranchAt_of_votedSlotU`). -/

namespace Consensus.Goldilocks.AC

variable {wm : WriteMode} {FGP : Type} {sp : ACParams} {ro : ReplayOrder sp FGP}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : GTrace sp FGP ro}
  {ini : Fin sp.n → ACState sp.n}

/-- `vote_ready` reads the state only through its pools. -/
theorem voteReady_congr_pool {A A' : ACState sp.n} (h : A'.pool = A.pool) (Φ : Frm sp.n FGP)
    (s : Nat) : voteReady sp A' Φ s ↔ voteReady sp A Φ s := by
  have hc : ∀ x, ShouldCountDeclaredVote sp A' x ↔ ShouldCountDeclaredVote sp A x := fun x => by
    simp only [ShouldCountDeclaredVote, ACState.poolAt, h]
  simp only [voteReady, AllDeclaredVotesCounted, hc]

/-- The read point of a vote branch has the pools of the branch's input. -/
private theorem readPoint_pool_eq {P : ACState sp.n} {L : Set Lock} {c : Prop} [Decidable c]
    {v : Int} : ({ (if c then { P with locks := L } else P) with votedSlot := v } :
      ACState sp.n).pool = P.pool := by
  split_ifs <;> rfl

/-- **Call `j` of `y` (label `ℓ`) takes the vote branch of `try_vote`, with read point `R`.** The
call reaches `try_vote` (a tick at the slot's vote deadline `t_s + Δ`, a message or a block); the
guard of `try_vote` passes there, as `try_vote` reads it (joined, `voted_slot ≠ s`, by `t_s + Δ`,
and at `t_s + Δ` or with a ready slot `s > 0`; the receipt before `try_vote` keeps the restart time
and `voted_slot`, so they are read at the state before the call, and `vote_ready` reads only the
pools, so it is read at `R`, which has the pools of `try_vote`'s input); and the call emits a vote
read at `R`, or emits nothing and leaves `R`. -/
def VoteBranchAt (tr : GTrace sp FGP ro) (y : Fin sp.n) (j : Nat)
    (ℓ : ACLabel (goldilocksAC sp FGP ro)) (R : ACState sp.n) : Prop :=
  tr.CallAt y j ℓ ∧
    ((ℓ.call = .tick ∧ tr.time j = sp.ts (sp.slot (tr.time j)) + sp.Δ) ∨
      (∃ m, ℓ.call = .message m) ∨ ∃ B, ℓ.call = .block B) ∧
    joined sp (tr.state y j) (tr.time j) ∧ (tr.state y j).votedSlot ≠ sp.slot (tr.time j) ∧
    tr.time j ≤ sp.ts (sp.slot (tr.time j)) + sp.Δ ∧
    ¬ (tr.time j < sp.ts (sp.slot (tr.time j)) + sp.Δ ∧
      (sp.slot (tr.time j) = 0 ∨ ¬ voteReady sp R ℓ.frame (sp.slot (tr.time j)))) ∧
    ((∃ e ∈ ℓ.emits, e.readPoint = R) ∨ (ℓ.emits = [] ∧ tr.post j = R))

theorem voteBranchAt_iff {y : Fin sp.n} {j : Nat} {ℓ : ACLabel (goldilocksAC sp FGP ro)}
    {R : ACState sp.n} :
    VoteBranchAt tr y j ℓ R ↔ tr.CallAt y j ℓ ∧
      ((ℓ.call = .tick ∧ tr.time j = sp.ts (sp.slot (tr.time j)) + sp.Δ) ∨
        (∃ m, ℓ.call = .message m) ∨ ∃ B, ℓ.call = .block B) ∧
      joined sp (tr.state y j) (tr.time j) ∧ (tr.state y j).votedSlot ≠ sp.slot (tr.time j) ∧
      tr.time j ≤ sp.ts (sp.slot (tr.time j)) + sp.Δ ∧
      ¬ (tr.time j < sp.ts (sp.slot (tr.time j)) + sp.Δ ∧
        (sp.slot (tr.time j) = 0 ∨ ¬ voteReady sp R ℓ.frame (sp.slot (tr.time j)))) ∧
      ((∃ e ∈ ℓ.emits, e.readPoint = R) ∨ (ℓ.emits = [] ∧ tr.post j = R)) := by
  exact Iff.rfl

/-- The call of a vote branch. -/
theorem VoteBranchAt.callAt {y : Fin sp.n} {j : Nat} {ℓ : ACLabel (goldilocksAC sp FGP ro)}
    {R : ACState sp.n} (hb : VoteBranchAt tr y j ℓ R) : tr.CallAt y j ℓ :=
  (voteBranchAt_iff.1 hb).1

/-! ## `try_vote` -/

/-- **`try_vote` past its guard takes its vote branch**, to the read point: the input with the
locks `L` after the unlock when `s > 0` (the input itself when `s = 0`) and `voted_slot ← s`. When
the node may vote in `s`, it emits its own vote of slot `s` read there and leaves that vote's
receipt; otherwise it emits nothing and leaves the read point. -/
theorem tryVoteWithM_branch {L : Set Lock} (self : Fin sp.n) {A : ACState sp.n}
    (Φ : Frm sp.n FGP) {t : Time} (hj : joined sp A t) (hv : A.votedSlot ≠ sp.slot t)
    (hlate : t ≤ sp.ts (sp.slot t) + sp.Δ)
    (hready : ¬ (t < sp.ts (sp.slot t) + sp.Δ ∧ (sp.slot t = 0 ∨ ¬ voteReady sp A Φ (sp.slot t)))) :
    (A.mayVote (sp.slot t) = true → ∃ e : Em sp FGP,
      tryVoteWithM sp wm self L A Φ t =
        (optimisticConfirmation sp (admitVote sp e.readPoint t e.msg) Φ t, [e]) ∧
      e.readPoint = { (if 0 < sp.slot t then { A with locks := L } else A) with
        votedSlot := (sp.slot t : Int) } ∧ e.msg.val = self ∧ e.msg.slot = sp.slot t) ∧
    (A.mayVote (sp.slot t) = false → tryVoteWithM sp wm self L A Φ t =
      ({ (if 0 < sp.slot t then { A with locks := L } else A) with
        votedSlot := (sp.slot t : Int) }, [])) := by
  have hg : ¬ (¬ joined sp A t ∨ A.votedSlot = sp.slot t ∨ sp.ts (sp.slot t) + sp.Δ < t) := by
    simp only [not_or, not_not, not_lt]
    exact ⟨hj, hv, hlate⟩
  unfold tryVoteWithM
  dsimp only
  rw [ite_eq_right hg, ite_eq_right hready]
  refine ⟨fun hm => ?_, fun hm => ?_⟩
  · simp only [hm, ↓reduceIte]
    refine ⟨_, Prod.ext ?_ rfl, ?_, ?_, ?_⟩ <;> rfl
  · simp only [hm, Bool.false_eq_true, ↓reduceIte]

/-- `try_vote` stops at its guard, leaving its input and emitting nothing, or passes it. -/
private theorem tryVoteWithM_cases {L : Set Lock} (self : Fin sp.n) (A : ACState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    tryVoteWithM sp wm self L A Φ t = (A, []) ∨
      (joined sp A t ∧ A.votedSlot ≠ sp.slot t ∧ t ≤ sp.ts (sp.slot t) + sp.Δ ∧
        ¬ (t < sp.ts (sp.slot t) + sp.Δ ∧ (sp.slot t = 0 ∨ ¬ voteReady sp A Φ (sp.slot t)))) := by
  by_cases h₁ : ¬ joined sp A t ∨ A.votedSlot = sp.slot t ∨ sp.ts (sp.slot t) + sp.Δ < t
  · left
    unfold tryVoteWithM
    dsimp only
    rw [ite_eq_left h₁]
  by_cases h₂ : t < sp.ts (sp.slot t) + sp.Δ ∧ (sp.slot t = 0 ∨ ¬ voteReady sp A Φ (sp.slot t))
  · left
    unfold tryVoteWithM
    dsimp only
    rw [ite_eq_right h₁, ite_eq_left h₂]
  simp only [not_or, not_not, not_lt] at h₁
  exact Or.inr ⟨h₁.1, h₁.2.1, h₁.2.2, h₂⟩

/-- The unlock input of a call keeps `voted_slot`, `restart_time` and the vote permission. -/
private theorem callInputM_keeps (A : ACState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (c : (goldilocksAC sp FGP ro).Call) :
    (callInputM sp wm A Φ t c).votedSlot = A.votedSlot ∧
      (callInputM sp wm A Φ t c).restartTime = A.restartTime ∧
      (callInputM sp wm A Φ t c).mayVote = A.mayVote := by
  cases c with
  | message v =>
    exact ⟨(optimistic_keeps _ _ _).1.trans (admitVote_keeps _ _ _).1,
      (optimistic_keeps _ _ _).2.trans (admitVote_keeps _ _ _).2,
      (optimisticConfirmation_mayVote _ _ _).trans (admitVote_mayVote _ _ _)⟩
  | block B =>
    exact ⟨(optimistic_keeps _ _ _).1.trans (blockReceipt_keeps _ _ _).1,
      (optimistic_keeps _ _ _).2.trans (blockReceipt_keeps _ _ _).2,
      (optimisticConfirmation_mayVote _ _ _).trans (blockReceipt_mayVote _ _ _)⟩
  | tick => exact ⟨rfl, rfl, rfl⟩
  | proposal => exact ⟨rfl, rfl, rfl⟩
  | toFG => exact ⟨rfl, rfl, rfl⟩
  | restart => exact ⟨rfl, rfl, rfl⟩

/-! ## Through a call -/

/-- **The vote branch through a call**: a call emits nothing and keeps `voted_slot` (a restart
resets it to `-1`); or it reaches `try_vote` (a tick at `t_s + Δ`, a message or a block), the
guard passes there, its unlock reads its unlock input `P`'s merged view, and the call is
`try_vote` from `P`. -/
theorem stepWithM_voteBranch {L : Set Lock} (self : Fin sp.n)
    {A A' : ACState sp.n} {Φ : Frm sp.n FGP} {t : Time} (hΦ : FrameOK Φ) (ht : 0 ≤ t)
    (c : (goldilocksAC sp FGP ro).Call) {es : List (Em sp FGP)}
    (hs : stepWithM sp ro wm self L A Φ t c = (A', es)) :
    (es = [] ∧ (A'.votedSlot = A.votedSlot ∨ A'.votedSlot = -1)) ∨
      (((c = .tick ∧ t = sp.ts (sp.slot t) + sp.Δ) ∨ (∃ m, c = .message m) ∨
          ∃ B, c = .block B) ∧
        joined sp A t ∧ A.votedSlot ≠ sp.slot t ∧ t ≤ sp.ts (sp.slot t) + sp.Δ ∧
        ¬ (t < sp.ts (sp.slot t) + sp.Δ ∧
          (sp.slot t = 0 ∨ ¬ voteReady sp (callInputM sp wm A Φ t c) Φ (sp.slot t))) ∧
        callViewM sp wm A Φ t c = mergedVoteView sp (callInputM sp wm A Φ t c) Φ (sp.slot t) ∧
        tryVoteWithM sp wm self L (callInputM sp wm A Φ t c) Φ t = (A', es)) := by
  have hkeep := callInputM_keeps (wm := wm) A Φ t c
  have ofTry : ((c = .tick ∧ t = sp.ts (sp.slot t) + sp.Δ) ∨ (∃ m, c = .message m) ∨
        ∃ B, c = .block B) →
      tryVoteWithM sp wm self L (callInputM sp wm A Φ t c) Φ t = (A', es) →
      callViewM sp wm A Φ t c = mergedVoteView sp (callInputM sp wm A Φ t c) Φ (sp.slot t) →
      (es = [] ∧ (A'.votedSlot = A.votedSlot ∨ A'.votedSlot = -1)) ∨
        (((c = .tick ∧ t = sp.ts (sp.slot t) + sp.Δ) ∨ (∃ m, c = .message m) ∨
            ∃ B, c = .block B) ∧
          joined sp A t ∧ A.votedSlot ≠ sp.slot t ∧ t ≤ sp.ts (sp.slot t) + sp.Δ ∧
          ¬ (t < sp.ts (sp.slot t) + sp.Δ ∧
            (sp.slot t = 0 ∨ ¬ voteReady sp (callInputM sp wm A Φ t c) Φ (sp.slot t))) ∧
          callViewM sp wm A Φ t c = mergedVoteView sp (callInputM sp wm A Φ t c) Φ (sp.slot t) ∧
          tryVoteWithM sp wm self L (callInputM sp wm A Φ t c) Φ t = (A', es)) := by
    intro hk htv hV
    rcases tryVoteWithM_cases (wm := wm) (L := L) self (callInputM sp wm A Φ t c) Φ t with
      h | ⟨hj, hv, hlate, hready⟩
    · rw [htv] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact Or.inl ⟨rfl, Or.inl hkeep.1⟩
    · refine Or.inr ⟨hk, ?_, hkeep.1 ▸ hv, hlate, hready, hV, htv⟩
      unfold joined at hj ⊢
      rwa [← hkeep.2.1]
  cases c with
  | tick =>
    change acOnTickWithM sp wm self L A Φ t = (A', es) at hs
    unfold acOnTickWithM at hs
    dsimp only at hs
    have hΔ := sp.toParams.hΔ
    split_ifs at hs with hj h₂ h₁ h₁
    all_goals first
      | exact ofTry (Or.inl ⟨rfl, by assumption⟩) hs rfl
      | (obtain ⟨rfl, rfl⟩ := Prod.mk.inj hs; exact Or.inl ⟨rfl, Or.inl rfl⟩)
      | (obtain ⟨rfl, rfl⟩ := Prod.mk.inj hs
         exact Or.inl ⟨rfl, Or.inl (updateConfirmationM_keeps _ _ _ _ _).1⟩)
      | (exfalso; linarith [h₂.1, h₁])
  | proposal =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hs
    exact Or.inl ⟨rfl, Or.inl (acProposalWith_keeps L _ _ _).1⟩
  | toFG =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hs
    exact Or.inl ⟨rfl, Or.inl (acToFG_keeps _ _ _).1⟩
  | message v => exact ofTry (Or.inr (Or.inl ⟨v, rfl⟩)) hs rfl
  | block B => exact ofTry (Or.inr (Or.inr ⟨B, rfl⟩)) hs rfl
  | restart =>
    obtain ⟨he, -, -, -, -, hv, -⟩ := restart_state sp FGP ro self A Φ t hΦ ht
    change acRestart sp ro self A Φ t = (A', es) at hs
    rw [hs] at he hv
    exact Or.inl ⟨he, Or.inr hv⟩

/-- A call that reaches `try_vote`, joined, runs `try_vote` from its unlock input, whose merged
view its unlock reads. -/
private theorem exec_tryVote {u : Nat → Set Lock} (h : ACLocalRunU wm u H U tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksAC sp FGP ro)}
    (hc : tr.CallAt y j ℓ)
    (hk : (ℓ.call = .tick ∧ tr.time j = sp.ts (sp.slot (tr.time j)) + sp.Δ) ∨
      (∃ m, ℓ.call = .message m) ∨ ∃ B, ℓ.call = .block B)
    (hj : joined sp (tr.state y j) (tr.time j)) :
    tryVoteWithM sp wm y (u j) (callInputM sp wm (tr.state y j) ℓ.frame (tr.time j) ℓ.call)
        ℓ.frame (tr.time j) = (tr.post j, ℓ.emits) ∧
      callViewM sp wm (tr.state y j) ℓ.frame (tr.time j) ℓ.call =
        mergedVoteView sp (callInputM sp wm (tr.state y j) ℓ.frame (tr.time j) ℓ.call) ℓ.frame
          (sp.slot (tr.time j)) := by
  have hexec := h.exec j ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1] at hexec
  rcases hk with ⟨hcall, ht⟩ | ⟨m, hcall⟩ | ⟨B, hcall⟩
  · rw [hcall] at hexec ⊢
    refine ⟨?_, rfl⟩
    rw [← hexec]
    change _ = acOnTickWithM sp wm y (u j) (tr.state y j) ℓ.frame (tr.time j)
    have hΔ := sp.toParams.hΔ
    unfold acOnTickWithM
    dsimp only
    rw [ite_eq_right (not_not.2 hj), ite_eq_left ht,
      ite_eq_right (fun h' => by linarith [ht.symm.trans h'.1])]
  · rw [hcall] at hexec ⊢
    exact ⟨hexec, rfl⟩
  · rw [hcall] at hexec ⊢
    exact ⟨hexec, rfl⟩

/-- The guard of a vote branch passes at the call's unlock input (the branch reads it at the
read point, which has the input's pools). -/
private theorem voteBranchAt_ready_input {u : Nat → Set Lock} (h : ACLocalRunU wm u H U tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksAC sp FGP ro)}
    {R : ACState sp.n} (hb : VoteBranchAt tr y j ℓ R) :
    ¬ (tr.time j < sp.ts (sp.slot (tr.time j)) + sp.Δ ∧ (sp.slot (tr.time j) = 0 ∨
      ¬ voteReady sp (callInputM sp wm (tr.state y j) ℓ.frame (tr.time j) ℓ.call) ℓ.frame
        (sp.slot (tr.time j)))) := by
  obtain ⟨hc, hk, hj, -, -, hready, hR⟩ := voteBranchAt_iff.1 hb
  obtain ⟨htv, -⟩ := exec_tryVote h hy hc hk hj
  rcases tryVoteWithM_cases (wm := wm) (L := u j) y
      (callInputM sp wm (tr.state y j) ℓ.frame (tr.time j) ℓ.call) ℓ.frame (tr.time j) with
    h' | ⟨-, -, -, h'⟩
  · obtain ⟨hpost, hem⟩ := Prod.mk.inj (htv.symm.trans h')
    rcases hR with ⟨e, he, -⟩ | ⟨-, hpR⟩
    · rw [hem] at he
      exact absurd he List.not_mem_nil
    · rw [← hpR, hpost] at hready
      exact hready
  · exact h'

/-- A call that reaches `try_vote` and passes its guard, running `try_vote` from `P` (which keeps
the state's restart time and `voted_slot`), takes the vote branch, to the read point of
`tryVoteWithM_branch`, and leaves `voted_slot` at the slot of its time. -/
private theorem voteBranchAt_of_tryVote {y : Fin sp.n} {j : Nat}
    {ℓ : ACLabel (goldilocksAC sp FGP ro)} {L : Set Lock} {P : ACState sp.n}
    (hc : tr.CallAt y j ℓ)
    (hk : (ℓ.call = .tick ∧ tr.time j = sp.ts (sp.slot (tr.time j)) + sp.Δ) ∨
      (∃ m, ℓ.call = .message m) ∨ ∃ B, ℓ.call = .block B)
    (hPv : P.votedSlot = (tr.state y j).votedSlot)
    (hPr : P.restartTime = (tr.state y j).restartTime)
    (hj : joined sp (tr.state y j) (tr.time j))
    (hv : (tr.state y j).votedSlot ≠ sp.slot (tr.time j))
    (hlate : tr.time j ≤ sp.ts (sp.slot (tr.time j)) + sp.Δ)
    (hready : ¬ (tr.time j < sp.ts (sp.slot (tr.time j)) + sp.Δ ∧
      (sp.slot (tr.time j) = 0 ∨ ¬ voteReady sp P ℓ.frame (sp.slot (tr.time j)))))
    (htv : tryVoteWithM sp wm y L P ℓ.frame (tr.time j) = (tr.post j, ℓ.emits)) :
    VoteBranchAt tr y j ℓ { (if 0 < sp.slot (tr.time j) then { P with locks := L } else P) with
        votedSlot := (sp.slot (tr.time j) : Int) } ∧
      (tr.post j).votedSlot = sp.slot (tr.time j) := by
  have hjP : joined sp P (tr.time j) := by
    unfold joined at hj ⊢
    rwa [hPr]
  have hb := tryVoteWithM_branch (wm := wm) (L := L) y ℓ.frame hjP (by rw [hPv]; exact hv)
    hlate hready
  have hready' : ¬ (tr.time j < sp.ts (sp.slot (tr.time j)) + sp.Δ ∧
      (sp.slot (tr.time j) = 0 ∨ ¬ voteReady sp
        { (if 0 < sp.slot (tr.time j) then { P with locks := L } else P) with
          votedSlot := (sp.slot (tr.time j) : Int) } ℓ.frame (sp.slot (tr.time j)))) := by
    rwa [voteReady_congr_pool readPoint_pool_eq]
  cases hm : P.mayVote (sp.slot (tr.time j)) with
  | true =>
    obtain ⟨e, he, hR, -, -⟩ := hb.1 hm
    obtain ⟨hpost, hem⟩ := Prod.mk.inj (htv.symm.trans he)
    refine ⟨voteBranchAt_iff.2 ⟨hc, hk, hj, hv, hlate, hready', Or.inl ⟨e,
      by rw [hem]; exact List.mem_singleton_self _, hR⟩⟩, ?_⟩
    rw [hpost, (optimistic_keeps _ _ _).1, (admitVote_keeps _ _ _).1, hR]
  | false =>
    obtain ⟨hpost, hem⟩ := Prod.mk.inj (htv.symm.trans (hb.2 hm))
    exact ⟨voteBranchAt_iff.2 ⟨hc, hk, hj, hv, hlate, hready', Or.inr ⟨hem, hpost⟩⟩,
      by rw [hpost]⟩

/-! ## An honest vote branch -/

/-- **The vote branch of an honest call, characterised**: its unlock reads the merged view of
its unlock input `P`; its read point `R` is `P` with the locks `u j` when `s > 0` (and `P` itself
when `s = 0`) and `voted_slot ← s`; and the call is `try_vote` from `P`. -/
theorem voteBranchAt_inputU {u : Nat → Set Lock} (h : ACLocalRunU wm u H U tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksAC sp FGP ro)} {R : ACState sp.n}
    (hb : VoteBranchAt tr y j ℓ R) :
    callViewM sp wm (tr.state y j) ℓ.frame (tr.time j) ℓ.call =
        mergedVoteView sp (callInputM sp wm (tr.state y j) ℓ.frame (tr.time j) ℓ.call) ℓ.frame
          (sp.slot (tr.time j)) ∧
      R = { (if 0 < sp.slot (tr.time j) then
          { callInputM sp wm (tr.state y j) ℓ.frame (tr.time j) ℓ.call with locks := u j }
          else callInputM sp wm (tr.state y j) ℓ.frame (tr.time j) ℓ.call) with
        votedSlot := (sp.slot (tr.time j) : Int) } ∧
      tryVoteWithM sp wm y (u j) (callInputM sp wm (tr.state y j) ℓ.frame (tr.time j) ℓ.call)
        ℓ.frame (tr.time j) = (tr.post j, ℓ.emits) := by
  have hready := voteBranchAt_ready_input h hy hb
  obtain ⟨hc, hk, hj, hv, hlate, -, hb⟩ := voteBranchAt_iff.1 hb
  obtain ⟨htv, hV⟩ := exec_tryVote h hy hc hk hj
  refine ⟨hV, ?_, htv⟩
  have hkeep := callInputM_keeps (wm := wm) (tr.state y j) ℓ.frame (tr.time j) ℓ.call
  have hjP : joined sp (callInputM sp wm (tr.state y j) ℓ.frame (tr.time j) ℓ.call)
      (tr.time j) := by
    unfold joined at hj ⊢
    rwa [hkeep.2.1]
  have hbr := tryVoteWithM_branch (wm := wm) (L := u j) y ℓ.frame hjP
    (by rw [hkeep.1]; exact hv) hlate hready
  cases hm : (callInputM sp wm (tr.state y j) ℓ.frame (tr.time j) ℓ.call).mayVote
      (sp.slot (tr.time j)) with
  | true =>
    obtain ⟨e₀, he₀, hR₀, -, -⟩ := hbr.1 hm
    obtain ⟨-, hem⟩ := Prod.mk.inj (htv.symm.trans he₀)
    rcases hb with ⟨e, he, rfl⟩ | ⟨hn, -⟩
    · rw [hem, List.mem_singleton] at he
      rw [he, hR₀]
    · rw [hn] at hem
      exact absurd hem (by simp)
  | false =>
    obtain ⟨hpost, hem⟩ := Prod.mk.inj (htv.symm.trans (hbr.2 hm))
    rcases hb with ⟨e, he, -⟩ | ⟨-, hpost'⟩
    · rw [hem] at he
      exact absurd he List.not_mem_nil
    · exact hpost'.symm.trans hpost

/-- `voteBranchAt_inputU` on the parent's runs: the vote branch is the parent's `try_vote` from
the call's unlock input `P`, and its read point holds `P`'s locks unlocked against `P`'s merged
view when `s > 0` (`P`'s locks when `s = 0`). -/
theorem voteBranchAt_input (h : ACLocalRun (goldilocksAC sp FGP ro) H U tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksAC sp FGP ro)} {R : ACState sp.n}
    (hb : VoteBranchAt tr y j ℓ R) :
    R = { (if 0 < sp.slot (tr.time j) then
        { callInput sp (tr.state y j) ℓ.frame (tr.time j) ℓ.call with
          locks := unlock sp (callInput sp (tr.state y j) ℓ.frame (tr.time j) ℓ.call).locks
            ℓ.frame (tr.time j) ((sp.slot (tr.time j) : Int) - 1)
            (mergedVoteView sp (callInput sp (tr.state y j) ℓ.frame (tr.time j) ℓ.call) ℓ.frame
              (sp.slot (tr.time j))) }
        else callInput sp (tr.state y j) ℓ.frame (tr.time j) ℓ.call) with
      votedSlot := (sp.slot (tr.time j) : Int) } ∧
    tryVote sp y (callInput sp (tr.state y j) ℓ.frame (tr.time j) ℓ.call) ℓ.frame (tr.time j) =
      (tr.post j, ℓ.emits) := by
  obtain ⟨hV, hR, htv⟩ := voteBranchAt_inputU h.toU hy hb
  have hc := hb.callAt
  have hu : parentOracle sp tr j = unlock sp
      (callInput sp (tr.state y j) ℓ.frame (tr.time j) ℓ.call).locks ℓ.frame (tr.time j)
      ((sp.slot (tr.time j) : Int) - 1)
      (mergedVoteView sp (callInput sp (tr.state y j) ℓ.frame (tr.time j) ℓ.call) ℓ.frame
        (sp.slot (tr.time j))) := by
    simp only [parentOracle, hc.2, hc.1]
    exact congrArg _ hV
  rw [hu] at hR htv
  exact ⟨hR, by rw [tryVote_eq_tryVoteWith]; exact htv⟩

/-- **The read point of a vote branch**: `voted_slot` is the slot of the call's time, the node is
joined there, and the call is by the slot's vote deadline `t_s + Δ`. -/
theorem voteBranchAt_specU {u : Nat → Set Lock} (h : ACLocalRunU wm u H U tr ini) {y : Fin sp.n}
    (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksAC sp FGP ro)} {R : ACState sp.n}
    (hb : VoteBranchAt tr y j ℓ R) :
    R.votedSlot = sp.slot (tr.time j) ∧ joined sp R (tr.time j) ∧
      tr.time j ≤ sp.ts (sp.slot (tr.time j)) + sp.Δ := by
  obtain ⟨-, -, hj, -, hlate, -⟩ := voteBranchAt_iff.1 hb
  obtain ⟨-, rfl, -⟩ := voteBranchAt_inputU h hy hb
  have hkeep := callInputM_keeps (wm := wm) (tr.state y j) ℓ.frame (tr.time j) ℓ.call
  refine ⟨rfl, ?_, hlate⟩
  unfold joined at hj ⊢
  rw [← hkeep.2.1] at hj
  split_ifs <;> exact hj

/-- **The state a vote branch leaves**: a node that may not vote in the slot emits nothing and
leaves the read point `R` (no emission, no admission of an own vote); one that may emits its own
vote of the slot, read at `R`, and leaves that vote's receipt (the optimistic check at the writes
of `wm`). -/
theorem post_of_voteBranchAtU {u : Nat → Set Lock} (h : ACLocalRunU wm u H U tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksAC sp FGP ro)}
    {R : ACState sp.n} (hb : VoteBranchAt tr y j ℓ R) :
    ((tr.state y j).mayVote (sp.slot (tr.time j)) = false ∧ ℓ.emits = [] ∧ tr.post j = R) ∨
      ((tr.state y j).mayVote (sp.slot (tr.time j)) = true ∧ ∃ e, ℓ.emits = [e] ∧
        e.readPoint = R ∧ e.msg.val = y ∧ e.msg.slot = sp.slot (tr.time j) ∧
        tr.post j = optimisticConfirmation sp (admitVote sp R (tr.time j) e.msg) ℓ.frame
          (tr.time j)) := by
  have hready := voteBranchAt_ready_input h hy hb
  obtain ⟨-, -, hj, hv, hlate, -, -⟩ := voteBranchAt_iff.1 hb
  obtain ⟨-, rfl, htv⟩ := voteBranchAt_inputU h hy hb
  have hkeep := callInputM_keeps (wm := wm) (tr.state y j) ℓ.frame (tr.time j) ℓ.call
  have hjP : joined sp (callInputM sp wm (tr.state y j) ℓ.frame (tr.time j) ℓ.call)
      (tr.time j) := by
    unfold joined at hj ⊢
    rwa [hkeep.2.1]
  have hbr := tryVoteWithM_branch (wm := wm) (L := u j) y ℓ.frame hjP
    (by rw [hkeep.1]; exact hv) hlate hready
  rw [← hkeep.2.2]
  cases hm : (callInputM sp wm (tr.state y j) ℓ.frame (tr.time j) ℓ.call).mayVote
      (sp.slot (tr.time j)) with
  | true =>
    obtain ⟨e, he, hR, hval, hsl⟩ := hbr.1 hm
    obtain ⟨hpost, hem⟩ := Prod.mk.inj (htv.symm.trans he)
    exact Or.inr ⟨rfl, e, hem, hR, hval, hsl, by rw [hpost, hR]⟩
  | false =>
    obtain ⟨hpost, hem⟩ := Prod.mk.inj (htv.symm.trans (hbr.2 hm))
    exact Or.inl ⟨rfl, hem, hpost⟩

/-- **A cast is a vote branch**, read at the emission's read point, with the unlock given. -/
theorem voteBranchAt_of_castAtU {u : Nat → Set Lock} (h : ACLocalRunU wm u H U tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksAC sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y j ℓ e) : VoteBranchAt tr y j ℓ e.readPoint := by
  have hexec := h.exec j ℓ hc.1.2 (hc.1.1 ▸ hy)
  rw [hc.1.1] at hexec
  have hΦ : FrameOK ℓ.frame := by
    rcases h.frameLaw y hy j ℓ hc.1 with ⟨-, _, -, -, hok⟩ | ⟨_, _, -, -, -, hok⟩ <;>
      exact hok.1.1
  rcases stepWithM_voteBranch y hΦ (h.time_nonneg j) ℓ.call hexec with
    ⟨hn, -⟩ | ⟨hk, hj, hv, hlate, hready, -, htv⟩
  · exact absurd (hn ▸ hc.2) List.not_mem_nil
  have hkeep := callInputM_keeps (wm := wm) (tr.state y j) ℓ.frame (tr.time j) ℓ.call
  have hb := (voteBranchAt_of_tryVote hc.1 hk hkeep.1 hkeep.2.1 hj hv hlate hready htv).1
  rcases post_of_voteBranchAtU h hy hb with ⟨-, hn, -⟩ | ⟨-, e', he', hR, -⟩
  · exact absurd (hn ▸ hc.2) List.not_mem_nil
  · have he := hc.2
    rw [he', List.mem_singleton] at he
    rw [he, hR]
    exact hb

/-- **A cast is a vote branch**, read at the emission's read point. -/
theorem voteBranchAt_of_castAt (h : ACLocalRun (goldilocksAC sp FGP ro) H U tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksAC sp FGP ro)}
    {e : Em sp FGP} (hc : CastAt tr y j ℓ e) : VoteBranchAt tr y j ℓ e.readPoint :=
  voteBranchAt_of_castAtU h.toU hy hc

/-- **A vote branch of a node that may vote in the slot is a cast**, read at the branch's read
point, of the node's own vote of the slot. -/
theorem castAt_of_voteBranchAtU {u : Nat → Set Lock} (h : ACLocalRunU wm u H U tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksAC sp FGP ro)}
    {R : ACState sp.n} (hb : VoteBranchAt tr y j ℓ R)
    (hm : (tr.state y j).mayVote (sp.slot (tr.time j)) = true) :
    ∃ e, CastAt tr y j ℓ e ∧ e.readPoint = R ∧ e.msg.val = y ∧
      e.msg.slot = sp.slot (tr.time j) := by
  rcases post_of_voteBranchAtU h hy hb with ⟨hm', -⟩ | ⟨-, e, he, hR, hval, hsl, -⟩
  · rw [hm] at hm'
    exact absurd hm' Bool.true_eq_false.mp
  · exact ⟨e, ⟨hb.callAt, by rw [he]; exact List.mem_singleton_self _⟩, hR, hval, hsl⟩

/-! ## Where vote branches come from -/

/-- **A tick at the vote deadline takes the vote branch**: an honest node's tick at `t_s + Δ`,
joined and with `voted_slot ≠ s`, takes the vote branch of slot `s`, whether or not it may vote
in `s`. -/
theorem voteBranchAt_of_tickU {u : Nat → Set Lock} (h : ACLocalRunU wm u H U tr ini)
    {y : Fin sp.n} (hy : y ∈ H) {j : Nat} {ℓ : ACLabel (goldilocksAC sp FGP ro)}
    (hc : tr.CallAt y j ℓ) (hcall : ℓ.call = .tick)
    (ht : tr.time j = sp.ts (sp.slot (tr.time j)) + sp.Δ)
    (hj : joined sp (tr.state y j) (tr.time j))
    (hv : (tr.state y j).votedSlot ≠ sp.slot (tr.time j)) :
    ∃ R, VoteBranchAt tr y j ℓ R := by
  have hk : (ℓ.call = .tick ∧ tr.time j = sp.ts (sp.slot (tr.time j)) + sp.Δ) ∨
      (∃ m, ℓ.call = .message m) ∨ ∃ B, ℓ.call = .block B := Or.inl ⟨hcall, ht⟩
  obtain ⟨htv, -⟩ := exec_tryVote h hy hc hk hj
  have hkeep := callInputM_keeps (wm := wm) (tr.state y j) ℓ.frame (tr.time j) ℓ.call
  exact ⟨_, (voteBranchAt_of_tryVote hc hk hkeep.1 hkeep.2.1 hj hv ht.le
    (fun h' => absurd ht (ne_of_lt h'.1)) htv).1⟩

/-- **`voted_slot` names a vote branch.** When an honest node's state before cut `i` has
`voted_slot = σ ≥ 0`, the node took the vote branch of slot `σ` at an earlier cut. From starts up
to the vote permission. -/
theorem voteBranchAt_of_votedSlotU {u : Nat → Set Lock} (h : ACLocalRunU wm u H U tr ini)
    (hini : ∀ y, VoteStart sp.genesisRoot (ini y)) {y : Fin sp.n}
    (hy : y ∈ H) (i σ : Nat) (hv : (tr.state y i).votedSlot = σ) :
    ∃ j < i, ∃ ℓ R, VoteBranchAt tr y j ℓ R ∧ sp.slot (tr.time j) = σ := by
  induction i with
  | zero =>
    exfalso
    change (tr.init y).votedSlot = σ at hv
    obtain ⟨m, hm⟩ := voteStart_iff.1 (hini y)
    rw [h.init y hy, hm] at hv
    change (-1 : Int) = σ at hv
    omega
  | succ i ih =>
    by_cases hc : ∃ ℓ, tr.CallAt y i ℓ
    · obtain ⟨ℓ, hc⟩ := hc
      rw [show tr.state y (i + 1) = tr.post i by simp [Trace.state, hc.1, hc.2]] at hv
      have hexec := h.exec i ℓ hc.2 (hc.1 ▸ hy)
      rw [hc.1] at hexec
      have hΦ : FrameOK ℓ.frame := by
        rcases h.frameLaw y hy i ℓ hc with ⟨-, _, -, -, hok⟩ | ⟨_, _, -, -, -, hok⟩ <;>
          exact hok.1.1
      rcases stepWithM_voteBranch y hΦ (h.time_nonneg i) ℓ.call hexec with
        ⟨-, hvs | hvs⟩ | ⟨hk, hj, hv', hlate, hready, -, htv⟩
      · obtain ⟨j, hj, h'⟩ := ih (hvs.symm.trans hv)
        exact ⟨j, by omega, h'⟩
      · omega
      · have hkeep := callInputM_keeps (wm := wm) (tr.state y i) ℓ.frame (tr.time i) ℓ.call
        obtain ⟨hb, hpost⟩ := voteBranchAt_of_tryVote hc hk hkeep.1 hkeep.2.1 hj hv' hlate
          hready htv
        exact ⟨i, by omega, ℓ, _, hb, by omega⟩
    · have hst : tr.state y (i + 1) = tr.state y i := by
        rw [Trace.state]
        split_ifs with h'
        · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 h'.2
          exact absurd ⟨ℓ, h'.1, hℓ⟩ hc
        · rfl
      rw [hst] at hv
      obtain ⟨j, hj, h'⟩ := ih hv
      exact ⟨j, by omega, h'⟩

end Consensus.Goldilocks.AC

end
