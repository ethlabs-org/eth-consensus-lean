module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks SA: where a saved result comes from

`saved[j]` is written only by the update of slot `j` (`update_confirmation`, at `t_j + 6Δ`, from
a joined state), with the root of its result, and a restart clears it: a saved root at an honest
node is the root of the result of that node's update of slot `j` at an earlier cut
(`saved_result`). -/

namespace Consensus.Goldilocks.SA

variable {FGP : Type} {sp : SAParams} {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)}
  {U : Set (Blk sp.n FGP)} {tr : SATrace sp FGP ro}

private theorem sv_admitVote (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).saved = A.saved := by
  unfold admitVote; split_ifs <;> rfl

private theorem sv_optimistic (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).saved = A.saved := by
  unfold optimisticConfirmation updateLatestConfirmed; split
  · rfl
  · split_ifs <;> rfl

private theorem sv_tryVote
    {L : Set Lock} (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (tryVoteWith sp x L A Φ t).1.saved = A.saved := by
  unfold tryVoteWith; dsimp only
  split_ifs <;> simp only [sv_optimistic, sv_admitVote]

private theorem sv_blockReceipt (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).saved = A.saved := by
  unfold blockReceipt
  generalize blockVotes B = l
  suffices h : ∀ A' : SAState sp.n,
      (l.foldl (fun A v => admitVote sp A t v) A').saved = A'.saved from h _
  induction l with
  | nil => exact fun _ => rfl
  | cons v l ih => intro A'; simp only [List.foldl_cons]; rw [ih, sv_admitVote]

/-- `update_confirmation` of slot `s` writes `saved[s]` with the root of its result and keeps
the other saved results. -/
private theorem sv_update (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) :
    (updateConfirmation sp A Φ t s).saved =
      Function.update A.saved s ((getConfirmation sp A Φ s).map Block.root) := by
  unfold updateConfirmation updateLatestConfirmed; dsimp only
  split
  · rfl
  · split_ifs <;> rfl

/-- One call keeps the saved results, or is a joined tick at `t_{σ} + 6Δ` that writes
`saved[σ]` with its update's result, or is a restart, which clears them. -/
private theorem sv_step
    {L : Set Lock} (self : Fin sp.n) (A : SAState sp.n) {Φ : Frm sp.n FGP} {t : Time}
    (hΦ : FrameOK Φ) (ht : 0 ≤ t) (c : (goldilocksSA sp FGP ro).Call) :
    let A' := (stepWith sp ro self L A Φ t c).1
    A'.saved = A.saved ∨ (c = .restart ∧ ∀ j, A'.saved j = none) ∨
      ∃ σ : Nat, c = .tick ∧ t = sp.ts σ + 6 * sp.Δ ∧ joined sp A t ∧
        A'.saved = Function.update A.saved σ ((getConfirmation sp A Φ σ).map Block.root) := by
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  cases c with
  | tick =>
    change (acOnTickWith sp self L A Φ t).1.saved = _ ∨
      (_ ∧ ∀ j, (acOnTickWith sp self L A Φ t).1.saved j = _) ∨
      ∃ σ : Nat, _ ∧ _ ∧ _ ∧ (acOnTickWith sp self L A Φ t).1.saved = _
    unfold acOnTickWith; dsimp only
    by_cases hj : joined sp A t
    swap
    · have hc : (¬ joined sp A t) = True := eq_true hj
      simp only [hc, ↓reduceIte, true_or]
    have hc : (¬ joined sp A t) = False := eq_false (not_not.2 hj)
    simp only [hc, ↓reduceIte]
    by_cases hu : t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t
    · have hv : ¬ t = sp.ts (sp.slot t) + sp.Δ := fun h => by linarith [hu.1.symm.trans h]
      have hc₁ : (t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t) = True := eq_true hu
      have hc₂ : (t = sp.ts (sp.slot t) + sp.Δ) = False := eq_false hv
      simp only [hc₁, hc₂, ↓reduceIte]
      refine Or.inr (Or.inr ⟨sp.slot t - 1, trivial, ?_, hj, sv_update _ _ _ _⟩)
      have hs1 : ((sp.slot t - 1 : Nat) : Int) = (sp.slot t : Int) - 1 := by omega
      have e := hu.1
      simp only [SAParams.ts] at e ⊢
      rw [hs1]
      linarith
    · have hc₁ : (t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t) = False := eq_false hu
      simp only [hc₁, ↓reduceIte]
      left
      split_ifs
      · exact sv_tryVote _ _ _ _
      · rfl
  | proposal =>
    left
    change (acProposalWith sp L A Φ t).1.saved = _
    unfold acProposalWith; split_ifs <;> rfl
  | toFG =>
    left
    change (acToFG sp A Φ t).1.saved = _
    unfold acToFG
    split_ifs
    all_goals first | rfl | (split <;> (try split_ifs) <;> rfl)
  | message m =>
    left
    change (tryVoteWith sp self L _ Φ t).1.saved = _
    rw [sv_tryVote, sv_optimistic, sv_admitVote]
  | block B =>
    left
    change (tryVoteWith sp self L _ Φ t).1.saved = _
    rw [sv_tryVote, sv_optimistic, sv_blockReceipt]
  | restart =>
    refine Or.inr (Or.inl ⟨rfl, fun j => ?_⟩)
    change (acRestart sp ro self A Φ t).1.saved j = none
    rw [((restart_state sp) FGP ro self A Φ t hΦ ht).2.2.2.1]
    rfl

/-- `saved_result` with the unlock given. -/
theorem saved_resultU
    {u : Nat → Set Lock} (hr : ACLocalRunU u H U tr) {x : Fin sp.n}
    (hx : x ∈ H) (i j : Nat) {r : Nat} (h : (tr.state x i).saved j = some r) :
    ∃ k < i, ∃ C CV, ResultAt tr x k j C CV ∧ C.root = r := by
  induction i with
  | zero =>
    change (tr.init x).saved j = some r at h
    rw [hr.init x hx] at h
    cases h
  | succ i ih =>
    by_cases hn : tr.node i = x ∧ tr.label i ≠ none
    · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 hn.2
      have hc : tr.CallAt x i ℓ := ⟨hn.1, hℓ⟩
      have hst : tr.state x (i + 1) = tr.post i := by
        simp only [Trace.state]; exact ite_eq_left hn
      have he := hr.exec i ℓ hℓ (hn.1 ▸ hx)
      rw [hn.1] at he
      have hpost : tr.post i =
          (stepWith sp ro x (u i) (tr.state x i) ℓ.frame (tr.time i) ℓ.call).1 := by
        rw [he]
      rw [hst, hpost] at h
      rcases sv_step (L := u i) (ro := ro) x (tr.state x i) (frameIn_of_callAtU hr hx hc).1
          (hr.time_nonneg i) ℓ.call with hs | hs | ⟨σ, hcall, ht, hj, hs⟩
      · obtain ⟨k, hk, hk'⟩ := ih (hs ▸ h)
        exact ⟨k, hk.trans (Nat.lt_succ_self i), hk'⟩
      · rw [hs.2 j] at h; cases h
      · rw [hs] at h
        by_cases hjσ : j = σ
        · subst hjσ
          rw [Function.update_self] at h
          obtain ⟨C, hC, rfl⟩ := Option.map_eq_some_iff.1 h
          exact ⟨i, Nat.lt_succ_self i, C, _, ⟨ℓ, ⟨hc, hcall, ht, hj⟩, hC, rfl⟩, rfl⟩
        · rw [Function.update_of_ne (by exact_mod_cast hjσ)] at h
          obtain ⟨k, hk, hk'⟩ := ih h
          exact ⟨k, hk.trans (Nat.lt_succ_self i), hk'⟩
    · have hst : tr.state x (i + 1) = tr.state x i := by
        simp only [Trace.state]; exact ite_eq_right hn
      rw [hst] at h
      obtain ⟨k, hk, hk'⟩ := ih h
      exact ⟨k, hk.trans (Nat.lt_succ_self i), hk'⟩

/-- **A saved result comes from the node's update.** When the state of an honest node before
cut `i` has `saved[j] = r`, the node's update of slot `j` at an earlier cut had a result with
root `r`. -/
theorem saved_result (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) (i j : Nat) {r : Nat} (h : (tr.state x i).saved j = some r) :
    ∃ k < i, ∃ C CV, ResultAt tr x k j C CV ∧ C.root = r :=
  saved_resultU (hr := hr.toU) (x := x) (hx := hx) (i := i) (j := j) (r := r) (h := h)

/-- The state after a call of an honest node. -/
private theorem post_step (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    tr.state x (i + 1) =
      ((goldilocksSA sp FGP ro).step x (tr.state x i) ℓ.frame (tr.time i) ℓ.call).1 := by
  have hst : tr.state x (i + 1) = tr.post i := by
    simp only [Trace.state]; exact ite_eq_left ⟨hc.1, by rw [hc.2]; exact Option.some_ne_none _⟩
  have he := hr.exec i ℓ hc.2 (hc.1 ▸ hx)
  rw [hc.1] at he
  rw [hst, he]

/-- **The state after an update** of slot `j` at cut `i` is `update_confirmation` of slot `j` on
the state before it. -/
theorem state_after_update (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hu : UpdateAt tr x i j ℓ) :
    tr.state x (i + 1) = updateConfirmation sp (tr.state x i) ℓ.frame (tr.time i) j := by
  obtain ⟨hc, hcall, ht, hj⟩ := hu
  have hΔ : (0 : Int) < sp.Δ := sp.toParams.hΔ
  have h6 : tr.time i = sp.ts ((j + 1 : Nat) : Int) + 2 * sp.Δ := by
    rw [ht]; simp only [SAParams.ts]; push_cast; ring
  have hsl : sp.slot (tr.time i) = j + 1 := slot_of_mem sp (j + 1) (by rw [h6]; linarith)
    (by rw [h6]; simp only [SAParams.ts]; push_cast; linarith)
  have hne : ¬ tr.time i = sp.ts ((j + 1 : Nat) : Int) + sp.Δ := by rw [h6]; intro h; linarith
  rw [post_step hr hx hc, hcall]
  change (acOnTick sp x (tr.state x i) ℓ.frame (tr.time i)).1 = _
  unfold acOnTick
  rw [ite_eq_right (not_not.2 hj)]
  simp only [hsl]
  rw [ite_eq_right hne, ite_eq_left ⟨h6, Nat.succ_pos j⟩, Nat.add_sub_cancel]

/-- **The update writes its slot's saved result.** After the update of slot `j` at cut `i`,
`saved[j]` is the root of its result, the other saved results unchanged. -/
theorem saved_after_update (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr) {x : Fin sp.n}
    (hx : x ∈ H) {i j : Nat} {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hu : UpdateAt tr x i j ℓ) :
    (tr.state x (i + 1)).saved =
      Function.update (tr.state x i).saved j
        ((getConfirmation sp (tr.state x i) ℓ.frame j).map Block.root) := by
  rw [state_after_update hr hx hu, sv_update]

/-- **Without a restart, `saved[j]` changes only at an update of slot `j`.** -/
theorem saved_step_of_not_restart (hr : ACLocalRun (goldilocksSA sp FGP ro) H U tr)
    {x : Fin sp.n} (hx : x ∈ H) (i j : Nat) (hnr : ¬ tr.RestartAt x i) :
    (tr.state x (i + 1)).saved j = (tr.state x i).saved j ∨
      ∃ ℓ, UpdateAt tr x i j ℓ ∧ (tr.state x (i + 1)).saved j =
        (getConfirmation sp (tr.state x i) ℓ.frame j).map Block.root := by
  by_cases hn : tr.node i = x ∧ tr.label i ≠ none
  · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 hn.2
    have hc : tr.CallAt x i ℓ := ⟨hn.1, hℓ⟩
    rw [post_step hr hx hc, step_eq_stepWith]
    rcases sv_step (ro := ro) x (tr.state x i) (frameIn_of_callAt hr hx hc).1
        (hr.time_nonneg i) ℓ.call with hs | ⟨hcr, -⟩ | ⟨σ, hcall, ht, hj, hs⟩
    · exact Or.inl (congrFun hs j)
    · exact absurd ⟨ℓ, hc, hcr⟩ hnr
    · rw [hs]
      by_cases hjσ : j = σ
      · subst hjσ
        exact Or.inr ⟨ℓ, ⟨hc, hcall, ht, hj⟩, Function.update_self ..⟩
      · exact Or.inl (Function.update_of_ne (by exact_mod_cast hjσ) _ _)
  · left
    have hst : tr.state x (i + 1) = tr.state x i := by
      simp only [Trace.state]; exact ite_eq_right hn
    rw [hst]

end Consensus.Goldilocks.SA

end
