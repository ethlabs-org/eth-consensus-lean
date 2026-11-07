module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.Retention.Prefix

public section

/-! # Pool changes within the signer's slot-start tick

These transition facts have no run or honesty assumptions.
-/

namespace Consensus.Goldilocks.Healing.Growing.KernelProof

variable {FGP : Type} {sp : SA.SAParams} {ro : SA.ReplayOrder sp FGP}

theorem admit_pool_mem {A : SA.SAState sp.n} {t : Time} {m w : SA.Vote sp.n} {s : Nat}
    (h : w ∈ (SA.admitVote sp A t m).pool s) : w ∈ A.pool s ∨ w = m := by
  unfold SA.admitVote at h
  split_ifs at h
  · exact Or.inl h
  · exact Or.inl h
  · simp only [Function.update_apply] at h
    split_ifs at h with hs
    · subst hs
      rcases List.mem_append.1 h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_singleton.1 h)
    · exact Or.inl h

theorem receipt_pool_mem {A : SA.SAState sp.n} {t : Time} {B : SA.Blk sp.n FGP}
    {w : SA.Vote sp.n} {s : Nat} (h : w ∈ (SA.blockReceipt sp A t B).pool s) :
    w ∈ A.pool s ∨ w ∈ SA.blockVotes B := by
  have key : ∀ (l : List (SA.Vote sp.n)) (A₀ : SA.SAState sp.n),
      w ∈ (l.foldl (fun A v => SA.admitVote sp A t v) A₀).pool s → w ∈ A₀.pool s ∨ w ∈ l := by
    intro l
    induction l with
    | nil => exact fun _ h => Or.inl h
    | cons x l ih =>
      intro A₀ h
      rcases ih _ h with h | h
      · rcases admit_pool_mem h with h | rfl
        · exact Or.inl h
        · exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem _ h)
  unfold SA.blockReceipt at h
  have h' := key _ _ h
  exact h'

private theorem tryVote_pool_mem (self : Fin sp.n) (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP)
    (t : Time) {w : SA.Vote sp.n} {s : Nat} (h : w ∈ (SA.tryVote sp self A Φ t).1.pool s) :
    w ∈ A.pool s ∨ w.val = self := by
  unfold SA.tryVote at h
  dsimp only at h
  split_ifs at h
  all_goals first
    | exact Or.inl h
    | (rw [SA.optimistic_pool] at h
       rcases admit_pool_mem h with h | rfl
       · exact Or.inl h
       · exact Or.inr rfl)

/-- At a slot start, a nondelivery call takes only own votes or votes from its input block. -/
theorem step_pool_new (self : Fin sp.n) (A : SA.SAState sp.n) (Φ : SA.Frm sp.n FGP)
    {t : Time} (ht : t = sp.ts (sp.slot t)) (hΔ : 0 < sp.Δ) (c : (SA.goldilocksSA sp FGP ro).Call)
    (hm : ∀ m, c ≠ .message m) (hc : c ≠ .restart) {w : SA.Vote sp.n} {s : Nat}
    (h : w ∈ ((SA.goldilocksSA sp FGP ro).step self A Φ t c).1.pool s) :
    w ∈ A.pool s ∨ w.val = self ∨ ∃ B, c = .block B ∧ w ∈ SA.blockVotes B := by
  cases c with
  | tick =>
    change w ∈ (SA.acOnTick sp self A Φ t).1.pool s at h
    unfold SA.acOnTick at h
    dsimp only at h
    split_ifs at h <;> first
      | exact Or.inl h
      | (exfalso; linarith)
  | proposal =>
    change w ∈ (SA.acProposal sp A Φ t).1.pool s at h
    unfold SA.acProposal at h
    dsimp only at h
    split_ifs at h <;> exact Or.inl h
  | toFG =>
    change w ∈ (SA.acToFG sp A Φ t).1.pool s at h
    unfold SA.acToFG at h
    split_ifs at h <;> (try split at h) <;> (try split_ifs at h) <;> exact Or.inl h
  | message m => exact absurd rfl (hm m)
  | block B =>
    change w ∈ (SA.tryVote sp self (SA.optimisticConfirmation sp (SA.blockReceipt sp A t B) Φ t)
      Φ t).1.pool s at h
    rcases tryVote_pool_mem _ _ _ _ h with h | h
    · rw [SA.optimistic_pool] at h
      rcases receipt_pool_mem h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨B, rfl, h⟩)
    · exact Or.inr (Or.inl h)
  | restart => exact absurd rfl hc

end Consensus.Goldilocks.Healing.Growing.KernelProof

end
