module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.TimeShiftedReceipt
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts

public section

namespace Consensus.Goldilocks.SA.TimeShifted

variable {sp : SAParams} {FGP : Type}

private theorem admitted {A : SAState sp.n} {t : Time} {m v : Vote sp.n} {s : Nat}
    (h : v ∈ (admitVote sp A t m).pool s) : v ∈ A.pool s ∨ v = m ∧ m.slot = s := by
  unfold admitVote at h
  split_ifs at h <;> try exact Or.inl h
  simp only [Function.update_apply] at h
  split_ifs at h with eq
  · subst eq
    exact (List.mem_append.mp h).imp_right fun e => ⟨List.mem_singleton.mp e, rfl⟩
  · exact Or.inl h

private theorem attempt_source (y : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    {s : Nat} {v : Vote sp.n} (h : v ∈ (tryVote sp y A Φ t).1.pool s) :
    v ∈ A.pool s ∨ ∃ e ∈ (tryVote sp y A Φ t).2, e.msg = v ∧ v.slot = s ∧ v.val = y := by
  unfold tryVote at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ <;> try exact Or.inl h
  all_goals rw [optimistic_pool_eq] at h
  all_goals rcases admitted h with old | ⟨rfl, hs⟩
  all_goals first | exact Or.inl old | exact Or.inr ⟨_, List.mem_singleton_self _, rfl, hs, rfl⟩

private theorem step_source (y : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (c : (instanceAC sp FGP).Call) {s : Nat} {v : Vote sp.n}
    (h : v ∈ ((instanceAC sp FGP).step y A Φ t c).1.pool s) :
    v ∈ A.pool s ∨ c = .message v ∧ v.slot = s ∨
      ∃ e ∈ ((instanceAC sp FGP).step y A Φ t c).2, e.msg = v ∧ v.slot = s ∧ v.val = y := by
  cases c with
  | restart => exact (List.not_mem_nil h).elim
  | proposal =>
    left
    change v ∈ (acProposal sp A Φ t).1.pool s at h
    unfold acProposal at h; split_ifs at h <;> exact h
  | toFG =>
    left
    change v ∈ (acToFG sp A Φ t).1.pool s at h
    unfold acToFG at h
    split_ifs at h <;> first | exact h | split at h <;> first | exact h | split_ifs at h <;> exact h
  | message m =>
    rcases attempt_source _ _ _ _ h with prev | own
    · rw [optimistic_pool_eq] at prev
      exact (admitted prev).imp_right fun ⟨eq, hs⟩ => Or.inl ⟨eq ▸ rfl, eq ▸ hs⟩
    · exact Or.inr (Or.inr own)
  | block B =>
    rcases attempt_source _ _ _ _ h with prev | own
    · rw [optimistic_pool_eq] at prev; exact Or.inl prev
    · exact Or.inr (Or.inr own)
  | tick =>
    simp only [ACInterface.step, instanceAC, Id.run, pure] at h ⊢
    split_ifs at h ⊢ <;> dsimp only at h ⊢ <;> try rw [updateConfirmation_pool_eq] at h
    all_goals first | exact Or.inl h | exact (attempt_source _ _ _ _ h).imp_right Or.inr

variable {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : ACTrace (instanceAC sp FGP)}
  {ini : Fin sp.n → SAState sp.n}

/-- Under ordinary wire authentication, each honest signer's vote held in a TSQ pre-state
was emitted by that signer strictly earlier and in the stated slot's pool. No carried-vote
authentication or replay assumption: both are absent in the candidate handler. -/
theorem pool_source (hr : ACLocalRun (instanceAC sp FGP) H U tr ini)
    (start : ∀ y ∈ H, ∀ s, (ini y).pool s = [])
    (auth : ∀ y ∈ H, ∀ i l v, tr.CallAt y i l → l.call = .message v → v.val ∈ H →
      ∃ j < i, ∃ r, tr.CallAt v.val j r ∧ ∃ e ∈ r.emits, e.msg = v)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) {s : Nat} {v : Vote sp.n} (hv : v.val ∈ H)
    (held : v ∈ (tr.state y i).pool s) : v.slot = s ∧
      ∃ j < i, ∃ r, tr.CallAt v.val j r ∧ ∃ e ∈ r.emits, e.msg = v := by
  induction i with
  | zero => simp [Trace.state, hr.init y hy, start y hy] at held
  | succ i ih =>
    have older (h : v ∈ (tr.state y i).pool s) : v.slot = s ∧
        ∃ j < i+1, ∃ r, tr.CallAt v.val j r ∧ ∃ e ∈ r.emits, e.msg = v :=
      (ih h).imp_right fun ⟨j, hj, rest⟩ =>
      ⟨j, hj.trans (Nat.lt_succ_self _), rest⟩
    rw [Trace.state] at held
    split_ifs at held with call
    · obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.mp call.2
      have hc : tr.CallAt y i l := ⟨call.1, hl⟩
      have exec := hr.exec i l hl (call.1 ▸ hy)
      rw [call.1] at exec
      rw [← show _ = tr.post i from congrArg Prod.fst exec] at held
      rcases step_source _ _ _ _ _ held with prev | ⟨msg, hs⟩ | ⟨e, he, eq, hs, signer⟩
      · exact older prev
      · obtain ⟨j, hj, rest⟩ := auth y hy i l v hc msg hv
        exact ⟨hs, j, hj.trans (Nat.lt_succ_self _), rest⟩
      · exact ⟨hs, i, Nat.lt_succ_self _, l, signer ▸ hc, e, by simpa only [exec] using he, eq⟩
    · exact older held

end Consensus.Goldilocks.SA.TimeShifted

end
