module
public import ConsensusLean.Instances.Goldilocks.Spec.SA.TimeShifted
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.AC.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.PoolFacts

public section

namespace Consensus.Goldilocks.SA.TimeShifted

variable {sp : SAParams} {FGP : Type}

private theorem grows_attempt (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    Grows A (tryVote sp self A Φ t).1 := by
  unfold tryVote
  dsimp only
  split_ifs <;> try exact Grows.of_pool_eq rfl
  all_goals
    refine Grows.trans ?_ (Grows.of_pool_eq (optimistic_pool_eq _ _ _))
    refine Grows.trans ?_ (grows_admitVote _ _ _)
    exact Grows.of_pool_eq rfl

variable {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {tr : ACTrace (instanceAC sp FGP)}
  {ini : Fin sp.n → SAState sp.n} {y : Fin sp.n} {i : Nat} {ℓ : ACLabel (instanceAC sp FGP)}

private theorem attempt_cover (y : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (e : Em sp FGP) (he : e ∈ (tryVote sp y A Φ t).2) :
    let B := (tryVote sp y A Φ t).1
    e.msg ∈ B.pool e.msg.slot ∨ e.msg.val ∈ equivocators {w | w ∈ B.pool e.msg.slot} := by
  unfold tryVote at he ⊢
  dsimp only at he ⊢
  split_ifs at he ⊢ <;> simp only [List.not_mem_nil, List.mem_singleton] at he
  all_goals subst e
  all_goals rw [optimistic_pool_eq]; apply admitVote_held <;> simp

/-- Processing one's own emitted vote also establishes cover; `SyncAC` permits this case in
place of a message receipt. -/
theorem held_after_emit (hr : ACLocalRun (instanceAC sp FGP) H U tr ini) (hy : y ∈ H)
    (hc : tr.CallAt y i ℓ) {e : Em sp FGP} (he : e ∈ ℓ.emits) :
    e.msg ∈ (tr.post i).pool e.msg.slot ∨
      e.msg.val ∈ equivocators {w | w ∈ (tr.post i).pool e.msg.slot} := by
  have exec := hr.exec i ℓ hc.2 (hc.1 ▸ hy)
  rw [hc.1] at exec
  have post := congrArg Prod.fst exec
  have emits := congrArg Prod.snd exec
  dsimp only at post emits
  rw [← post]; rw [← emits] at he
  generalize ℓ.call = c at he ⊢
  cases c with
  | restart | proposal | toFG => exact (List.not_mem_nil he).elim
  | block B => exact attempt_cover _ _ _ _ _ he
  | message m => exact attempt_cover _ _ _ _ _ he
  | tick =>
    simp only [ACInterface.step, instanceAC, Id.run, pure] at he ⊢
    split_ifs at he ⊢ <;> try contradiction
    all_goals first | exact attempt_cover _ _ _ _ _ he |
      rw [updateConfirmation_pool_eq]; exact attempt_cover _ _ _ _ _ he

private theorem grows_step (y : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (c : (instanceAC sp FGP).Call) (hr : c ≠ .restart) :
    Grows A ((instanceAC sp FGP).step y A Φ t c).1 := by
  cases c with
  | restart => exact (hr rfl).elim
  | message v =>
    refine Grows.trans ?_ (grows_attempt _ _ _ _)
    exact (grows_admitVote _ _ _).trans (Grows.of_pool_eq (optimistic_pool_eq _ _ _))
  | block B =>
    refine Grows.trans ?_ (grows_attempt _ _ _ _)
    exact Grows.of_pool_eq (optimistic_pool_eq _ _ _)
  | proposal =>
    change Grows A (acProposal sp A Φ t).1
    unfold acProposal
    split_ifs <;> exact Grows.of_pool_eq rfl
  | toFG =>
    change Grows A (acToFG sp A Φ t).1
    unfold acToFG
    split_ifs <;> first | exact Grows.of_pool_eq rfl |
      split <;> first | exact Grows.of_pool_eq rfl | split_ifs <;> exact Grows.of_pool_eq rfl
  | tick =>
    simp only [ACInterface.step, instanceAC, Id.run, pure]
    split_ifs <;> first | exact Grows.of_pool_eq rfl | exact grows_attempt _ _ _ _ |
      exact Grows.of_pool_eq (updateConfirmation_pool_eq _ _ _ _) |
      exact (grows_attempt _ _ _ _).trans (Grows.of_pool_eq (updateConfirmation_pool_eq _ _ _ _))

/-- At an actual honest message cut in the admission window, even an immediate cast leaves
either the delivered vote or two distinct votes naming its validator in that slot's pool.
This is a pool-membership result; it does not establish signature authenticity. -/
theorem held_after_receipt (hr : ACLocalRun (instanceAC sp FGP) H U tr ini) (hy : y ∈ H)
    (hc : tr.CallAt y i ℓ) {v : Vote sp.n} (hm : ℓ.call = .message v)
    (lo : (sp.slot (tr.time i) : Int) - 1 ≤ v.slot) (hi : v.slot ≤ sp.slot (tr.time i)) :
    v ∈ (tr.post i).pool v.slot ∨ v.val ∈ equivocators {w | w ∈ (tr.post i).pool v.slot} := by
  have he := congrArg Prod.fst (hr.exec i ℓ hc.2 (hc.1 ▸ hy))
  rw [hm] at he
  dsimp only at he
  rw [← he]
  apply held_of_grows ((Grows.of_pool_eq (optimistic_pool_eq _ _ _)).trans
    (grows_attempt _ _ _ _))
  exact admitVote_held _ _ _ lo hi

/-- Exact-or-pair cover in a call's output survives to the next restart pre-state. -/
theorem cover_before_restart (hr : ACLocalRun (instanceAC sp FGP) H U tr ini) (hy : y ∈ H)
    (hc : tr.CallAt y i ℓ) {v : Vote sp.n}
    (covered : v ∈ (tr.post i).pool v.slot ∨ v.val ∈ equivocators {w | w ∈ (tr.post i).pool v.slot})
    {j : Nat} (hij : i < j) (awake : ∀ k, i < k → k < j → ¬ tr.RestartAt y k) :
    v ∈ (tr.state y j).pool v.slot ∨ v.val ∈ equivocators {w | w ∈ (tr.state y j).pool v.slot} := by
  induction j, hij using Nat.le_induction with
  | base =>
    simpa [Trace.state, hc.1, hc.2] using covered
  | succ k hik ih =>
    have prev := ih (fun m him hmk => awake m him (hmk.trans (Nat.lt_succ_self _)))
    rw [Trace.state]
    split_ifs with h
    · obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.1 h.2
      have hn : l.call ≠ .restart := fun eq => awake k hik (Nat.lt_succ_self _) ⟨l, ⟨h.1, hl⟩, eq⟩
      have he := congrArg Prod.fst (hr.exec k l hl (h.1 ▸ hy))
      dsimp only at he
      rw [← he, h.1]
      exact held_of_grows (grows_step _ _ _ _ _ hn) prev
    · exact prev

/-- In-window message receipt followed by a restart-free interval gives cast-input cover. -/
theorem receipt_cover_before_restart (hr : ACLocalRun (instanceAC sp FGP) H U tr ini) (hy : y ∈ H)
    (hc : tr.CallAt y i ℓ) {v : Vote sp.n} (hm : ℓ.call = .message v)
    (lo : (sp.slot (tr.time i) : Int) - 1 ≤ v.slot) (hi : v.slot ≤ sp.slot (tr.time i))
    {j : Nat} (hij : i < j) (awake : ∀ k, i < k → k < j → ¬ tr.RestartAt y k) :
    v ∈ (tr.state y j).pool v.slot ∨ v.val ∈ equivocators {w | w ∈ (tr.state y j).pool v.slot} :=
  cover_before_restart hr hy hc (held_after_receipt hr hy hc hm lo hi) hij awake

/-- A real restart preserves locks, but no pre-restart vote (not even an equivocating pair)
survives in the pool. Delivery before restart alone cannot establish post-restart cover. -/
theorem reset_cut (hr : ACLocalRun (instanceAC sp FGP) H U tr ini) (hy : y ∈ H)
    (hc : tr.CallAt y i ℓ) (hw : ℓ.call = .restart) :
    (tr.post i).locks = (tr.state y i).locks ∧ (∀ s, (tr.post i).pool s = []) ∧ ℓ.emits = [] := by
  have he := hr.exec i ℓ hc.2 (hc.1 ▸ hy)
  rw [hw, hc.1] at he
  have hs := congrArg Prod.fst he
  dsimp only at hs
  rw [← hs]
  exact ⟨rfl, fun _ => rfl, (congrArg Prod.snd he).symm⟩

end Consensus.Goldilocks.SA.TimeShifted

end
