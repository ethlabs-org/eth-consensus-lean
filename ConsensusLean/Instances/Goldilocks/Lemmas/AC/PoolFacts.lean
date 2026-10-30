module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace

public section

/-! # Goldilocks SA: pools, stamps and resolution at reachable states (A0.1–A0.3, A0.7, A0.9)

The ACBase statements that ACSteps does not use: admission slots, stable stamps and carried votes
(A0.1), stable resolution (A0.2), the merged view's opponents (A0.3), what a joined node kept at
its restarts (A0.7) and the proposal payload (A0.9). Kept out of the import closure of ACSteps,
so that ACSteps' closure is free of `sorry` while these are open. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-! ### Admission at a time

`Admits A A' t`: every vote of the pools of `A'` is in the same pool of `A`, or is of slot
`slot(t) − 1` or `slot(t)` (admission at `t` takes only those). -/

section Admission

variable {sp} {FGP : Type}

/-- The pools of `A'` are those of `A` plus votes of slot `slot(t) − 1` or `slot(t)`. -/
def Admits (A A' : SAState sp.n) (t : Time) : Prop :=
  ∀ σ, ∀ x ∈ A'.pool σ, x ∈ A.pool σ ∨ x.slot + 1 = sp.slot t ∨ x.slot = sp.slot t

theorem Admits.refl (A : SAState sp.n) (t : Time) : Admits A A t :=
  fun _ _ => Or.inl

theorem Admits.of_pool_eq {A A' : SAState sp.n} {t : Time} (h : A'.pool = A.pool) :
    Admits A A' t := fun _ _ hx => Or.inl (h ▸ hx)

theorem Admits.trans {A B C : SAState sp.n} {t : Time} (h₁ : Admits A B t) (h₂ : Admits B C t) :
    Admits A C t := fun σ x hx => (h₂ σ x hx).elim (fun h => h₁ σ x h) Or.inr

theorem admits_admitVote (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    Admits A (admitVote sp A t v) t := by
  intro σ x hx
  unfold admitVote at hx
  split_ifs at hx with h₁ h₂
  · exact Or.inl hx
  · exact Or.inl hx
  · simp only [Function.update_apply] at hx
    split_ifs at hx with hσ
    · rcases List.mem_append.mp hx with hx | hx
      · exact Or.inl (hσ ▸ hx)
      · rw [List.mem_singleton.mp hx]
        right; omega
    · exact Or.inl hx

private theorem updateLatestConfirmed_pool_eq (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (C : Blk sp.n FGP) : (updateLatestConfirmed sp A Φ C).pool = A.pool := by
  unfold updateLatestConfirmed
  split_ifs <;> rfl

private theorem optimistic_pool_eq (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).pool = A.pool := by
  unfold optimisticConfirmation
  split
  · rfl
  · exact updateLatestConfirmed_pool_eq _ _ _

private theorem updateConfirmation_pool_eq (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (s : Nat) : (updateConfirmation sp A Φ t s).pool = A.pool := by
  unfold updateConfirmation
  dsimp only
  split
  · rfl
  · split_ifs
    · rfl
    · exact updateLatestConfirmed_pool_eq _ _ _

theorem admits_tryVote (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    Admits A (tryVote sp self A Φ t).1 t := by
  unfold tryVote
  dsimp only
  split_ifs
  · exact Admits.refl _ _
  · exact Admits.refl _ _
  all_goals
    refine Admits.trans ?_ (Admits.of_pool_eq (optimistic_pool_eq _ _ _))
    refine Admits.trans (Admits.of_pool_eq ?_) (admits_admitVote _ _ _)
    rfl

theorem admits_blockReceipt (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) :
    Admits A (blockReceipt sp A t B) t := by
  unfold blockReceipt
  generalize blockVotes B = l
  suffices h : ∀ A' : SAState sp.n, Admits A A' t →
      Admits A (l.foldl (fun A v => admitVote sp A t v) A') t from
    h _ (Admits.of_pool_eq rfl)
  induction l with
  | nil => exact fun _ h => h
  | cons v l ih =>
    intro A' h
    simp only [List.foldl_cons]
    exact ih _ (h.trans (admits_admitVote _ _ _))

theorem admits_acOnBlock (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (B : Blk sp.n FGP) : Admits A (acOnBlock sp self A Φ t B).1 t := by
  unfold acOnBlock
  exact (admits_blockReceipt A t B).trans
    ((Admits.of_pool_eq (optimistic_pool_eq _ _ _)).trans (admits_tryVote _ _ _ _))

theorem admits_acOnMessage (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (v : Vote sp.n) : Admits A (acOnMessage sp self A Φ t v).1 t := by
  unfold acOnMessage
  exact (admits_admitVote A t v).trans
    ((Admits.of_pool_eq (optimistic_pool_eq _ _ _)).trans (admits_tryVote _ _ _ _))

theorem admits_acOnTick (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    Admits A (acOnTick sp self A Φ t).1 t := by
  unfold acOnTick
  dsimp only
  split_ifs
  all_goals first
    | exact Admits.refl _ _
    | exact admits_tryVote _ _ _ _
    | exact Admits.of_pool_eq (updateConfirmation_pool_eq _ _ _ _)
    | exact (admits_tryVote _ _ _ _).trans (Admits.of_pool_eq (updateConfirmation_pool_eq _ _ _ _))

/-- A restart's pools hold only votes of slot `slot(t) − 1` or `slot(t)`. -/
theorem restart_admits (ro : ReplayOrder sp FGP) (self : Fin sp.n) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    ∀ σ, ∀ x ∈ (acRestart sp ro self A Φ t).1.pool σ,
      x.slot + 1 = sp.slot t ∨ x.slot = sp.slot t := by
  unfold acRestart
  generalize ro.order t Φ = l
  set A₀ : SAState sp.n := { SAState.initial sp.genesisRoot with
    locks := A.locks, latestConfirmed := A.latestConfirmed, restartTime := (t : WithBot Time) }
  suffices h : ∀ (l : List (Blk sp.n FGP)) (acc : SAState sp.n × List (Em sp FGP)),
      Admits A₀ acc.1 t → Admits A₀ (l.foldl (fun acc B => let r := acOnBlock sp self acc.1 Φ t B;
        (r.1, acc.2 ++ r.2)) acc).1 t by
    intro σ x hx
    rcases h l (A₀, []) (Admits.refl _ _) σ x hx with hx | hx
    · simp [A₀, SAState.initial] at hx
    · exact hx
  intro l
  induction l with
  | nil => exact fun _ h => h
  | cons B l ih =>
    intro acc h
    simp only [List.foldl_cons]
    exact ih _ (h.trans (admits_acOnBlock _ _ _ _ _))

end Admission

/-- **A0.1, admission slots.** -/
theorem admission_slots : AdmissionSlots sp := by
  intro FGP ro self U _ A Φ t₀ _ c Φ' t _ _
  dsimp only
  intro σ x hx
  cases c with
  | restart => exact Or.inr (restart_admits ro self A Φ' t σ x hx)
  | tick => exact (admits_acOnTick self A Φ' t σ x hx).imp_left fun h => ⟨h, by simp⟩
  | message m => exact (admits_acOnMessage self A Φ' t m σ x hx).imp_left fun h => ⟨h, by simp⟩
  | block B => exact (admits_acOnBlock self A Φ' t B σ x hx).imp_left fun h => ⟨h, by simp⟩
  | proposal =>
    refine Or.inl ⟨?_, by simp⟩
    change x ∈ (acProposal sp A Φ' t).1.pool σ at hx
    unfold acProposal at hx
    split_ifs at hx <;> exact hx
  | toFG =>
    refine Or.inl ⟨?_, by simp⟩
    change x ∈ (acToFG sp A Φ' t).1.pool σ at hx
    unfold acToFG at hx
    dsimp only at hx
    split_ifs at hx
    · split at hx
      · exact hx
      · split_ifs at hx <;> exact hx
    · exact hx

/-- **A0.1, stamps.** -/
theorem stamp_stable : StampStable sp := by
  sorry

/-- **A0.1, carried votes.** -/
theorem carried_votes : CarriedVotes sp := by
  sorry

/-- **A0.2, resolution is stable.** -/
theorem resolution_stable : ResolutionStable sp := by
  sorry

/-- **A0.3, the merged view's opponents.** -/
theorem merged_opponents : MergedOpponents sp := by
  sorry

/-- **A0.9.** The payload of a proposal at `t_σ` is the slot-`(σ−1)` vote view of the pool, whose
votes are of slot `σ − 1` (`pool_cap`) and whose support is among its votes. -/
theorem proposal_payload_valid : ProposalPayloadValid sp := by
  intro FGP ro self U hU A Φ t₀ hr σ _ d p hp B hBs hBp
  have hσ : sp.slot (sp.toParams.slotTime σ) = σ := by
    rw [sp.slotTime_eq]
    exact slot_of_mem sp σ (by simp [SAParams.ts]) (by
      simp only [SAParams.ts]; push_cast; have := sp.toParams.hΔ; nlinarith)
  change (acProposal sp A Φ (sp.toParams.slotTime σ)).2 = some (d, p) at hp
  unfold acProposal at hp
  split_ifs at hp
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hp)
  rw [hσ] at *
  have hpool := pool_cap sp FGP ro self U hU A Φ t₀ hr
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · simp only [blockVotes, hBp, voteViewList, List.mem_filter, SAState.poolAt] at hv
    split_ifs at hv with hneg
    · simp at hv
    · have := (hpool _).1 v hv.1
      omega
  · simp only [blockSupport, blockVotes, hBp, voteViewList, List.mem_filter] at hv ⊢
    exact hv.1

/-- **A0.7, joining.** -/
theorem joined_keeps_votes : JoinedKeepsVotes sp := by
  sorry

end Consensus.Goldilocks.SA

end
