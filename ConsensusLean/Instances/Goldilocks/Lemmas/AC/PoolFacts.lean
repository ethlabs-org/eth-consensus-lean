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

/-! ### Pools only grow outside a restart; carried votes -/

section Grows

variable {sp} {FGP : Type}

/-- Every pool of `A` is contained in the same pool of `A'`. -/
def Grows (A A' : SAState sp.n) : Prop := ∀ σ, ∀ x ∈ A.pool σ, x ∈ A'.pool σ

theorem Grows.trans {A B C : SAState sp.n} (h₁ : Grows A B) (h₂ : Grows B C) : Grows A C :=
  fun σ x hx => h₂ σ x (h₁ σ x hx)

theorem Grows.of_pool_eq {A A' : SAState sp.n} (h : A'.pool = A.pool) : Grows A A' :=
  fun _ _ hx => h ▸ hx

theorem grows_admitVote (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    Grows A (admitVote sp A t v) := by
  intro σ x hx
  unfold admitVote
  split_ifs
  · exact hx
  · exact hx
  · simp only [Function.update_apply]
    split_ifs with hσ
    · subst hσ; exact List.mem_append_left _ hx
    · exact hx

theorem grows_tryVote (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    Grows A (tryVote sp self A Φ t).1 := by
  unfold tryVote
  dsimp only
  split_ifs
  · exact fun _ _ h => h
  · exact fun _ _ h => h
  all_goals
    refine Grows.trans ?_ (Grows.of_pool_eq (optimistic_pool_eq _ _ _))
    refine Grows.trans (Grows.of_pool_eq ?_) (grows_admitVote _ _ _)
    rfl

theorem grows_fold_admit (t : Time) (l : List (Vote sp.n)) (A : SAState sp.n) :
    Grows A (l.foldl (fun A v => admitVote sp A t v) A) := by
  induction l generalizing A with
  | nil => exact fun _ _ h => h
  | cons v l ih => exact (grows_admitVote A t v).trans (ih _)

/-- A vote of slot `slot(t) − 1` or `slot(t)` offered to admission at `t` ends up in its pool, or
its validator then has two distinct votes there. -/
theorem admitVote_held (A : SAState sp.n) (t : Time) (v : Vote sp.n)
    (h₁ : (sp.slot t : Int) - 1 ≤ v.slot) (h₂ : v.slot ≤ sp.slot t) :
    v ∈ (admitVote sp A t v).pool v.slot ∨
      v.val ∈ equivocators {x | x ∈ (admitVote sp A t v).pool v.slot} := by
  unfold admitVote
  split_ifs with ha hb
  · rcases ha with ha | ha | ha
    · omega
    · omega
    · exact Or.inl ha
  · right
    generalize hl : ((A.pool v.slot).filter (fun x => x.val = v.val)).dedup = l at hb
    have hnd : l.Nodup := hl ▸ List.nodup_dedup _
    have hmem : ∀ x ∈ l, x ∈ A.pool v.slot ∧ x.val = v.val := fun x hx => by
      rw [← hl, List.mem_dedup, List.mem_filter, decide_eq_true_eq] at hx
      exact hx
    match l, hnd, hmem, hb with
    | a :: b :: _, hnd, hmem, _ =>
      have hab : a ≠ b := fun h => (List.nodup_cons.mp hnd).1 (h ▸ List.mem_cons_self)
      obtain ⟨ha, hav⟩ := hmem a List.mem_cons_self
      obtain ⟨hb', hbv⟩ := hmem b (List.mem_cons_of_mem _ List.mem_cons_self)
      exact ⟨a, ha, b, hb', hab, hav, hbv⟩
  · left
    simp only [Function.update_apply, ite_true]
    exact List.mem_append_right _ (List.mem_singleton_self _)

/-- Equivocators of a larger vote set include those of a smaller one. -/
theorem equivocators_mono {S T : Set (Vote sp.n)} (h : S ⊆ T) : equivocators S ⊆ equivocators T :=
  fun _ ⟨x, hx, y, hy, hxy, hxi, hyi⟩ => ⟨x, h hx, y, h hy, hxy, hxi, hyi⟩

/-- "Held or equivocating" is kept as the pools grow. -/
theorem held_of_grows {A A' : SAState sp.n} (hg : Grows A A') {v : Vote sp.n}
    (h : v ∈ A.pool v.slot ∨ v.val ∈ equivocators {x | x ∈ A.pool v.slot}) :
    v ∈ A'.pool v.slot ∨ v.val ∈ equivocators {x | x ∈ A'.pool v.slot} :=
  h.imp (hg _ _) fun he => equivocators_mono (fun x (hx : x ∈ A.pool v.slot) => hg _ x hx) he

/-- After admitting the votes of `l` at `t`, each of them (of slot `slot(t) − 1` or `slot(t)`) is
held, or its validator equivocates. -/
theorem fold_admit_held (t : Time) (l : List (Vote sp.n))
    (hl : ∀ v ∈ l, (sp.slot t : Int) - 1 ≤ v.slot ∧ v.slot ≤ sp.slot t) (A : SAState sp.n) :
    ∀ v ∈ l, v ∈ (l.foldl (fun A v => admitVote sp A t v) A).pool v.slot ∨
      v.val ∈ equivocators {x | x ∈ (l.foldl (fun A v => admitVote sp A t v) A).pool v.slot} := by
  induction l generalizing A with
  | nil => intro v hv; exact absurd hv List.not_mem_nil
  | cons w l ih =>
    intro v hv
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hv with rfl | hv
    · obtain ⟨h₁, h₂⟩ := hl v List.mem_cons_self
      exact held_of_grows (grows_fold_admit t l _) (admitVote_held A t v h₁ h₂)
    · exact ih (fun u hu => hl u (List.mem_cons_of_mem _ hu)) _ v hv

end Grows

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
  intro FGP ro self U _ A Φ t₀ _ B Φ' t _ hok hBs
  dsimp only
  obtain ⟨-, -, hpay, -⟩ := hok
  have hrange : ∀ v ∈ blockVotes B, (sp.slot t : Int) - 1 ≤ v.slot ∧ v.slot ≤ sp.slot t :=
    fun v hv => by have := hpay.1 v hv; omega
  intro v hv hnot
  have hrec := fold_admit_held t (blockVotes B) hrange
    { A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) } v hv
  have hg : Grows (blockReceipt sp A t B) (acOnBlock sp self A Φ' t B).1 := by
    unfold acOnBlock
    exact (Grows.of_pool_eq (optimistic_pool_eq _ _ _)).trans (grows_tryVote _ _ _ _)
  exact (held_of_grows hg hrec).resolve_left hnot

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

/-- At a reachable state, every pool vote is of a slot at most the slot of the last call's time
(admission at `t` takes votes of slot `slot(t) − 1` or `slot(t)`, and calls are at nondecreasing
times from `0`). -/
theorem pool_slot_le {FGP : Type} {ro : ReplayOrder sp FGP} {self : Fin sp.n}
    {U : Set (Blk sp.n FGP)} (hU : Coherent U) {A : (goldilocksSA sp FGP ro).State}
    {Φ : (goldilocksSA sp FGP ro).Frm} {t₀ : Time}
    (h : (goldilocksSA sp FGP ro).ReachableAt self U A Φ t₀) :
    0 ≤ t₀ ∧ ∀ σ, ∀ x ∈ (A : SAState sp.n).pool σ, x.slot ≤ sp.slot t₀ := by
  induction h with
  | init Φ _ _ =>
    refine ⟨le_rfl, fun σ x hx => ?_⟩
    change x ∈ (SAState.initial sp.genesisRoot : SAState sp.n).pool σ at hx
    simp [SAState.initial] at hx
  | @step A Φ Φ' t t' c hr ht hok ih =>
    obtain ⟨h0, hle⟩ := ih
    refine ⟨le_trans h0 ht, fun σ x hx => ?_⟩
    rcases admission_slots sp FGP ro self U hU A Φ t hr c Φ' t' ht hok σ x hx with
      ⟨hx, -⟩ | hx | hx
    · exact le_trans (hle σ x hx) (slot_mono sp h0 ht)
    · omega
    · omega

/-- **A0.7, joining.** A joined node's restarts were before `t_{slot(t)−1}`, and before each the
node had been asleep after its previous call (at `t'`), so the votes it erased are of slot at most
`slot(t') < slot(t) − 1`. -/
theorem joined_keeps_votes : JoinedKeepsVotes sp := by
  intro FGP ro H U tr h y hy i ℓ hc hj j hji hr σ x hx
  have hle := (joined_awake sp FGP ro H U tr h y hy i ℓ hc hj).2 j hji hr
  obtain ⟨ℓr, hcr, hrr⟩ := hr
  obtain ⟨u, -, hu, -, hbefore⟩ := h.sleep_of_restart y hy j ℓr hcr hrr
  rcases tr.noCall_or_lastCall y j with hn | ⟨j', hj', ℓ', hc', hnb⟩
  · rw [tr.state_of_noCall hn, h.init y hy] at hx
    change x ∈ (SAState.initial sp.genesisRoot : SAState sp.n).pool σ at hx
    simp [SAState.initial] at hx
  · rw [tr.state_of_lastCall hc' hj' hnb] at hx
    have hreach := localRun_reachable _ _ _ _ _ tr h y hy j' ℓ' hc'
    have hxs := (pool_slot_le sp h.coherent hreach).2 σ x hx
    have hlt : tr.time j' < sp.ts ((sp.slot (tr.time i) : Int) - 1) :=
      lt_of_lt_of_le ((hbefore j' hj' ℓ' hc').trans hu) hle
    have := (ts_le_iff_le_slot sp (h.time_nonneg j') ((sp.slot (tr.time i) : Int) - 1)).not.mp
      (not_le.mpr hlt)
    omega

end Consensus.Goldilocks.SA

end
