module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic

public section

/-! # Goldilocks SA: the restart (A0.7)

What `ac_restart` keeps, resets and writes, and that the node is not joined at the restart, so
the replay emits nothing. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- A well-formed frame has a parent-order enumeration of its blocks other than genesis: by
slot (parents have smaller slots). -/
theorem parentOrder_exists {FGP : Type} {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) :
    ∃ l, ParentOrder sp Φ l := by
  classical
  have hS : {B | B ∈ Φ.tree ∧ B.root ≠ sp.genesisRoot}.Finite :=
    hΦ.finite.subset (fun B h => h.1)
  refine ⟨hS.toFinset.toList.mergeSort (fun a b => decide (a.slot ≤ b.slot)), ?_, ?_, ?_⟩
  · exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
  · intro B
    simp only [List.mem_mergeSort, Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  · intro i j hi hj hp
    have hsorted := List.pairwise_mergeSort (le := fun a b : Blk sp.n FGP => decide (a.slot ≤ b.slot))
      (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) hS.toFinset.toList
    have hm : ∀ k (hk : k < (hS.toFinset.toList.mergeSort
        (fun a b => decide (a.slot ≤ b.slot))).length),
        (hS.toFinset.toList.mergeSort (fun a b => decide (a.slot ≤ b.slot)))[k] ∈ Φ.tree := by
      intro k hk
      have := List.getElem_mem hk
      simp only [List.mem_mergeSort, Finset.mem_toList, Set.Finite.mem_toFinset,
        Set.mem_ofPred_eq] at this
      exact this.1
    have hlt := hΦ.coherent.2 _ (hm j hj) _ (hm i hi) hp
    by_contra hji
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hji) with h | h
    · have := hsorted.rel_getElem_of_lt hi hj h
      simp only [decide_eq_true_eq] at this
      omega
    · subst h; omega

/-- What a restart at `t` from `A₀` leaves in a state, after any part of the replay with frame
`Φ`: the kept and reset fields, the pools (votes of blocks of the tree, stamped `t`), and the
stamps. -/
structure RestartInv {FGP : Type} (A₀ : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (A : SAState sp.n) : Prop where
  locks : A.locks = A₀.locks
  latestConfirmed : A.latestConfirmed = A₀.latestConfirmed
  restartTime : A.restartTime = (t : WithBot Time)
  saved : A.saved = (SAState.initial sp.genesisRoot : SAState sp.n).saved
  fgReported : A.fgReported = (SAState.initial sp.genesisRoot : SAState sp.n).fgReported
  votedSlot : A.votedSlot = (SAState.initial sp.genesisRoot : SAState sp.n).votedSlot
  pool : ∀ σ, ∀ x ∈ A.pool σ, A.voteStamp x = ETime.of t ∧ ∃ B ∈ Φ.tree, x ∈ blockVotes B
  voteStamp : ∀ x, A.voteStamp x = ⊤ ∨ A.voteStamp x = ETime.of t
  blockStamp : ∀ q, A.blockStamp q = (SAState.initial sp.genesisRoot : SAState sp.n).blockStamp q ∨
    (A.blockStamp q = ETime.of t ∧ q ≠ sp.genesisRoot ∧ InTree Φ q)

/-- Admission at `t` of a vote of a block of the tree keeps the restart invariant. -/
theorem RestartInv.admitVote {FGP : Type} {A₀ A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    (h : RestartInv sp A₀ Φ t A) {B : Blk sp.n FGP} (hB : B ∈ Φ.tree) {v : Vote sp.n}
    (hv : v ∈ blockVotes B) : RestartInv sp A₀ Φ t (SA.admitVote sp A t v) := by
  unfold SA.admitVote
  split_ifs
  · exact h
  · exact h
  · refine ⟨h.locks, h.latestConfirmed, h.restartTime, h.saved, h.fgReported, h.votedSlot,
      fun σ x hx => ?_, fun x => ?_, h.blockStamp⟩
    · simp only [Function.update_apply] at hx ⊢
      split_ifs at hx with hσ
      · rcases List.mem_append.mp hx with hx | hx
        · split_ifs with hxv
          · exact ⟨rfl, B, hB, hxv ▸ hv⟩
          · exact h.pool _ x (hσ ▸ hx)
        · simp only [List.mem_singleton] at hx
          subst hx
          simp only [ite_true]
          exact ⟨trivial, B, hB, hv⟩
      · split_ifs with hxv
        · exact ⟨rfl, B, hB, hxv ▸ hv⟩
        · exact h.pool σ x hx
    · simp only [Function.update_apply]
      split_ifs
      · exact Or.inr rfl
      · exact h.voteStamp x

/-- The receipt of a block of the tree other than genesis at `t` keeps the restart invariant. -/
theorem RestartInv.blockReceipt {FGP : Type} {A₀ A : SAState sp.n} {Φ : Frm sp.n FGP}
    {t : Time} (h : RestartInv sp A₀ Φ t A) {B : Blk sp.n FGP} (hB : B ∈ Φ.tree)
    (hg : B.root ≠ sp.genesisRoot) : RestartInv sp A₀ Φ t (SA.blockReceipt sp A t B) := by
  unfold SA.blockReceipt
  have h₀ : RestartInv sp A₀ Φ t
      { A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) } :=
    ⟨h.locks, h.latestConfirmed, h.restartTime, h.saved, h.fgReported, h.votedSlot, h.pool,
      h.voteStamp, fun q => by
        simp only [Function.update_apply]
        split_ifs with hq
        · exact Or.inr ⟨rfl, hq ▸ hg, ⟨B, hB, hq.symm⟩⟩
        · exact h.blockStamp q⟩
  generalize { A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) } = A' at h₀
  have key : ∀ vs : List (Vote sp.n), (∀ v ∈ vs, v ∈ blockVotes B) → ∀ A',
      RestartInv sp A₀ Φ t A' → RestartInv sp A₀ Φ t (vs.foldl (fun A v => SA.admitVote sp A t v) A') := by
    intro vs
    induction vs with
    | nil => intro _ A' h; exact h
    | cons v vs ih =>
      intro hvs A' h
      exact ih (fun w hw => hvs w (List.mem_cons_of_mem _ hw)) _
        (h.admitVote sp hB (hvs v List.mem_cons_self))
  exact key _ (fun _ h => h) A' h₀

/-- A node whose latest restart is at `t ≥ 0` is not joined at `t`. -/
theorem not_joined_of_restartTime {A : SAState sp.n} {t : Time} (ht : 0 ≤ t)
    (h : A.restartTime = (t : WithBot Time)) : ¬ joined sp A t := by
  simp only [joined, h, WithBot.coe_le_coe]
  have h₁ := (ts_le_iff_le_slot sp ht (sp.slot t)).mpr le_rfl
  have h₂ : sp.ts ((sp.slot t : Int) - 1) < sp.ts (sp.slot t) := (ts_lt_iff sp).mpr (by omega)
  intro h₃
  exact absurd (lt_of_lt_of_le h₂ h₁) (not_lt.mpr h₃)

/-- At a state with the restart invariant (so not joined), `ac_on_block` is its receipt and emits
nothing. -/
theorem RestartInv.acOnBlock {FGP : Type} {A₀ A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    (ht : 0 ≤ t) (h : RestartInv sp A₀ Φ t A) {B : Blk sp.n FGP} (hB : B ∈ Φ.tree)
    (hg : B.root ≠ sp.genesisRoot) (self : Fin sp.n) :
    SA.acOnBlock sp self A Φ t B = (SA.blockReceipt sp A t B, []) := by
  have hR := h.blockReceipt sp hB hg
  have hnj := not_joined_of_restartTime sp ht hR.restartTime
  have hopt : optimisticConfirmation sp (SA.blockReceipt sp A t B) Φ t =
      SA.blockReceipt sp A t B := by
    simp only [optimisticConfirmation, optimisticSelect, hnj, not_false_eq_true, true_or,
      ite_true]
  simp only [SA.acOnBlock, hopt, tryVote, hnj, not_false_eq_true, true_or, ite_true]

/-- **A0.7, restart.** -/
theorem restart_state : RestartState sp := by
  intro FGP ro self A Φ t hΦ ht
  have hl := ro.parentOrder t Φ (parentOrder_exists sp hΦ)
  have h₀ : RestartInv sp A Φ t { SAState.initial sp.genesisRoot with
      locks := A.locks, latestConfirmed := A.latestConfirmed,
      restartTime := (t : WithBot Time) } :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun σ x hx => by simp [SAState.initial] at hx,
      fun x => Or.inl rfl, fun q => Or.inl rfl⟩
  have key : ∀ l : List (Blk sp.n FGP), (∀ B ∈ l, B ∈ Φ.tree ∧ B.root ≠ sp.genesisRoot) →
      ∀ acc : SAState sp.n × List (Em sp FGP), acc.2 = [] → RestartInv sp A Φ t acc.1 →
      let r := l.foldl (fun acc B => let r := SA.acOnBlock sp self acc.1 Φ t B;
        (r.1, acc.2 ++ r.2)) acc
      r.2 = [] ∧ RestartInv sp A Φ t r.1 := by
    intro l
    induction l with
    | nil => intro _ acc h₂ h₁; exact ⟨h₂, h₁⟩
    | cons B l ih =>
      intro hl acc h₂ h₁
      obtain ⟨hB, hg⟩ := hl B List.mem_cons_self
      simp only [List.foldl_cons]
      apply ih (fun C hC => hl C (List.mem_cons_of_mem _ hC))
      · simp only [h₁.acOnBlock sp ht hB hg self, h₂, List.append_nil]
      · simp only [h₁.acOnBlock sp ht hB hg self]
        exact h₁.blockReceipt sp hB hg
  obtain ⟨hr2, hr1⟩ := key (ro.order t Φ) (fun B hB => (hl.2.1 B).mp hB) (_, []) rfl h₀
  exact ⟨hr2, hr1.locks, hr1.latestConfirmed, hr1.saved, hr1.fgReported, hr1.votedSlot,
    hr1.restartTime, not_joined_of_restartTime sp ht hr1.restartTime, hr1.pool, hr1.voteStamp,
    hr1.blockStamp⟩

end Consensus.Goldilocks.SA

end
