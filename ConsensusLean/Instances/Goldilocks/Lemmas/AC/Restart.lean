module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic

public section

/-! # Goldilocks AC: the restart (A0.7)

What `ac_restart` keeps, resets and writes, and that the node is not joined at the restart, so
the replay emits nothing. -/

namespace Consensus.Goldilocks.AC

variable (sp : ACParams)

/-- Parent order at the genesis root of these protocol parameters. -/
abbrev ParentOrder {FGP : Type} (Φ : Frm sp.n FGP) (l : List (Blk sp.n FGP)) : Prop :=
  ParentOrderAt sp.genesisRoot Φ l

open Classical in
/-- One replay order: a chosen parent-order enumeration (`[]` if there is none). -/
noncomputable def ReplayOrder.choice {FGP : Type} : ReplayOrder sp FGP where
  order := fun _ Φ => if h : ∃ l, ParentOrder sp Φ l then h.choose else []
  parentOrder := fun _ Φ h => by simp only [h, ↓reduceDIte]; exact h.choose_spec

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
    have hsorted :=
      List.pairwise_mergeSort (le := fun a b : Blk sp.n FGP => decide (a.slot ≤ b.slot))
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
`Φ`: the kept and reset fields, the empty pools (the replay admits nothing), and the stamps. -/
structure RestartInv {FGP : Type} (A₀ : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (A : ACState sp.n) : Prop where
  locks : A.locks = A₀.locks
  latestConfirmed : A.latestConfirmed = A₀.latestConfirmed
  restartTime : A.restartTime = (t : WithBot Time)
  saved : A.saved = (ACState.initial sp.genesisRoot : ACState sp.n).saved
  votedSlot : A.votedSlot = (ACState.initial sp.genesisRoot : ACState sp.n).votedSlot
  pool : ∀ σ, A.pool σ = []
  voteStamp : ∀ x, A.voteStamp x = ⊤ ∨ A.voteStamp x = ETime.of t
  blockStamp : ∀ q, A.blockStamp q = (ACState.initial sp.genesisRoot : ACState sp.n).blockStamp q ∨
    (A.blockStamp q = ETime.of t ∧ q ≠ sp.genesisRoot ∧ InTree Φ q)

/-- The receipt of a block of the tree other than genesis at `t` keeps the restart invariant. -/
theorem RestartInv.blockReceipt {FGP : Type} {A₀ A : ACState sp.n} {Φ : Frm sp.n FGP}
    {t : Time} (h : RestartInv sp A₀ Φ t A) {B : Blk sp.n FGP} (hB : B ∈ Φ.tree)
    (hg : B.root ≠ sp.genesisRoot) : RestartInv sp A₀ Φ t (AC.blockReceipt sp A t B) := by
  exact ⟨h.locks, h.latestConfirmed, h.restartTime, h.saved, h.votedSlot, h.pool,
    h.voteStamp, fun q => by
      simp only [AC.blockReceipt, Function.update_apply]
      split_ifs with hq
      · exact Or.inr ⟨rfl, hq ▸ hg, ⟨B, hB, hq.symm⟩⟩
      · exact h.blockStamp q⟩

/-- A node whose latest restart is at `t ≥ 0` is not joined at `t`. -/
theorem not_joined_of_restartTime {A : ACState sp.n} {t : Time} (ht : 0 ≤ t)
    (h : A.restartTime = (t : WithBot Time)) : ¬ joined sp A t := by
  simp only [joined, h, WithBot.coe_le_coe]
  have h₁ := (ts_le_iff_le_slot sp ht (sp.slot t)).mpr le_rfl
  have h₂ : sp.ts ((sp.slot t : Int) - 1) < sp.ts (sp.slot t) := (ts_lt_iff sp).mpr (by omega)
  intro h₃
  exact absurd (lt_of_lt_of_le h₂ h₁) (not_lt.mpr h₃)

/-- At a state with the restart invariant (so not joined), `ac_on_block` is its receipt and emits
nothing. -/
theorem RestartInv.acOnBlock {FGP : Type} {A₀ A : ACState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    (ht : 0 ≤ t) (h : RestartInv sp A₀ Φ t A) {B : Blk sp.n FGP} (hB : B ∈ Φ.tree)
    (hg : B.root ≠ sp.genesisRoot) (self : Fin sp.n) :
    AC.acOnBlock sp self A Φ t B = (AC.blockReceipt sp A t B, []) := by
  have hR := h.blockReceipt sp hB hg
  have hnj := not_joined_of_restartTime sp ht hR.restartTime
  have hopt : optimisticConfirmation sp (AC.blockReceipt sp A t B) Φ t =
      AC.blockReceipt sp A t B := by
    simp only [optimisticConfirmation, optimisticSelect, hnj, not_false_eq_true, true_or,
      ite_true]
  simp only [AC.acOnBlock, hopt, tryVote, hnj, not_false_eq_true, true_or, ite_true]

/-- **A0.7, restart.** -/
theorem restart_state : RestartState sp := by
  intro FGP ro self A Φ t hΦ ht
  have hl := ro.parentOrder t Φ (parentOrder_exists sp hΦ)
  have h₀ : RestartInv sp A Φ t { ACState.initial sp.genesisRoot with
      locks := A.locks, latestConfirmed := A.latestConfirmed,
      restartTime := (t : WithBot Time), mayVote := A.mayVote } :=
    ⟨rfl, rfl, rfl, rfl, rfl, fun σ => rfl,
      fun x => Or.inl rfl, fun q => Or.inl rfl⟩
  have key : ∀ l : List (Blk sp.n FGP), (∀ B ∈ l, B ∈ Φ.tree ∧ B.root ≠ sp.genesisRoot) →
      ∀ acc : ACState sp.n × List (Em sp FGP), acc.2 = [] → RestartInv sp A Φ t acc.1 →
      let r := l.foldl (fun acc B => let r := AC.acOnBlock sp self acc.1 Φ t B;
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
  exact ⟨hr2, hr1.locks, hr1.latestConfirmed, hr1.saved, hr1.votedSlot,
    hr1.restartTime, not_joined_of_restartTime sp ht hr1.restartTime,
    hr1.pool, hr1.voteStamp,
    hr1.blockStamp⟩

end Consensus.Goldilocks.AC

end
