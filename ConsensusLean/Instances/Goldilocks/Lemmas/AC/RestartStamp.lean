module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Schedule
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Basic

public section

/-! # Restart replay is a bulk stamp

The replay preserves every field except `blockStamp`, independently of the deep-source and
optimistic switches. Its list need not be in parent order, or even duplicate-free. A full
restart needs only a nonnegative time and an enumeration of the non-genesis tree roots;
`FrameOK` supplies that enumeration for every `ReplayOrder`.
-/

namespace Consensus.Goldilocks.AC

variable {FGP : Type} (sp : ACParams)

/-- A well-formed frame has a parent-order enumeration of its non-genesis blocks. -/
theorem parentOrder_exists {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) :
    ∃ l, ParentOrderAt sp.genesisRoot Φ l := by
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

/-- A node whose latest restart is at `t ≥ 0` is not joined at `t`. -/
theorem not_joined_of_restartTime {A : ACState sp.n} {t : Time} (ht : 0 ≤ t)
    (h : A.restartTime = (t : WithBot Time)) : ¬ joined sp A t := by
  simp only [joined, h, WithBot.coe_le_coe]
  have h₁ := (ts_le_iff_le_slot sp ht (sp.slot t)).mpr le_rfl
  have h₂ : sp.ts ((sp.slot t : Int) - 1) < sp.ts (sp.slot t) := (ts_lt_iff sp).mpr (by omega)
  intro h₃
  exact absurd (lt_of_lt_of_le h₂ h₁) (not_lt.mpr h₃)

/-- A non-joined block handler is exactly the stamp update, without emissions. -/
theorem acOnBlock_eq_receipt_of_not_joined (self : Fin sp.n) (A : ACState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (B : Blk sp.n FGP) (h : ¬ joined sp A t) :
    acOnBlock sp self A Φ t B = (blockReceipt sp A t B, []) := by
  have hn : ¬ joined sp (blockReceipt sp A t B) t := h
  simp only [acOnBlock, optimisticConfirmation, optimisticSelect, hn, not_false_eq_true,
    true_or, ite_true, tryVote]

/-- Any list replay on a non-joined state stamps exactly its roots; duplicates and order do
not matter, and all other fields are unchanged. -/
theorem replay_eq_stamp_of_not_joined (self : Fin sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (l : List (Blk sp.n FGP)) (A : ACState sp.n) (h : ¬ joined sp A t) :
    l.foldl (fun acc B => let r := acOnBlock sp self acc.1 Φ t B;
      (r.1, acc.2 ++ r.2)) (A, ([] : List (Em sp FGP))) =
      ({ A with blockStamp := fun q =>
        if ∃ B ∈ l, B.root = q then ETime.of t else A.blockStamp q }, []) := by
  classical
  induction l generalizing A with
  | nil => simp
  | cons B l ih =>
    rw [List.foldl_cons, acOnBlock_eq_receipt_of_not_joined sp self A Φ t B h]
    simp only [List.nil_append]
    rw [ih (blockReceipt sp A t B) h]
    congr 2
    funext q
    simp only [blockReceipt, Function.update_apply, List.mem_cons]
    by_cases he : ∃ C ∈ l, C.root = q
    · simp [he]
    · by_cases hb : q = B.root
      · subst q; simp
      · simp [he, hb, Ne.symm hb]

/-- The order-free restart result, including all reset and retained fields. -/
noncomputable def restartStamp (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    ACState sp.n := by
  classical
  exact { ACState.initial sp.genesisRoot with
    locks := A.locks, latestConfirmed := A.latestConfirmed,
    restartTime := (t : WithBot Time), mayVote := A.mayVote,
    blockStamp := fun q => if q = sp.genesisRoot then ⊥
      else if InTree Φ q then ETime.of t else ⊤ }

open Classical in
/-- The retained fields, reset fields and stamps of the bulk restart. -/
theorem restartStamp_eq (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    restartStamp sp A Φ t =
      { ACState.initial sp.genesisRoot with
        locks := A.locks, latestConfirmed := A.latestConfirmed,
        restartTime := (t : WithBot Time), mayVote := A.mayVote,
        blockStamp := fun q => if q = sp.genesisRoot then ⊥
          else if InTree Φ q then ETime.of t else ⊤ } := by
  rfl

set_option linter.unusedVariables false in
/-- At every well-formed nonnegative restart, for any input state and every replay order,
the result is the bulk stamp and emits nothing. No reachability or deep-depth premise is needed. -/
theorem acRestart_eq_stamp (ro : ReplayOrder sp FGP) (self : Fin sp.n) (A : ACState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (hΦ : FrameOK Φ) (ht : 0 ≤ t) :
    acRestart sp ro self A Φ t = (restartStamp sp A Φ t, []) := by
  rw [restartStamp_eq]
  rfl

/-- The former restart replay, retained only to state its lawful equivalence to stamping. -/
noncomputable def restartReplay (ro : ReplayOrder sp FGP) (self : Fin sp.n)
    (A : ACState sp.n) (Φ : Frm sp.n FGP) (t : Time) : ACState sp.n × List (Em sp FGP) :=
  (ro.order t Φ).foldl
    (fun acc B => let r := acOnBlock sp self acc.1 Φ t B; (r.1, acc.2 ++ r.2))
    ({ ACState.initial sp.genesisRoot with
      locks := A.locks, latestConfirmed := A.latestConfirmed,
      restartTime := (t : WithBot Time), mayVote := A.mayVote }, [])

/-- The former replay and the bulk restart agree under exactly the lawful restart guards.
Malformed frames and negative times are deliberately not covered. -/
theorem restartReplay_eq_stamp (ro : ReplayOrder sp FGP) (self : Fin sp.n) (A : ACState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (hΦ : FrameOK Φ) (ht : 0 ≤ t) :
    restartReplay sp ro self A Φ t = (restartStamp sp A Φ t, []) := by
  classical
  have hl := ro.parentOrder t Φ (parentOrder_exists sp hΦ)
  let A₀ : ACState sp.n := { ACState.initial sp.genesisRoot with
    locks := A.locks, latestConfirmed := A.latestConfirmed,
    restartTime := (t : WithBot Time), mayVote := A.mayVote }
  have hn : ¬ joined sp A₀ t := not_joined_of_restartTime sp ht rfl
  rw [restartReplay, replay_eq_stamp_of_not_joined sp self Φ t (ro.order t Φ) A₀ hn]
  rw [restartStamp_eq]
  have he (q : Nat) : (∃ B ∈ ro.order t Φ, B.root = q) ↔
      q ≠ sp.genesisRoot ∧ InTree Φ q := by
    constructor
    · rintro ⟨B, hB, rfl⟩
      obtain ⟨hB, hg⟩ := (hl.2.1 B).mp hB
      exact ⟨hg, B, hB, rfl⟩
    · rintro ⟨hg, B, hB, rfl⟩
      exact ⟨B, (hl.2.1 B).mpr ⟨hB, hg⟩, rfl⟩
  congr 2
  funext q
  simp only [he, A₀, ACState.initial]
  split_ifs <;> simp_all

end Consensus.Goldilocks.AC

end
