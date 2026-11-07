module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.EvidenceRelease.RelTrace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Provenance
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Evidence-release: the saved counts and the weight of a slow lock on runs

A slow lock weighs, at each block, the maximum of the counts saved for its `k` formation slots
(`slowWeight`). On a run of the evidence-release SA these counts are the counts of the node's own
updates:

* **the handlers** (`counts_stepE`, `wlocks_stepE`): every call keeps the saved counts, except the
  update of slot `s` (the tick at `t_{s+1} + 2Δ`, joined), which saves the update's count for `s`,
  and the restart, which drops them; every stored lock after a call is a stored lock before it
  (moved, with its weight, origin, slot and fast bit), a fast or optimistic write, or a slow write
  of the update with the slow weight of the counts it saves;
* **the saved count of slot `σ`** (`savedCount_spec`): at every cut, the count of the latest
  update of slot `σ` since the latest restart, or none (`0`) with a restart after every earlier
  update of `σ`;
* **the weight of a stored slow lock** (`slowLock_written`): the slow weight of the update that
  wrote it, from the counts saved there;
* **Lemma O, the weight half** (`card_le_slowWeight`): a set of validators that every update of a
  formation slot `σ` of the lock counts for `Y` is at most the lock's weight at `Y`, when the node
  updated `σ` and did not restart since. -/

namespace Consensus.Goldilocks.EvidenceRelease

open SA

variable {sp : SAParams} {FGP : Type}

/-! ### The handlers keep the saved counts -/

section Handlers

variable {σ : Type} (E : UnlockStage sp wlockStore σ) (c : σ)

theorem counts_tryVoteE (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (tryVoteE sp E c self X Φ t).1.counts = X.counts := by
  unfold tryVoteE
  dsimp only
  split_ifs <;> rfl

open Classical in
theorem counts_acOnTickE (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acOnTickE sp E c self X Φ t).1.counts =
      if joined sp X.ac t ∧ t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t then
        saveCount sp X.counts X.ac Φ (sp.slot t - 1)
      else X.counts := by
  have hΔ := sp.toParams.hΔ
  unfold acOnTickE
  dsimp only
  generalize sp.slot t = s
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;>
    first
    | rfl
    | exact counts_tryVoteE E c self X Φ t
    | (exfalso; linarith)
    | (exfalso; tauto)

theorem counts_acOnBlockE (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (B : Blk sp.n FGP) : (acOnBlockE sp E c self X Φ t B).1.counts = X.counts := by
  unfold acOnBlockE
  rw [counts_tryVoteE]
  rfl

theorem counts_acOnMessageE (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (v : Vote sp.n) : (acOnMessageE sp E c self X Φ t v).1.counts = X.counts := by
  unfold acOnMessageE
  rw [counts_tryVoteE]
  rfl

theorem counts_acProposalE (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acProposalE sp E c X Φ t).1.counts = X.counts := by
  unfold acProposalE
  dsimp only
  split_ifs <;> rfl

theorem counts_acRestartE (ro : ReplayOrder sp FGP) (self : Fin sp.n) (X : WState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : (acRestartE sp E c ro self X Φ t).1.counts = fun _ _ => 0 := by
  unfold acRestartE
  dsimp only
  have key : ∀ (l : List (Blk sp.n FGP)) (acc : WState sp.n × List (EmW sp FGP)),
      acc.1.counts = (fun _ _ => 0) →
      (l.foldl (fun acc B => let r := acOnBlockE sp E c self acc.1 Φ t B;
        (r.1, acc.2 ++ r.2)) acc).1.counts = fun _ _ => 0 := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons B l ih =>
      intro acc h
      simp only [List.foldl_cons]
      exact ih _ ((counts_acOnBlockE E c self acc.1 Φ t B).trans h)
  exact key _ _ rfl

/-- Two weighted locks with the same weight, origin, slot and fast bit. -/
abbrev SameW (w w' : WLock) : Prop :=
  w'.weight = w.weight ∧ w'.origin = w.origin ∧ w'.lock.slot = w.lock.slot ∧
    w'.lock.fast = w.lock.fast

/-- Every lock of `W'` is a lock of `W` (moved) or fast. -/
abbrev MovedOrFast (W W' : Set WLock) : Prop :=
  ∀ w' ∈ W', w'.lock.fast = true ∨ ∃ w ∈ W, SameW w w'

theorem MovedOrFast.refl (W : Set WLock) : MovedOrFast W W :=
  fun w hw => Or.inr ⟨w, hw, rfl, rfl, rfl, rfl⟩

theorem MovedOrFast.trans {W₁ W₂ W₃ : Set WLock} (h₁ : MovedOrFast W₁ W₂)
    (h₂ : MovedOrFast W₂ W₃) : MovedOrFast W₁ W₃ := by
  intro w₃ hw₃
  rcases h₂ w₃ hw₃ with h | ⟨w₂, hw₂, h1, h2, h3, h4⟩
  · exact Or.inl h
  · rcases h₁ w₂ hw₂ with h | ⟨w₁, hw₁, g1, g2, g3, g4⟩
    · exact Or.inl (h4.trans h)
    · exact Or.inr ⟨w₁, hw₁, h1.trans g1, h2.trans g2, h3.trans g3, h4.trans g4⟩

theorem liveLocks_same (W : Set WLock) (Φ : Frm sp.n FGP) (t : Time) :
    ∀ w' ∈ wlockStore.liveLocks sp W Φ t, ∃ w ∈ W, SameW w w' := by
  rintro _ ⟨w, hw, -, -, -, -, rfl⟩
  exact ⟨w, hw, rfl, rfl, rfl, rfl⟩

theorem unlockWith_same {σ' : Type} (E' : UnlockStage sp wlockStore σ') (c' : σ')
    (W : Set WLock) (Φ : Frm sp.n FGP) (t : Time) (s : Int) (V : View sp.n) :
    MovedOrFast W (wlockStore.unlockWith sp E' c' W Φ t s V) := by
  rintro _ ⟨w, hw, -, -, -, rfl⟩
  obtain ⟨w₀, hw₀, h1, h2, h3, h4⟩ := liveLocks_same W Φ t w hw
  refine Or.inr ⟨w₀, hw₀, ?_⟩
  split_ifs
  · exact ⟨h1, h2, h3, h4⟩
  · exact ⟨h1, h2, h3, h4⟩

theorem movedOrFast_optimisticConfirmationW (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    MovedOrFast X.wlocks (optimisticConfirmationW sp X Φ t).wlocks := by
  change MovedOrFast X.wlocks (optimisticLocksW sp X.wlocks X.ac Φ t)
  unfold optimisticLocksW
  split
  · exact MovedOrFast.refl _
  · intro w' hw'
    rw [LockStore.addLocksWith_eq] at hw'
    obtain ⟨w, hw | rfl, h1, h2, h3, h4⟩ := liveLocks_same _ Φ t w' hw'
    · exact Or.inr ⟨w, hw, h1, h2, h3, h4⟩
    · exact Or.inl h4

theorem movedOrFast_tryVoteE (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : MovedOrFast X.wlocks (tryVoteE sp E c self X Φ t).1.wlocks := by
  unfold tryVoteE
  dsimp only
  split_ifs
  · exact MovedOrFast.refl _
  · exact MovedOrFast.refl _
  · exact (unlockWith_same E c X.wlocks Φ t _ _).trans (movedOrFast_optimisticConfirmationW _ Φ t)
  · exact movedOrFast_optimisticConfirmationW _ Φ t

theorem movedOrFast_acOnBlockE (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (B : Blk sp.n FGP) : MovedOrFast X.wlocks (acOnBlockE sp E c self X Φ t B).1.wlocks :=
  (movedOrFast_optimisticConfirmationW { X with ac := blockReceipt sp X.ac t B } Φ t).trans
    (movedOrFast_tryVoteE E c self _ Φ t)

theorem movedOrFast_acOnMessageE (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (v : Vote sp.n) :
    MovedOrFast X.wlocks (acOnMessageE sp E c self X Φ t v).1.wlocks :=
  (movedOrFast_optimisticConfirmationW { X with ac := admitVote sp X.ac t v } Φ t).trans
    (movedOrFast_tryVoteE E c self _ Φ t)

theorem movedOrFast_acProposalE (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    MovedOrFast X.wlocks (acProposalE sp E c X Φ t).1.wlocks := by
  unfold acProposalE
  dsimp only
  split_ifs
  · exact unlockWith_same E c X.wlocks Φ t _ _
  · exact MovedOrFast.refl _

theorem movedOrFast_acRestartE (ro : ReplayOrder sp FGP) (self : Fin sp.n) (X : WState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    MovedOrFast X.wlocks (acRestartE sp E c ro self X Φ t).1.wlocks := by
  unfold acRestartE
  dsimp only
  have key : ∀ (l : List (Blk sp.n FGP)) (acc : WState sp.n × List (EmW sp FGP)),
      MovedOrFast X.wlocks acc.1.wlocks →
      MovedOrFast X.wlocks (l.foldl (fun acc B => let r := acOnBlockE sp E c self acc.1 Φ t B;
        (r.1, acc.2 ++ r.2)) acc).1.wlocks := by
    intro l
    induction l with
    | nil => intro acc h; exact h
    | cons B l ih =>
      intro acc h
      simp only [List.foldl_cons]
      exact ih _ (h.trans (movedOrFast_acOnBlockE E c self acc.1 Φ t B))
  exact key _ _ (MovedOrFast.refl _)

/-- The slow lock `w'` is a write of the update of slot `s` from the state `X`: its weight is the
slow weight of the counts the update saves, and its slot is `s`. -/
abbrev SlowWriteOf (X : WState sp.n) (Φ : Frm sp.n FGP) (s : Nat) (w' : WLock) : Prop :=
  w'.weight = slowWeight sp Φ (saveCount sp X.counts X.ac Φ s) s w'.origin ∧ w'.lock.slot = s

theorem wlocks_updateConfirmationW (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) (s : Nat) :
    ∀ w' ∈ (updateConfirmationW sp X Φ t s).wlocks,
      w'.lock.fast = true ∨ (∃ w ∈ X.wlocks, SameW w w') ∨ SlowWriteOf X Φ s w' := by
  intro w' hw'
  change w' ∈ updateLocksW sp X.wlocks X.ac X.counts Φ t s at hw'
  unfold updateLocksW at hw'
  split at hw'
  · exact Or.inr (Or.inl ⟨w', hw', rfl, rfl, rfl, rfl⟩)
  · rw [LockStore.addLocksWith_eq] at hw'
    obtain ⟨w, hw | ⟨p, -, rfl⟩, h1, h2, h3, h4⟩ := liveLocks_same _ Φ t w' hw'
    · exact Or.inr (Or.inl ⟨w, hw, h1, h2, h3, h4⟩)
    · rcases hp : p.2.1
      · refine Or.inr (Or.inr ⟨?_, h3⟩)
        rw [h1, h2]
        simp [hp]
      · exact Or.inl (h4.trans hp)

open Classical in
theorem wlocks_acOnTickE (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    ∀ w' ∈ (acOnTickE sp E c self X Φ t).1.wlocks,
      w'.lock.fast = true ∨ (∃ w ∈ X.wlocks, SameW w w') ∨
        ((joined sp X.ac t ∧ t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t) ∧
          SlowWriteOf X Φ (sp.slot t - 1) w') := by
  have hΔ := sp.toParams.hΔ
  have hv := movedOrFast_tryVoteE E c self X Φ t
  intro w' hw'
  unfold acOnTickE at hw'
  dsimp only at hw'
  by_cases hj : joined sp X.ac t
  · rw [ite_eq_right (not_not.2 hj)] at hw'
    by_cases hu : t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t
    · have hne : ¬ t = sp.ts (sp.slot t) + sp.Δ := fun h => by linarith [hu.1]
      rw [ite_eq_right hne, ite_eq_left hu] at hw'
      rcases wlocks_updateConfirmationW X Φ t _ w' hw' with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨⟨hj, hu⟩, h⟩)
    · rw [ite_eq_right hu] at hw'
      split_ifs at hw'
      · rcases hv w' hw' with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inl ⟨w', hw', rfl, rfl, rfl, rfl⟩)
  · rw [ite_eq_left hj] at hw'
    exact Or.inr (Or.inl ⟨w', hw', rfl, rfl, rfl, rfl⟩)

end Handlers

/-! ### The calls of a run -/

variable {ro : ReplayOrder sp FGP} {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}
  {tr : ACTrace (evidenceReleaseSA sp FGP ro)}

private theorem lookup_self' {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {B : Blk sp.n FGP}
    (hB : B ∈ Φ.tree) : lookup Φ B.root = some B := by
  cases h : lookup Φ B.root with
  | none => exact absurd ⟨B, hB, rfl⟩ (lookup_eq_none h)
  | some B' =>
    obtain ⟨hB', hr⟩ := lookup_eq_some h
    exact congrArg some (hΦ.coherent.1 hB' hB hr)

private theorem state_succ_of_call {y : Fin sp.n} {i : Nat}
    {ℓ : ACLabel (evidenceReleaseSA sp FGP ro)} (hc : tr.CallAt y i ℓ) :
    tr.state y (i + 1) = tr.post i := by
  have h : tr.node i = y ∧ tr.label i ≠ none := ⟨hc.1, by simp [hc.2]⟩
  simp only [Trace.state]
  rw [ite_eq_left h]

private theorem state_succ_of_not {y : Fin sp.n} {i : Nat}
    (hn : ∀ ℓ : ACLabel (evidenceReleaseSA sp FGP ro), ¬ tr.CallAt y i ℓ) :
    tr.state y (i + 1) = tr.state y i := by
  have h : ¬ (tr.node i = y ∧ tr.label i ≠ none) := by
    rintro ⟨h1, h2⟩
    obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp h2
    exact hn ℓ ⟨h1, hℓ⟩
  simp only [Trace.state]
  rw [ite_eq_right h]

private theorem slot_update_time {σ : Nat} : sp.slot (sp.ts σ + 6 * sp.Δ) = σ + 1 := by
  have hΔ := sp.toParams.hΔ
  have h6 : sp.ts σ + 6 * sp.Δ = sp.ts ((σ + 1 : Nat) : Int) + 2 * sp.Δ := by
    simp only [SAParams.ts]; push_cast; ring
  rw [h6]
  exact slot_of_mem sp (σ + 1) (by linarith) (by simp only [SAParams.ts]; push_cast; linarith)

private theorem projCall_tick {k : (evidenceReleaseSA sp FGP ro).Call} :
    projCall ro k = .tick ↔ k = .tick := by
  cases k <;> simp

/-- An update of the forgotten trace is a tick of the run at the update's time, joined. -/
theorem updateAt_projTrace_iff {y : Fin sp.n} {c σ : Nat}
    {ℓP : ACLabel (goldilocksSA sp FGP ro)} :
    UpdateAt (projTrace tr) y c σ ℓP ↔ ∃ ℓ, tr.CallAt y c ℓ ∧ ℓP = projLabel ℓ ∧
      ℓ.call = .tick ∧ tr.time c = sp.ts σ + 6 * sp.Δ ∧ joined sp (tr.state y c).ac (tr.time c) :=
          by
  constructor
  · rintro ⟨hc, hk, ht, hj⟩
    obtain ⟨ℓ, hc', rfl⟩ := projTrace_callAt.1 hc
    exact ⟨ℓ, hc', rfl, projCall_tick.1 hk, ht, by rwa [projTrace_state] at hj⟩
  · rintro ⟨ℓ, hc, rfl, hk, ht, hj⟩
    refine ⟨projTrace_callAt.2 ⟨ℓ, hc, rfl⟩, by simp [hk], ht, by rwa [projTrace_state]⟩

/-- The update condition of a tick at `t`: joined at `t_{s+1} + 2Δ`, that is an update of `s`. -/
private theorem tickCond_time {t : Time} (h : t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t) :
    t = sp.ts ((sp.slot t - 1 : Nat) : Int) + 6 * sp.Δ := by
  have h1 : ((sp.slot t - 1 : Nat) : Int) = (sp.slot t : Int) - 1 := by omega
  rw [h1]
  conv_lhs => rw [h.1]
  simp only [SAParams.ts]; ring

private theorem updateAt_slot {y : Fin sp.n} {c σ : Nat} {ℓP : ACLabel (goldilocksSA sp FGP ro)}
    (h : UpdateAt (projTrace tr) y c σ ℓP) : sp.slot (tr.time c) = σ + 1 := by
  obtain ⟨-, -, -, -, ht, -⟩ := updateAt_projTrace_iff.1 h
  rw [ht, slot_update_time]

open Classical in
/-- **The saved count of slot `σ`** at cut `i` of an honest node: the count of its latest update
of `σ` since its latest restart, or none, with a restart after every earlier update of `σ`. -/
theorem savedCount_spec (hrun : ACLocalRun (evidenceReleaseSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) (j : Int) :
    (∃ c < i, ∃ (ℓ : ACLabel (evidenceReleaseSA sp FGP ro)) (σ : Nat), (σ : Int) = j ∧
      UpdateAt (projTrace tr) y c σ (projLabel ℓ) ∧
      (tr.state y i).counts j = updateCount sp (tr.state y c).ac ℓ.frame σ ∧
      ∀ k, c < k → k < i → ¬ tr.RestartAt y k ∧
        ∀ (σ' : Nat) ℓ', (σ' : Int) = j → ¬ UpdateAt (projTrace tr) y k σ' ℓ') ∨
    ((tr.state y i).counts j = (fun _ => 0) ∧
      ∀ c < i, ∀ ℓP (σ : Nat), (σ : Int) = j → UpdateAt (projTrace tr) y c σ ℓP →
        ∃ k, c < k ∧ k < i ∧ tr.RestartAt y k) := by
  induction i with
  | zero =>
    refine Or.inr ⟨?_, fun c hc => absurd hc (Nat.not_lt_zero c)⟩
    rw [show tr.state y 0 = tr.init y from rfl, hrun.init y hy]
    rfl
  | succ i ih =>
    by_cases hcall : ∃ ℓ, tr.CallAt y i ℓ
    swap
    · -- no call at `i`
      have hn : ∀ ℓ, ¬ tr.CallAt y i ℓ := fun ℓ h => hcall ⟨ℓ, h⟩
      have hnu : ∀ σ ℓP, ¬ UpdateAt (projTrace tr) y i σ ℓP := fun σ ℓP h => by
        obtain ⟨ℓ, hc, -⟩ := updateAt_projTrace_iff.1 h
        exact hn ℓ hc
      rw [state_succ_of_not hn]
      rcases ih with ⟨c, hc, ℓ, σ, hσ, hu, hv, hk⟩ | ⟨h0, hk⟩
      · refine Or.inl ⟨c, by omega, ℓ, σ, hσ, hu, hv, fun k hck hki => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hki with hki | rfl
        · exact hk k hck hki
        · exact ⟨fun ⟨ℓ', h, _⟩ => hn ℓ' h, fun σ' ℓ' _ h => hnu σ' ℓ' h⟩
      · refine Or.inr ⟨h0, fun c hc ℓP σ hσ hu => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
        · obtain ⟨k, h1, h2, h3⟩ := hk c hc ℓP σ hσ hu
          exact ⟨k, h1, by omega, h3⟩
        · exact absurd hu (hnu σ ℓP)
    obtain ⟨ℓ, hc⟩ := hcall
    have hlabel : ∀ ℓ', tr.CallAt y i ℓ' → ℓ' = ℓ := fun ℓ' h' =>
      Option.some_injective _ (h'.2.symm.trans hc.2)
    have hex := hrun.exec i ℓ hc.2 (hc.1 ▸ hy)
    rw [hc.1, step_eq_stepE] at hex
    have hpost : tr.state y (i + 1) = (stepE sp ro (evidenceStage sp) () y (tr.state y i) ℓ.frame
        (tr.time i) (projCall ro ℓ.call)).1 := by
      rw [state_succ_of_call hc]
      exact (congrArg Prod.fst hex).symm
    -- the update at `i`, if any, is of slot `slot(t_i) − 1`
    have hupd_i : ∀ σ ℓP, UpdateAt (projTrace tr) y i σ ℓP →
        ℓ.call = .tick ∧ joined sp (tr.state y i).ac (tr.time i) ∧
          tr.time i = sp.ts (sp.slot (tr.time i)) + 2 * sp.Δ ∧ 0 < sp.slot (tr.time i) ∧
          sp.slot (tr.time i) - 1 = σ := fun σ ℓP h => by
      obtain ⟨ℓ', hc', -, hk, ht, hj⟩ := updateAt_projTrace_iff.1 h
      obtain rfl := hlabel ℓ' hc'
      have hs := updateAt_slot h
      refine ⟨hk, hj, ?_, by omega, by omega⟩
      rw [hs, ht]; simp only [SAParams.ts]; push_cast; ring
    -- the counts after the call
    have hcnt : (tr.state y (i + 1)).counts =
        if ℓ.call = .restart then (fun _ _ => 0)
        else if ℓ.call = .tick ∧ joined sp (tr.state y i).ac (tr.time i) ∧
          tr.time i = sp.ts (sp.slot (tr.time i)) + 2 * sp.Δ ∧ 0 < sp.slot (tr.time i) then
          saveCount sp (tr.state y i).counts (tr.state y i).ac ℓ.frame (sp.slot (tr.time i) - 1)
        else (tr.state y i).counts := by
      rw [hpost]
      rcases hk : ℓ.call with _ | _ | _ | m | B | _ <;>
        simp only [projCall, reduceCtorEq, ↓reduceIte, false_and, true_and]
      · exact counts_acOnTickE _ _ _ _ _ _
      · exact counts_acProposalE _ _ _ _ _
      · rfl
      · exact counts_acOnMessageE _ _ _ _ _ _ _
      · exact counts_acOnBlockE _ _ _ _ _ _ _
      · exact counts_acRestartE _ _ _ _ _ _ _
    by_cases hr : ℓ.call = .restart
    · -- a restart drops the counts
      rw [ite_eq_left hr] at hcnt
      refine Or.inr ⟨by rw [hcnt], fun c hci ℓP σ hσ hu => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hci with hci | rfl
      · exact ⟨i, hci, Nat.lt_succ_self i, ℓ, hc, hr⟩
      · have := (hupd_i σ ℓP hu).1
        rw [hr] at this
        exact absurd this (by simp)
    rw [ite_eq_right hr] at hcnt
    by_cases hu : ℓ.call = .tick ∧ joined sp (tr.state y i).ac (tr.time i) ∧
        tr.time i = sp.ts (sp.slot (tr.time i)) + 2 * sp.Δ ∧ 0 < sp.slot (tr.time i)
    · rw [ite_eq_left hu] at hcnt
      set σ₀ := sp.slot (tr.time i) - 1
      have hU₀ : UpdateAt (projTrace tr) y i σ₀ (projLabel ℓ) :=
        updateAt_projTrace_iff.2 ⟨ℓ, hc, rfl, hu.1, tickCond_time hu.2.2, hu.2.1⟩
      by_cases hj : j = (σ₀ : Int)
      · subst hj
        refine Or.inl ⟨i, Nat.lt_succ_self i, ℓ, σ₀, rfl, hU₀, ?_, fun k h1 h2 => by omega⟩
        rw [hcnt, saveCount, Function.update_self]
      · have hcj : (tr.state y (i + 1)).counts j = (tr.state y i).counts j := by
          rw [hcnt, saveCount, Function.update_of_ne hj]
        have hnot : ∀ (σ' : Nat) ℓ', (σ' : Int) = j → ¬ UpdateAt (projTrace tr) y i σ' ℓ' :=
          fun σ' ℓ' hσ' h => hj (by rw [← hσ', ← (hupd_i σ' ℓ' h).2.2.2.2])
        rw [hcj]
        rcases ih with ⟨c, hci, ℓc, σ, hσ, hU, hv, hk⟩ | ⟨h0, hk⟩
        · refine Or.inl ⟨c, by omega, ℓc, σ, hσ, hU, hv, fun k h1 h2 => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
          · exact hk k h1 h2
          · exact ⟨fun ⟨ℓ', h', hr'⟩ => hr (hlabel ℓ' h' ▸ hr'), hnot⟩
        · refine Or.inr ⟨h0, fun c hci ℓP σ hσ hU => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hci with hci | rfl
          · obtain ⟨k, h1, h2, h3⟩ := hk c hci ℓP σ hσ hU
            exact ⟨k, h1, by omega, h3⟩
          · exact absurd hU (hnot σ ℓP hσ)
    · rw [ite_eq_right hu] at hcnt
      have hnot : ∀ (σ' : Nat) ℓ', ¬ UpdateAt (projTrace tr) y i σ' ℓ' := fun σ' ℓ' h => by
        obtain ⟨h1, h2, h3, h4, -⟩ := hupd_i σ' ℓ' h
        exact hu ⟨h1, h2, h3, h4⟩
      rw [hcnt]
      rcases ih with ⟨c, hci, ℓc, σ, hσ, hU, hv, hk⟩ | ⟨h0, hk⟩
      · refine Or.inl ⟨c, by omega, ℓc, σ, hσ, hU, hv, fun k h1 h2 => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
        · exact hk k h1 h2
        · exact ⟨fun ⟨ℓ', h', hr'⟩ => hr (hlabel ℓ' h' ▸ hr'), fun σ' ℓ' _ => hnot σ' ℓ'⟩
      · refine Or.inr ⟨h0, fun c hci ℓP σ hσ hU => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hci with hci | rfl
        · obtain ⟨k, h1, h2, h3⟩ := hk c hci ℓP σ hσ hU
          exact ⟨k, h1, by omega, h3⟩
        · exact absurd hU (hnot σ ℓP)

/-- **The weight of a stored slow lock** of an honest node: the slow weight of the update that
wrote it, from the counts saved there. -/
theorem slowLock_written (hrun : ACLocalRun (evidenceReleaseSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) :
    ∀ w ∈ (tr.state y i).wlocks, w.lock.fast = false →
      ∃ c < i, ∃ ℓ : ACLabel (evidenceReleaseSA sp FGP ro),
        UpdateAt (projTrace tr) y c w.lock.slot (projLabel ℓ) ∧
        SlowWriteOf (tr.state y c) ℓ.frame w.lock.slot w := by
  induction i with
  | zero =>
    intro w hw
    rw [show tr.state y 0 = tr.init y from rfl, hrun.init y hy] at hw
    exact absurd hw (Set.notMem_empty w)
  | succ i ih =>
    by_cases hcall : ∃ ℓ, tr.CallAt y i ℓ
    swap
    · intro w hw hf
      rw [state_succ_of_not fun ℓ h => hcall ⟨ℓ, h⟩] at hw
      obtain ⟨c, hc, ℓ, h1, h2⟩ := ih w hw hf
      exact ⟨c, by omega, ℓ, h1, h2⟩
    obtain ⟨ℓ, hc⟩ := hcall
    have hex := hrun.exec i ℓ hc.2 (hc.1 ▸ hy)
    rw [hc.1, step_eq_stepE] at hex
    intro w' hw' hf
    rw [state_succ_of_call hc] at hw'
    replace hw' : w' ∈ (stepE sp ro (evidenceStage sp) () y (tr.state y i) ℓ.frame (tr.time i)
        (projCall ro ℓ.call)).1.wlocks := by rw [hex]; exact hw'
    -- a moved lock keeps its write
    have hmoved : (∃ w ∈ (tr.state y i).wlocks, SameW w w') →
        ∃ c < i + 1, ∃ ℓ' : ACLabel (evidenceReleaseSA sp FGP ro),
          UpdateAt (projTrace tr) y c w'.lock.slot (projLabel ℓ') ∧
          SlowWriteOf (tr.state y c) ℓ'.frame w'.lock.slot w' := by
      rintro ⟨w, hw, h1, h2, h3, h4⟩
      obtain ⟨c, hci, ℓ', hu, hsw1, -⟩ := ih w hw (h4.symm.trans hf)
      refine ⟨c, by omega, ℓ', by rw [h3]; exact hu, ?_, rfl⟩
      rw [h1, hsw1, h2, h3]
    have hmf : MovedOrFast (tr.state y i).wlocks
        (stepE sp ro (evidenceStage sp) () y (tr.state y i) ℓ.frame (tr.time i)
          (projCall ro ℓ.call)).1.wlocks ∨ ℓ.call = .tick := by
      rcases hk : ℓ.call with _ | _ | _ | m | B | _ <;> simp only [projCall, or_true]
      · exact Or.inl (movedOrFast_acProposalE _ _ _ _ _)
      · exact Or.inl (MovedOrFast.refl _)
      · exact Or.inl (movedOrFast_acOnMessageE _ _ _ _ _ _ _)
      · exact Or.inl (movedOrFast_acOnBlockE _ _ _ _ _ _ _)
      · exact Or.inl (movedOrFast_acRestartE _ _ _ _ _ _ _)
    rcases hmf with hmf | hk
    · rcases hmf w' hw' with h | h
      · rw [hf] at h; exact absurd h (by simp)
      · exact hmoved h
    · rw [hk] at hw'
      rcases wlocks_acOnTickE _ _ y (tr.state y i) ℓ.frame (tr.time i) w' hw' with h | h | ⟨hu, h⟩
      · rw [hf] at h; exact absurd h (by simp)
      · exact hmoved h
      · refine ⟨i, Nat.lt_succ_self i, ℓ, ?_, by rw [h.2]; exact h⟩
        rw [h.2]
        exact updateAt_projTrace_iff.2 ⟨ℓ, hc, rfl, hk, tickCond_time hu.2, hu.1⟩

/-- **Lemma O, the weight half.** Let `w` be a stored slow lock of an honest node `y` at cut `i`,
and `σ` one of its formation slots (`slot(w) − k < σ ≤ slot(w)`). If `y` updated `σ` before `i`
and did not restart since, and every update of `σ` by `y` before `i` counts at least `|S|`
validators for the block of root `Y.root`, then `|S| ≤ W(Y)`, for `Y` at or below the lock's
origin in the frame of every update of `w`'s slot by `y`.

The premises are sufficient, uniformly quantified arming facts, not minimal ones: the score fact
at every update of `σ` by `y` before `i`, the origin fact at every update of `w`'s slot by `y`
before `i`, and no restart of `y` from an update of `σ` through `i`. -/
theorem card_le_slowWeight (hrun : ACLocalRun (evidenceReleaseSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {w : WLock} (hw : w ∈ (tr.state y i).wlocks)
    (hf : w.lock.fast = false) {σ : Nat} (hσ₁ : (w.lock.slot : Int) - sp.k < σ)
    (hσ₂ : σ ≤ w.lock.slot) {Y : Blk sp.n FGP} {S : Set (Fin sp.n)}
    (hupd : ∃ c₁ < i, ∃ ℓ₁, UpdateAt (projTrace tr) y c₁ σ ℓ₁ ∧
      ∀ k, c₁ < k → k < i → ¬ tr.RestartAt y k)
    (hS : ∀ c < i, ∀ ℓP, UpdateAt (projTrace tr) y c σ ℓP →
      ∃ Y' ∈ ℓP.frame.tree, Y'.root = Y.root ∧
        S.ncard ≤ confirmationScore sp ((projTrace tr).state y c) ℓP.frame σ Y')
    (hY : ∀ c < i, ∀ ℓP, UpdateAt (projTrace tr) y c w.lock.slot ℓP →
      ∃ Y₀ ∈ ℓP.frame.tree, Y₀.root = Y.root ∧ AncR ℓP.frame Y₀ w.origin) :
    S.ncard ≤ w.weight Y.root := by
  have hU := localRunU_projTrace hrun
  obtain ⟨c₀, hc₀, ℓ₀, hu₀, hw₁, -⟩ := slowLock_written hrun hy i w hw hf
  have hΦ₀ := (frameIn_of_callAtU hU hy hu₀.1).1
  obtain ⟨Y₀, hY₀, hY₀r, hY₀o⟩ := hY c₀ hc₀ _ hu₀
  set s := w.lock.slot
  -- the count the update saves for `σ` is at most the weight at `Y₀`
  have hle := le_slowWeight hΦ₀ (saveCount sp (tr.state y c₀).counts (tr.state y c₀).ac ℓ₀.frame s)
    hY₀ hY₀o (s := s) (j := s - σ) (by omega)
  rw [show ((s : Int) - ((s - σ : Nat) : Int)) = σ by omega, ← hw₁, hY₀r] at hle
  refine le_trans ?_ hle
  -- the count saved for `σ` at the update `c₀`
  have hcount : ∀ c < i, ∀ ℓ' : ACLabel (evidenceReleaseSA sp FGP ro),
      UpdateAt (projTrace tr) y c σ (projLabel ℓ') →
      S.ncard ≤ updateCount sp (tr.state y c).ac ℓ'.frame σ Y.root := by
    intro c hc ℓ' hu
    obtain ⟨Y', hY', hY'r, hle'⟩ := hS c hc _ hu
    have hΦ' := (frameIn_of_callAtU hU hy hu.1).1
    simp only [updateCount, ← hY'r, lookup_self' hΦ' hY', Option.map_some, Option.getD_some]
    rwa [projTrace_state] at hle'
  rcases hσ₂.lt_or_eq with hlt | heq
  · rw [saveCount, Function.update_of_ne (by omega)]
    rcases savedCount_spec hrun hy c₀ σ with ⟨c, hc, ℓ', σ', hσ', hu, hv, -⟩ | ⟨-, hk⟩
    · obtain rfl : σ' = σ := by omega
      rw [hv]
      exact hcount c (by omega) ℓ' hu
    · -- the update `c₁` of `σ` is before `c₀`, with no restart after it
      obtain ⟨c₁, hc₁, ℓ₁, hu₁, hnr⟩ := hupd
      have hc₁₀ : c₁ < c₀ := by
        by_contra h
        have := hU.time_mono (not_lt.1 h)
        obtain ⟨-, -, ht₁, -⟩ := hu₁
        obtain ⟨-, -, ht₀, -⟩ := hu₀
        change tr.time c₀ ≤ tr.time c₁ at this
        change tr.time c₁ = _ at ht₁
        change tr.time c₀ = _ at ht₀
        have hΔ := sp.toParams.hΔ
        have : sp.ts σ < sp.ts s := (ts_lt_iff sp).2 (by exact_mod_cast hlt)
        linarith
      obtain ⟨k, h1, h2, h3⟩ := hk c₁ hc₁₀ ℓ₁ σ rfl hu₁
      exact absurd h3 (hnr k h1 (by omega))
  · subst heq
    rw [saveCount, Function.update_self]
    exact hcount c₀ hc₀ ℓ₀ hu₀

end Consensus.Goldilocks.EvidenceRelease

end
