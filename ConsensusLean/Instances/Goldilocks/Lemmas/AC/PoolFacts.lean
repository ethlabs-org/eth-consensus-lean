module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Goldilocks SA: pools and stamps at reachable states (A0.1, A0.7, A0.9)

The ACBase statements that ACSteps does not use: admission slots, stable stamps and carried votes
(A0.1), what a joined node kept at its restarts (A0.7) and the proposal payload (A0.9); and the
properties every call other than the restart keeps (`VoteClosed`). Stable resolution (A0.2) and
the merged view's opponents (A0.3) are in `Resolution`. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-- A vote is in the pool of an integer slot `s` iff `s ≥ 0` and it is in the pool of slot
`s.toNat`; the pool of a negative slot is empty. -/
theorem SAState.mem_poolAt {n : Nat} {A : SAState n} {s : Int} {v : Vote n} :
    v ∈ A.poolAt s ↔ 0 ≤ s ∧ v ∈ A.pool s.toNat := by
  unfold SAState.poolAt
  split_ifs with hs
  · exact ⟨fun h => (List.not_mem_nil h).elim, fun h => absurd h.1 (not_le.mpr hs)⟩
  · exact ⟨fun h => ⟨not_lt.mp hs, h⟩, And.right⟩

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

theorem optimistic_pool_eq (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).pool = A.pool := by
  unfold optimisticConfirmation
  split
  · rfl
  · exact updateLatestConfirmed_pool_eq _ _ _

theorem updateConfirmation_pool_eq (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (s : Nat) : (updateConfirmation sp A Φ t s).pool = A.pool := by
  unfold updateConfirmation
  dsimp only
  split
  · rfl
  · split_ifs <;> first | rfl | exact updateLatestConfirmed_pool_eq _ _ _

theorem admits_tryVote (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    Admits A (tryVote sp self A Φ t).1 t := by
  unfold tryVote
  dsimp only
  split_ifs
  · exact Admits.refl _ _
  · exact Admits.refl _ _
  all_goals try exact Admits.of_pool_eq rfl
  all_goals
    refine Admits.trans ?_ (Admits.of_pool_eq (optimistic_pool_eq _ _ _))
  all_goals
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
    locks := A.locks, latestConfirmed := A.latestConfirmed, restartTime := (t : WithBot Time),
    mayVote := A.mayVote }
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

theorem Grows.refl (A : SAState sp.n) : Grows A A := fun _ _ h => h

theorem Grows.trans {A B C : SAState sp.n} (h₁ : Grows A B) (h₂ : Grows B C) : Grows A C :=
  fun σ x hx => h₂ σ x (h₁ σ x hx)

theorem Grows.of_pool_eq {A A' : SAState sp.n} (h : A'.pool = A.pool) : Grows A A' :=
  fun _ _ hx => h ▸ hx

/-- Membership form of `Grows`, for other modules. -/
theorem Grows.mem {A A' : SAState sp.n} (h : Grows A A') {σ : Nat} {x : Vote sp.n}
    (hx : x ∈ A.pool σ) : x ∈ A'.pool σ :=
  h σ x hx

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
  all_goals try exact Grows.of_pool_eq rfl
  all_goals
    refine Grows.trans ?_ (Grows.of_pool_eq (optimistic_pool_eq _ _ _))
  all_goals
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

/-! ### Stamps between restarts

`VOK A`: a vote with a stamp is in its pool. `Keep A A'`: the pools grow and the stamps of held
votes stay. Every call other than a restart keeps `VOK` and satisfies `Keep`; a restart keeps
`VOK`. -/

section Stamps

variable {sp} {FGP : Type}

/-- A vote with a stamp (not `+∞`) is held in the pool of its slot. -/
private def VOK (A : SAState sp.n) : Prop := ∀ x, A.voteStamp x ≠ ⊤ → x ∈ A.pool x.slot

/-- The pools grow and the stamps of the votes held in `A` stay. -/
private def Keep (A A' : SAState sp.n) : Prop :=
  Grows A A' ∧ ∀ x ∈ A.pool x.slot, A'.voteStamp x = A.voteStamp x

private theorem Keep.trans {A B C : SAState sp.n} (h₁ : Keep A B) (h₂ : Keep B C) : Keep A C :=
  ⟨h₁.1.trans h₂.1, fun x hx => (h₂.2 x (h₁.1 _ x hx)).trans (h₁.2 x hx)⟩

private theorem Keep.refl (A : SAState sp.n) : Keep A A := ⟨fun _ _ h => h, fun _ _ => rfl⟩

private theorem Keep.of_eq {A A' : SAState sp.n} (hp : A'.pool = A.pool)
    (hv : A'.voteStamp = A.voteStamp) : Keep A A' :=
  ⟨Grows.of_pool_eq hp, fun x _ => by rw [hv]⟩

private theorem VOK.of_eq {A A' : SAState sp.n} (h : VOK A) (hp : A'.pool = A.pool)
    (hv : A'.voteStamp = A.voteStamp) : VOK A' := fun x hx => by
  rw [hp]; exact h x (by rwa [hv] at hx)

private theorem admitVote_vok_keep {A : SAState sp.n} (h : VOK A) (t : Time) (v : Vote sp.n) :
    VOK (admitVote sp A t v) ∧ Keep A (admitVote sp A t v) := by
  refine ⟨fun x hx => ?_, grows_admitVote A t v, fun x hx => ?_⟩
  · by_cases hxv : x = v
    · subst hxv
      unfold admitVote at hx ⊢
      split_ifs at hx ⊢ with h₁
      · exact h x hx
      · exact h x hx
      · simp only [Function.update_apply, ite_true]
        exact List.mem_append_right _ (List.mem_singleton_self _)
    · have hx' : A.voteStamp x ≠ ⊤ := by
        unfold admitVote at hx
        split_ifs at hx
        · exact hx
        · exact hx
        · simpa only [Function.update_apply, hxv, ite_false] using hx
      exact grows_admitVote A t v _ x (h x hx')
  · unfold admitVote
    split_ifs with h₁
    · rfl
    · rfl
    · simp only [Function.update_apply]
      split_ifs with hxv
      · subst hxv; exact absurd hx (by tauto)
      · rfl

private theorem updateLatestConfirmed_vs (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (C : Blk sp.n FGP) : (updateLatestConfirmed sp A Φ C).voteStamp = A.voteStamp := by
  unfold updateLatestConfirmed
  split_ifs <;> rfl

private theorem optimistic_vs (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).voteStamp = A.voteStamp := by
  unfold optimisticConfirmation
  split
  · rfl
  · exact updateLatestConfirmed_vs _ _ _

private theorem updateConfirmation_vs (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (s : Nat) : (updateConfirmation sp A Φ t s).voteStamp = A.voteStamp := by
  unfold updateConfirmation
  dsimp only
  split
  · rfl
  · split_ifs <;> first | rfl | exact updateLatestConfirmed_vs _ _ _

private theorem optimistic_vok_keep {A : SAState sp.n} (h : VOK A) (Φ : Frm sp.n FGP) (t : Time) :
    VOK (optimisticConfirmation sp A Φ t) ∧ Keep A (optimisticConfirmation sp A Φ t) :=
  ⟨h.of_eq (optimistic_pool_eq _ _ _) (optimistic_vs _ _ _),
    Keep.of_eq (optimistic_pool_eq _ _ _) (optimistic_vs _ _ _)⟩

private theorem tryVote_vok_keep (self : Fin sp.n) {A : SAState sp.n} (h : VOK A) (Φ : Frm sp.n FGP)
    (t : Time) : VOK (tryVote sp self A Φ t).1 ∧ Keep A (tryVote sp self A Φ t).1 := by
  unfold tryVote
  dsimp only
  have key : ∀ {A₂ : SAState sp.n} (v : Vote sp.n), A₂.pool = A.pool →
      A₂.voteStamp = A.voteStamp → VOK (optimisticConfirmation sp (admitVote sp A₂ t v) Φ t) ∧
        Keep A (optimisticConfirmation sp (admitVote sp A₂ t v) Φ t) := fun v hp hv =>
    ⟨(optimistic_vok_keep (admitVote_vok_keep (h.of_eq hp hv) t v).1 Φ t).1,
      (Keep.of_eq hp hv).trans ((admitVote_vok_keep (h.of_eq hp hv) t v).2.trans
        (optimistic_vok_keep (admitVote_vok_keep (h.of_eq hp hv) t v).1 Φ t).2)⟩
  have keyNoVote : ∀ (A₂ : SAState sp.n), A₂.pool = A.pool → A₂.voteStamp = A.voteStamp →
      VOK A₂ ∧ Keep A A₂ := by
    intro A₂ hp hv
    exact ⟨h.of_eq hp hv, Keep.of_eq hp hv⟩
  split_ifs
  · exact ⟨h, Keep.refl _⟩
  · exact ⟨h, Keep.refl _⟩
  all_goals
    first
    | exact key _ rfl rfl
    | exact keyNoVote _ rfl rfl

private theorem fold_admit_vok_keep (t : Time) (l : List (Vote sp.n)) {A : SAState sp.n}
    (h : VOK A) :
    VOK (l.foldl (fun A v => admitVote sp A t v) A) ∧
      Keep A (l.foldl (fun A v => admitVote sp A t v) A) := by
  induction l generalizing A with
  | nil => exact ⟨h, Keep.of_eq rfl rfl⟩
  | cons v l ih =>
    obtain ⟨h₁, k₁⟩ := admitVote_vok_keep h t v
    obtain ⟨h₂, k₂⟩ := ih h₁
    exact ⟨h₂, k₁.trans k₂⟩

private theorem acOnBlock_vok_keep (self : Fin sp.n) {A : SAState sp.n} (h : VOK A)
    (Φ : Frm sp.n FGP) (t : Time) (B : Blk sp.n FGP) :
    VOK (acOnBlock sp self A Φ t B).1 ∧ Keep A (acOnBlock sp self A Φ t B).1 := by
  unfold acOnBlock blockReceipt
  obtain ⟨h₁, k₁⟩ := fold_admit_vok_keep t (blockVotes B)
    (A := { A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) })
    (h.of_eq rfl rfl)
  obtain ⟨h₂, k₂⟩ := optimistic_vok_keep h₁ Φ t
  obtain ⟨h₃, k₃⟩ := tryVote_vok_keep self h₂ Φ t
  exact ⟨h₃, (Keep.of_eq rfl rfl).trans (k₁.trans (k₂.trans k₃))⟩

private theorem acOnMessage_vok_keep (self : Fin sp.n) {A : SAState sp.n} (h : VOK A)
    (Φ : Frm sp.n FGP) (t : Time) (v : Vote sp.n) :
    VOK (acOnMessage sp self A Φ t v).1 ∧ Keep A (acOnMessage sp self A Φ t v).1 := by
  unfold acOnMessage
  obtain ⟨h₁, k₁⟩ := admitVote_vok_keep h t v
  obtain ⟨h₂, k₂⟩ := optimistic_vok_keep h₁ Φ t
  obtain ⟨h₃, k₃⟩ := tryVote_vok_keep self h₂ Φ t
  exact ⟨h₃, k₁.trans (k₂.trans k₃)⟩

private theorem acOnTick_vok_keep (self : Fin sp.n) {A : SAState sp.n} (h : VOK A)
    (Φ : Frm sp.n FGP) (t : Time) :
    VOK (acOnTick sp self A Φ t).1 ∧ Keep A (acOnTick sp self A Φ t).1 := by
  unfold acOnTick
  dsimp only
  have hu : ∀ {B : SAState sp.n} (s : Nat), VOK B →
      VOK (updateConfirmation sp B Φ t s) ∧ Keep B (updateConfirmation sp B Φ t s) :=
    fun s hB => ⟨hB.of_eq (updateConfirmation_pool_eq _ _ _ _) (updateConfirmation_vs _ _ _ _),
      Keep.of_eq (updateConfirmation_pool_eq _ _ _ _) (updateConfirmation_vs _ _ _ _)⟩
  have hv := tryVote_vok_keep self h Φ t
  split_ifs
  all_goals first
    | with_reducible exact ⟨h, Keep.refl _⟩
    | with_reducible exact hv
    | with_reducible exact hu _ h
    | with_reducible exact ⟨(hu _ hv.1).1, hv.2.trans (hu _ hv.1).2⟩

private theorem acRestart_vok (ro : ReplayOrder sp FGP) (self : Fin sp.n) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : VOK (acRestart sp ro self A Φ t).1 := by
  unfold acRestart
  generalize ro.order t Φ = l
  suffices h : ∀ (l : List (Blk sp.n FGP)) (acc : SAState sp.n × List (Em sp FGP)), VOK acc.1 →
      VOK (l.foldl (fun acc B => let r := acOnBlock sp self acc.1 Φ t B;
        (r.1, acc.2 ++ r.2)) acc).1 from
    h l _ fun x hx => absurd rfl hx
  intro l
  induction l with
  | nil => exact fun _ h => h
  | cons B l ih =>
    intro acc h
    simp only [List.foldl_cons]
    exact ih _ (acOnBlock_vok_keep self h Φ t B).1

/-- The stamp invariant at a reachable state with frame `Φ`, inside `U`: held stamps, and every
stamped root names a block of `U` that is in the tree or does not extend `Φ.F`. -/
private structure SInv (U : Set (Blk sp.n FGP)) (A : SAState sp.n) (Φ : Frm sp.n FGP) : Prop where
  vok : VOK A
  block : ∀ r, A.blockStamp r ≠ ⊤ → ∃ X ∈ U, X.root = r ∧ (X ∈ Φ.tree ∨ ¬ Anc U Φ.F X)
  frame : FrameOK Φ ∧ Φ.tree ⊆ U
  genesis : ∃ G ∈ U, G.root = sp.genesisRoot ∧ G.parent = none

private theorem acProposal_pv (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acProposal sp A Φ t).1.pool = A.pool ∧ (acProposal sp A Φ t).1.voteStamp = A.voteStamp := by
  unfold acProposal
  split_ifs <;> exact ⟨rfl, rfl⟩

private theorem acToFG_pv (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acToFG sp A Φ t).1.pool = A.pool ∧ (acToFG sp A Φ t).1.voteStamp = A.voteStamp := by
  unfold acToFG
  split_ifs
  · split
    · exact ⟨rfl, rfl⟩
    · split_ifs <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- Every call other than the restart keeps the held stamps and grows the pools. -/
private theorem step_vok_keep (ro : ReplayOrder sp FGP) (self : Fin sp.n) {A : SAState sp.n}
    (h : VOK A) (Φ : Frm sp.n FGP) (t : Time) {c : (goldilocksSA sp FGP ro).Call}
    (hc : c ≠ .restart) :
    VOK ((goldilocksSA sp FGP ro).step self A Φ t c).1 ∧
      Keep A ((goldilocksSA sp FGP ro).step self A Φ t c).1 := by
  cases c with
  | tick => exact acOnTick_vok_keep self h Φ t
  | message m => exact acOnMessage_vok_keep self h Φ t m
  | block B => exact acOnBlock_vok_keep self h Φ t B
  | restart => exact absurd rfl hc
  | proposal =>
    exact ⟨h.of_eq (acProposal_pv A Φ t).1 (acProposal_pv A Φ t).2,
      Keep.of_eq (acProposal_pv A Φ t).1 (acProposal_pv A Φ t).2⟩
  | toFG =>
    exact ⟨h.of_eq (acToFG_pv A Φ t).1 (acToFG_pv A Φ t).2,
      Keep.of_eq (acToFG_pv A Φ t).1 (acToFG_pv A Φ t).2⟩

/-- `P` is closed under admission and under every change that keeps the pools and the vote
stamps: then every call other than the restart keeps it (`VoteClosed.step`). -/
structure VoteClosed (P : SAState sp.n → Prop) : Prop where
  admit : ∀ A t v, P A → P (admitVote sp A t v)
  congr : ∀ A A' : SAState sp.n, A'.pool = A.pool → A'.voteStamp = A.voteStamp → P A → P A'

theorem VoteClosed.tryVote {P : SAState sp.n → Prop} (hP : VoteClosed P) (self : Fin sp.n)
    {A : SAState sp.n} (Φ : Frm sp.n FGP) (t : Time) (h : P A) : P (tryVote sp self A Φ t).1 := by
  have key : ∀ {A₂ : SAState sp.n} (v : Vote sp.n), A₂.pool = A.pool →
      A₂.voteStamp = A.voteStamp → P (optimisticConfirmation sp (admitVote sp A₂ t v) Φ t) :=
    fun v hp hv => hP.congr _ _ (optimistic_pool_eq _ _ _) (optimistic_vs _ _ _)
      (hP.admit _ _ _ (hP.congr _ _ hp hv h))
  unfold SA.tryVote
  dsimp only
  split_ifs
  · exact h
  · exact h
  all_goals
    first
    | exact key _ rfl rfl
    | exact hP.congr A _ rfl rfl h

theorem VoteClosed.acOnBlock {P : SAState sp.n → Prop} (hP : VoteClosed P) (self : Fin sp.n)
    {A : SAState sp.n} (Φ : Frm sp.n FGP) (t : Time) (B : Blk sp.n FGP) (h : P A) :
    P (SA.acOnBlock sp self A Φ t B).1 := by
  unfold SA.acOnBlock blockReceipt
  refine hP.tryVote self Φ t (hP.congr _ _ (optimistic_pool_eq _ _ _) (optimistic_vs _ _ _) ?_)
  have h₀ : P { A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) } :=
    hP.congr A _ rfl rfl h
  generalize { A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) } = A₀ at h₀
  induction blockVotes B generalizing A₀ with
  | nil => exact h₀
  | cons v l ih => exact ih _ (hP.admit _ _ _ h₀)

theorem VoteClosed.step {P : SAState sp.n → Prop} (hP : VoteClosed P) (ro : ReplayOrder sp FGP)
    (self : Fin sp.n) {A : SAState sp.n} (Φ : Frm sp.n FGP) (t : Time)
    {c : (goldilocksSA sp FGP ro).Call} (hc : c ≠ .restart) (h : P A) :
    P ((goldilocksSA sp FGP ro).step self A Φ t c).1 := by
  cases c with
  | block B => exact hP.acOnBlock self Φ t B h
  | message m =>
    exact hP.tryVote self Φ t (hP.congr _ _ (optimistic_pool_eq _ _ _) (optimistic_vs _ _ _)
      (hP.admit _ _ _ h))
  | restart => exact absurd rfl hc
  | proposal => exact hP.congr _ _ (acProposal_pv A Φ t).1 (acProposal_pv A Φ t).2 h
  | toFG => exact hP.congr _ _ (acToFG_pv A Φ t).1 (acToFG_pv A Φ t).2 h
  | tick =>
    have hu : ∀ {B : SAState sp.n} (s : Nat), P B → P (updateConfirmation sp B Φ t s) :=
      fun s hB =>
        hP.congr _ _ (updateConfirmation_pool_eq _ _ _ _) (updateConfirmation_vs _ _ _ _) hB
    have hv := hP.tryVote self Φ t h
    change P (acOnTick sp self A Φ t).1
    unfold acOnTick
    dsimp only
    split_ifs
    all_goals first
      | with_reducible exact h
      | with_reducible exact hv
      | with_reducible exact hu _ h
      | with_reducible exact hu _ hv

/-- Pools only grow outside a restart. -/
theorem voteClosed_grows (A₀ : SAState sp.n) : VoteClosed (Grows A₀) :=
  ⟨fun A t v h => h.trans (grows_admitVote A t v), fun _ _ hp _ h => h.trans (Grows.of_pool_eq hp)⟩

end Stamps

/-- **A0.1, admission slots.** -/
theorem admission_slots : AdmissionSlots sp := by
  intro FGP ro self A Φ' t c
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
    split_ifs at hx
    · split at hx
      · exact hx
      · split_ifs at hx <;> exact hx
    · exact hx

/-- The votes of a block received at `t`, of slot `slot(t) − 1` or `slot(t)`, are held after
`ac_on_block`, or their validators equivocate there. -/
theorem acOnBlock_held {FGP : Type} (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (B : Blk sp.n FGP)
    (hrange : ∀ v ∈ blockVotes B, (sp.slot t : Int) - 1 ≤ v.slot ∧ v.slot ≤ sp.slot t) :
    ∀ v ∈ blockVotes B, v ∈ (acOnBlock sp self A Φ t B).1.pool v.slot ∨
      v.val ∈ equivocators {x | x ∈ (acOnBlock sp self A Φ t B).1.pool v.slot} := by
  intro v hv
  have hrec := fold_admit_held t (blockVotes B) hrange
    { A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) } v hv
  have hg : Grows (blockReceipt sp A t B) (acOnBlock sp self A Φ t B).1 := by
    unfold acOnBlock
    exact (Grows.of_pool_eq (optimistic_pool_eq _ _ _)).trans (grows_tryVote _ _ _ _)
  exact held_of_grows hg hrec

/-- **A0.1, carried votes.** -/
theorem carried_votes : CarriedVotes sp := by
  intro FGP self A Φ' t B hpay hBs
  dsimp only
  intro v hv hnot
  refine (acOnBlock_held sp self A Φ' t B (fun v hv => ?_) v hv).resolve_left hnot
  have := hpay.1 v hv
  omega

/-- **A0.9 from a start `s₀` with empty pools** (the initial state, or a start that differs from
it only in `mayVote`). The payload of a proposal at `t_σ` is the slot-`(σ−1)` vote view of the
pool, whose votes are of slot `σ − 1` (the pool form, kept by every call) and whose support is
among its votes. -/
theorem proposal_payload_valid_from {FGP : Type} {ro : ReplayOrder sp FGP}
    {s₀ : (goldilocksSA sp FGP ro).State} (h₀ : ∀ σ, (s₀ : SAState sp.n).pool σ = [])
    (self : Fin sp.n) (U : Set (Blk sp.n FGP)) (A : (goldilocksSA sp FGP ro).State)
    (Φ : (goldilocksSA sp FGP ro).Frm) (t₀ : Time)
    (hr : (goldilocksSA sp FGP ro).ReachableAtFrom s₀ self U A Φ t₀) :
    ∀ σ : Nat, t₀ ≤ sp.toParams.slotTime σ → ∀ d p,
      ((goldilocksSA sp FGP ro).proposal A Φ (sp.toParams.slotTime σ)).2 = some (d, p) →
      ∀ B : Blk sp.n FGP, B.slot = σ → B.acPayload = p → validPayload B := by
  have hpool : ∀ σ, (∀ m ∈ (A : SAState sp.n).pool σ, m.slot = σ) ∧
      ∀ x : Fin sp.n,
        (((A : SAState sp.n).pool σ).filter (fun m => m.val = x)).dedup.length ≤ 2 := by
    induction hr with
    | init => intro σ; simp [h₀]
    | step c _ _ _ ih => exact step_pool_cap ro self _ _ _ c ih
  intro σ _ d p hp B hBs hBp
  have hσ : sp.slot (sp.toParams.slotTime σ) = σ := by
    rw [sp.slotTime_eq]
    exact slot_of_mem sp σ (by simp [SAParams.ts]) (by
      simp only [SAParams.ts]; push_cast; have := sp.toParams.hΔ; linarith)
  change (acProposal sp A Φ (sp.toParams.slotTime σ)).2 = some (d, p) at hp
  unfold acProposal at hp
  split_ifs at hp
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hp)
  rw [hσ] at *
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · simp only [blockVotes, hBp, voteViewList, List.mem_filter, SAState.poolAt] at hv
    split_ifs at hv with hneg
    · simp at hv
    · have := (hpool _).1 v hv.1
      omega
  · simp only [blockSupport, blockVotes, hBp, voteViewList, List.mem_filter] at hv ⊢
    exact hv.1

/-- **A0.9.** `proposal_payload_valid_from` at the initial state. -/
theorem proposal_payload_valid : ProposalPayloadValid sp :=
  fun _ _ self U _ A Φ t₀ hr => proposal_payload_valid_from sp (fun _ => rfl) self U A Φ t₀ hr

/-- At a reachable state, every pool vote is of a slot at most the slot of the last call's time
(admission at `t` takes votes of slot `slot(t) − 1` or `slot(t)`, and calls are at nondecreasing
times from `0`). -/
theorem pool_slot_le {FGP : Type} {ro : ReplayOrder sp FGP} {self : Fin sp.n}
    {U : Set (Blk sp.n FGP)} {A : (goldilocksSA sp FGP ro).State}
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
    rcases admission_slots sp FGP ro self A Φ' t' c σ x hx with
      ⟨hx, -⟩ | hx | hx
    · exact le_trans (hle σ x hx) (slot_mono sp h0 ht)
    · omega
    · omega

/-- The stamp invariant holds at every reachable state. -/
private theorem sinv_of_reachable {FGP : Type} {ro : ReplayOrder sp FGP} {self : Fin sp.n}
    {U : Set (Blk sp.n FGP)} (hU : Coherent U) {A : (goldilocksSA sp FGP ro).State}
    {Φ : (goldilocksSA sp FGP ro).Frm} {t₀ : Time}
    (h : (goldilocksSA sp FGP ro).ReachableAt self U A Φ t₀) : SInv U A Φ := by
  induction h with
  | init Φ hi hf =>
    obtain ⟨htree, hroot, -, hpar, -⟩ := hi
    have hFt : Φ.F ∈ Φ.tree := htree ▸ rfl
    refine ⟨fun x hx => absurd rfl hx, fun r hr => ?_, hf, ⟨Φ.F, hf.2 hFt, hroot, hpar⟩⟩
    have hg : r = sp.genesisRoot := by
      by_contra hne
      refine hr ?_
      change (SAState.initial sp.genesisRoot : SAState sp.n).blockStamp r = ⊤
      simp [SAState.initial, hne]
    exact ⟨Φ.F, hf.2 hFt, hroot.trans hg.symm, Or.inl hFt⟩
  | @step A Φ Φ' t t' c hr ht hok ih =>
    have h0 : 0 ≤ t' := (pool_slot_le sp hr).1.trans ht
    have hΦ' := hok.1
    have hret := callOK_retains sp hU ih.frame hok
    have hkeep : ∀ X, (X ∈ Φ.tree ∨ ¬ Anc U Φ.F X) → X ∈ Φ'.tree ∨ ¬ Anc U Φ'.F X := by
      rintro X (hX | hX)
      · by_cases hF : Anc U Φ'.F X
        · exact Or.inl (hret.2 X hX hF)
        · exact Or.inr hF
      · exact Or.inr fun hF => hX (hret.1.trans hF)
    have hstep := step_blockStamp_eq ro self A hΦ'.1 h0 c
    by_cases hc : c = .restart
    · subst hc
      refine ⟨acRestart_vok ro self A Φ' t', fun r hr' => ?_, hΦ', ih.genesis⟩
      rcases (restart_state sp FGP ro self A Φ' t' hΦ'.1 h0).2.2.2.2.2.2.2.2.2.2 r with
        hq | ⟨-, -, X, hX, hXr⟩
      · obtain ⟨G, hG, hGr, hGp⟩ := ih.genesis
        have hg : r = sp.genesisRoot := by
          by_contra hne
          refine hr' ?_
          change (acRestart sp ro self A Φ' t').1.blockStamp r = ⊤
          rw [hq]
          simp [SAState.initial, hne]
        refine ⟨G, hG, hGr.trans hg.symm, ?_⟩
        by_cases hA : Anc U Φ'.F G
        · rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 hA with hFG | ⟨p, -, hp⟩
          · exact Or.inl (hFG ▸ hΦ'.1.rooted.1)
          · have hpar := hp.2.2
            rw [hGp] at hpar
            cases hpar
        · exact Or.inr hA
      · exact ⟨X, hΦ'.2 hX, hXr, Or.inl hX⟩
    refine ⟨(step_vok_keep ro self ih.vok Φ' t' hc).1, fun r hr' => ?_, hΦ', ih.genesis⟩
    by_cases hb : ∃ B, c = .block B
    · obtain ⟨B, rfl⟩ := hb
      rw [hstep.1 B rfl] at hr'
      by_cases hrB : r = B.root
      · obtain ⟨-, hst, -, -⟩ := hok
        have hB : B ∈ Φ'.tree := by
          rw [hst.tree_eq]
          exact ⟨Set.mem_insert _ _, hst.F'_anc_B⟩
        exact ⟨B, hΦ'.2 hB, hrB.symm, Or.inl hB⟩
      · rw [Function.update_of_ne hrB] at hr'
        obtain ⟨X, hXU, hXr, hX⟩ := ih.block r hr'
        exact ⟨X, hXU, hXr, hkeep X hX⟩
    · rw [hstep.2.2 (fun B hB => hb ⟨B, hB⟩) hc] at hr'
      obtain ⟨X, hXU, hXr, hX⟩ := ih.block r hr'
      exact ⟨X, hXU, hXr, hkeep X hX⟩

/-- **A0.1, stamps.** -/
theorem stamp_stable : StampStable sp := by
  intro FGP ro self U hU A Φ t₀ hr c Φ' t ht hok hc
  dsimp only
  have h := sinv_of_reachable sp hU hr
  have h0 : 0 ≤ t := (pool_slot_le sp hr).1.trans ht
  refine ⟨fun x hx => (step_vok_keep ro self h.vok Φ' t hc).2.2 x (h.vok x hx), fun r hr' => ?_⟩
  have hstep := step_blockStamp_eq ro self A hok.1.1 h0 c
  by_cases hb : ∃ B, c = .block B
  · obtain ⟨B, rfl⟩ := hb
    rw [hstep.1 B rfl]
    by_cases hrB : r = B.root
    · exfalso
      subst hrB
      obtain ⟨X, hXU, hXr, hX⟩ := h.block _ hr'
      obtain ⟨⟨-, hΦ'U⟩, hst, -, -⟩ := hok
      have hB : B ∈ Φ'.tree := by
        rw [hst.tree_eq]
        exact ⟨Set.mem_insert _ _, hst.F'_anc_B⟩
      have hXB : X = B := hU.1 hXU (hΦ'U hB) hXr
      subst hXB
      have hins : insert X Φ.tree ⊆ U := Set.insert_subset hXU h.frame.2
      rcases hX with hX | hX
      · exact hst.new hX
      · exact hX (Goldilocks.Anc.mono hins (hst.F_anc_F'.trans hst.F'_anc_B))
    · exact Function.update_of_ne hrB _ _
  · rw [hstep.2.2 (fun B hB => hb ⟨B, hB⟩) hc]

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
    have hxs := (pool_slot_le sp hreach).2 σ x hx
    have hlt : tr.time j' < sp.ts ((sp.slot (tr.time i) : Int) - 1) :=
      lt_of_lt_of_le ((hbefore j' hj' ℓ' hc').trans hu) hle
    have := (ts_le_iff_le_slot sp (h.time_nonneg j') ((sp.slot (tr.time i) : Int) - 1)).not.mp
      (not_le.mpr hlt)
    omega

end Consensus.Goldilocks.SA

end
