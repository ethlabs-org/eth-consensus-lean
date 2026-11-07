module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Views
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Locks
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Restart
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.RelTrace

public section

/-! # Goldilocks SA: the reachable-state invariant (A0.1: pools and block stamps)

By induction over `ReachableAt`: the pools hold votes of their slot, at most two per validator
(`pool_cap`), and block stamps do not decrease along parent edges of the tree (`stamp_parent`);
and how each call writes the block stamps (`step_blockStamp_eq`). The other reachable-state
statements are in `PoolFacts`, `Resolution` and `LockStore`. -/

namespace Consensus.Goldilocks.SA

variable (sp : SAParams)

/-! ### Pools and block stamps

Only `admitVote` changes a pool and only the receipt of a block changes a block stamp; a restart
empties the pools and stamps every block of the tree other than genesis with its time. -/

section Fields

variable {sp} {FGP : Type}

private theorem updateLatestConfirmed_fields (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (C : Blk sp.n FGP) : (updateLatestConfirmed sp A Φ C).pool = A.pool ∧
      (updateLatestConfirmed sp A Φ C).blockStamp = A.blockStamp := by
  unfold updateLatestConfirmed
  split_ifs <;> exact ⟨rfl, rfl⟩

private theorem optimistic_fields (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmation sp A Φ t).pool = A.pool ∧
      (optimisticConfirmation sp A Φ t).blockStamp = A.blockStamp := by
  unfold optimisticConfirmation
  split
  · exact ⟨rfl, rfl⟩
  · exact updateLatestConfirmed_fields _ _ _

private theorem updateConfirmation_fields (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (s : Nat) : (updateConfirmation sp A Φ t s).pool = A.pool ∧
      (updateConfirmation sp A Φ t s).blockStamp = A.blockStamp := by
  unfold updateConfirmation
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · split_ifs <;> first | exact ⟨rfl, rfl⟩ | exact updateLatestConfirmed_fields _ _ _

theorem admitVote_blockStamp (A : SAState sp.n) (t : Time) (v : Vote sp.n) :
    (admitVote sp A t v).blockStamp = A.blockStamp := by
  unfold admitVote
  split_ifs <;> rfl

/-- The pool invariant of A0.1: the slot-`σ` pool holds slot-`σ` votes, at most two distinct
ones per validator. -/
private def PoolOK (p : Nat → List (Vote sp.n)) : Prop :=
  ∀ σ, (∀ x ∈ p σ, x.slot = σ) ∧
    ∀ i : Fin sp.n, ((p σ).filter (fun x => x.val = i)).dedup.length ≤ 2

private theorem admitVote_poolOK {A : SAState sp.n} (h : PoolOK A.pool) (t : Time)
    (v : Vote sp.n) : PoolOK (admitVote sp A t v).pool := by
  unfold admitVote
  split_ifs with h₁ h₂
  · exact h
  · exact h
  · intro σ
    simp only [Function.update_apply]
    split_ifs with hσ
    · subst hσ
      refine ⟨fun x hx => ?_, fun i => ?_⟩
      · rcases List.mem_append.mp hx with hx | hx
        · exact (h _).1 x hx
        · rw [List.mem_singleton.mp hx]
      · rw [← List.card_toFinset, List.filter_append, List.toFinset_append]
        by_cases hi : v.val = i
        · have h₃ := Nat.lt_of_not_le h₂
          rw [← List.card_toFinset] at h₃
          simp only [List.filter_singleton, hi, decide_true, Bool.cond_true, List.toFinset_cons,
            List.toFinset_nil, insert_empty_eq]
          refine (Finset.card_union_le _ _).trans ?_
          subst hi
          simp only [Finset.card_singleton]
          omega
        · simp only [List.filter_singleton, hi, decide_false, Bool.cond_false, List.toFinset_nil,
            Finset.union_empty, List.card_toFinset]
          exact (h _).2 i
    · exact h σ


private theorem tryVote_fields (self : Fin sp.n) (L : Set Lock) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    (PoolOK A.pool → PoolOK (tryVoteWith sp self L A Φ t).1.pool) ∧
      (tryVoteWith sp self L A Φ t).1.blockStamp = A.blockStamp := by
  unfold tryVoteWith
  dsimp only
  split_ifs
  · exact ⟨id, rfl⟩
  · exact ⟨id, rfl⟩
  all_goals
    rw [(optimistic_fields _ _ _).1, (optimistic_fields _ _ _).2, admitVote_blockStamp]
    exact ⟨fun h => admitVote_poolOK (by exact h) _ _, rfl⟩

private theorem blockReceipt_fields (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (PoolOK A.pool → PoolOK (blockReceipt sp A t B).pool) ∧
      (blockReceipt sp A t B).blockStamp = Function.update A.blockStamp B.root (ETime.of t) := by
  unfold blockReceipt
  generalize blockVotes B = l
  suffices h : ∀ A' : SAState sp.n, (PoolOK A'.pool →
      PoolOK (l.foldl (fun A v => admitVote sp A t v) A').pool) ∧
      (l.foldl (fun A v => admitVote sp A t v) A').blockStamp = A'.blockStamp from
    h { A with blockStamp := Function.update A.blockStamp B.root (ETime.of t) }
  induction l with
  | nil => exact fun _ => ⟨id, rfl⟩
  | cons v l ih =>
    intro A'
    simp only [List.foldl_cons]
    exact ⟨fun h => (ih _).1 (admitVote_poolOK h _ _), (ih _).2.trans (admitVote_blockStamp _ _ _)⟩

private theorem acOnBlockWith_fields (self : Fin sp.n) (L : Set Lock) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (B : Blk sp.n FGP) :
    (PoolOK A.pool → PoolOK (acOnBlockWith sp self L A Φ t B).1.pool) ∧
      (acOnBlockWith sp self L A Φ t B).1.blockStamp =
        Function.update A.blockStamp B.root (ETime.of t) := by
  unfold acOnBlockWith
  rw [(tryVote_fields _ _ _ _ _).2, (optimistic_fields _ _ _).2, (blockReceipt_fields _ _ _).2]
  refine ⟨fun h => (tryVote_fields _ _ _ _ _).1 ?_, rfl⟩
  rw [(optimistic_fields _ _ _).1]
  exact (blockReceipt_fields _ _ _).1 h

private theorem acOnBlock_fields (self : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (B : Blk sp.n FGP) :
    (PoolOK A.pool → PoolOK (acOnBlock sp self A Φ t B).1.pool) ∧
      (acOnBlock sp self A Φ t B).1.blockStamp =
        Function.update A.blockStamp B.root (ETime.of t) :=
  acOnBlockWith_fields self _ A Φ t B

private theorem acOnTick_fields (self : Fin sp.n) (L : Set Lock) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    (PoolOK A.pool → PoolOK (acOnTickWith sp self L A Φ t).1.pool) ∧
      (acOnTickWith sp self L A Φ t).1.blockStamp = A.blockStamp := by
  unfold acOnTickWith
  dsimp only
  split_ifs
  all_goals
    try rw [(updateConfirmation_fields _ _ _ _).1, (updateConfirmation_fields _ _ _ _).2]
  all_goals first | exact ⟨id, rfl⟩ | exact tryVote_fields _ _ _ _ _


private theorem acProposal_fields (L : Set Lock) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) :
    (PoolOK A.pool → PoolOK (acProposalWith sp L A Φ t).1.pool) ∧
      (acProposalWith sp L A Φ t).1.blockStamp = A.blockStamp := by
  unfold acProposalWith
  split_ifs <;> exact ⟨id, rfl⟩

private theorem acToFG_fields (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (PoolOK A.pool → PoolOK (acToFG sp A Φ t).1.pool) ∧
      (acToFG sp A Φ t).1.blockStamp = A.blockStamp := by
  unfold acToFG
  split_ifs
  · split
    · exact ⟨id, rfl⟩
    · split_ifs <;> exact ⟨id, rfl⟩
  · exact ⟨id, rfl⟩

private theorem acOnMessage_fields (self : Fin sp.n) (L : Set Lock) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (v : Vote sp.n) :
    (PoolOK A.pool → PoolOK (acOnMessageWith sp self L A Φ t v).1.pool) ∧
      (acOnMessageWith sp self L A Φ t v).1.blockStamp = A.blockStamp := by
  unfold acOnMessageWith
  rw [(tryVote_fields _ _ _ _ _).2, (optimistic_fields _ _ _).2, admitVote_blockStamp]
  refine ⟨fun h => (tryVote_fields _ _ _ _ _).1 ?_, rfl⟩
  rw [(optimistic_fields _ _ _).1]
  exact admitVote_poolOK h _ _

/-- Message and block receipt preserve the slot of every pooled vote. -/
theorem receipt_pool_slot (A : SAState sp.n) (t : Time)
    (h : ∀ σ, (∀ m ∈ A.pool σ, m.slot = σ) ∧
      ∀ x : Fin sp.n, ((A.pool σ).filter (fun m => m.val = x)).dedup.length ≤ 2) :
    (∀ v σ m, m ∈ (admitVote sp A t v).pool σ → m.slot = σ) ∧
      (∀ (B : Blk sp.n FGP) σ m, m ∈ (blockReceipt sp A t B).pool σ → m.slot = σ) := by
  exact ⟨fun v σ => (admitVote_poolOK h t v σ).1,
    fun B σ => ((blockReceipt_fields A t B).1 h σ).1⟩

/-- The replay of a restart keeps the pool invariant, from the empty pools. -/
private theorem acRestart_poolOK (ro : ReplayOrder sp FGP) (self : Fin sp.n) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : PoolOK (acRestart sp ro self A Φ t).1.pool := by
  unfold acRestart
  suffices h : ∀ (l : List (Blk sp.n FGP)) (acc : SAState sp.n × List (Em sp FGP)),
      PoolOK acc.1.pool → PoolOK (l.foldl (fun acc B => let r := acOnBlock sp self acc.1 Φ t B;
        (r.1, acc.2 ++ r.2)) acc).1.pool from
    h _ _ fun σ => ⟨fun x hx => by simp [SAState.initial] at hx, fun i => by simp [SAState.initial]⟩
  intro l
  induction l with
  | nil => exact fun _ h => h
  | cons B l ih =>
    intro acc h
    simp only [List.foldl_cons]
    exact ih _ ((acOnBlock_fields _ _ _ _ _).1 h)

/-- `step_pool_cap` with the locks after the unlock given. -/
theorem stepWith_pool_cap (ro : ReplayOrder sp FGP) (self : Fin sp.n) (L : Set Lock)
    (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) (c : (goldilocksSA sp FGP ro).Call)
    (h : ∀ σ, (∀ m ∈ A.pool σ, m.slot = σ) ∧
      ∀ x : Fin sp.n, ((A.pool σ).filter (fun m => m.val = x)).dedup.length ≤ 2) :
    ∀ σ, (∀ m ∈ (stepWith sp ro self L A Φ t c).1.pool σ, m.slot = σ) ∧
      ∀ x : Fin sp.n, (((stepWith sp ro self L A Φ t c).1.pool σ).filter
        (fun m => m.val = x)).dedup.length ≤ 2 := by
  cases c with
  | tick => exact (acOnTick_fields self L A Φ t).1 h
  | proposal => exact (acProposal_fields L A Φ t).1 h
  | toFG => exact (acToFG_fields A Φ t).1 h
  | message m => exact (acOnMessage_fields self L A Φ t m).1 h
  | block B => exact (acOnBlockWith_fields self L A Φ t B).1 h
  | restart => exact acRestart_poolOK ro self A Φ t

/-- Pool form and capacity are preserved locally, independently of frame coherence.
A restart establishes them from its empty pools. -/
theorem step_pool_cap (ro : ReplayOrder sp FGP) (self : Fin sp.n) (A : SAState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (c : (goldilocksSA sp FGP ro).Call)
    (h : ∀ σ, (∀ m ∈ A.pool σ, m.slot = σ) ∧
      ∀ x : Fin sp.n, ((A.pool σ).filter (fun m => m.val = x)).dedup.length ≤ 2) :
    ∀ σ, (∀ m ∈ ((goldilocksSA sp FGP ro).step self A Φ t c).1.pool σ, m.slot = σ) ∧
      ∀ x : Fin sp.n, ((((goldilocksSA sp FGP ro).step self A Φ t c).1.pool σ).filter
        (fun m => m.val = x)).dedup.length ≤ 2 := by
  rw [step_eq_stepWith]
  exact stepWith_pool_cap ro self _ A Φ t c h

/-- The replay of a restart at `t` stamps `t` on every block it receives (and keeps the stamps
`t` it finds). -/
private theorem replay_blockStamp (self : Fin sp.n) (A₀ : SAState sp.n) {Φ : Frm sp.n FGP}
    {t : Time} (ht : 0 ≤ t) :
    ∀ l : List (Blk sp.n FGP), (∀ B ∈ l, B ∈ Φ.tree ∧ B.root ≠ sp.genesisRoot) →
    ∀ acc : SAState sp.n × List (Em sp FGP), RestartInv sp A₀ Φ t acc.1 →
    ∀ q, (acc.1.blockStamp q = ETime.of t ∨ ∃ B ∈ l, B.root = q) →
      (l.foldl (fun acc B => let r := acOnBlock sp self acc.1 Φ t B; (r.1, acc.2 ++ r.2))
        acc).1.blockStamp q = ETime.of t := by
  intro l
  induction l with
  | nil =>
    intro _ acc _ q hq
    rcases hq with hq | ⟨B, hB, -⟩
    · exact hq
    · exact absurd hB List.not_mem_nil
  | cons B l ih =>
    intro hl acc h q hq
    obtain ⟨hB, hg⟩ := hl B List.mem_cons_self
    have hr : (acOnBlock sp self acc.1 Φ t B).1 = blockReceipt sp acc.1 t B := by
      rw [h.acOnBlock sp ht hB hg self]
    simp only [List.foldl_cons]
    apply ih (fun C hC => hl C (List.mem_cons_of_mem _ hC))
    · rw [hr]
      exact h.blockReceipt sp hB hg
    · rw [hr, (blockReceipt_fields _ _ _).2, Function.update_apply]
      split_ifs with hqB
      · exact Or.inl rfl
      · rcases hq with hq | ⟨C, hC, hCq⟩
        · exact Or.inl hq
        · rcases List.mem_cons.mp hC with rfl | hC
          · exact absurd hCq.symm hqB
          · exact Or.inr ⟨C, hC, hCq⟩

/-- After a restart at `t`, a block of the tree other than genesis has the stamp `t`. -/
private theorem acRestart_blockStamp (ro : ReplayOrder sp FGP) (self : Fin sp.n)
    (A : SAState sp.n) {Φ : Frm sp.n FGP} {t : Time} (hΦ : FrameOK Φ) (ht : 0 ≤ t)
    {X : Blk sp.n FGP} (hX : X ∈ Φ.tree) (hg : X.root ≠ sp.genesisRoot) :
    (acRestart sp ro self A Φ t).1.blockStamp X.root = ETime.of t := by
  have hl := ro.parentOrder t Φ (parentOrder_exists sp hΦ)
  have h₀ : RestartInv sp A Φ t { SAState.initial sp.genesisRoot with
      locks := A.locks, latestConfirmed := A.latestConfirmed,
      restartTime := (t : WithBot Time) } :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun σ x hx => by simp [SAState.initial] at hx,
      fun x => Or.inl rfl, fun q => Or.inl rfl⟩
  exact replay_blockStamp self A ht _ (fun B hB => (hl.2.1 B).mp hB) (_, []) h₀ X.root
    (Or.inr ⟨X, (hl.2.1 X).mpr ⟨hX, hg⟩, rfl⟩)

/-- After a restart, genesis has the stamp `−∞`. -/
private theorem acRestart_blockStamp_genesis (ro : ReplayOrder sp FGP) (self : Fin sp.n)
    (A : SAState sp.n) {Φ : Frm sp.n FGP} {t : Time} (hΦ : FrameOK Φ) (ht : 0 ≤ t) :
    (acRestart sp ro self A Φ t).1.blockStamp sp.genesisRoot = ⊥ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h⟩ := restart_state sp FGP ro self A Φ t hΦ ht
  rcases h sp.genesisRoot with h | h
  · rw [h]
    simp only [SAState.initial, ite_true]
  · exact absurd rfl h.2.1

/-- `step_blockStamp_eq` with the locks after the unlock given. -/
theorem stepWith_blockStamp_eq (ro : ReplayOrder sp FGP) (self : Fin sp.n) (L : Set Lock)
    (A : SAState sp.n)
    {Φ : Frm sp.n FGP} {t : Time} (hΦ : FrameOK Φ) (ht : 0 ≤ t)
    (c : (goldilocksSA sp FGP ro).Call) :
    (∀ B, c = .block B → (stepWith sp ro self L A Φ t c).1.blockStamp =
        Function.update A.blockStamp B.root (ETime.of t)) ∧
      (c = .restart → ∀ X ∈ Φ.tree, (stepWith sp ro self L A Φ t c).1.blockStamp
        X.root = if X.root = sp.genesisRoot then ⊥ else ETime.of t) ∧
      ((∀ B, c ≠ .block B) → c ≠ .restart →
        (stepWith sp ro self L A Φ t c).1.blockStamp = A.blockStamp) := by
  cases c with
  | block B =>
    refine ⟨fun B' hB => ?_, fun h => absurd h (by simp), fun h => absurd rfl (h B)⟩
    cases hB
    exact (acOnBlockWith_fields _ _ _ _ _ _).2
  | restart =>
    refine ⟨fun B h => absurd h (by simp), fun _ X hX => ?_, fun _ h => absurd rfl h⟩
    split_ifs with hg
    · rw [hg]; exact acRestart_blockStamp_genesis ro self A hΦ ht
    · exact acRestart_blockStamp ro self A hΦ ht hX hg
  | tick => exact ⟨fun B h => absurd h (by simp), fun h => absurd h (by simp),
      fun _ _ => (acOnTick_fields _ _ _ _ _).2⟩
  | proposal => exact ⟨fun B h => absurd h (by simp), fun h => absurd h (by simp),
      fun _ _ => (acProposal_fields _ _ _ _).2⟩
  | toFG => exact ⟨fun B h => absurd h (by simp), fun h => absurd h (by simp),
      fun _ _ => (acToFG_fields _ _ _).2⟩
  | message m => exact ⟨fun B h => absurd h (by simp), fun h => absurd h (by simp),
      fun _ _ => (acOnMessage_fields _ _ _ _ _ _).2⟩

/-- **How one lawful call writes the block stamps.** `ac_on_block(B)` at `t` stamps `B.root`
with `t`; a restart at `t ≥ 0` with a well-formed frame stamps every block of the tree with `t`,
genesis with `−∞`; every other call keeps the stamps. -/
theorem step_blockStamp_eq (ro : ReplayOrder sp FGP) (self : Fin sp.n) (A : SAState sp.n)
    {Φ : Frm sp.n FGP} {t : Time} (hΦ : FrameOK Φ) (ht : 0 ≤ t)
    (c : (goldilocksSA sp FGP ro).Call) :
    (∀ B, c = .block B → ((goldilocksSA sp FGP ro).step self A Φ t c).1.blockStamp =
        Function.update A.blockStamp B.root (ETime.of t)) ∧
      (c = .restart → ∀ X ∈ Φ.tree, ((goldilocksSA sp FGP ro).step self A Φ t c).1.blockStamp
        X.root = if X.root = sp.genesisRoot then ⊥ else ETime.of t) ∧
      ((∀ B, c ≠ .block B) → c ≠ .restart →
        ((goldilocksSA sp FGP ro).step self A Φ t c).1.blockStamp = A.blockStamp) := by
  rw [step_eq_stepWith]
  exact stepWith_blockStamp_eq ro self _ A hΦ ht c

end Fields

private theorem ETime.of_le_of {t t' : Time} (h : t ≤ t') : ETime.of t ≤ ETime.of t' :=
  WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr h)

/-- The invariant of a reachable state `A` with frame `Φ` and last time `t₀` inside `U`: the
frame is in `U`, `U` holds genesis, `t₀ ≥ 0`, the pools are well formed, and the stamps of the
tree are at most `t₀` and do not decrease along parent edges. -/
private structure Inv {FGP : Type} (ro : ReplayOrder sp FGP) (U : Set (Blk sp.n FGP))
    (A : SAState sp.n) (Φ : Frm sp.n FGP) (t₀ : Time) : Prop where
  frame : (goldilocksSA sp FGP ro).FrameIn U Φ
  genesis : ∃ G ∈ U, G.root = sp.genesisRoot ∧ G.parent = none
  time : 0 ≤ t₀
  pool : PoolOK A.pool
  stamp_le : ∀ X ∈ Φ.tree, A.blockStamp X.root ≤ ETime.of t₀
  stamp_parent : ∀ B ∈ Φ.tree, ∀ Pa ∈ Φ.tree, B.parent = some Pa.root →
    A.blockStamp Pa.root ≤ A.blockStamp B.root

/-- A call other than `ac_on_block` and the restart keeps the stamps and the frame. -/
private theorem Inv.of_stamps {FGP : Type} {ro : ReplayOrder sp FGP} {U : Set (Blk sp.n FGP)}
    {A A' : SAState sp.n} {Φ : Frm sp.n FGP} {t₀ t : Time} (h : Inv sp ro U A Φ t₀)
    (ht : t₀ ≤ t) (hp : PoolOK A'.pool) (hs : A'.blockStamp = A.blockStamp) :
    Inv sp ro U A' Φ t :=
  ⟨h.frame, h.genesis, h.time.trans ht, hp,
    fun X hX => hs ▸ (h.stamp_le X hX).trans (ETime.of_le_of ht), hs ▸ h.stamp_parent⟩

private theorem Inv.block {FGP : Type} {ro : ReplayOrder sp FGP} {U : Set (Blk sp.n FGP)}
    (hU : Coherent U) {self : Fin sp.n} {A : SAState sp.n} {Φ Φ' : Frm sp.n FGP} {t₀ t : Time}
    {B : Blk sp.n FGP} (h : Inv sp ro U A Φ t₀) (ht : t₀ ≤ t)
    (hc : (goldilocksSA sp FGP ro).CallOK U Φ t (.block B) Φ') (L : Set Lock) :
    Inv sp ro U (acOnBlockWith sp self L A Φ' t B).1 Φ' t := by
  obtain ⟨⟨hΦ', hΦ'U⟩, hst, -, -⟩ := hc
  obtain ⟨hp, hs⟩ := acOnBlockWith_fields self L A Φ' t B
  have hB : B ∈ Φ'.tree := by
    rw [hst.tree_eq]
    exact ⟨Set.mem_insert _ _, hst.F'_anc_B⟩
  have hold : ∀ X ∈ Φ'.tree, X ≠ B → X ∈ Φ.tree ∧
      (acOnBlockWith sp self L A Φ' t B).1.blockStamp X.root = A.blockStamp X.root := by
    intro X hX hXB
    have hX' := hX
    rw [hst.tree_eq] at hX'
    refine ⟨(Set.mem_insert_iff.mp hX'.1).resolve_left hXB, ?_⟩
    rw [hs, Function.update_of_ne fun hr => hXB (hΦ'.coherent.1 hX hB hr)]
  have hBt : (acOnBlockWith sp self L A Φ' t B).1.blockStamp B.root = ETime.of t := by
    rw [hs, Function.update_self]
  refine ⟨⟨hΦ', hΦ'U⟩, h.genesis, h.time.trans ht, hp h.pool, fun X hX => ?_,
    fun C hC Pa hPa hCPa => ?_⟩
  · by_cases hXB : X = B
    · rw [hXB, hBt]
    · rw [(hold X hX hXB).2]
      exact (h.stamp_le X (hold X hX hXB).1).trans (ETime.of_le_of ht)
  by_cases hCB : C = B
  · subst hCB
    by_cases hPaB : Pa = C
    · rw [hPaB]
    · rw [hBt, (hold Pa hPa hPaB).2]
      exact (h.stamp_le Pa (hold Pa hPa hPaB).1).trans (ETime.of_le_of ht)
  by_cases hPaB : Pa = B
  · -- `C` is a block of the old tree whose parent `B` is new: impossible.
    subst hPaB
    exfalso
    have hC' := (hold C hC hCB).1
    obtain ⟨hΦ, hΦU⟩ := h.frame
    have hins : insert Pa Φ.tree ⊆ U := Set.insert_subset (hΦ'U hB) hΦU
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (hΦ.rooted.2 C hC') with
      hCF | ⟨p, -, hp⟩
    · subst hCF
      have h₁ : Goldilocks.Anc (insert Pa Φ.tree) Pa Φ.F :=
        Relation.ReflTransGen.single ⟨Set.mem_insert _ _, Set.mem_insert_of_mem _ hC', hCPa⟩
      have h₂ := Anc.antisymm hU (Goldilocks.Anc.mono hins h₁)
        (Goldilocks.Anc.mono hins (hst.F_anc_F'.trans hst.F'_anc_B))
      exact hst.new (h₂ ▸ hC')
    · have : p = Pa := hU.1 (hΦU hp.1) (hΦ'U hB) (Option.some.inj (hp.2.2.symm.trans hCPa))
      exact hst.new (this ▸ hp.1)
  rw [(hold C hC hCB).2, (hold Pa hPa hPaB).2]
  exact h.stamp_parent C (hold C hC hCB).1 Pa (hold Pa hPa hPaB).1 hCPa

private theorem Inv.restart {FGP : Type} {ro : ReplayOrder sp FGP} {U : Set (Blk sp.n FGP)}
    (hU : Coherent U) {self : Fin sp.n} {A : SAState sp.n} {Φ Φ' : Frm sp.n FGP} {t₀ t : Time}
    (h : Inv sp ro U A Φ t₀) (ht : t₀ ≤ t)
    (hc : (goldilocksSA sp FGP ro).CallOK U Φ t .restart Φ') :
    Inv sp ro U (acRestart sp ro self A Φ' t).1 Φ' t := by
  obtain ⟨⟨hΦ', hΦ'U⟩, rfl⟩ := hc
  have ht' := h.time.trans ht
  have hle : ∀ X ∈ Φ'.tree, (acRestart sp ro self A Φ' t).1.blockStamp X.root ≤ ETime.of t := by
    intro X hX
    by_cases hg : X.root = sp.genesisRoot
    · rw [hg, acRestart_blockStamp_genesis ro self A hΦ' ht']
      exact bot_le
    · rw [acRestart_blockStamp ro self A hΦ' ht' hX hg]
  refine ⟨⟨hΦ', hΦ'U⟩, h.genesis, ht', acRestart_poolOK ro self A Φ' t, hle,
    fun C hC Pa hPa hCPa => ?_⟩
  obtain ⟨G, hG, hGr, hGp⟩ := h.genesis
  have hg : C.root ≠ sp.genesisRoot := by
    intro hCg
    have : C = G := hU.1 (hΦ'U hC) hG (hCg.trans hGr.symm)
    rw [this, hGp] at hCPa
    cases hCPa
  rw [acRestart_blockStamp ro self A hΦ' ht' hC hg]
  exact hle Pa hPa

/-- Every state reachable with the unlock given satisfies the invariant. -/
private theorem inv_of_reachableU {FGP : Type} {ro : ReplayOrder sp FGP} {self : Fin sp.n}
    {U : Set (Blk sp.n FGP)} (hU : Coherent U) {A : SAState sp.n} {Φ : Frm sp.n FGP} {t₀ : Time}
    (h : ReachableAtU (ro := ro) self U A Φ t₀) :
    Inv sp ro U A Φ t₀ := by
  induction h with
  | init Φ hi hf =>
    obtain ⟨htree, hroot, -, hpar, -⟩ := hi
    have hF : ∀ X ∈ Φ.tree, X = Φ.F := fun X hX => by rw [htree] at hX; exact hX
    refine ⟨hf, ⟨Φ.F, hf.2 (htree ▸ rfl), hroot, hpar⟩, le_rfl,
      fun σ => ⟨fun x hx => by simp [SAState.initial] at hx, fun i => by simp [SAState.initial]⟩,
      fun X hX => ?_, fun C hC Pa hPa _ => by rw [hF C hC, hF Pa hPa]⟩
    simp only [SAState.initial, hF X hX, hroot, ite_true]
    exact bot_le
  | step c L _ ht hc _ ih =>
    cases c with
    | tick =>
      obtain ⟨-, rfl⟩ := hc
      exact ih.of_stamps sp ht ((acOnTick_fields _ L _ _ _).1 ih.pool)
        (acOnTick_fields _ L _ _ _).2
    | proposal =>
      obtain ⟨-, rfl⟩ := hc
      exact ih.of_stamps sp ht ((acProposal_fields L _ _ _).1 ih.pool)
        (acProposal_fields L _ _ _).2
    | toFG =>
      obtain ⟨-, rfl⟩ := hc
      exact ih.of_stamps sp ht ((acToFG_fields _ _ _).1 ih.pool) (acToFG_fields _ _ _).2
    | message m =>
      obtain ⟨-, rfl, -⟩ := hc
      exact ih.of_stamps sp ht ((acOnMessage_fields _ L _ _ _ _).1 ih.pool)
        (acOnMessage_fields _ L _ _ _ _).2
    | block B => exact ih.block sp hU ht hc L
    | restart => exact ih.restart sp hU ht hc

/-- **A0.1, pool capacity.** -/
theorem pool_cap : PoolCap sp :=
  fun _ _ _ _ hU _ _ _ h => (inv_of_reachableU sp hU h.toU).pool

/-- **A0.1, pool capacity**, at the states reachable with the unlock given. -/
theorem pool_capU (FGP : Type) (ro : ReplayOrder sp FGP) (self : Fin sp.n)
    (U : Set (Blk sp.n FGP)) (hU : Coherent U) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t₀ : Time)
    (h : ReachableAtU (ro := ro) self U A Φ t₀) :
    ∀ σ, (∀ x ∈ A.pool σ, x.slot = σ) ∧
      ∀ i : Fin sp.n, ((A.pool σ).filter (fun x => x.val = i)).dedup.length ≤ 2 :=
  (inv_of_reachableU sp hU h).pool

/-- At a reachable state, every block of the frame tree has a stamp at or before the time of the
last call (finite, or `−∞` for genesis). -/
theorem tree_blockStamp_le {FGP : Type} {ro : ReplayOrder sp FGP} {self : Fin sp.n}
    {U : Set (Blk sp.n FGP)} (hU : Coherent U) {A : SAState sp.n} {Φ : Frm sp.n FGP} {t₀ : Time}
    (h : (goldilocksSA sp FGP ro).ReachableAt self U A Φ t₀) :
    ∀ X ∈ Φ.tree, A.blockStamp X.root ≤ ETime.of t₀ :=
  (inv_of_reachableU sp hU h.toU).stamp_le

/-- `tree_blockStamp_le` at the states reachable with the unlock given. -/
theorem tree_blockStamp_leU {FGP : Type} {ro : ReplayOrder sp FGP} {self : Fin sp.n}
    {U : Set (Blk sp.n FGP)} (hU : Coherent U) {A : SAState sp.n} {Φ : Frm sp.n FGP} {t₀ : Time}
    (h : ReachableAtU (ro := ro) self U A Φ t₀) :
    ∀ X ∈ Φ.tree, A.blockStamp X.root ≤ ETime.of t₀ :=
  (inv_of_reachableU sp hU h).stamp_le

/-- **A0.1, stamps along parent edges.** -/
theorem stamp_parent : StampParent sp :=
  fun _ _ _ _ hU _ _ _ h => (inv_of_reachableU sp hU h.toU).stamp_parent

/-- **A0.1, stamps along parent edges**, at the states reachable with the unlock given. -/
theorem stamp_parentU (FGP : Type) (ro : ReplayOrder sp FGP) (self : Fin sp.n)
    (U : Set (Blk sp.n FGP)) (hU : Coherent U) (A : SAState sp.n) (Φ : Frm sp.n FGP) (t₀ : Time)
    (h : ReachableAtU (ro := ro) self U A Φ t₀) :
    ∀ B ∈ Φ.tree, ∀ Pa ∈ Φ.tree, B.parent = some Pa.root →
      A.blockStamp Pa.root ≤ A.blockStamp B.root :=
  (inv_of_reachableU sp hU h).stamp_parent

end Consensus.Goldilocks.SA

end
