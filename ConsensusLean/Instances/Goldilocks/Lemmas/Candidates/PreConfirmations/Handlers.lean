module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Candidates.PreConfirmations.Store
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Restart
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Steps.Writer

public section

/-! # ½ pre-confirmations: the handlers on the store and on the core

* `ackCallCoreId`: an ack receipt is a core identity;
* `restartResets`: a restart is the core's restart, its replay runs unjoined (or in slot `0`
  before `t_0 + Δ`) and emits nothing, and the store after it is the empty store with the
  replayed payloads' votes recorded;
* `projStateCore`: the forgotten trace's state of an honest node is the core of its state;
* the store across a call: a predicate kept by the store operations (`StoreStable`) is kept by
  every call (`step_storeStable`); a call keeps the node's ack decisions, but for the tick's
  decision after its update (`step_myAcks`); an emitted ack is a decision of its sender
  (`step_ack_emission`). -/

namespace Consensus.Goldilocks.PreConfirmations

open SA EvidenceRelease

variable {sp : SAParams} {FGP : Type} {σ : Type} {E : UnlockStage sp wlockStore σ} {c : σ}
  {m : WriteMode} {ro : ReplayOrder sp FGP}

/-! ## The store operations, field by field -/

/-- The fields a record keeps: all but the vote record. -/
def KeepsButVotes (Q P : PCStore sp.n) : Prop :=
  Q.acks = P.acks ∧ Q.pcs = P.pcs ∧ Q.valid = P.valid ∧ Q.dead = P.dead ∧ Q.myAcks = P.myAcks

theorem keepsButVotes_iff (Q P : PCStore sp.n) :
    KeepsButVotes Q P ↔ Q.acks = P.acks ∧ Q.pcs = P.pcs ∧ Q.valid = P.valid ∧ Q.dead = P.dead ∧
      Q.myAcks = P.myAcks := Iff.rfl

theorem KeepsButVotes.trans {Q R P : PCStore sp.n} (h₁ : KeepsButVotes Q R)
    (h₂ : KeepsButVotes R P) : KeepsButVotes Q P :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1, h₁.2.2.2.1.trans h₂.2.2.2.1,
    h₁.2.2.2.2.trans h₂.2.2.2.2⟩

theorem recordVote_keeps (P : PCStore sp.n) (t : Time) (v : Vote sp.n) :
    KeepsButVotes (recordVote sp P t v) P := by
  unfold recordVote
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem recordVotes_keeps (P : PCStore sp.n) (t : Time) (l : List (Vote sp.n)) :
    KeepsButVotes (recordVotes sp P t l) P := by
  induction l generalizing P with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons v l ih => exact (ih (recordVote sp P t v)).trans (recordVote_keeps P t v)

theorem foldRecord_keeps (t : Time) (l : List (Blk sp.n FGP)) (P : PCStore sp.n) :
    KeepsButVotes (l.foldl (fun P B => recordVotes sp P t (blockVotes B)) P) P := by
  induction l generalizing P with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons B l ih => exact (ih _).trans (recordVotes_keeps P t _)

theorem onAck_myAcks (P : PCStore sp.n) (t : Time) (a : Ack sp.n) :
    (onAck sp P t a).myAcks = P.myAcks := by
  unfold onAck
  dsimp only
  split_ifs <;> rfl

theorem foldl_onAck_myAcks (P : PCStore sp.n) (t : Time) (l : List (Ack sp.n)) :
    (l.foldl (fun Q a => onAck sp Q t a) P).myAcks = P.myAcks := by
  induction l generalizing P with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, ih, onAck_myAcks]

theorem recordVotes_myAcks (P : PCStore sp.n) (t : Time) (l : List (Vote sp.n)) :
    (recordVotes sp P t l).myAcks = P.myAcks :=
  (recordVotes_keeps P t l).2.2.2.2

theorem recordVote_myAcks (P : PCStore sp.n) (t : Time) (v : Vote sp.n) :
    (recordVote sp P t v).myAcks = P.myAcks :=
  (recordVote_keeps P t v).2.2.2.2

/-! ## The PC `try_vote` -/

theorem tryVotePC_myAcks (self : Fin sp.n) (X : PCState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (tryVotePC sp E c m self X Φ t).1.store.myAcks = X.store.myAcks := by
  unfold tryVotePC
  dsimp only
  split_ifs
  · rw [foldl_onAck_myAcks, recordVotes_myAcks, refresh_myAcks]
  · rfl

/-- An ack the PC `try_vote` emits is a decision of the store it was called with. -/
theorem tryVotePC_ack_emission (self : Fin sp.n) (X : PCState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) {e : EmPC sp FGP} (he : e ∈ (tryVotePC sp E c m self X Φ t).2) {a : Ack sp.n}
    (ha : e.msg = .inr a) : a.val = self ∧ X.store.myAcks a.slot = some a.target := by
  unfold tryVotePC at he
  dsimp only at he
  split_ifs at he
  · rcases List.mem_append.1 he with he | he
    · obtain ⟨e', -, rfl⟩ := List.mem_map.1 he
      simp [liftEm] at ha
    · obtain ⟨a', ha', rfl⟩ := List.mem_map.1 he
      cases ha
      obtain ⟨h1, -, -, -, h5⟩ := ackSendsWindow (sp := sp) _ self _ a ha'
      exact ⟨h1, by rw [← refresh_myAcks (Φ := Φ) (t := t)]; exact h5⟩
  · obtain ⟨e', -, rfl⟩ := List.mem_map.1 he
    simp [liftEm] at ha

/-! ## The replay of a restart -/

theorem optimisticConfirmationWM_restartTime (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (optimisticConfirmationWM sp m X Φ t).ac.restartTime = X.ac.restartTime := by
  unfold optimisticConfirmationWM withLocks optimisticConfirmationM
  cases m.optimistic
  · rfl
  · dsimp only
    split
    · rfl
    · unfold updateLatestConfirmed
      split_ifs <;> rfl

theorem blockReceipt_restartTime' (A : SAState sp.n) (t : Time) (B : Blk sp.n FGP) :
    (blockReceipt sp A t B).restartTime = A.restartTime := by
  unfold blockReceipt
  have key : ∀ (l : List (Vote sp.n)) (A₀ : SAState sp.n),
      (l.foldl (fun A v => admitVote sp A t v) A₀).restartTime = A₀.restartTime := by
    intro l
    induction l with
    | nil => exact fun _ => rfl
    | cons v l ih => exact fun A₀ => (ih _).trans (admitVote_restartTime A₀ t v)
  exact key _ _

theorem slot_of_neg {t : Time} (ht : t < 0) : sp.slot t = 0 := by
  simp [SAParams.slot, Params.slotOf, Int.toNat_of_nonpos ht.le]

/-- A node whose latest restart is at `t` casts no vote at `t`: it is not joined (`t ≥ 0`), or it is
in slot `0` before `t_0 + Δ` (`t < 0`). -/
theorem tryVoteEMAt_of_restartTime (st : StartFn sp FGP) (self : Fin sp.n) {X : WState sp.n}
    (Φ : Frm sp.n FGP) {t : Time} (h : X.ac.restartTime = (t : WithBot Time)) :
    tryVoteEMAt sp E c m st self X Φ t = (X, []) := by
  unfold tryVoteEMAt
  dsimp only
  by_cases ht : 0 ≤ t
  · have hnj := not_joined_of_restartTime sp ht h
    simp only [hnj, not_false_eq_true, true_or, ite_true]
  · have hs := slot_of_neg (sp := sp) (not_le.1 ht)
    have hΔ := sp.toParams.hΔ
    have hts : sp.ts ((0 : Nat) : Int) = 0 := by simp [SAParams.ts]
    have hlt : t < sp.ts (sp.slot t) + sp.Δ := by
      rw [hs, hts, zero_add]
      exact lt_trans (not_le.1 ht) hΔ
    split_ifs with h1 h2
    · rfl
    · rfl
    all_goals exact absurd ⟨hlt, Or.inl hs⟩ h2

theorem acOnBlockPC_of_restartTime (self : Fin sp.n) (X : PCState sp.n) (Φ : Frm sp.n FGP)
    {t : Time} (B : Blk sp.n FGP) (h : X.core.ac.restartTime = (t : WithBot Time)) :
    acOnBlockPC sp E c m self X Φ t B =
      (⟨optimisticConfirmationWM sp m { X.core with ac := blockReceipt sp X.core.ac t B } Φ t,
        recordVotes sp X.store t (blockVotes B)⟩, []) := by
  have h' : (optimisticConfirmationWM sp m { X.core with ac := blockReceipt sp X.core.ac t B } Φ
      t).ac.restartTime = (t : WithBot Time) := by
    rw [optimisticConfirmationWM_restartTime]
    exact (blockReceipt_restartTime' X.core.ac t B).trans h
  unfold acOnBlockPC tryVotePC
  dsimp only
  rw [tryVoteEMAt_of_restartTime _ self Φ h']
  simp

theorem acOnBlockEM_of_restartTime (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP)
    {t : Time} (B : Blk sp.n FGP) (h : X.ac.restartTime = (t : WithBot Time)) :
    acOnBlockEM sp E c m self X Φ t B =
      (optimisticConfirmationWM sp m { X with ac := blockReceipt sp X.ac t B } Φ t, []) := by
  have h' : (optimisticConfirmationWM sp m { X with ac := blockReceipt sp X.ac t B } Φ
      t).ac.restartTime = (t : WithBot Time) := by
    rw [optimisticConfirmationWM_restartTime]
    exact (blockReceipt_restartTime' X.ac t B).trans h
  exact tryVoteEMAt_of_restartTime (parentStart sp Φ t) self Φ h'

theorem optimisticConfirmationWM_blockReceipt_restartTime (X : WState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) (B : Blk sp.n FGP) :
    (optimisticConfirmationWM sp m { X with ac := blockReceipt sp X.ac t B } Φ t).ac.restartTime =
      X.ac.restartTime := by
  rw [optimisticConfirmationWM_restartTime]
  exact blockReceipt_restartTime' X.ac t B

/-- The replay, run from states restarted at `t`: the PC replay's core is the core's replay, both
emit nothing, and the store only records the payloads' votes. -/
theorem replay_fold (self : Fin sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    ∀ (l : List (Blk sp.n FGP)) (acc : PCState sp.n × List (EmPC sp FGP))
      (acc' : WState sp.n × List (EmW sp FGP)),
    acc.1.core = acc'.1 → acc.1.core.ac.restartTime = (t : WithBot Time) →
    (l.foldl (fun acc B => let r := acOnBlockPC sp E c m self acc.1 Φ t B;
        (r.1, acc.2 ++ r.2)) acc).1.core =
      (l.foldl (fun acc B => let r := acOnBlockEM sp E c m self acc.1 Φ t B;
        (r.1, acc.2 ++ r.2)) acc').1 ∧
    (l.foldl (fun acc B => let r := acOnBlockPC sp E c m self acc.1 Φ t B;
        (r.1, acc.2 ++ r.2)) acc).2 = acc.2 ∧
    (l.foldl (fun acc B => let r := acOnBlockEM sp E c m self acc.1 Φ t B;
        (r.1, acc.2 ++ r.2)) acc').2 = acc'.2 ∧
    (l.foldl (fun acc B => let r := acOnBlockPC sp E c m self acc.1 Φ t B;
        (r.1, acc.2 ++ r.2)) acc).1.store =
      l.foldl (fun P B => recordVotes sp P t (blockVotes B)) acc.1.store := by
  intro l
  induction l with
  | nil => intro acc acc' h₁ _; exact ⟨h₁, rfl, rfl, rfl⟩
  | cons B l ih =>
    intro acc acc' h₁ h₂
    have e₁ := acOnBlockPC_of_restartTime (E := E) (c := c) (m := m) self acc.1 Φ B h₂
    have e₂ := acOnBlockEM_of_restartTime (E := E) (c := c) (m := m) self acc'.1 Φ B (h₁ ▸ h₂)
    simp only [List.foldl_cons, e₁, e₂, List.append_nil]
    refine ih _ _ ?_ ?_
    · change optimisticConfirmationWM sp m { acc.1.core with ac := _ } Φ t =
        optimisticConfirmationWM sp m { acc'.1 with ac := _ } Φ t
      rw [h₁]
    · change (optimisticConfirmationWM sp m { acc.1.core with ac := _ } Φ t).ac.restartTime = _
      rw [optimisticConfirmationWM_blockReceipt_restartTime]
      exact h₂

/-- The PC restart, unfolded: the core's restart and the store's replay record. -/
theorem acRestartPC_eq (self : Fin sp.n) (X : PCState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acRestartPC sp E c m ro self X Φ t).1.core = (acRestartEM sp E c m ro self X.core Φ t).1 ∧
    (acRestartPC sp E c m ro self X Φ t).2 = [] ∧
    (acRestartEM sp E c m ro self X.core Φ t).2 = [] ∧
    (acRestartPC sp E c m ro self X Φ t).1.store =
      (ro.order t Φ).foldl (fun P B => recordVotes sp P t (blockVotes B)) PCStore.empty :=
  replay_fold self Φ t (ro.order t Φ) _ _ rfl rfl

/-! ## The statements of the core -/

/-- **An ack receipt is a core identity.** -/
theorem ackCallCoreId : AckCallCoreId sp FGP E c m ro :=
  fun _ _ _ _ _ => rfl

/-- **A restart empties the store.** -/
theorem restartResets : RestartResets sp FGP E c m ro := by
  intro self X Φ t
  obtain ⟨h₁, h₂, h₃, h₄⟩ := acRestartPC_eq (E := E) (c := c) (m := m) (ro := ro) self X Φ t
  change (acRestartPC sp E c m ro self X Φ t).1.core = _ ∧
    (acRestartPC sp E c m ro self X Φ t).2.filterMap projEmPC = _ ∧
    (acRestartPC sp E c m ro self X Φ t).1.store.pcs = ∅ ∧
    (acRestartPC sp E c m ro self X Φ t).1.store.valid = ∅ ∧
    (acRestartPC sp E c m ro self X Φ t).1.store.dead = ∅ ∧
    (∀ s X' j, (acRestartPC sp E c m ro self X Φ t).1.store.acks s X' j = ∅) ∧
    (∀ s, (acRestartPC sp E c m ro self X Φ t).1.store.myAcks s = none) ∧
    (acRestartPC sp E c m ro self X Φ t).1.store.votes = _
  obtain ⟨k₁, k₂, k₃, k₄, k₅⟩ := foldRecord_keeps t (ro.order t Φ) (PCStore.empty (n := sp.n))
  rw [h₁, h₂, h₃, h₄, k₁, k₂, k₃, k₄, k₅]
  exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl, fun _ => rfl, rfl⟩

set_option linter.unusedSimpArgs false in
/-- **The forgotten state is the core.** -/
theorem projStateCore : ProjStateCore sp FGP E c m ro := by
  intro H U tr hr y hy i
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [Trace.state]
    rcases hl : tr.label i with _ | ℓ
    · simp only [Option.bind_none, ne_eq, not_true_eq_false, and_false, ite_false]
      exact ih
    · by_cases hn : tr.node i = y
      · have hex := hr.exec i ℓ hl (hn ▸ hy)
        rw [hn] at hex
        rcases hk : ℓ.call with _ | _ | _ | (v | a) | B | _ <;>
          simp only [hl, hk, hn, Option.bind_some, projLabelPC, projCallPC, Option.map_some,
            Option.map_none, ne_eq, reduceCtorEq, not_false_eq_true, and_self, ite_true,
            not_true_eq_false, and_false, ite_false, Option.some_ne_none]
        rw [hk] at hex
        have := congrArg (fun p => p.1.core.ac) hex
        simp only [ACInterface.step, preConfSAM, acOnMessagePC] at this
        rw [ih, ← this]
      · simp only [hn, false_and, ite_false]
        exact ih

/-! ## The store across a call -/

/-- A predicate on stores kept by every store operation, and true of the empty store. -/
structure StoreStable (Q : PCStore sp.n → Prop) : Prop where
  empty_ok : Q PCStore.empty
  refresh_ok : ∀ P (Φ : Frm sp.n FGP) t, Q P → Q (refresh sp P Φ t)
  record_ok : ∀ P t v, Q P → Q (recordVote sp P t v)
  onAck_ok : ∀ P t a, Q P → Q (onAck sp P t a)
  decide_ok : ∀ P A (Φ : Frm sp.n FGP) t u, Q P → Q (decideAck sp P A Φ t u)

variable {Q : PCStore sp.n → Prop}

theorem StoreStable.records (hQ : StoreStable (FGP := FGP) Q) (P : PCStore sp.n) (t : Time)
    (l : List (Vote sp.n)) (h : Q P) : Q (recordVotes sp P t l) := by
  induction l generalizing P with
  | nil => exact h
  | cons v l ih => exact ih _ (hQ.record_ok P t v h)

theorem StoreStable.onAcks (hQ : StoreStable (FGP := FGP) Q) (P : PCStore sp.n) (t : Time)
    (l : List (Ack sp.n)) (h : Q P) : Q (l.foldl (fun P a => onAck sp P t a) P) := by
  induction l generalizing P with
  | nil => exact h
  | cons a l ih => exact ih _ (hQ.onAck_ok P t a h)

theorem tryVotePC_storeStable (hQ : StoreStable (FGP := FGP) Q) (self : Fin sp.n)
    (X : PCState sp.n) (Φ : Frm sp.n FGP) (t : Time) (h : Q X.store) :
    Q (tryVotePC sp E c m self X Φ t).1.store := by
  unfold tryVotePC
  dsimp only
  split_ifs
  · exact hQ.onAcks _ t _ (hQ.records _ t _ (hQ.refresh_ok _ Φ t h))
  · exact h

theorem acOnBlockPC_storeStable (hQ : StoreStable (FGP := FGP) Q) (self : Fin sp.n)
    (X : PCState sp.n) (Φ : Frm sp.n FGP) (t : Time) (B : Blk sp.n FGP) (h : Q X.store) :
    Q (acOnBlockPC sp E c m self X Φ t B).1.store :=
  tryVotePC_storeStable hQ self _ Φ t (hQ.records _ t _ h)

/-- **A stable predicate of the store is kept by every call.** -/
theorem step_storeStable (hQ : StoreStable (FGP := FGP) Q) (self : Fin sp.n) (X : PCState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) (k : (preConfSAM sp E c m FGP ro).Call) (h : Q X.store) :
    Q ((preConfSAM sp E c m FGP ro).step self X Φ t k).1.store := by
  cases k with
  | tick =>
    change Q (acOnTickPC sp E c m self X Φ t).1.store
    unfold acOnTickPC
    dsimp only
    have hr : Q (if t = sp.ts (sp.slot t) + sp.Δ then tryVotePC sp E c m self X Φ t
        else (X, [])).1.store := by
      split_ifs
      · exact tryVotePC_storeStable hQ self X Φ t h
      · exact h
    generalize (if t = sp.ts (sp.slot t) + sp.Δ then tryVotePC sp E c m self X Φ t
      else (X, [])) = r at hr ⊢
    split_ifs <;> first | exact h | exact hr | exact hQ.decide_ok _ _ Φ t _ hr
  | proposal =>
    change Q (acProposalPC sp E c X Φ t).1.store
    unfold acProposalPC
    split_ifs <;> first | exact h | exact hQ.refresh_ok _ Φ t h
  | toFG => exact h
  | message msg =>
    cases msg with
    | inl v => exact tryVotePC_storeStable hQ self _ Φ t (hQ.record_ok _ t v h)
    | inr a => exact hQ.onAck_ok _ t a h
  | block B => exact acOnBlockPC_storeStable hQ self X Φ t B h
  | restart =>
    change Q (acRestartPC sp E c m ro self X Φ t).1.store
    rw [(acRestartPC_eq (E := E) (c := c) (m := m) (ro := ro) self X Φ t).2.2.2]
    have : ∀ (l : List (Blk sp.n FGP)) (P : PCStore sp.n), Q P →
        Q (l.foldl (fun P B => recordVotes sp P t (blockVotes B)) P) := by
      intro l
      induction l with
      | nil => exact fun _ hP => hP
      | cons B l ih => exact fun P hP => ih _ (hQ.records P t _ hP)
    exact this _ _ hQ.empty_ok

/-! ## The node's ack decisions across a call -/

/-- The decision sets a decision of slot `u` only, when there is none, on a block of the tree with
`μ` clean early supporters at the update. -/
theorem decideAck_myAcks {P : PCStore sp.n} {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time}
    {u s x : Nat} (h : (decideAck sp P A Φ t u).myAcks s = some x) :
    P.myAcks s = some x ∨ (s = u ∧ P.myAcks u = none ∧
      ∃ B ∈ Φ.tree, B.root = x ∧ pcMu sp ≤ confirmationScore sp A Φ u B) := by
  unfold decideAck at h
  split at h
  · exact Or.inl h
  · rename_i C _
    split_ifs at h with h₁
    · exact Or.inl h
    · split at h
      · exact Or.inl h
      · rename_i X hX
        dsimp only at h
        split_ifs at h with h₂
        · exact Or.inl h
        · change Function.update (refresh sp P Φ t).myAcks u (some X.root) s = some x at h
          by_cases hsu : s = u
          · subst hsu
            simp only [Function.update_self, Option.some.injEq] at h
            obtain ⟨⟨hXt, -, -⟩, hXs⟩ := (deepest_mem hX).1
            refine Or.inr ⟨rfl, ?_, X, hXt, h, hXs⟩
            simp only [not_or, Option.isSome_iff_ne_none, ne_eq, not_not] at h₁
            exact h₁.1
          · rw [Function.update_of_ne hsu] at h
            exact Or.inl h

theorem acOnTickPC_myAcks (self : Fin sp.n) (X : PCState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    {s x : Nat} (h : (acOnTickPC sp E c m self X Φ t).1.store.myAcks s = some x) :
    X.store.myAcks s = some x ∨ (X.store.myAcks s = none ∧
      ∃ B ∈ Φ.tree, B.root = x ∧ pcMu sp ≤
        confirmationScore sp (acOnTickPC sp E c m self X Φ t).1.core.ac Φ s B) := by
  unfold acOnTickPC at h ⊢
  dsimp only at h ⊢
  have hr : (if t = sp.ts (sp.slot t) + sp.Δ then tryVotePC sp E c m self X Φ t
      else (X, [])).1.store.myAcks = X.store.myAcks := by
    split_ifs
    · exact tryVotePC_myAcks self X Φ t
    · rfl
  generalize (if t = sp.ts (sp.slot t) + sp.Δ then tryVotePC sp E c m self X Φ t
    else (X, [])) = r at hr h ⊢
  split_ifs at h ⊢
  · rcases decideAck_myAcks h with h' | ⟨rfl, h₂, h₃⟩
    · rw [hr] at h'
      exact Or.inl h'
    · rw [hr] at h₂
      exact Or.inr ⟨h₂, h₃⟩
  · rw [hr] at h
    exact Or.inl h
  · exact Or.inl h

/-- **A call keeps the node's ack decisions**, but for the decision of the tick after its update:
then the decided slot had none, and the target is a block of the frame with `μ` clean early
supporters at the state after the call. -/
theorem step_myAcks (self : Fin sp.n) (X : PCState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (k : (preConfSAM sp E c m FGP ro).Call) {s x : Nat}
    (h : ((preConfSAM sp E c m FGP ro).step self X Φ t k).1.store.myAcks s = some x) :
    X.store.myAcks s = some x ∨ (k = .tick ∧ X.store.myAcks s = none ∧
      ∃ B ∈ Φ.tree, B.root = x ∧ pcMu sp ≤
        confirmationScore sp ((preConfSAM sp E c m FGP ro).step self X Φ t k).1.core.ac Φ s B) := by
  cases k with
  | tick =>
    rcases acOnTickPC_myAcks self X Φ t h with h' | ⟨h₁, h₂⟩
    · exact Or.inl h'
    · exact Or.inr ⟨rfl, h₁, h₂⟩
  | proposal =>
    left
    change (acProposalPC sp E c X Φ t).1.store.myAcks s = some x at h
    unfold acProposalPC at h
    split_ifs at h
    · exact h
    · exact h
  | toFG => exact Or.inl h
  | message msg =>
    left
    cases msg with
    | inl v =>
      change (tryVotePC sp E c m self _ Φ t).1.store.myAcks s = some x at h
      rw [tryVotePC_myAcks] at h
      exact (recordVote_myAcks X.store t v) ▸ h
    | inr a =>
      change (onAck sp X.store t a).myAcks s = some x at h
      rwa [onAck_myAcks] at h
  | block B =>
    left
    change (tryVotePC sp E c m self _ Φ t).1.store.myAcks s = some x at h
    rw [tryVotePC_myAcks] at h
    exact (recordVotes_myAcks X.store t _) ▸ h
  | restart =>
    exfalso
    change (acRestartPC sp E c m ro self X Φ t).1.store.myAcks s = some x at h
    rw [(acRestartPC_eq (E := E) (c := c) (m := m) (ro := ro) self X Φ t).2.2.2,
      (foldRecord_keeps t _ _).2.2.2.2] at h
    cases h

/-- **An emitted ack is a decision of its sender** at the call's pre-state. -/
theorem step_ack_emission (self : Fin sp.n) (X : PCState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (k : (preConfSAM sp E c m FGP ro).Call) {e : EmPC sp FGP}
    (he : e ∈ ((preConfSAM sp E c m FGP ro).step self X Φ t k).2) {a : Ack sp.n}
    (ha : e.msg = .inr a) : a.val = self ∧ X.store.myAcks a.slot = some a.target := by
  cases k with
  | tick =>
    change e ∈ (acOnTickPC sp E c m self X Φ t).2 at he
    unfold acOnTickPC at he
    dsimp only at he
    have hr : e ∈ (if t = sp.ts (sp.slot t) + sp.Δ then tryVotePC sp E c m self X Φ t
        else (X, [])).2 → a.val = self ∧ X.store.myAcks a.slot = some a.target := by
      split_ifs
      · exact fun he => tryVotePC_ack_emission self X Φ t he ha
      · exact fun he => absurd he List.not_mem_nil
    generalize (if t = sp.ts (sp.slot t) + sp.Δ then tryVotePC sp E c m self X Φ t
      else (X, [])) = r at hr he
    split_ifs at he <;> first | exact absurd he List.not_mem_nil | exact hr he
  | proposal => exact absurd he List.not_mem_nil
  | toFG => exact absurd he List.not_mem_nil
  | message msg =>
    cases msg with
    | inl v =>
      obtain ⟨h1, h2⟩ := tryVotePC_ack_emission self _ Φ t he ha
      exact ⟨h1, (recordVote_myAcks X.store t v) ▸ h2⟩
    | inr a' => exact absurd he List.not_mem_nil
  | block B =>
    obtain ⟨h1, h2⟩ := tryVotePC_ack_emission self _ Φ t he ha
    exact ⟨h1, (recordVotes_myAcks X.store t _) ▸ h2⟩
  | restart =>
    change e ∈ (acRestartPC sp E c m ro self X Φ t).2 at he
    rw [(acRestartPC_eq (E := E) (c := c) (m := m) (ro := ro) self X Φ t).2.1] at he
    exact absurd he List.not_mem_nil

end Consensus.Goldilocks.PreConfirmations

end
