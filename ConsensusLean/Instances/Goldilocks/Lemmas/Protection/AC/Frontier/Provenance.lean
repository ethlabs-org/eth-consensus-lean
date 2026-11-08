module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Protection.AC.Frontier.Defs
public import ConsensusLean.Instances.Goldilocks.Lemmas.Compose.Sleepy.RecordWrites
public import ConsensusLean.Instances.Goldilocks.Lemmas.Healing.AC.SlowLocks
import ConsensusLean.Lemmas.Tactic.Linarith

public section

/-! # Tier A protection, the frontier over AC traces: where records and locks come from

The provenance part of the frontier, which needs no comparison and no network premise; it holds
of every AC trace with the unlock given at a write mode:

* **the record writes of a call** (`call_record_writeAC`, after `Compose.call_writes`): the record
  after an honest call is the record before it, or a block of the call's frame that is the result
  of the call's update or the selection of one of its optimistic checks. The update and the
  optimistic confirmation at mode `wm` write the record as the parent's do
  (`updateConfirmationM_field`, `optimisticConfirmationM_of`); the given locks `u i` are not read;
* `record_originAC`: hence, by induction over the cuts, the record names genesis or an origin
  written at an earlier cut;
* `lock_below_originU` (Healing, with the unlock given): every stored lock sits below an origin of
  its slot from an earlier cut. -/

namespace Consensus.Goldilocks.Comparison

open SA Compose

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {tr : SATrace sp FGP ro}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)} {wm : WriteMode} {u : Nat → Set Lock}

/-! ### Record writes at a mode, with the locks given -/

/-- The last write of a sequence of record writes: the record is kept, or it is the root of a
written candidate. -/
theorem writes_lastAC {Φ : Frm sp.n FGP} {New : Blk sp.n FGP → Prop} {r r' : Nat}
    (h : Writes Φ New r r') : r' = r ∨ ∃ C ∈ Φ.tree, New C ∧ C.root = r' := by
  rw [writes_iff] at h
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hs ih =>
    obtain ⟨C, hC, hn, (⟨-, rfl⟩ | ⟨-, rfl⟩)⟩ := hs
    · exact ih
    · exact Or.inr ⟨C, hC, hn, rfl⟩

theorem writes_transAC {Φ : Frm sp.n FGP} {New : Blk sp.n FGP → Prop} {r r' r'' : Nat}
    (h : Writes Φ New r r') (h' : Writes Φ New r' r'') : Writes Φ New r r'' :=
  writes_iff.2 ((writes_iff.1 h).trans (writes_iff.1 h'))

theorem writes_optimisticM (A : SAState sp.n) (Φ : Frm sp.n FGP) (t : Time) {r : Nat}
    (hr : A.latestConfirmed = r) :
    Writes Φ (fun B => optimisticSelect sp A Φ t = some B) r
      (optimisticConfirmationM sp wm A Φ t).latestConfirmed :=
  optimisticConfirmationM_of (P := fun X => Writes Φ _ r X.latestConfirmed)
    (writes_optimistic A Φ t hr) (Compose.Writes.of_eq hr)

theorem writes_tryVoteWithM {L : Set Lock} (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) :
    Writes Φ (fun B => ∃ e ∈ (tryVoteWithM sp wm x L A Φ t).2,
        optimisticSelect sp (admitVote sp e.readPoint t e.msg) Φ t = some B)
      A.latestConfirmed (tryVoteWithM sp wm x L A Φ t).1.latestConfirmed := by
  unfold tryVoteWithM
  dsimp only
  by_cases h₁ : ¬ joined sp A t ∨ A.votedSlot = sp.slot t ∨ sp.ts (sp.slot t) + sp.Δ < t
  · rw [ite_eq_left h₁]
    exact Compose.Writes.of_eq rfl
  rw [ite_eq_right h₁]
  by_cases h₂ : t < sp.ts (sp.slot t) + sp.Δ ∧ (sp.slot t = 0 ∨ ¬ voteReady sp Φ (sp.slot t))
  · rw [ite_eq_left h₂]
    exact Compose.Writes.of_eq rfl
  rw [ite_eq_right h₂]
  refine (writes_optimisticM _ Φ t ?_).mono fun B hB => ⟨_, List.mem_singleton_self _, hB⟩
  rw [admitVote_latestConfirmed]
  split_ifs <;> rfl

theorem writes_onTickWithM {L : Set Lock} (x : Fin sp.n) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) :
    Writes Φ (fun C => (∃ e ∈ (acOnTickWithM sp wm x L A Φ t).2,
        optimisticSelect sp (admitVote sp e.readPoint t e.msg) Φ t = some C) ∨
        (t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t ∧ joined sp A t ∧
          getConfirmation sp A Φ (sp.slot t - 1) = some C))
      A.latestConfirmed (acOnTickWithM sp wm x L A Φ t).1.latestConfirmed := by
  unfold acOnTickWithM
  dsimp only
  by_cases hj : joined sp A t
  · rw [ite_eq_right (not_not_intro hj)]
    by_cases hu : t = sp.ts (sp.slot t) + sp.Δ
    · rw [ite_eq_left hu]
      by_cases ht : t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t
      · exfalso
        have := sp.toParams.hΔ
        linarith [ht.1.symm.trans hu]
      · rw [ite_eq_right ht]
        exact (writes_tryVoteWithM x A Φ t).mono fun C h => Or.inl h
    · rw [ite_eq_right hu]
      by_cases ht : t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t
      · rw [ite_eq_left ht, updateConfirmationM_field SAState.latestConfirmed (fun _ _ => rfl)]
        exact (writes_updateConfirmation A Φ t _).mono fun C h => Or.inr ⟨ht.1, ht.2, hj, h.1⟩
      · rw [ite_eq_right ht]
        exact Compose.Writes.of_eq rfl
  · rw [ite_eq_left hj]
    exact Compose.Writes.of_eq rfl

theorem acProposalWith_latestConfirmed (L : Set Lock) (A : SAState sp.n) (Φ : Frm sp.n FGP)
    (t : Time) : (acProposalWith sp L A Φ t).1.latestConfirmed = A.latestConfirmed := by
  unfold acProposalWith
  split_ifs <;> rfl

/-- **The record writes of an honest call** (`Compose.call_writes` with the unlock given, at a
write mode): every candidate is the result of the call's update or the selection of one of its
optimistic checks, a block of the call's frame. -/
theorem call_writesAC (hr : ACLocalRunU wm u H U tr) {x : Fin sp.n} (hx : x ∈ H) {i : Nat}
    {ℓ : ACLabel (goldilocksSA sp FGP ro)} (hc : tr.CallAt x i ℓ) :
    Writes ℓ.frame (fun C => ∃ s CV, ResultAt tr x i s C CV ∨ OptimisticLockAt tr x i s C CV)
      (tr.state x i).latestConfirmed (tr.post i).latestConfirmed := by
  obtain ⟨hΦ, -⟩ := frameIn_of_callAtU hr hx hc
  have opt : ∀ C, (∃ CV, OptimisticLockAt tr x i (sp.slot (tr.time i)) C CV) →
      ∃ s CV, ResultAt tr x i s C CV ∨ OptimisticLockAt tr x i s C CV :=
    fun C ⟨CV, h⟩ => ⟨_, CV, Or.inr h⟩
  have he := hr.exec i ℓ hc.2 (hc.1 ▸ hx)
  rw [hc.1] at he
  have hpost := congrArg Prod.fst he
  have hemits := congrArg Prod.snd he
  simp only at hpost hemits
  rw [← hpost]
  generalize hA : tr.state x i = A at hpost hemits
  cases hcall : ℓ.call with
  | tick =>
    rw [hcall] at hemits
    refine (writes_onTickWithM x A ℓ.frame _).mono fun C h => ?_
    rcases h with ⟨e, he', hsel⟩ | ⟨ht, hs0, hj, hC⟩
    · exact opt C ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr ⟨e, hemits ▸ he', rfl⟩)⟩, rfl, hsel, rfl⟩
    · have hu : UpdateAt tr x i (sp.slot (tr.time i) - 1) ℓ := by
        refine ⟨hc, hcall, ?_, hA ▸ hj⟩
        conv_lhs => rw [ht]
        simp only [SAParams.ts]
        push_cast [Nat.cast_sub hs0]
        ring
      exact ⟨_, _, Or.inl ⟨ℓ, hu, hA ▸ hC, rfl⟩⟩
  | proposal => exact Compose.Writes.of_eq (acProposalWith_latestConfirmed _ A _ _)
  | toFG => exact Compose.Writes.of_eq (toFG_latestConfirmed A _ _)
  | message m =>
    rw [hcall] at hemits
    have h₁ := writes_optimisticM (wm := wm) (admitVote sp A (tr.time i) m) ℓ.frame (tr.time i)
      (admitVote_latestConfirmed _ _ _)
    refine writes_transAC (h₁.mono fun C h => ?_)
      ((writes_tryVoteWithM x _ _ _).mono fun C h => ?_)
    · exact opt C ⟨_, ℓ, _, ⟨hc, Or.inl ⟨m, hcall, hA ▸ rfl⟩⟩, rfl, h, rfl⟩
    · obtain ⟨e, he', hsel⟩ := h
      exact opt C ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr ⟨e, hemits ▸ he', rfl⟩)⟩, rfl, hsel, rfl⟩
  | block B =>
    rw [hcall] at hemits
    have h₁ := writes_optimisticM (wm := wm) (blockReceipt sp A (tr.time i) B) ℓ.frame
      (tr.time i) (blockReceipt_latestConfirmed _ _ _)
    refine writes_transAC (h₁.mono fun C h => ?_)
      ((writes_tryVoteWithM x _ _ _).mono fun C h => ?_)
    · exact opt C ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inl ⟨B, hcall, hA ▸ rfl⟩)⟩, rfl, h, rfl⟩
    · obtain ⟨e, he', hsel⟩ := h
      exact opt C ⟨_, ℓ, _, ⟨hc, Or.inr (Or.inr ⟨e, hemits ▸ he', rfl⟩)⟩, rfl, hsel, rfl⟩
  | restart =>
    exact Compose.Writes.of_eq ((restart_state sp) FGP ro x A ℓ.frame (tr.time i) hΦ
      (hr.time_nonneg i)).2.2.1

/-- **The record names genesis or an origin** written at an earlier cut, a block of the frame of
that cut's call. -/
theorem record_originAC (hr : ACLocalRunU wm u H U tr) {y : Fin sp.n} (hy : y ∈ H) :
    ∀ i, (tr.state y i).latestConfirmed = sp.genesisRoot ∨
      ∃ C, C.root = (tr.state y i).latestConfirmed ∧ ∃ k < i, ∃ ℓ, tr.CallAt y k ℓ ∧
        C ∈ ℓ.frame.tree ∧ ∃ s CV, ResultAt tr y k s C CV ∨ OptimisticLockAt tr y k s C CV := by
  intro i
  induction i with
  | zero =>
    left
    change (tr.init y).latestConfirmed = _
    rw [hr.init y hy]
    rfl
  | succ i ih =>
    have mono : ∀ (h : (tr.state y i).latestConfirmed = sp.genesisRoot ∨
        ∃ C, C.root = (tr.state y i).latestConfirmed ∧ ∃ k < i, ∃ ℓ, tr.CallAt y k ℓ ∧
          C ∈ ℓ.frame.tree ∧ ∃ s CV, ResultAt tr y k s C CV ∨ OptimisticLockAt tr y k s C CV)
        (r : Nat), r = (tr.state y i).latestConfirmed → r = sp.genesisRoot ∨
        ∃ C, C.root = r ∧ ∃ k < i + 1, ∃ ℓ, tr.CallAt y k ℓ ∧
          C ∈ ℓ.frame.tree ∧ ∃ s CV, ResultAt tr y k s C CV ∨ OptimisticLockAt tr y k s C CV := by
      rintro (h | ⟨C, hCr, k, hk, ℓ, hc, hC, h⟩) r rfl
      · exact Or.inl h
      · exact Or.inr ⟨C, hCr, k, by omega, ℓ, hc, hC, h⟩
    by_cases hn : tr.node i = y ∧ tr.label i ≠ none
    · obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 hn.2
      have hc : tr.CallAt y i ℓ := ⟨hn.1, hℓ⟩
      rw [state_succ_of_call hc]
      rcases writes_lastAC (call_writesAC hr hy hc) with h | ⟨C, hC, hnew, hCr⟩
      · exact mono ih _ h
      · exact Or.inr ⟨C, hCr, i, by omega, ℓ, hc, hC, hnew⟩
    · have hst : tr.state y (i + 1) = tr.state y i := by
        simp only [Trace.state]; exact ite_eq_right hn
      rw [hst]
      exact mono ih _ rfl

/-- **The record field of the frontier**: at a cut within `b`, the record is genesis or names an
origin within `b`, in the frame of the call that wrote it. -/
theorem record_withinAC (hr : ACLocalRunU wm u H U tr) {y : Fin sp.n} (hy : y ∈ H) {b : Time}
    {i : Nat} (hi : ∀ k < i, tr.time k ≤ b) :
    (tr.state y i).latestConfirmed = sp.genesisRoot ∨
      ∃ C ∈ U, C.root = (tr.state y i).latestConfirmed ∧
        (∃ k < i, ∃ ℓ, tr.CallAt y k ℓ ∧ C ∈ ℓ.frame.tree) ∧ ∃ s, OriginWithinAC tr H C s b := by
  rcases record_originAC hr hy i with h | ⟨C, hCr, k, hk, ℓ, hc, hC, s, CV, hO⟩
  · exact Or.inl h
  · exact Or.inr ⟨C, (frameIn_of_callAtU hr hy hc).2 hC, hCr, ⟨k, hk, ℓ, hc, hC⟩, s,
      originWithinAC_iff.2 ⟨y, hy, k, CV, hi k hk, hO⟩⟩

/-- **The lock field of the frontier**: at a cut within `b`, every stored lock names a block of
`U` below an origin of its slot within `b` (`lock_below_originU`). -/
theorem locks_withinAC (hr : ACLocalRunU wm u H U tr) {y : Fin sp.n} (hy : y ∈ H) {b : Time}
    {i : Nat} (hi : ∀ k < i, tr.time k ≤ b) :
    ∀ l ∈ (tr.state y i).locks, ∃ L ∈ U, L.root = l.block ∧ OnOriginChainWithinAC tr H U L b := by
  intro l hl
  obtain ⟨L, hL, hLr, O, hLO, k, hk, CV, hO⟩ := lock_below_originU hr hy i l hl
  exact ⟨L, hL, hLr, onOriginChainWithinAC_iff.2
    (Or.inr ⟨O, l.slot, originWithinAC_iff.2 ⟨y, hy, k, CV, hi k hk, hO⟩, hLO⟩)⟩

end Consensus.Goldilocks.Comparison

end
