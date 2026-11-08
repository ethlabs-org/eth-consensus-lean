module
public import ConsensusLean.Instances.Goldilocks.Lemmas.Candidates.LockCount
public import ConsensusLean.Instances.Goldilocks.Lemmas.Candidates.LateCertificate
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Restart

public section

/-! # Counting evidence-release's stored weighted locks and saved-count rows at a write mode

Evidence-release's calls at a write mode `m` without the optimistic write, at any unlock stage
`E` with any context (`stepEM`), are lock steps of the weighted lock store (`stepEM_lockStep`)
and row steps of its saved-count rows (`stepEM_rowStep`): the unlock is the stage's
`unlockWith` of the stored weighted locks, only the update of slot `s − 1` at the tick at
`t_s + 2Δ` writes weighted locks (one per fast bit, of slot `s − 1`, expiry at most `s − 1 + k`)
and a saved-count row, and the restart keeps the weighted locks and drops the saved counts. So
along an AC trace of evidence-release's SA at mode `m` (`er_lockMemory`) and of the
late-certificate SA at mode `m` (`cert_lockMemory`, whose calls are evidence-release's at the
candidate's stage on its evidence-release state, `step_erM`), with one tick per honest node and
time, every honest node holds at most `(fast arm ? 2 : 1) · k` unexpired weighted locks, saves no
count of a slot `≥ slot(t)`, and holds saved counts in at most `max w 1` rows of the slots
`slot(t) − max w 1 ≤ j`, at every `w`. -/

namespace Consensus.Goldilocks.EvidenceRelease

open SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {m : WriteMode}
  {σ : Type} (E : UnlockStage sp wlockStore σ) (c : σ)

/-! ### The fields of the handlers -/

private theorem optimisticConfirmationWM_fields (h : m.optimistic = false) (X : WState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) : (optimisticConfirmationWM sp m X Φ t).wlocks = X.wlocks ∧
      (optimisticConfirmationWM sp m X Φ t).counts = X.counts := by
  unfold optimisticConfirmationWM withLocks
  rw [optimisticLocksWM_off h]
  exact ⟨rfl, rfl⟩

/-- The unlock of a call, as a store move. -/
private abbrev Moved (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) (W : Set WLock) : Prop :=
  W = X.wlocks ∨ ∃ (σ' : Type) (E' : UnlockStage sp wlockStore σ') (c' : σ') (s : Int)
    (V : View sp.n), W = wlockStore.unlockWith sp E' c' X.wlocks Φ t s V

private theorem tryVoteEM_fields (h : m.optimistic = false) (self : Fin sp.n) (X : WState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    Moved X Φ t (tryVoteEM sp E c m self X Φ t).1.wlocks ∧
      (tryVoteEM sp E c m self X Φ t).1.counts = X.counts := by
  unfold tryVoteEM
  dsimp only
  split_ifs with h₁ h₂ h₃
  · exact ⟨Or.inl rfl, rfl⟩
  · exact ⟨Or.inl rfl, rfl⟩
  · rw [(optimisticConfirmationWM_fields h _ Φ t).1, (optimisticConfirmationWM_fields h _ Φ t).2]
    exact ⟨Or.inr ⟨σ, E, c, _, _, rfl⟩, rfl⟩
  · rw [(optimisticConfirmationWM_fields h _ Φ t).1, (optimisticConfirmationWM_fields h _ Φ t).2]
    exact ⟨Or.inl rfl, rfl⟩

private theorem acProposalE_fields (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    Moved X Φ t (acProposalE sp E c X Φ t).1.wlocks ∧
      (acProposalE sp E c X Φ t).1.counts = X.counts := by
  unfold acProposalE
  split_ifs <;> first
    | exact ⟨Or.inl rfl, rfl⟩
    | exact ⟨Or.inr ⟨σ, E, c, _, _, rfl⟩, rfl⟩

/-- The new weighted locks of the update of slot `s` at mode `m`. -/
private theorem newOK_updateWritesM {A : SAState sp.n} {Φ : Frm sp.n FGP} {t : Time} {s : Nat}
    {C : Int → Nat → Nat} {N : Set (Nat × Bool × Nat)}
    (hN : updateNewLocksM sp m A Φ t s = some N) :
    NewOK sp wlockStore m.fastArm s (updateWritesM sp m A Φ C s N) := by
  obtain ⟨D, -, rfl⟩ := Option.map_eq_some_iff.1 hN
  rw [newOK_iff, keyInj_iff]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    refine ⟨rfl, ?_, fun hf => newLocksM_no_fast hf p hp⟩
    rcases mem_newLocksM.1 hp with ⟨-, B, -, rfl⟩ | ⟨B, -, rfl⟩
    · exact min_le_left _ _
    · exact le_rfl
  · rintro _ ⟨p₁, hp₁, rfl⟩ _ ⟨p₂, hp₂, rfl⟩ - hf
    change p₁.2.1 = p₂.2.1 at hf
    rcases mem_newLocksM.1 hp₁ with ⟨-, B₁, h₁, rfl⟩ | ⟨B₁, h₁, rfl⟩ <;>
      rcases mem_newLocksM.1 hp₂ with ⟨-, B₂, h₂, rfl⟩ | ⟨B₂, h₂, rfl⟩
    · obtain rfl : B₁ = B₂ := Option.some_injective _ (h₁.symm.trans h₂)
      rfl
    · exact absurd hf Bool.noConfusion
    · exact absurd hf Bool.noConfusion
    · obtain rfl : B₁ = B₂ := Option.some_injective _ (h₁.symm.trans h₂)
      rfl

/-- The weighted update after a moved store, at a tick at `t_s + 2Δ`, is a lock step. -/
private theorem upd_lockStep {X Y : WState sp.n} {Φ : Frm sp.n FGP} {t : Time} {tk : Prop}
    (htk : tk) (hY : Moved X Φ t Y.wlocks)
    (hu : t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t) :
    LockStep sp wlockStore m.fastArm X.wlocks
      (updateConfirmationWM sp m Y Φ t (sp.slot t - 1)).wlocks Φ t tk := by
  change LockStep sp wlockStore m.fastArm X.wlocks
    (updateLocksWM sp m Y.wlocks Y.ac Y.counts Φ t (sp.slot t - 1)) Φ t tk
  unfold updateLocksWM
  split
  · exact (lockStep_iff _ _ _ _ _ _).2 ⟨_, hY, Or.inl rfl⟩
  · rename_i N hN
    exact (lockStep_iff _ _ _ _ _ _).2 ⟨_, hY,
      Or.inr ⟨htk, hu.1, hu.2, _, newOK_updateWritesM hN, rfl⟩⟩

private theorem keep_lockStep {X : WState sp.n} {Φ : Frm sp.n FGP} {t : Time} {W : Set WLock}
    (tk : Prop) (hW : Moved X Φ t W) : LockStep sp wlockStore m.fastArm X.wlocks W Φ t tk :=
  (lockStep_iff _ _ _ _ _ _).2 ⟨W, hW, Or.inl rfl⟩

/-- The restart keeps the weighted locks and drops the saved counts. -/
private theorem acRestartEM_fields {X : WState sp.n} (hX : LocksForget X)
    (ro : ReplayOrder sp FGP) (self : Fin sp.n) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time}
    (ht : 0 ≤ t) : (acRestartEM sp E c m ro self X Φ t).1.wlocks = X.wlocks ∧
      (acRestartEM sp E c m ro self X Φ t).1.counts = fun _ _ => 0 := by
  have hl := ro.parentOrder t Φ (parentOrder_exists sp hΦ)
  let A' : SAState sp.n := { SAState.initial sp.genesisRoot with
    locks := X.ac.locks, latestConfirmed := X.ac.latestConfirmed,
    restartTime := (t : WithBot Time) }
  have h₀ : RestartInv sp X.ac Φ t A' :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun σ x hx => by simp [A', SAState.initial] at hx,
      fun x => Or.inl rfl, fun q => Or.inl rfl⟩
  have key : ∀ l : List (Blk sp.n FGP), (∀ B ∈ l, B ∈ Φ.tree ∧ B.root ≠ sp.genesisRoot) →
      ∀ acc : WState sp.n × List (EmW sp FGP), acc.1.wlocks = X.wlocks →
      acc.1.counts = (fun _ _ => 0) → LocksForget acc.1 → RestartInv sp X.ac Φ t acc.1.ac →
      let r := l.foldl (fun acc B => let r := acOnBlockEM sp E c m self acc.1 Φ t B;
        (r.1, acc.2 ++ r.2)) acc
      r.1.wlocks = X.wlocks ∧ r.1.counts = fun _ _ => 0 := by
    intro l
    induction l with
    | nil => intro _ acc hw hc _ _; exact ⟨hw, hc⟩
    | cons B l ih =>
      intro hl acc hw hc hf h₁
      obtain ⟨hB, hg⟩ := hl B List.mem_cons_self
      have hR := h₁.blockReceipt sp hB hg
      have hnj := not_joined_of_restartTime sp ht hR.restartTime
      have hb := acOnBlockEM_of_not_joined E c m hf self Φ t B hnj
      simp only [List.foldl_cons]
      apply ih (fun C hC => hl C (List.mem_cons_of_mem _ hC))
      · simp only [hb]; exact hw
      · simp only [hb]; exact hc
      · simp only [hb]
        exact (locksForget_iff _).2
          ((blockReceipt_keeps_locks acc.1.ac t B).1.trans ((locksForget_iff acc.1).1 hf))
      · simp only [hb]; exact hR
  exact key (ro.order t Φ) (fun B hB => (hl.2.1 B).mp hB)
    ({ ac := A', wlocks := X.wlocks, counts := fun _ _ => 0 }, []) rfl rfl
    ((locksForget_iff _).2 ((locksForget_iff X).1 hX)) h₀

/-! ### The steps -/

/-- **Evidence-release's calls at mode `m` without the optimistic write are lock steps**, at
every unlock stage. -/
theorem stepEM_lockStep (h : m.optimistic = false) (self : Fin sp.n) {X : WState sp.n}
    (hX : LocksForget X) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} (ht : 0 ≤ t)
    (k : (goldilocksSA sp FGP ro).Call) :
    LockStep sp wlockStore m.fastArm X.wlocks (stepEM sp ro E c m self X Φ t k).1.wlocks Φ t
      (k = .tick) := by
  cases k with
  | tick =>
    simp only [stepEM, acOnTickEM]
    split_ifs <;> first
      | exact keep_lockStep _ (Or.inl rfl)
      | exact keep_lockStep _ (tryVoteEM_fields E c h _ _ _ _).1
      | exact upd_lockStep trivial (tryVoteEM_fields E c h _ _ _ _).1 ‹_›
      | exact upd_lockStep trivial (Or.inl rfl) ‹_›
  | proposal => exact keep_lockStep _ (acProposalE_fields E c _ _ _).1
  | toFG => exact keep_lockStep _ (Or.inl rfl)
  | message v =>
    simp only [stepEM, acOnMessageEM]
    have := (tryVoteEM_fields E c h self
      (optimisticConfirmationWM sp m { X with ac := admitVote sp X.ac t v } Φ t) Φ t).1
    unfold Moved at this
    rw [(optimisticConfirmationWM_fields h _ Φ t).1] at this
    exact keep_lockStep _ this
  | block B =>
    simp only [stepEM, acOnBlockEM]
    have := (tryVoteEM_fields E c h self
      (optimisticConfirmationWM sp m { X with ac := blockReceipt sp X.ac t B } Φ t) Φ t).1
    unfold Moved at this
    rw [(optimisticConfirmationWM_fields h _ Φ t).1] at this
    exact keep_lockStep _ this
  | restart =>
    simp only [stepEM]
    rw [(acRestartEM_fields E c hX ro self hΦ ht).1]
    exact keep_lockStep _ (Or.inl rfl)

/-- The saved-count rows of a weighted state. -/
abbrev countRowSet (X : WState sp.n) : Set Int := {j | ∃ r, X.counts j r ≠ 0}

private theorem keep_rowStep {X Y : WState sp.n} {t : Time} (tk : Prop)
    (hY : Y.counts = X.counts) : RowStep (sp := sp) (countRowSet X) (countRowSet Y) t tk :=
  (rowStep_iff _ _ _ _).2 fun j ⟨r, hj⟩ => Or.inl ⟨r, by rw [← hY]; exact hj⟩

private theorem upd_rowStep {X Y : WState sp.n} {Φ : Frm sp.n FGP} {t : Time} {tk : Prop}
    (htk : tk) (hY : Y.counts = X.counts)
    (hu : t = sp.ts (sp.slot t) + 2 * sp.Δ ∧ 0 < sp.slot t) :
    RowStep (sp := sp) (countRowSet X)
      (countRowSet (updateConfirmationWM sp m Y Φ t (sp.slot t - 1))) t tk := by
  refine (rowStep_iff _ _ _ _).2 fun j ⟨r, hj⟩ => ?_
  change saveCount sp Y.counts Y.ac Φ (sp.slot t - 1) j r ≠ 0 at hj
  unfold saveCount at hj
  by_cases hjs : j = ((sp.slot t - 1 : Nat) : Int)
  · exact Or.inr ⟨htk, hu.1, hu.2, hjs⟩
  · rw [Function.update_of_ne hjs, hY] at hj
    exact Or.inl ⟨r, hj⟩

/-- **Evidence-release's calls at mode `m` without the optimistic write are row steps** of the
saved-count rows, at every unlock stage. -/
theorem stepEM_rowStep (h : m.optimistic = false) (self : Fin sp.n) {X : WState sp.n}
    (hX : LocksForget X) {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} (ht : 0 ≤ t)
    (k : (goldilocksSA sp FGP ro).Call) :
    RowStep (sp := sp) (countRowSet X) (countRowSet (stepEM sp ro E c m self X Φ t k).1) t
      (k = .tick) := by
  cases k with
  | tick =>
    simp only [stepEM, acOnTickEM]
    split_ifs <;> first
      | exact keep_rowStep _ rfl
      | exact keep_rowStep _ (tryVoteEM_fields E c h _ _ _ _).2
      | exact upd_rowStep trivial (tryVoteEM_fields E c h _ _ _ _).2 ‹_›
      | exact upd_rowStep trivial rfl ‹_›
  | proposal => exact keep_rowStep _ (acProposalE_fields E c _ _ _).2
  | toFG => exact keep_rowStep _ rfl
  | message v =>
    simp only [stepEM, acOnMessageEM]
    refine keep_rowStep _ ?_
    rw [(tryVoteEM_fields E c h _ _ _ _).2, (optimisticConfirmationWM_fields h _ Φ t).2]
  | block B =>
    simp only [stepEM, acOnBlockEM]
    refine keep_rowStep _ ?_
    rw [(tryVoteEM_fields E c h _ _ _ _).2, (optimisticConfirmationWM_fields h _ Φ t).2]
  | restart =>
    refine (rowStep_iff _ _ _ _).2 fun j ⟨r, hj⟩ => ?_
    simp only [stepEM] at hj
    rw [(acRestartEM_fields E c hX ro self hΦ ht).2] at hj
    exact absurd rfl hj

/-! ### Along the traces of the evidence-release and late-certificate SAs -/

variable {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}

/-- **Evidence-release at mode `m` without the optimistic write: lock memory and working rows.**
On an AC trace of evidence-release's SA at mode `m` with one tick per honest node and time,
every honest node holds before each cut at most `(fast arm ? 2 : 1) · k` unexpired weighted
locks, saves no count of a slot `≥ slot(t)`, and holds saved counts in at most `max w 1` rows of
the slots `slot(t) − max w 1 ≤ j`, at every `w`. -/
theorem er_lockMemory (hopt : m.optimistic = false) {tr : ACTrace (evidenceReleaseSAM sp m FGP ro)}
    (h : ACLocalRun (evidenceReleaseSAM sp m FGP ro) H U tr)
    (hone : ∀ y ∈ H, ∀ i j (ℓ ℓ' : ACLabel (evidenceReleaseSAM sp m FGP ro)), tr.CallAt y i ℓ →
      tr.CallAt y j ℓ' → ℓ.call = .tick → ℓ'.call = .tick → tr.time i = tr.time j → i = j)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    {w | w ∈ (tr.state y i).wlocks ∧ w.lock.LiveAt sp (tr.time i)}.encard ≤
        ((if m.fastArm then 2 else 1) * sp.k : ℕ) ∧
      (∀ (j : Int) r, (tr.state y i).counts j r ≠ 0 → j < sp.slot (tr.time i)) ∧
      ∀ w : Nat, {j : Int | (sp.slot (tr.time i) : Int) - (max w 1 : Nat) ≤ j ∧
        ∃ r, (tr.state y i).counts j r ≠ 0}.encard ≤ (max w 1 : ℕ) := by
  have h0 : tr.state y 0 = WState.initial sp.genesisRoot := h.init y hy
  have hΦ : ∀ i ℓ, tr.CallAt y i ℓ → FrameOK ℓ.frame := fun i ℓ hc => by
    rcases h.frameLaw y hy i ℓ hc with ⟨-, Φ₀, -, -, hk⟩ | ⟨-, ℓ₀, -, -, -, hk⟩ <;> exact hk.1.1
  have hpost : ∀ i ℓ, tr.CallAt y i ℓ → tr.post i = (stepEM sp ro (evidenceStage sp) () m y
      (tr.state y i) ℓ.frame (tr.time i) (projCallM ro ℓ.call)).1 := fun i ℓ hc => by
    have he := h.exec i ℓ hc.2 (hc.1 ▸ hy)
    rw [hc.1, step_eq_stepEM] at he
    rw [he]
  have htk : ∀ k : (evidenceReleaseSAM sp m FGP ro).Call, projCallM ro k = .tick → k = .tick := by
    intro k hk
    cases k <;> first | rfl | exact absurd hk (by simp)
  have hinv := lockInv_of_steps (tr := tr) (y := y) wlockStore_lawful WState.wlocks m.fastArm
    (by rw [h0]; rfl) (fun i ℓ hc => ⟨ℓ.frame, (hΦ i ℓ hc).coherent.1, by
      rw [hpost i ℓ hc]
      exact (stepEM_lockStep (evidenceStage sp) () hopt y (locksForget_stateM h hy i)
        (hΦ i ℓ hc) (h.time_nonneg i) _).mono_tick (htk _)⟩)
    (hone y hy) i
  have hrows := rowInv_of_steps (tr := tr) (y := y) countRowSet
    (by rw [h0]; ext j; simp [WState.initial]) (fun i ℓ hc => by
      rw [hpost i ℓ hc]
      exact (stepEM_rowStep (evidenceStage sp) () hopt y (locksForget_stateM h hy i)
        (hΦ i ℓ hc) (h.time_nonneg i) _).mono_tick (htk _)) i
  have hlt := row_lt_slot (tr := tr) h.time_mono (h.time_nonneg i) hrows
  exact ⟨held_encard_le h.time_mono (h.time_nonneg i) hinv, fun j r hj => hlt j ⟨r, hj⟩,
    fun w => rows_encard_le (R := countRowSet (tr.state y i)) hlt (max w 1)⟩

end Consensus.Goldilocks.EvidenceRelease

namespace Consensus.Goldilocks.LateCertificate

open SA EvidenceRelease

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP} {m : WriteMode}
  {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}

/-- **The late-certificate rule at mode `m` without the optimistic write: lock memory and
working rows**, on its evidence-release state, as `er_lockMemory`. -/
theorem cert_lockMemory (hopt : m.optimistic = false) {tr : ACTrace (certRecoverySAM sp m FGP ro)}
    (h : ACLocalRun (certRecoverySAM sp m FGP ro) H U tr)
    (hone : ∀ y ∈ H, ∀ i j (ℓ ℓ' : ACLabel (certRecoverySAM sp m FGP ro)), tr.CallAt y i ℓ →
      tr.CallAt y j ℓ' → ℓ.call = .tick → ℓ'.call = .tick → tr.time i = tr.time j → i = j)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) :
    {w | w ∈ (tr.state y i).er.wlocks ∧ w.lock.LiveAt sp (tr.time i)}.encard ≤
        ((if m.fastArm then 2 else 1) * sp.k : ℕ) ∧
      (∀ (j : Int) r, (tr.state y i).er.counts j r ≠ 0 → j < sp.slot (tr.time i)) ∧
      ∀ w : Nat, {j : Int | (sp.slot (tr.time i) : Int) - (max w 1 : Nat) ≤ j ∧
        ∃ r, (tr.state y i).er.counts j r ≠ 0}.encard ≤ (max w 1 : ℕ) := by
  have h0 : (tr.state y 0).er = WState.initial sp.genesisRoot := by
    rw [Trace.state, h.init y hy]
    rfl
  have hΦ : ∀ i ℓ, tr.CallAt y i ℓ → FrameOK ℓ.frame := fun i ℓ hc => by
    rcases h.frameLaw y hy i ℓ hc with ⟨-, Φ₀, -, -, hk⟩ | ⟨-, ℓ₀, -, -, -, hk⟩ <;> exact hk.1.1
  have hpost : ∀ i ℓ, tr.CallAt y i ℓ → (tr.post i).er = (stepEM sp ro (certStageW sp)
      (ctxCM ro (tr.state y i) (tr.time i) ℓ.call) m y (tr.state y i).er ℓ.frame (tr.time i)
      (projCallCM ro ℓ.call)).1 := fun i ℓ hc => by
    have he := h.exec i ℓ hc.2 (hc.1 ▸ hy)
    rw [hc.1] at he
    rw [← (step_erM y (tr.state y i) ℓ.frame (tr.time i) ℓ.call).1, he]
  have htk : ∀ k : (certRecoverySAM sp m FGP ro).Call, projCallCM ro k = .tick → k = .tick := by
    intro k hk
    cases k <;> first | rfl | exact absurd hk (by simp)
  have hinv := lockInv_of_steps (tr := tr) (y := y) wlockStore_lawful (fun X => X.er.wlocks)
    m.fastArm (by rw [h0]; rfl) (fun i ℓ hc => ⟨ℓ.frame, (hΦ i ℓ hc).coherent.1, by
      rw [hpost i ℓ hc]
      exact (stepEM_lockStep (certStageW sp) _ hopt y (locksForget_state_certM h hy i)
        (hΦ i ℓ hc) (h.time_nonneg i) _).mono_tick (htk _)⟩)
    (hone y hy) i
  have hrows := rowInv_of_steps (tr := tr) (y := y) (fun X => countRowSet X.er)
    (by rw [h0]; ext j; simp [WState.initial]) (fun i ℓ hc => by
      rw [hpost i ℓ hc]
      exact (stepEM_rowStep (certStageW sp) _ hopt y (locksForget_state_certM h hy i)
        (hΦ i ℓ hc) (h.time_nonneg i) _).mono_tick (htk _)) i
  have hlt := row_lt_slot (tr := tr) h.time_mono (h.time_nonneg i) hrows
  exact ⟨held_encard_le h.time_mono (h.time_nonneg i) hinv, fun j r hj => hlt j ⟨r, hj⟩,
    fun w => rows_encard_le (R := countRowSet (tr.state y i).er) hlt (max w 1)⟩

end Consensus.Goldilocks.LateCertificate


end
