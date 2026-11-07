module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.EvidenceRelease.Projection
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.EvidenceRelease.Rule
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.LockRule
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace

public section

/-! # Evidence-release traces are SA traces with the unlock given

The weighted handlers of any unlock stage, forgotten, are the parent's handlers with the locks
after the unlock given (`Projection`). Here that step correspondence is lifted to traces:

* `stepE`: a call of the weighted SA at a stage `E` with context `c`; its forgotten result is
  `stepWith` at the forgotten locks after the stage's unlock of the call's input
  (`unlockAtE`, `stepWith_stepE`), which the parent's unlock relation relates to the call's
  unlock input for every lawful stage (`unlockRel_unlockWith`, `unlockAtE_rel`);
* `projTrace`: an AC trace of the evidence-release SA with its states, calls and emissions
  forgotten; its honest states keep `LocksForget` (`locksForget_state`), and its run is a run
  with the unlock given by `erOracle` (`localRunU_projTrace`).

So every lemma over `ACLocalRunU` (H.1 and its cone) applies to evidence-release's runs. -/

namespace Consensus.Goldilocks.EvidenceRelease

open SA

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}

/-! ### The unlock relation for every lawful stage -/

/-- **The forgotten unlock of a lawful stage satisfies the parent's unlock relation.** -/
theorem unlockRel_unlockWith {S : LockStore} {σ : Type} (hS : S.Lawful)
    {E : UnlockStage sp S σ} {K : UnlockStage.Keep sp S σ} (hE : E.Lawful K) (c : σ)
    {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (L : Set S.Lk) (t : Time) (s : Int) (V : View sp.n) :
    UnlockRel sp (S.lock '' L) Φ t s V (S.lock '' S.unlockWith sp E c L Φ t s V) := by
  rintro _ ⟨w', hw', rfl⟩
  obtain ⟨w, hw, B, hB, hBr, hlive, rfl⟩ := LockStore.mem_unlockWith_stored hS hE hΦ hw'
  have hvt := (viableAncestor_anc hΦ hB).1
  obtain ⟨hTt, -⟩ := unlockTarget_anc sp hΦ V s hvt
  refine ⟨S.lock w, ⟨w, hw, rfl⟩, B, hB, hBr, hlive, ?_⟩
  split_ifs with hlt
  · obtain ⟨h0, h1, h2, h3⟩ := LockStore.lock_withBlock_fields hS w
      (E.target c Φ V s w (unlockTarget sp Φ V s (Φ.viableAncestor B))).root
    obtain ⟨hYt, hYT⟩ := hE.target_anc c V s w hΦ hTt
    exact ⟨h1, h2, h3, fun _ => ⟨_, hYt, h0.symm, hYT⟩, fun h => absurd hlt (not_lt.2 h)⟩
  · obtain ⟨h0, h1, h2, h3⟩ := LockStore.lock_withBlock_fields hS w (Φ.viableAncestor B).root
    exact ⟨h1, h2, h3, fun h => absurd h hlt, fun _ => h0⟩

/-! ### A call at a stage -/

section Stage

variable {σ : Type} (E : UnlockStage sp wlockStore σ) (c : σ)

variable (sp ro) in
/-- A call of the weighted SA at the stage `E` with context `c`. -/
noncomputable abbrev stepE (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (goldilocksSA sp FGP ro).Call → WState sp.n × List (EmW sp FGP)
  | .tick => acOnTickE sp E c self X Φ t
  | .proposal => ((acProposalE sp E c X Φ t).1, [])
  | .toFG => ((acToFGW sp X Φ t).1, [])
  | .message m => acOnMessageE sp E c self X Φ t m
  | .block B => acOnBlockE sp E c self X Φ t B
  | .restart => acRestartE sp E c ro self X Φ t

variable (sp) in
/-- The weighted state whose locks the unlock of the call reads (`callInput`). -/
noncomputable abbrev callInputW (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (goldilocksSA sp FGP ro).Call → WState sp.n
  | .message v => optimisticConfirmationW sp { X with ac := admitVote sp X.ac t v } Φ t
  | .block B => optimisticConfirmationW sp { X with ac := blockReceipt sp X.ac t B } Φ t
  | _ => X

variable (sp) in
/-- The forgotten locks after the stage's unlock of the call's input. -/
noncomputable abbrev unlockAtE (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (k : (goldilocksSA sp FGP ro).Call) : Set Lock :=
  WLock.lock '' wlockStore.unlockWith sp E c (callInputW sp X Φ t k).wlocks Φ t
    ((sp.slot t : Int) - 1) (callView sp X.ac Φ t k)

theorem callInputW_spec {X : WState sp.n} (hX : LocksForget X) (Φ : Frm sp.n FGP) (t : Time)
    (k : (goldilocksSA sp FGP ro).Call) :
    LocksForget (callInputW sp X Φ t k) ∧ (callInputW sp X Φ t k).ac = callInput sp X.ac Φ t k := by
  cases k with
  | message v =>
    exact ⟨locksForget_optimisticConfirmationW _ _ _,
      optimisticConfirmationW_ac (locksForget_admitVote hX t v) Φ t⟩
  | block B =>
    exact ⟨locksForget_optimisticConfirmationW _ _ _, optimisticConfirmationW_ac
      ((locksForget_iff _).2 ((blockReceipt_keeps_locks X.ac t B).1.trans ((locksForget_iff _).1
          hX))) Φ t⟩
  | _ => exact ⟨hX, rfl⟩

/-- **The stage's unlock is related to the call's unlock input**, for every stage whose
forgotten unlock satisfies the unlock relation at the frame. -/
theorem unlockAtE_rel {Φ : Frm sp.n FGP}
    (hrel : ∀ (L : Set WLock) (t : Time) (s : Int) (V : View sp.n),
      UnlockRel sp (WLock.lock '' L) Φ t s V (WLock.lock '' wlockStore.unlockWith sp E c L Φ t s V))
    {X : WState sp.n} (hX : LocksForget X) (t : Time) (k : (goldilocksSA sp FGP ro).Call) :
    UnlockRel sp (callInput sp X.ac Φ t k).locks Φ t ((sp.slot t : Int) - 1)
      (callView sp X.ac Φ t k) (unlockAtE sp E c X Φ t k) := by
  obtain ⟨hf, he⟩ := callInputW_spec hX Φ t k
  rw [← he, (locksForget_iff _).1 hf]
  exact hrel _ t _ _

/-- **A call at a stage, forgotten, is `stepWith` of the stage's unlock.** -/
theorem stepWith_stepE {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} (ht : 0 ≤ t)
    (k : (goldilocksSA sp FGP ro).Call) :
    stepWith sp ro self (unlockAtE sp E c X Φ t k) X.ac Φ t k =
      ((stepE sp ro E c self X Φ t k).1.ac, (stepE sp ro E c self X Φ t k).2.map projEm) := by
  cases k with
  | tick => exact (acOnTickE_proj E c hX self Φ t).symm
  | proposal =>
    have h := congrArg Prod.fst (acProposalE_proj E c X Φ t)
    exact Prod.ext h.symm rfl
  | toFG => rfl
  | message v =>
    have h := acOnMessageE_proj E c hX self Φ t v
    dsimp only at h
    rw [optimisticConfirmationW_ac (locksForget_admitVote hX t v) Φ t] at h
    exact h.symm
  | block B =>
    have h := acOnBlockE_proj E c hX self Φ t B
    dsimp only at h
    rw [optimisticConfirmationW_ac ((locksForget_iff _).2
      ((blockReceipt_keeps_locks X.ac t B).1.trans ((locksForget_iff _).1 hX))) Φ t] at h
    exact h.symm
  | restart =>
    obtain ⟨h1, h2, -⟩ := acRestartE_proj E c hX ro self hΦ ht
    refine Prod.ext h1.symm ?_
    change (acRestart sp ro self X.ac Φ t).2 = (acRestartE sp E c ro self X Φ t).2.map projEm
    rw [h2, (restart_state sp FGP ro self X.ac Φ t hΦ ht).1]
    rfl

/-- Every call at a stage keeps `LocksForget`. -/
theorem locksForget_stepE {X : WState sp.n} (hX : LocksForget X) (self : Fin sp.n)
    {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) {t : Time} (ht : 0 ≤ t)
    (k : (goldilocksSA sp FGP ro).Call) : LocksForget (stepE sp ro E c self X Φ t k).1 := by
  cases k with
  | tick => exact (locksForget_acOnTickE E c hX self Φ t).1
  | proposal => exact locksForget_acProposalE E c hX Φ t
  | toFG => exact locksForget_acToFGW hX Φ t
  | message v => exact (locksForget_acOnMessageE E c self X Φ t v).1
  | block B => exact (locksForget_acOnBlockE E c self X Φ t B).1
  | restart => exact (acRestartE_proj E c hX ro self hΦ ht).2.2

end Stage

/-! ### Evidence-release's traces -/

variable (ro) in
/-- The parent's call of a call of the evidence-release SA. -/
abbrev projCall : (evidenceReleaseSA sp FGP ro).Call → (goldilocksSA sp FGP ro).Call
  | .tick => .tick
  | .proposal => .proposal
  | .toFG => .toFG
  | .message m => .message m
  | .block B => .block B
  | .restart => .restart

theorem step_eq_stepE (self : Fin sp.n) (X : WState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (k : (evidenceReleaseSA sp FGP ro).Call) :
    (evidenceReleaseSA sp FGP ro).step self X Φ t k =
      stepE sp ro (evidenceStage sp) () self X Φ t (projCall ro k) := by
  cases k <;> rfl

theorem projCall_eq_restart {k : (evidenceReleaseSA sp FGP ro).Call} :
    projCall ro k = .restart ↔ k = .restart := by
  cases k <;> simp

theorem callOK_projCall {U : Set (Blk sp.n FGP)} {Φ Φ' : Frm sp.n FGP} {t : Time}
    {k : (evidenceReleaseSA sp FGP ro).Call} (h : (evidenceReleaseSA sp FGP ro).CallOK U Φ t k Φ') :
    (goldilocksSA sp FGP ro).CallOK U Φ t (projCall ro k) Φ' := by
  cases k <;> exact h

/-- The parent's label of a label of the evidence-release SA. -/
abbrev projLabel (ℓ : ACLabel (evidenceReleaseSA sp FGP ro)) : ACLabel (goldilocksSA sp FGP ro) :=
  ⟨projCall ro ℓ.call, ℓ.frame, ℓ.emits.map projEm⟩

/-- **The forgotten trace**: the parent's states, calls and emissions of an AC trace of the
evidence-release SA. -/
abbrev projTrace (tr : ACTrace (evidenceReleaseSA sp FGP ro)) : SATrace sp FGP ro where
  init y := (tr.init y).ac
  node := tr.node
  time := tr.time
  event := tr.event
  pos := tr.pos
  label i := (tr.label i).map projLabel
  post i := (tr.post i).ac
  awake := tr.awake
  observationHorizon := tr.observationHorizon

/-- The unlock oracle of a trace of the evidence-release SA: at each labelled cut, the forgotten
locks after `unlockW` of the call's input. -/
noncomputable abbrev erOracle (tr : ACTrace (evidenceReleaseSA sp FGP ro)) (i : Nat) :
    Set Lock :=
  match tr.label i with
  | some ℓ => unlockAtE sp (evidenceStage sp) () (tr.state (tr.node i) i) ℓ.frame (tr.time i)
      (projCall ro ℓ.call)
  | none => ∅

variable {tr : ACTrace (evidenceReleaseSA sp FGP ro)}

theorem projTrace_state (y : Fin sp.n)
    (i : Nat) : (projTrace tr).state y i = (tr.state y i).ac := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [Trace.state]
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact absurd ⟨h₁.1, by simpa using h₁.2⟩ h₂
    · exact absurd ⟨h₂.1, by simpa using h₂.2⟩ h₁
    · exact ih

theorem projTrace_callAt {y : Fin sp.n} {i : Nat} {ℓP : ACLabel (goldilocksSA sp FGP ro)} :
    (projTrace tr).CallAt y i ℓP ↔ ∃ ℓ, tr.CallAt y i ℓ ∧ projLabel ℓ = ℓP := by
  simp only [Trace.CallAt, Option.map_eq_some_iff]
  constructor
  · rintro ⟨h1, ℓ, h2, rfl⟩
    exact ⟨ℓ, ⟨h1, h2⟩, rfl⟩
  · rintro ⟨ℓ, ⟨h1, h2⟩, rfl⟩
    exact ⟨h1, ℓ, h2, rfl⟩

theorem projTrace_noCallBetween {y : Fin sp.n} {j i : Nat} :
    (projTrace tr).NoCallBetween y j i ↔ tr.NoCallBetween y j i :=
  ⟨fun h k hj hi ℓ hc => h k hj hi _ (projTrace_callAt.2 ⟨ℓ, hc, rfl⟩),
    fun h k hj hi _ hc => by
      obtain ⟨ℓ, hc, -⟩ := projTrace_callAt.1 hc
      exact h k hj hi ℓ hc⟩

theorem projTrace_restartAt {y : Fin sp.n} {k : Nat} :
    (projTrace tr).RestartAt y k ↔ tr.RestartAt y k := by
  constructor
  · rintro ⟨_, hc, hr⟩
    obtain ⟨ℓ, hc₀, rfl⟩ := projTrace_callAt.1 hc
    exact ⟨ℓ, hc₀, projCall_eq_restart.1 hr⟩
  · rintro ⟨ℓ, hc, hr⟩
    exact ⟨_, projTrace_callAt.2 ⟨ℓ, hc, rfl⟩, projCall_eq_restart.2 hr⟩

variable {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}

/-- At a proposal call, the oracle's `ac_proposal` is evidence-release's, forgotten: the honest
proposals with the unlock given (`HonestProposalU`, `DrivenU`) are evidence-release's. -/
theorem acProposalWith_erOracle {x : Fin sp.n} {k : Nat}
    {ℓ : ACLabel (evidenceReleaseSA sp FGP ro)} (hc : tr.CallAt x k ℓ)
    (hcall : ℓ.call = .proposal) :
    acProposalWith sp (erOracle tr k) ((projTrace tr).state x k) ℓ.frame (tr.time k) =
      ((acProposalW sp (tr.state x k) ℓ.frame (tr.time k)).1.ac,
        (acProposalW sp (tr.state x k) ℓ.frame (tr.time k)).2) := by
  rw [projTrace_state, acProposalW_proj]
  simp only [erOracle, hc.2, hc.1, hcall]
  rfl

/-- Reachable states of the evidence-release SA keep `LocksForget`, at times from `0`. -/
theorem locksForget_of_reachable {self : Fin sp.n} {X : (evidenceReleaseSA sp FGP ro).State}
    {Φ : (evidenceReleaseSA sp FGP ro).Frm} {t : Time}
        (h : (evidenceReleaseSA sp FGP ro).ReachableAt self U X Φ t) :
    LocksForget X ∧ 0 ≤ t := by
  induction h with
  | init => exact ⟨locksForget_initial _, le_rfl⟩
  | step k _ ht hc ih =>
    refine ⟨?_, ih.2.trans ht⟩
    rw [step_eq_stepE]
    exact locksForget_stepE _ _ ih.1 _ hc.1.1 (ih.2.trans ht) _

/-- The honest states of a run of the evidence-release SA keep `LocksForget`. -/
theorem locksForget_state (h : ACLocalRun (evidenceReleaseSA sp FGP ro) H U tr) {y : Fin sp.n}
    (hy : y ∈ H) (i : Nat) : LocksForget (tr.state y i) := by
  rcases tr.noCall_or_lastCall y i with hnone | ⟨j, hj, ℓ, hc, hnb⟩
  · rw [tr.state_of_noCall hnone, h.init y hy]
    exact locksForget_initial _
  · rw [tr.state_of_lastCall hc hj hnb]
    exact (locksForget_of_reachable (localRun_reachable _ _ _ _ _ tr h y hy j ℓ hc)).1

private theorem frameOK_of_call (h : ACLocalRun (evidenceReleaseSA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (evidenceReleaseSA sp FGP ro)}
    (hc : tr.CallAt y i ℓ) : FrameOK ℓ.frame := by
  rcases h.frameLaw y hy i ℓ hc with ⟨-, Φ₀, -, -, hk⟩ | ⟨-, ℓ₀, -, -, -, hk⟩ <;> exact hk.1.1

/-- **A run of the evidence-release SA, forgotten, is a run with the unlock given** by
`erOracle`. -/
theorem localRunU_projTrace (h : ACLocalRun (evidenceReleaseSA sp FGP ro) H U tr) :
    ACLocalRunU (erOracle tr) H U (projTrace tr) where
  coherent := h.coherent
  init y hy := by
    change (tr.init y).ac = _
    rw [h.init y hy]
    rfl
  exec i ℓP hl hH := by
    obtain ⟨ℓ, hl', rfl⟩ := Option.map_eq_some_iff.1 hl
    have hc : tr.CallAt (tr.node i) i ℓ := ⟨rfl, hl'⟩
    rw [projTrace_state]
    simp only [erOracle, hl']
    rw [stepWith_stepE _ _ (locksForget_state h hH i) _ (frameOK_of_call h hH hc)
      (h.time_nonneg i), ← step_eq_stepE, h.exec i ℓ hl' hH]
  lawful i ℓP hl hH hΦ := by
    obtain ⟨ℓ, hl', rfl⟩ := Option.map_eq_some_iff.1 hl
    rw [projTrace_state]
    simp only [erOracle, hl']
    exact unlockAtE_rel _ _ (unlockRel_unlockWith wlockStore_lawful (evidenceStage_lawful sp) () hΦ)
      (locksForget_state h hH i) _ _
  frameLaw y hy i ℓP hc := by
    obtain ⟨ℓ, hc₀, rfl⟩ := projTrace_callAt.1 hc
    rcases h.frameLaw y hy i ℓ hc₀ with ⟨hn, Φ₀, h1, h2, h3⟩ | ⟨j, ℓ', hj, hc', hn, h3⟩
    · exact Or.inl ⟨projTrace_noCallBetween.2 hn, Φ₀, h1, h2, callOK_projCall h3⟩
    · exact Or.inr ⟨j, projLabel ℓ', hj, projTrace_callAt.2 ⟨ℓ', hc', rfl⟩,
        projTrace_noCallBetween.2 hn, callOK_projCall h3⟩
  time_nonneg := h.time_nonneg
  time_mono := h.time_mono
  awake_of_call y hy i ℓP hc := by
    obtain ⟨ℓ, hc₀, rfl⟩ := projTrace_callAt.1 hc
    exact h.awake_of_call y hy i ℓ hc₀
  restart_of_sleep y hy i ℓP u hc h0 hu hna hb := by
    obtain ⟨ℓ, hc₀, rfl⟩ := projTrace_callAt.1 hc
    exact projCall_eq_restart.2 (h.restart_of_sleep y hy i ℓ u hc₀ h0 hu hna
      fun j hj ℓ' hc' => hb j hj _ (projTrace_callAt.2 ⟨ℓ', hc', rfl⟩))
  restart_at_wake y hy u v h0 huv hna hv := by
    obtain ⟨k, hk, h1, h2⟩ := h.restart_at_wake y hy u v h0 huv hna hv
    exact ⟨k, projTrace_restartAt.2 hk, h1, h2⟩
  sleep_of_restart y hy i ℓP hc hr := by
    obtain ⟨ℓ, hc₀, rfl⟩ := projTrace_callAt.1 hc
    obtain ⟨u, h0, hu, hna, hb⟩ := h.sleep_of_restart y hy i ℓ hc₀ (projCall_eq_restart.1 hr)
    exact ⟨u, h0, hu, hna, fun j hj ℓ' hc' => by
      obtain ⟨ℓ'', hc'', -⟩ := projTrace_callAt.1 hc'
      exact hb j hj ℓ'' hc''⟩

end Consensus.Goldilocks.EvidenceRelease

end
