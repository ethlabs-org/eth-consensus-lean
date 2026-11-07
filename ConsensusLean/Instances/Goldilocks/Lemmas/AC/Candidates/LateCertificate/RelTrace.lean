module
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.LateCertificate.SA
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.EvidenceRelease.RelTrace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace

public section

/-! # Late-certificate traces are SA traces with the unlock given

The late-certificate SA's handlers, with the archive forgotten, are evidence-release's
stage-generic handlers at `certStageW` with a context read off the archive (`SA`), so a call is
`stepE` at that stage and context (`step_er`), and its forgotten result is `stepWith` at the
forgotten locks after the stage's unlock (`stepWith_stepE`). The stage's forgotten unlock satisfies
the parent's unlock relation (`unlockRel_certStageW`, through the composite stage `certStage` on
locks with formation slots, which is lawful). So a run of the late-certificate SA with its archive
and weights forgotten (`projTraceC`) is a run with the unlock given by `certOracle`
(`localRunU_projTraceC`).

The forgotten trace's states are the parent's (the pool), so its `holdsMsg` is the pool's: the
archive-only votes the late-certificate SA also holds are not read there. -/

namespace Consensus.Goldilocks.LateCertificate

open SA EvidenceRelease

variable {sp : SAParams} {FGP : Type} {ro : ReplayOrder sp FGP}

/-- **The candidate's unlock on weighted locks satisfies the parent's unlock relation.** -/
theorem unlockRel_certStageW {Φ : Frm sp.n FGP} (hΦ : FrameOK Φ) (ctx : CertCtx sp.n)
    (L : Set WLock) (t : Time) (s : Int) (V : View sp.n) :
    UnlockRel sp (WLock.lock '' L) Φ t s V
      (WLock.lock '' wlockStore.unlockWith sp (certStageW sp) ctx L Φ t s V) := by
  have hl : ∀ M : Set WLock, clockStore.lock '' ((tagW sp).toFun '' M) = WLock.lock '' M :=
    fun M => by
      rw [Set.image_image]
      simp only [tagW_apply]
  have h := unlockRel_unlockWith clockStore_lawful (certStage_lawful sp) ((), ctx) hΦ
    ((tagW sp).toFun '' L) t s V
  rwa [← certUnlock_eq, ← image_unlockWith_certStageW hΦ, hl, hl] at h

variable (ro) in
/-- The parent's call of a call of the late-certificate SA. -/
abbrev projCallC : (certRecoverySA sp FGP ro).Call → (goldilocksSA sp FGP ro).Call
  | .tick => .tick
  | .proposal => .proposal
  | .toFG => .toFG
  | .message m => .message m
  | .block B => .block B
  | .restart => .restart

variable (ro) in
/-- The stage's context of a call: the archive after the call's receipt, and the last restart. -/
abbrev ctxC (X : CState sp.n) (t : Time) : (certRecoverySA sp FGP ro).Call → CertCtx sp.n
  | .message v => certCtx (archiveRecord sp X.arch t v) X.er.ac
  | .block B => certCtx (archiveAll sp X.arch t (blockVotes B)) X.er.ac
  | .restart => ⟨Archive.arrival [], (t : WithBot Time)⟩
  | _ => certCtx X.arch X.er.ac

/-- **A call of the late-certificate SA, with its archive forgotten**, is `stepE` at the
candidate's stage and the call's context. -/
theorem step_er (self : Fin sp.n) (X : CState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (k : (certRecoverySA sp FGP ro).Call) :
    ((certRecoverySA sp FGP ro).step self X Φ t k).1.er =
        (stepE sp ro (certStageW sp) (ctxC ro X t k) self X.er Φ t (projCallC ro k)).1 ∧
      ((certRecoverySA sp FGP ro).step self X Φ t k).2.map projC =
        (stepE sp ro (certStageW sp) (ctxC ro X t k) self X.er Φ t (projCallC ro k)).2 := by
  cases k with
  | tick => exact ⟨acOnTickC_er self X Φ t, acOnTickC_emits self X Φ t⟩
  | proposal => exact ⟨rfl, rfl⟩
  | toFG => exact ⟨rfl, rfl⟩
  | message v => exact ⟨acOnMessageC_er self X Φ t v, acOnMessageC_emits self X Φ t v⟩
  | block B => exact ⟨acOnBlockC_er self X Φ t B, acOnBlockC_emits self X Φ t B⟩
  | restart => exact ⟨acRestartC_er ro self X Φ t, acRestartC_emits ro self X Φ t⟩

theorem projCallC_eq_restart {k : (certRecoverySA sp FGP ro).Call} :
    projCallC ro k = .restart ↔ k = .restart := by
  cases k <;> simp

theorem callOK_projCallC {U : Set (Blk sp.n FGP)} {Φ Φ' : Frm sp.n FGP} {t : Time}
    {k : (certRecoverySA sp FGP ro).Call} (h : (certRecoverySA sp FGP ro).CallOK U Φ t k Φ') :
    (goldilocksSA sp FGP ro).CallOK U Φ t (projCallC ro k) Φ' := by
  cases k <;> exact h

/-- The parent's label of a label of the late-certificate SA. -/
abbrev projLabelC (ℓ : ACLabel (certRecoverySA sp FGP ro)) : ACLabel (goldilocksSA sp FGP ro) :=
  ⟨projCallC ro ℓ.call, ℓ.frame, (ℓ.emits.map projC).map projEm⟩

/-- **The forgotten trace**: the parent's states, calls and emissions of an AC trace of the
late-certificate SA. -/
abbrev projTraceC (tr : ACTrace (certRecoverySA sp FGP ro)) : SATrace sp FGP ro where
  init y := (tr.init y).er.ac
  node := tr.node
  time := tr.time
  event := tr.event
  pos := tr.pos
  label i := (tr.label i).map projLabelC
  post i := (tr.post i).er.ac
  awake := tr.awake
  observationHorizon := tr.observationHorizon

/-- The unlock oracle of a trace of the late-certificate SA: at each labelled cut, the forgotten
locks after the candidate's unlock of the call's input, at the call's context. -/
noncomputable abbrev certOracle (tr : ACTrace (certRecoverySA sp FGP ro)) (i : Nat) :
    Set Lock :=
  match tr.label i with
  | some ℓ => unlockAtE sp (certStageW sp) (ctxC ro (tr.state (tr.node i) i) (tr.time i) ℓ.call)
      (tr.state (tr.node i) i).er ℓ.frame (tr.time i) (projCallC ro ℓ.call)
  | none => ∅

variable {tr : ACTrace (certRecoverySA sp FGP ro)}

theorem projTraceC_state (y : Fin sp.n) (i : Nat) :
    (projTraceC tr).state y i = (tr.state y i).er.ac := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [Trace.state]
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact absurd ⟨h₁.1, by simpa using h₁.2⟩ h₂
    · exact absurd ⟨h₂.1, by simpa using h₂.2⟩ h₁
    · exact ih

theorem projTraceC_callAt {y : Fin sp.n} {i : Nat} {ℓP : ACLabel (goldilocksSA sp FGP ro)} :
    (projTraceC tr).CallAt y i ℓP ↔ ∃ ℓ, tr.CallAt y i ℓ ∧ projLabelC ℓ = ℓP := by
  simp only [Trace.CallAt, Option.map_eq_some_iff]
  constructor
  · rintro ⟨h1, ℓ, h2, rfl⟩
    exact ⟨ℓ, ⟨h1, h2⟩, rfl⟩
  · rintro ⟨ℓ, ⟨h1, h2⟩, rfl⟩
    exact ⟨h1, ℓ, h2, rfl⟩

theorem projTraceC_noCallBetween {y : Fin sp.n} {j i : Nat} :
    (projTraceC tr).NoCallBetween y j i ↔ tr.NoCallBetween y j i :=
  ⟨fun h k hj hi ℓ hc => h k hj hi _ (projTraceC_callAt.2 ⟨ℓ, hc, rfl⟩),
    fun h k hj hi _ hc => by
      obtain ⟨ℓ, hc, -⟩ := projTraceC_callAt.1 hc
      exact h k hj hi ℓ hc⟩

theorem projTraceC_restartAt {y : Fin sp.n} {k : Nat} :
    (projTraceC tr).RestartAt y k ↔ tr.RestartAt y k := by
  constructor
  · rintro ⟨_, hc, hr⟩
    obtain ⟨ℓ, hc₀, rfl⟩ := projTraceC_callAt.1 hc
    exact ⟨ℓ, hc₀, projCallC_eq_restart.1 hr⟩
  · rintro ⟨ℓ, hc, hr⟩
    exact ⟨_, projTraceC_callAt.2 ⟨ℓ, hc, rfl⟩, projCallC_eq_restart.2 hr⟩

variable {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}

/-- At a proposal call, the oracle's `ac_proposal` is the late-certificate SA's, forgotten: the
honest proposals with the unlock given (`HonestProposalU`, `DrivenU`) are the candidate's. -/
theorem acProposalWith_certOracle {x : Fin sp.n} {k : Nat}
    {ℓ : ACLabel (certRecoverySA sp FGP ro)} (hc : tr.CallAt x k ℓ)
    (hcall : ℓ.call = .proposal) :
    acProposalWith sp (certOracle tr k) ((projTraceC tr).state x k) ℓ.frame (tr.time k) =
      ((acProposalC sp (tr.state x k) ℓ.frame (tr.time k)).1.er.ac,
        (acProposalC sp (tr.state x k) ℓ.frame (tr.time k)).2) := by
  rw [projTraceC_state]
  have h := acProposalE_proj (certStageW sp) (certCtx (tr.state x k).arch (tr.state x k).er.ac)
    (tr.state x k).er ℓ.frame (tr.time k)
  simp only [certOracle, hc.2, hc.1, hcall]
  exact h.symm

/-- Reachable states of the late-certificate SA keep `LocksForget`, at times from `0`. -/
theorem locksForget_of_reachable_cert {self : Fin sp.n} {X : (certRecoverySA sp FGP ro).State}
    {Φ : (certRecoverySA sp FGP ro).Frm} {t : Time}
    (h : (certRecoverySA sp FGP ro).ReachableAt self U X Φ t) : LocksForget X.er ∧ 0 ≤ t := by
  induction h with
  | init => exact ⟨locksForget_initial _, le_rfl⟩
  | @step X Φ Φ' t t' k _ ht hc ih =>
    refine ⟨?_, ih.2.trans ht⟩
    rw [(step_er self X Φ' t' k).1]
    exact locksForget_stepE _ _ ih.1 _ hc.1.1 (ih.2.trans ht) _

/-- The honest states of a run of the late-certificate SA keep `LocksForget`. -/
theorem locksForget_state_cert (h : ACLocalRun (certRecoverySA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) : LocksForget (tr.state y i).er := by
  rcases tr.noCall_or_lastCall y i with hnone | ⟨j, hj, ℓ, hc, hnb⟩
  · rw [tr.state_of_noCall hnone, h.init y hy]
    exact locksForget_initial _
  · rw [tr.state_of_lastCall hc hj hnb]
    exact (locksForget_of_reachable_cert (localRun_reachable _ _ _ _ _ tr h y hy j ℓ hc)).1

private theorem frameOK_of_call (h : ACLocalRun (certRecoverySA sp FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (certRecoverySA sp FGP ro)}
    (hc : tr.CallAt y i ℓ) : FrameOK ℓ.frame := by
  rcases h.frameLaw y hy i ℓ hc with ⟨-, Φ₀, -, -, hk⟩ | ⟨-, ℓ₀, -, -, -, hk⟩ <;> exact hk.1.1

/-- **A run of the late-certificate SA, forgotten, is a run with the unlock given** by
`certOracle`. -/
theorem localRunU_projTraceC (h : ACLocalRun (certRecoverySA sp FGP ro) H U tr) :
    ACLocalRunU (certOracle tr) H U (projTraceC tr) where
  coherent := h.coherent
  init y hy := by
    change (tr.init y).er.ac = _
    rw [h.init y hy]
    rfl
  exec i ℓP hl hH := by
    obtain ⟨ℓ, hl', rfl⟩ := Option.map_eq_some_iff.1 hl
    have hc : tr.CallAt (tr.node i) i ℓ := ⟨rfl, hl'⟩
    have hs := step_er (tr.node i) (tr.state (tr.node i) i) ℓ.frame (tr.time i) ℓ.call
    rw [h.exec i ℓ hl' hH] at hs
    rw [projTraceC_state]
    simp only [certOracle, hl']
    rw [stepWith_stepE _ _ (locksForget_state_cert h hH i) _ (frameOK_of_call h hH hc)
      (h.time_nonneg i), ← hs.1, ← hs.2]
  lawful i ℓP hl hH hΦ := by
    obtain ⟨ℓ, hl', rfl⟩ := Option.map_eq_some_iff.1 hl
    rw [projTraceC_state]
    simp only [certOracle, hl']
    exact unlockAtE_rel _ _ (unlockRel_certStageW hΦ _) (locksForget_state_cert h hH i) _ _
  frameLaw y hy i ℓP hc := by
    obtain ⟨ℓ, hc₀, rfl⟩ := projTraceC_callAt.1 hc
    rcases h.frameLaw y hy i ℓ hc₀ with ⟨hn, Φ₀, h1, h2, h3⟩ | ⟨j, ℓ', hj, hc', hn, h3⟩
    · exact Or.inl ⟨projTraceC_noCallBetween.2 hn, Φ₀, h1, h2, callOK_projCallC h3⟩
    · exact Or.inr ⟨j, projLabelC ℓ', hj, projTraceC_callAt.2 ⟨ℓ', hc', rfl⟩,
        projTraceC_noCallBetween.2 hn, callOK_projCallC h3⟩
  time_nonneg := h.time_nonneg
  time_mono := h.time_mono
  awake_of_call y hy i ℓP hc := by
    obtain ⟨ℓ, hc₀, rfl⟩ := projTraceC_callAt.1 hc
    exact h.awake_of_call y hy i ℓ hc₀
  restart_of_sleep y hy i ℓP u hc h0 hu hna hb := by
    obtain ⟨ℓ, hc₀, rfl⟩ := projTraceC_callAt.1 hc
    exact projCallC_eq_restart.2 (h.restart_of_sleep y hy i ℓ u hc₀ h0 hu hna
      fun j hj ℓ' hc' => hb j hj _ (projTraceC_callAt.2 ⟨ℓ', hc', rfl⟩))
  restart_at_wake y hy u v h0 huv hna hv := by
    obtain ⟨k, hk, h1, h2⟩ := h.restart_at_wake y hy u v h0 huv hna hv
    exact ⟨k, projTraceC_restartAt.2 hk, h1, h2⟩
  sleep_of_restart y hy i ℓP hc hr := by
    obtain ⟨ℓ, hc₀, rfl⟩ := projTraceC_callAt.1 hc
    obtain ⟨u, h0, hu, hna, hb⟩ := h.sleep_of_restart y hy i ℓ hc₀ (projCallC_eq_restart.1 hr)
    exact ⟨u, h0, hu, hna, fun j hj ℓ' hc' => by
      obtain ⟨ℓ'', hc'', -⟩ := projTraceC_callAt.1 hc'
      exact hb j hj ℓ'' hc''⟩

end Consensus.Goldilocks.LateCertificate

end
