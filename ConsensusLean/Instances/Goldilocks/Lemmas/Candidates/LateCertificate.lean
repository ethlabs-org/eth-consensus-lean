module
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Candidates.Projection
public import ConsensusLean.Instances.Goldilocks.Milestones.Spec.Candidates.LateCertificate
public import ConsensusLean.Instances.Goldilocks.Lemmas.Candidates.EvidenceRelease
public import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Candidates.LateCertificate.RelTrace
import ConsensusLean.Instances.Goldilocks.Lemmas.AC.Trace

public section

/-! # The late-certificate SA at a write mode projects to the SA's step at the same mode

The late-certificate SA at a write mode `m` (`Milestones/Spec/Candidates/LateCertificate`), with
its archive and weights forgotten, is the SA's step at mode `m` (`stepWithM m`) with the locks
after the candidate's unlock given, as at the parent's mode
(`Lemmas/AC/Candidates/LateCertificate/RelTrace`):

* at the parent's mode it is the late-certificate SA (`acOnTickCM_parent`,
  `certRecoverySAM_parent`), which certifies the parent's mode only;
* forgetting the archive, each handler is evidence-release's handler at mode `m` at the
  candidate's stage `certStageW` with the archive as context, by `rfl`, and each emission is that
  handler's emission with the archive added (`acOnMessageCM_er`, …, `acRestartCM_emits`), so a
  call is `stepEM m` at that stage and the call's context (`step_erM`);
* the stage-generic projection at mode `m` (`stepWithM_stepEM`, `unlockAtEM_rel`,
  `locksForget_stepEM`, `Lemmas/Candidates/EvidenceRelease`) and the stage's unlock relation
  (`unlockRel_certStageW`) lift it to traces: a run of the late-certificate SA at mode `m`,
  forgotten, is a run at mode `m` with the unlock given by `certOracleM`
  (`localRunU_projTraceCM`); proposals: `acProposalWith_certOracleM`.

The forgotten trace's states are the parent's (the pool), so its `holdsMsg` is the pool's, as at
the parent's mode. -/

namespace Consensus.Goldilocks.LateCertificate

open SA EvidenceRelease

variable {sp : SAParams} {FGP : Type}

/-! ### The parent's mode -/

/-- At the parent's mode, `ac_on_tick` is the late-certificate SA's. -/
theorem acOnTickCM_parent :
    acOnTickCM (FGP := FGP) sp (WriteMode.parent sp) = acOnTickC sp := by
  funext self X Φ t
  simp only [acOnTickCM, acOnTickC, acOnTickEM_parent]

/-- **At the parent's mode, the SA is the late-certificate SA.** -/
theorem certRecoverySAM_parent (ro : ReplayOrder sp FGP) :
    certRecoverySAM sp (WriteMode.parent sp) FGP ro = certRecoverySA sp FGP ro := by
  unfold certRecoverySAM
  rw [acOnTickCM_parent]
  rfl

/-! ### The projection to evidence-release's state at mode `m` -/

variable (m : WriteMode)

theorem acOnMessageCM_er (self : Fin sp.n) (X : CState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (v : Vote sp.n) :
    (acOnMessageCM sp m self X Φ t v).1.er = (acOnMessageEM sp (certStageW sp)
      (certCtx (archiveRecord sp X.arch t v) X.er.ac) m self X.er Φ t v).1 := by
  rfl

theorem acOnMessageCM_emits (self : Fin sp.n) (X : CState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (v : Vote sp.n) :
    (acOnMessageCM sp m self X Φ t v).2.map projC = (acOnMessageEM sp (certStageW sp)
      (certCtx (archiveRecord sp X.arch t v) X.er.ac) m self X.er Φ t v).2 :=
  map_projC_liftEm _ _

theorem acOnBlockCM_er (self : Fin sp.n) (X : CState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (B : Blk sp.n FGP) :
    (acOnBlockCM sp m self X Φ t B).1.er = (acOnBlockEM sp (certStageW sp)
      (certCtx (archiveAll sp X.arch t (blockVotes B)) X.er.ac) m self X.er Φ t B).1 := by
  rfl

theorem acOnBlockCM_emits (self : Fin sp.n) (X : CState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (B : Blk sp.n FGP) :
    (acOnBlockCM sp m self X Φ t B).2.map projC = (acOnBlockEM sp (certStageW sp)
      (certCtx (archiveAll sp X.arch t (blockVotes B)) X.er.ac) m self X.er Φ t B).2 :=
  map_projC_liftEm _ _

theorem acOnTickCM_er (self : Fin sp.n) (X : CState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acOnTickCM sp m self X Φ t).1.er =
      (acOnTickEM sp (certStageW sp) (certCtx X.arch X.er.ac) m self X.er Φ t).1 := by
  rfl

theorem acOnTickCM_emits (self : Fin sp.n) (X : CState sp.n) (Φ : Frm sp.n FGP) (t : Time) :
    (acOnTickCM sp m self X Φ t).2.map projC =
      (acOnTickEM sp (certStageW sp) (certCtx X.arch X.er.ac) m self X.er Φ t).2 :=
  map_projC_liftEm _ _

theorem acRestartCM_er (ro : ReplayOrder sp FGP) (self : Fin sp.n) (X : CState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    (acRestartCM sp m ro self X Φ t).1.er = (acRestartEM sp (certStageW sp)
      ⟨Archive.arrival [], (t : WithBot Time)⟩ m ro self X.er Φ t).1 := by
  rfl

theorem acRestartCM_emits (ro : ReplayOrder sp FGP) (self : Fin sp.n) (X : CState sp.n)
    (Φ : Frm sp.n FGP) (t : Time) :
    (acRestartCM sp m ro self X Φ t).2.map projC = (acRestartEM sp (certStageW sp)
      ⟨Archive.arrival [], (t : WithBot Time)⟩ m ro self X.er Φ t).2 :=
  map_projC_liftEm _ _

/-! ### Traces -/

variable {m} {ro : ReplayOrder sp FGP}

/-- **A call of the late-certificate SA at mode `m`, with its archive forgotten**, is `stepEM` at
mode `m`, the candidate's stage and the call's context. -/
theorem step_erM (self : Fin sp.n) (X : CState sp.n) (Φ : Frm sp.n FGP) (t : Time)
    (k : (certRecoverySAM sp m FGP ro).Call) :
    ((certRecoverySAM sp m FGP ro).step self X Φ t k).1.er =
        (stepEM sp ro (certStageW sp) (ctxCM ro X t k) m self X.er Φ t (projCallCM ro k)).1 ∧
      ((certRecoverySAM sp m FGP ro).step self X Φ t k).2.map projC =
        (stepEM sp ro (certStageW sp) (ctxCM ro X t k) m self X.er Φ t (projCallCM ro k)).2 := by
  cases k with
  | tick => exact ⟨acOnTickCM_er m self X Φ t, acOnTickCM_emits m self X Φ t⟩
  | proposal => exact ⟨rfl, rfl⟩
  | toFG => exact ⟨rfl, rfl⟩
  | message v => exact ⟨acOnMessageCM_er m self X Φ t v, acOnMessageCM_emits m self X Φ t v⟩
  | block B => exact ⟨acOnBlockCM_er m self X Φ t B, acOnBlockCM_emits m self X Φ t B⟩
  | restart => exact ⟨acRestartCM_er m ro self X Φ t, acRestartCM_emits m ro self X Φ t⟩

theorem projCallCM_eq_restart {k : (certRecoverySAM sp m FGP ro).Call} :
    projCallCM ro k = .restart ↔ k = .restart := by
  cases k <;> simp

theorem callOK_projCallCM {U : Set (Blk sp.n FGP)} {Φ Φ' : Frm sp.n FGP} {t : Time}
    {k : (certRecoverySAM sp m FGP ro).Call}
    (h : (certRecoverySAM sp m FGP ro).CallOK U Φ t k Φ') :
    (goldilocksSA sp FGP ro).CallOK U Φ t (projCallCM ro k) Φ' := by
  cases k <;> exact h

variable {tr : ACTrace (certRecoverySAM sp m FGP ro)}

theorem projTraceCM_state (y : Fin sp.n) (i : Nat) :
    (projTraceCM tr).state y i = (tr.state y i).er.ac := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [Trace.state]
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact absurd ⟨h₁.1, by simpa using h₁.2⟩ h₂
    · exact absurd ⟨h₂.1, by simpa using h₂.2⟩ h₁
    · exact ih

theorem projTraceCM_callAt {y : Fin sp.n} {i : Nat} {ℓP : ACLabel (goldilocksSA sp FGP ro)} :
    (projTraceCM tr).CallAt y i ℓP ↔ ∃ ℓ, tr.CallAt y i ℓ ∧ projLabelCM ℓ = ℓP := by
  simp only [Trace.CallAt, Option.map_eq_some_iff]
  constructor
  · rintro ⟨h1, ℓ, h2, rfl⟩
    exact ⟨ℓ, ⟨h1, h2⟩, rfl⟩
  · rintro ⟨ℓ, ⟨h1, h2⟩, rfl⟩
    exact ⟨h1, ℓ, h2, rfl⟩

theorem projTraceCM_noCallBetween {y : Fin sp.n} {j i : Nat} :
    (projTraceCM tr).NoCallBetween y j i ↔ tr.NoCallBetween y j i :=
  ⟨fun h k hj hi ℓ hc => h k hj hi _ (projTraceCM_callAt.2 ⟨ℓ, hc, rfl⟩),
    fun h k hj hi _ hc => by
      obtain ⟨ℓ, hc, -⟩ := projTraceCM_callAt.1 hc
      exact h k hj hi ℓ hc⟩

theorem projTraceCM_restartAt {y : Fin sp.n} {k : Nat} :
    (projTraceCM tr).RestartAt y k ↔ tr.RestartAt y k := by
  constructor
  · rintro ⟨_, hc, hr⟩
    obtain ⟨ℓ, hc₀, rfl⟩ := projTraceCM_callAt.1 hc
    exact ⟨ℓ, hc₀, projCallCM_eq_restart.1 hr⟩
  · rintro ⟨ℓ, hc, hr⟩
    exact ⟨_, projTraceCM_callAt.2 ⟨ℓ, hc, rfl⟩, projCallCM_eq_restart.2 hr⟩

variable {H : Set (Fin sp.n)} {U : Set (Blk sp.n FGP)}

/-- At a proposal call, the oracle's `ac_proposal` is the late-certificate SA's, forgotten, at
every mode (the proposal writes nothing): the honest proposals with the unlock given
(`HonestProposalU`, `DrivenU`) are the candidate's at mode `m`. -/
theorem acProposalWith_certOracleM {x : Fin sp.n} {k : Nat}
    {ℓ : ACLabel (certRecoverySAM sp m FGP ro)} (hc : tr.CallAt x k ℓ)
    (hcall : ℓ.call = .proposal) :
    acProposalWith sp (certOracleM tr k) ((projTraceCM tr).state x k) ℓ.frame (tr.time k) =
      ((acProposalC sp (tr.state x k) ℓ.frame (tr.time k)).1.er.ac,
        (acProposalC sp (tr.state x k) ℓ.frame (tr.time k)).2) := by
  rw [projTraceCM_state]
  have h := acProposalE_proj (certStageW sp) (certCtx (tr.state x k).arch (tr.state x k).er.ac)
    (tr.state x k).er ℓ.frame (tr.time k)
  simp only [certOracleM, hc.2, hc.1, hcall]
  exact h.symm

/-- Reachable states of the late-certificate SA at mode `m` keep `LocksForget`, at times from
`0`. -/
theorem locksForget_of_reachable_certM {self : Fin sp.n}
    {X : (certRecoverySAM sp m FGP ro).State} {Φ : (certRecoverySAM sp m FGP ro).Frm} {t : Time}
    (h : (certRecoverySAM sp m FGP ro).ReachableAt self U X Φ t) : LocksForget X.er ∧ 0 ≤ t := by
  induction h with
  | init => exact ⟨locksForget_initial _, le_rfl⟩
  | @step X Φ Φ' t t' k _ ht hc ih =>
    refine ⟨?_, ih.2.trans ht⟩
    rw [(step_erM self X Φ' t' k).1]
    exact locksForget_stepEM _ _ _ ih.1 _ hc.1.1 (ih.2.trans ht) _

/-- The honest states of a run of the late-certificate SA at mode `m` keep `LocksForget`. -/
theorem locksForget_state_certM (h : ACLocalRun (certRecoverySAM sp m FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) (i : Nat) : LocksForget (tr.state y i).er := by
  rcases tr.noCall_or_lastCall y i with hnone | ⟨j, hj, ℓ, hc, hnb⟩
  · rw [tr.state_of_noCall hnone, h.init y hy]
    exact locksForget_initial _
  · rw [tr.state_of_lastCall hc hj hnb]
    exact (locksForget_of_reachable_certM (localRun_reachable _ _ _ _ _ tr h y hy j ℓ hc)).1

private theorem frameOK_of_callCM (h : ACLocalRun (certRecoverySAM sp m FGP ro) H U tr)
    {y : Fin sp.n} (hy : y ∈ H) {i : Nat} {ℓ : ACLabel (certRecoverySAM sp m FGP ro)}
    (hc : tr.CallAt y i ℓ) : FrameOK ℓ.frame := by
  rcases h.frameLaw y hy i ℓ hc with ⟨-, Φ₀, -, -, hk⟩ | ⟨-, ℓ₀, -, -, -, hk⟩ <;> exact hk.1.1

/-- **A run of the late-certificate SA at mode `m`, forgotten, is a run at mode `m` with the
unlock given by `certOracleM`.** -/
theorem localRunU_projTraceCM (h : ACLocalRun (certRecoverySAM sp m FGP ro) H U tr) :
    ACLocalRunU m (certOracleM tr) H U (projTraceCM tr) where
  coherent := h.coherent
  init y hy := by
    change (tr.init y).er.ac = _
    rw [h.init y hy]
    rfl
  exec i ℓP hl hH := by
    obtain ⟨ℓ, hl', rfl⟩ := Option.map_eq_some_iff.1 hl
    have hc : tr.CallAt (tr.node i) i ℓ := ⟨rfl, hl'⟩
    have hs := step_erM (tr.node i) (tr.state (tr.node i) i) ℓ.frame (tr.time i) ℓ.call
    rw [h.exec i ℓ hl' hH] at hs
    rw [projTraceCM_state]
    simp only [certOracleM, hl']
    rw [stepWithM_stepEM _ _ _ (locksForget_state_certM h hH i) _ (frameOK_of_callCM h hH hc)
      (h.time_nonneg i), ← hs.1, ← hs.2]
  lawful i ℓP hl hH hΦ := by
    obtain ⟨ℓ, hl', rfl⟩ := Option.map_eq_some_iff.1 hl
    rw [projTraceCM_state]
    simp only [certOracleM, hl']
    exact unlockAtEM_rel _ _ _ (unlockRel_certStageW hΦ _) (locksForget_state_certM h hH i) _ _
  frameLaw y hy i ℓP hc := by
    obtain ⟨ℓ, hc₀, rfl⟩ := projTraceCM_callAt.1 hc
    rcases h.frameLaw y hy i ℓ hc₀ with ⟨hn, Φ₀, h1, h2, h3⟩ | ⟨j, ℓ', hj, hc', hn, h3⟩
    · exact Or.inl ⟨projTraceCM_noCallBetween.2 hn, Φ₀, h1, h2, callOK_projCallCM h3⟩
    · exact Or.inr ⟨j, projLabelCM ℓ', hj, projTraceCM_callAt.2 ⟨ℓ', hc', rfl⟩,
        projTraceCM_noCallBetween.2 hn, callOK_projCallCM h3⟩
  time_nonneg := h.time_nonneg
  time_mono := h.time_mono
  awake_of_call y hy i ℓP hc := by
    obtain ⟨ℓ, hc₀, rfl⟩ := projTraceCM_callAt.1 hc
    exact h.awake_of_call y hy i ℓ hc₀
  restart_of_sleep y hy i ℓP u hc h0 hu hna hb := by
    obtain ⟨ℓ, hc₀, rfl⟩ := projTraceCM_callAt.1 hc
    exact projCallCM_eq_restart.2 (h.restart_of_sleep y hy i ℓ u hc₀ h0 hu hna
      fun j hj ℓ' hc' => hb j hj _ (projTraceCM_callAt.2 ⟨ℓ', hc', rfl⟩))
  restart_at_wake y hy u v h0 huv hna hv := by
    obtain ⟨k, hk, h1, h2⟩ := h.restart_at_wake y hy u v h0 huv hna hv
    exact ⟨k, projTraceCM_restartAt.2 hk, h1, h2⟩
  sleep_of_restart y hy i ℓP hc hr := by
    obtain ⟨ℓ, hc₀, rfl⟩ := projTraceCM_callAt.1 hc
    obtain ⟨u, h0, hu, hna, hb⟩ := h.sleep_of_restart y hy i ℓ hc₀ (projCallCM_eq_restart.1 hr)
    exact ⟨u, h0, hu, hna, fun j hj ℓ' hc' => by
      obtain ⟨ℓ'', hc'', -⟩ := projTraceCM_callAt.1 hc'
      exact hb j hj ℓ'' hc''⟩

end Consensus.Goldilocks.LateCertificate

end
