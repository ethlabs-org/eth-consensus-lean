module
public import AvailableChainFGCompose.Proofs.SafetyAccountable
public import AvailableChainFGCompose.Proofs.SafetyCount
public import AvailableChainFGCompose.Proofs.SafetyMonotone
public import AvailableChainFGCompose.Proofs.SafetySlashing
public import AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyStore
public import AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyScope
public import AvailableChainPCSAProofs.Proofs.Foundations.FGSafetyClientLaws
public import AvailableChainPCSAClaims.Statements.Slashing
public import AvailableChainPCSAClaims.Statements.Regimes

public section

/-! PC-SA adapters and suppliers for the generic FG safety proofs. Both FG modes. -/

namespace AvailableChain.PCSA.Run
open AvailableChain.SimplexFG AvailableChain.FGCompose

variable (m : FGMode) (p : Params) {V : Type} [DecidableEq V] {In : Type}
    (c : AppCodec In) (E : Generic.Env V) (rho : V2.D.Run V (pcsaWith m p c))

/-- The run block reads include emitted and delivered proposals and their ancestors. -/
theorem pcsa_safety_runBlock_iff (K : FGBlock (Fin p.n)) :
    safetyRunBlock (pcsaCoreReadsWith m p c) (pcsaSafetyReads m p c) E rho K ↔
      PCFinalityBlock p c E rho K := by
  rw [safetyRunBlock_def, pcsa_PCFinalityBlock_def,
    pcsa_coreReadsWith_erase, pcsa_safetyReads_proposalErase]
  constructor
  · rintro ⟨o, b, hb, hrun, hKb⟩
    obtain ⟨N, ho, rfl⟩ := pcsa_safetyProposalErase_some o b hb
    exact ⟨o, N, ho, hrun, hKb⟩
  · rintro ⟨o, N, ho, hrun, hKN⟩
    refine ⟨o, N.erase, ?_, hrun, hKN⟩
    rw [pcsa_safetyProposalErase_def p (show Obj p from o), ho]

/-- The all-run bounds use the same blocks and row evidence. -/
theorem pcsa_safety_bound_iff :
    safetyBound (pcsaCoreReadsWith m p c) (pcsaSafetyReads m p c) p.E E rho ↔
      PCFinalitySlashableBound p c E rho := by
  rw [safetyBound_def, pcsa_PCFinalitySlashableBound_def]
  simp only [pcsa_safety_runBlock_iff]

/-- The finalized certificate reads agree. -/
theorem pcsa_safety_finalizedAt_iff (K T : FGBlock (Fin p.n)) (h : Nat) :
    safetyFinalizedAt (pcsa_finalityView p) K T h ↔ PCFinalizedAt p K T h := Iff.rfl

/-- The row reads contain all rows on the stored chains. -/
theorem pcsa_safety_rows_eq (nd : Node p) :
    safetyRows (pcsaCoreReadsWith m p c) nd = pcFinalityRows p nd.st := by
  rw [safetyRows_def (pcsaCoreReadsWith m p c) nd, pcsaCoreReadsWith_def,
    pcsa_pcFinalityRows_def]

/-- The emission reads agree at every tick. -/
theorem pcsa_safety_emits_iff (x : V) (a : RowWire p.n) :
    safetyEmits (pcsaSafetyReads m p c) E rho x a ↔ PCEmitsRow p c E rho x a := by
  rw [safetyEmits_def, pcsaSafetyReads_def, pcsa_PCEmitsRow_def]
  rfl

/-- The honest emission safety reads agree. -/
theorem pcsa_safety_noSlash_iff (x : V) :
    safetyNoSlash (pcsaSafetyReads m p c) E rho x ↔
      PCEmittedRowsNoSlash p c E rho x := by
  rw [safetyNoSlash_def, pcsa_PCEmittedRowsNoSlash_def]
  simp only [pcsa_safety_emits_iff m p c E rho]
  rw [pcsaSafetyReads_def]

/-- PC carriage supplies Compose carriage. The action time is not needed by Compose. -/
theorem pcsa_safety_carriage_of (A : Finset (Row (Fin p.n)))
    (h : PCFinalityRowCarriage p c E rho A) :
    safetyCarriage (pcsaSafetyReads m p c) E rho A := by
  rw [safetyCarriage_def]
  simp only [safetyHolder_def, safetyEmits_def, pcsaSafetyReads_def]
  intro u hu
  obtain ⟨a, ha, hauth, hem⟩ := h u hu
  refine ⟨a, ha, ?_⟩
  intro hh
  change rho.seatOf (.base .fg) u.signer ∈ rho.honest at hh
  obtain ⟨j, r, -, hj, hout⟩ := hem _ ⟨u.signer, hauth, rfl⟩ hh
  exact ⟨j, p.actionTime r, hj, hout⟩

/-- All three whole-run accountability clauses use the PC reads. -/
theorem pcsa_safety_wholeAccountable_iff :
    SafetyWholeAccountable (pcsaCoreReadsWith m p c) (pcsaSafetyReads m p c)
      p.E (pcsa_finalityView p) E rho ↔ PCWholeRunAccountable p c E rho := by
  rw [SafetyWholeAccountable_def, pcsa_PCWholeRunAccountable_def]
  simp only [pcsa_safety_runBlock_iff m p c E rho, pcsa_safety_finalizedAt_iff]
  simp only [safetyRows_def, pcsaCoreReadsWith_def, pcsa_pcFinalityRows_def]
  rfl

/-- Both whole-run agreement clauses use the PC reads. -/
theorem pcsa_safety_wholeAgreement_iff :
    SafetyWholeAgreement (pcsaCoreReadsWith m p c) (pcsaSafetyReads m p c)
      (pcsa_finalityView p) E rho ↔ PCWholeRunAgreement p c E rho := by
  rw [SafetyWholeAgreement_def, pcsa_PCWholeRunAgreement_def]
  simp only [pcsa_safety_runBlock_iff m p c E rho, pcsa_safety_finalizedAt_iff]
  rw [pcsaCoreReadsWith_def]

/-- Whole-run accountability from the PC store, scope, and certificate laws. -/
theorem pcsa_safety_accountable_supply (hr : NamedRootCollisionFree p c E rho) :
    PCWholeRunAccountable p c E rho :=
  (pcsa_safety_wholeAccountable_iff m p c E rho).1
    (safety_run_accountable _ _ _ _ _ E rho _ _ (pcsaCoreLawsWith m p c)
      (pcsaSafetyStoreLaws m p c) (pcsaSafetyCertificateLaws p)
      (pcsaSafetyScopeLaws m p c E rho) (pcsa_safetyScopedRoots m p c E rho hr))

/-- Whole-run agreement under the unchanged all-run slashable bound. -/
theorem pcsa_safety_agreement_supply (hr : NamedRootCollisionFree p c E rho)
    (hb : PCFinalitySlashableBound p c E rho) : PCWholeRunAgreement p c E rho :=
  (pcsa_safety_wholeAgreement_iff m p c E rho).1
    (safety_run_agreement _ _ _ _ _ E rho _ _ (pcsaCoreLawsWith m p c)
      (pcsaSafetyStoreLaws m p c) (pcsaSafetyCertificateLaws p)
      (pcsaSafetyScopeLaws m p c E rho) (pcsa_safetyScopedRoots m p c E rho hr)
      ((pcsa_safety_bound_iff m p c E rho).2 hb))

/-- Any two event prefixes agree under the all-run slashable bound. -/
theorem pcsa_safety_eventAgreement_supply (hr : NamedRootCollisionFree p c E rho)
    (hb : PCFinalitySlashableBound p c E rho) (i j : Nat) (x y : V) :
    FGBlock.compatible (storeBefore p c E rho i x).fg.F
      (storeBefore p c E rho j y).fg.F = true := by
  have h := safety_event_agreement _ _ _ _ _ E rho _ _ (pcsaCoreLawsWith m p c)
    (pcsaSafetyStoreLaws m p c) (pcsaSafetyCertificateLaws p)
    (pcsaSafetyScopeLaws m p c E rho) (pcsa_safetyScopedRoots m p c E rho hr)
    ((pcsa_safety_bound_iff m p c E rho).2 hb) i j x y
  rw [pcsaCoreReadsWith_def] at h
  exact h

/-- Sorted time reads preserve finality when there is no restart. -/
theorem pcsa_safety_monotone_supply (hs : PCFinalityExecution p c rho)
    (hnr : V2.D.NoRestart rho) :
    ∀ x ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
      Block.Preceq (pcsaFinalizedOut (V2.D.Run.readAt E rho t x))
        (pcsaFinalizedOut (V2.D.Run.readAt E rho t' x)) := by
  have h := safety_finalized_monotone _ _ E rho (pcsaCoreLawsWith m p c)
    (pcsaSafetyOrderLaws m p c) hs hnr
  rw [pcsaSafetyReads_def] at h
  exact h

/-- Fault counting retains carriage of every run block, including ancestors. -/
theorem pcsa_safety_count_supply [Fintype V]
    (hl : V2.D.Linked (pcsaFamilies p c).linked rho)
    (hc : ∀ K, PCFinalityBlock p c E rho K →
      PCFinalityRowCarriage p c E rho (chainRows K))
    (he : ∀ x ∈ rho.honest, PCEmittedRowsNoSlash p c E rho x)
    (hf : FGSafetyBound p c rho) : PCFinalitySlashableBound p c E rho :=
  (pcsa_safety_bound_iff m p c E rho).1
    (safety_fault_count_bound _ _ p.E E rho (pcsaSafetyUnitLaws p)
      (pcsaFamilies p c).linked (by rw [pcsaSafetyReads_def]; trivial) hl
      (fun K hK => pcsa_safety_carriage_of m p c E rho _
        (hc K ((pcsa_safety_runBlock_iff m p c E rho K).1 hK)))
      (fun x hx => (pcsa_safety_noSlash_iff m p c E rho x).2 (he x hx)) hf)

/-- The PC slashing interface uses the stored-chain row reads and FG holder. -/
theorem pcsa_safetySlashesRead (m : FGMode) (p : Params) {In : Type} (c : AppCodec In)
    (E : Generic.Env (Fin p.n)) (rho : V2.D.Run (Fin p.n) (pcsaWith m p c)) :
    safetySlashesRead (pcsaCoreReadsWith m p c) (pcsaSafetyReads m p c)
      E rho (pcsaSlashing p c E) := by
  rw [safetySlashesRead_def]
  intro v
  rw [pcsa_pcsaSlashing_slashes_def]
  simp only [safetyRows_def, pcsaCoreReadsWith_def, pcsa_pcFinalityRows_def,
    safetyHolder_def, pcsaSafetyReads_def]
  rfl

/-- Stored-row carriage and client safety exclude slashing of an honest holder. -/
theorem pcsa_safety_nonSlashing_supply (m : FGMode) (p : Params) {In : Type}
    (c : AppCodec In) (E : Generic.Env (Fin p.n))
    (rho : V2.D.Run (Fin p.n) (pcsaWith m p c))
    (hu : V2.D.UnforgeableSignatures E rho)
    (hl : V2.D.Linked (pcsaFamilies p c).linked rho) :
    Gen.V2.Duty.HonestNeverSlashed (pcsaSlashing p c E) rho :=
  safety_honest_never_slashed _ _ _ _ _ _ E rho _ (pcsaCoreLawsWith m p c)
    (pcsaSafetyWireLaws m p c) (pcsaSafetyStoreLaws m p c) (pcsaSafetyClientLaws m p c)
    (pcsaFamilies p c).linked (by rw [pcsaSafetyReads_def]; trivial) (pcsaSlashing p c E)
    (pcsa_safetySlashesRead m p c E rho) hu hl

end AvailableChain.PCSA.Run
end
