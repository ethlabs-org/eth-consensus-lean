module
public import AvailableChainFGSAProofs.Proofs.Foundations.HonestNeverSlashed
public import AvailableChainFGSAProofs.Proofs.Foundations.FinalizedSafety
public import AvailableChainFGSAProofs.Proofs.Foundations.Crossing
public import AvailableChainGeneric.Statements.Pure.Props
public import AvailableChainFGSAClaims.Statements.FinalityApi

public section

namespace AvailableChain.FGSA.Run
open AvailableChain.SimplexFG

variable (p : Params) {In V : Type} [DecidableEq V] (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c))

private theorem finalizedAt_eq (K T : FGBlock (Fin p.n)) (h : Nat) :
    FinalityFinalizedAt p K T h = FGFinalizedAt p K T h := by
  rw [FinalityFinalizedAt_def, FGFinalizedAt_def]

private theorem finalityBlock_eq (K : FGBlock (Fin p.n)) :
    FinalityBlock p c E rho K = FinalityRunBlock p c E rho K := by
  rw [FinalityBlock_def, FinalityRunBlock_def]

private theorem finalityRows_eq (st : State p.n) :
    finalityRows p st = finalityStoreRows p st := by
  rw [finalityRows_def, finalityStoreRows_def]

private theorem slashableBound_iff :
    FinalitySlashableBound p c E rho ↔ FGSASlashableBound p c E rho := by
  rw [FinalitySlashableBound_def, FGSASlashableBound_def]
  simp only [finalityBlock_eq]

/-- ROOT-DIGEST W2b. DC Consensus.certificatesAccountable: INTENTIONAL selected W certificate.
The owner equations transfer the run-free accountability theorem. -/
theorem fgsa_apiPureAccountableClaim_body :
    ∀ (K W T₁ T₂ : FGBlock (Fin p.n)) (h₁ h₂ : Nat),
      KitFG.RootInjectiveOn K W →
      FinalityFinalizedAt p K T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
      HasSlashableWeightBetween p.E (chainRows K) (chainRows W) ∨
        FGBlock.compatible T₁ T₂ = true := by
  simpa only [finalizedAt_eq] using fgsa_pureAccountable p

/-- ROOT-DIGEST W2b. DC certificatesAccountable agreement: INTENTIONAL selected W certificate.
The owner equations transfer the run-free agreement theorem. -/
theorem fgsa_apiPureAgreementClaim_body :
    ∀ (K W T₁ T₂ : FGBlock (Fin p.n)) (h₁ h₂ : Nat),
      KitFG.RootInjectiveOn K W →
      FinalityFinalizedAt p K T₁ h₁ → FinalityFinalizedAt p W T₂ h₂ →
      ¬ HasSlashableWeightBetween p.E (chainRows K) (chainRows W) →
        FGBlock.compatible T₁ T₂ = true := by
  simpa only [finalizedAt_eq] using fgsa_pureAgreement p

/-- ROOT-DIGEST W2b. DC Consensus.finalizedAccountable: INTENTIONAL W observations.
The owner equations transfer chain, event-prefix, and time-read accountability. -/
theorem fgsa_apiWholeRunAccountableClaim_body :
    ∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      NamedRootCollisionFree p c E rho → FinalityExecution p c rho → WholeRunAccountable p c E rho
        := by
  intro V _ In c E rho hroots _
  rw [WholeRunAccountable_def]
  have ha := fgsa_wholeRunAccountable (hroots := hroots) p c E rho
  simpa only [finalityBlock_eq, finalizedAt_eq, finalityRows_eq] using
    And.intro ha.chains (And.intro ha.eventPrefixes ha.reads)

/-- ROOT-DIGEST W2b. DC Consensus.finalizedSafe: INTENTIONAL selected W observations.
The owner equations transfer whole-run agreement under the same all-run bound. -/
theorem fgsa_apiWholeRunAgreementClaim_body :
    ∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      NamedRootCollisionFree p c E rho → FinalityExecution p c rho → FinalitySlashableBound p c E
        rho →
      WholeRunAgreement p c E rho := by
  intro V _ In c E rho hroots _ hb
  rw [WholeRunAgreement_def]
  simpa only [finalityBlock_eq, finalizedAt_eq] using
    fgsa_wholeRunAgreement (hroots := hroots) p c E rho ((slashableBound_iff p c E rho).mp hb)

/-- ROOT-DIGEST W2b. DC internal event-prefix agreement: INTENTIONAL stored W finality.
The owner equations transfer the all-run bound; no new premise is required. -/
theorem fgsa_apiEventPrefixAgreementClaim_body :
    ∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      NamedRootCollisionFree p c E rho → FinalityExecution p c rho → FinalitySlashableBound p c E
        rho →
      ∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ i j,
        FGBlock.compatible (storeAt p c E rho i x).fg.F
          (storeAt p c E rho j y).fg.F = true := by
  intro V _ In c E rho hroots _ hb x _ y _ i j
  exact fgsa_eventPrefixAgreement_of_bound (hroots := hroots) p c E rho
    ((slashableBound_iff p c E rho).mp hb) i j x y

private theorem finalityCarriage_of_rows (A : Finset (Row (Fin p.n)))
    (hA : FinalityRowCarriage p c E rho A) : FinalityCarriage p c E rho A := by
  rw [FinalityRowCarriage_def] at hA
  rw [FinalityCarriage_def]
  intro u hu
  obtain ⟨a, ha, hs, he⟩ := hA u hu
  refine ⟨a, 0, ha, hs, ?_⟩
  intro z hz hh
  obtain ⟨j, r, hj⟩ := he z hz hh
  rw [HonestRowAt_def] at hj
  exact ⟨j, p.actionTime r, hj.2⟩

/-- DC internal slashableBound_of_belowOneThird: INTENTIONAL fixed FG seats.
The row-carriage equation supplies actual emission; unit weights supply the bound. -/
theorem fgsa_apiFaultCountSlashableBoundClaim_body :
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
      V2.D.Linked (fgsaFamilies p c).linked rho →
      (∀ K, FinalityBlock p c E rho K → FinalityRowCarriage p c E rho (chainRows K)) →
      (∀ x ∈ rho.honest, EmittedRowsNoSlash p c E rho x) →
      (Gen.V2.Duty.faulty rho).card ≤ (p.n - 1) / 3 →
      FinalitySlashableBound p c E rho := by
  intro V _ _ In c E rho hL hcar hC hbot
  apply (slashableBound_iff p c E rho).mpr
  apply fgsa_slashableBound_of_faults p c E rho hL hbot hC
  intro K hK
  apply finalityCarriage_of_rows p c E rho
  exact hcar K ((finalityBlock_eq p c E rho K).mpr hK)

/-- DC Generic/Claims.lean:61 Consensus.finalizedMonotone; class: INTENTIONAL.
The legacy interface keeps NoRestart; restore now keeps F.
This body has exactly the premises of the restored monotonicity contract. -/
theorem fgsa_apiFinalizedMonotonicityClaim_body :
  ∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    rho.events.Pairwise (fun a b => a.key ≤ b.key) → V2.D.NoRestart rho →
    ∀ x ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
      Block.Preceq (finalizedOut (V2.D.Run.readAt E rho t x))
        (finalizedOut (V2.D.Run.readAt E rho t' x)) :=
  fun c E rho hs hnr => fgsa_finalizedMonotone p c E rho hs hnr

/-- The approved P21 companion permits retained-store restarts. -/
theorem fgsa_apiFinalizedMonotonicityRestartClaim_body :
  ∀ {V : Type} [DecidableEq V] {In : Type} (c : AppCodec In)
    (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)),
    rho.events.Pairwise (fun a b => a.key ≤ b.key) →
    ∀ x ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
      Block.Preceq (finalizedOut (V2.D.Run.readAt E rho t x))
        (finalizedOut (V2.D.Run.readAt E rho t' x)) :=
  fun c E rho hs => fgsa_finalizedMonotone_restart p c E rho hs

/-- ROOT-DIGEST W2b. DC Consensus.finalizedSafe/finalizedMonotone: INTENTIONAL event-prefix reads.
BaseSet and the fault bound supply agreement; the retained store supplies monotonicity. -/
theorem fgsa_apiFinalizedSafetyClaim_body :
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
      FinalizedSafetyPrem p c E rho pt →
        Gen.Pure.CompatOn (· ∈ rho.honest) (F_at p c E rho) (· ≤ rho.events.length) ∧
        Gen.Pure.MonoOn (· ∈ rho.honest) (F_at p c E rho) (· ≤ rho.events.length) := by
  intro V _ _ In c E rho pt hp
  constructor
  · intro i j x y _ _ hx hy
    exact eraseFG_compatible (fgsa_finalizedSafety (hroots := hp.set.idealization) p c E rho hp i
      j x y hx hy)
  · intro i j x _ _ hij hx
    exact eraseFG_preceq (fgsa_rMonoAll p c E rho i j x hx hij).1

/-- ROOT-DIGEST W2b. DC finalized_preceq_of_height_lt: INTENTIONAL accepted W carrier observation.
BaseSet and the fault bound discharge the strict crossing channel. -/
theorem fgsa_apiFinalLockClaim_body :
    ∀ {V : Type} [DecidableEq V] [Fintype V] {In : Type} (c : AppCodec In)
      (E : Generic.Env V) (rho : V2.D.Run V (fgsa p c)) (pt : Unit),
      FinalizedSafetyPrem p c E rho pt → RXing p c E rho := by
  intro V _ _ In c E rho pt hp i j x y K W hx hij hK hKF hW hh
  apply fgsa_finalLock (hroots := hp.set.idealization) p c E rho hp.set.linked (Gen.Pure.count_rec
    p.nPos hp.fault)
    hp.set.valid.toUnforgeableSignatures x hx i j hij K hK hKF y W hW
  simpa only [heightView_eq_simplex, KitFG.simplexHeightView_def, KitFG.heightOf_def, hOf] using hh

/-- DC honestNeverSlashed: SAME conclusion and signature premise;
INTENTIONAL fixed-seat Linked premise. The base theorem supplies this body. -/
theorem fgsa_apiHonestNeverSlashedClaim_body :
    ∀ {In : Type} (c : AppCodec In) (E : Generic.Env (Fin p.n))
      (rho : V2.D.Run (Fin p.n) (fgsa p c)),
      V2.D.UnforgeableSignatures E rho →
      V2.D.Linked (fgsaFamilies p c).linked rho →
      Gen.V2.Duty.HonestNeverSlashed (fgsaSlashing p c E) rho :=
  fun c E rho hU hL => fgsa_honestNeverSlashed p c E rho hU hL

end AvailableChain.FGSA.Run
end
