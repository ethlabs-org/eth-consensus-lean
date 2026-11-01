module
public import AvailableChainFGCompose.Statements.SafetyClaims -- shake: keep (examples)
public import AvailableChainFGCompose.Proofs.SafetyAccountable -- shake: keep (examples)
public import AvailableChainFGCompose.Proofs.SafetyCount -- shake: keep (examples)
public import AvailableChainFGCompose.Proofs.SafetyMonotone -- shake: keep (examples)
public import AvailableChainFGCompose.Proofs.SafetySlashing -- shake: keep (examples)

public section

/-! PROVISIONAL safety contracts. S1 does not freeze these laws. -/

namespace AvailableChain.FGCompose
open AvailableChain.SimplexFG AvailableChain.KitFG
variable {In V : Type} {P : V2.ProtocolSpecD In}
variable {n : Nat} {Base Proposal Wire : Type}
variable (R : FGCoreReads P n Base Proposal Wire)
variable (S : FGSafetyReads P n Wire)
variable (Ef : Electorate (Fin n)) (H : FGHeightView (Fin n))
variable (f : FGFinalityView (Fin n)) (cfg : FGConfig)
variable [DecidableEq V] (E : Generic.Env V) (rho : V2.D.Run V P)

variable (Good : P.State → Prop) (Q : Block → Prop)

-- safety_run_accountable has the provisional field type.
example : (∀ (_C : FGCoreLaws R) (_L : FGSafetyStoreLaws R S H f Good)
    (_K : FGCertificateLaws Ef H f) (_N : FGSafetyScopeLaws R S E rho Q)
    (_hr : safetyScopedRoots R Q),
    SafetyWholeAccountable R S Ef f E rho) :=
  safety_run_accountable R S Ef H f E rho Good Q

-- safety_run_agreement has the provisional field type.
example : (∀ (_C : FGCoreLaws R) (_L : FGSafetyStoreLaws R S H f Good)
    (_K : FGCertificateLaws Ef H f) (_N : FGSafetyScopeLaws R S E rho Q)
    (_hr : safetyScopedRoots R Q) (_hb : safetyBound R S Ef E rho),
    SafetyWholeAgreement R S f E rho) :=
  safety_run_agreement R S Ef H f E rho Good Q

-- safety_event_agreement has the provisional field type.
example : (∀ (_C : FGCoreLaws R) (_L : FGSafetyStoreLaws R S H f Good)
    (_K : FGCertificateLaws Ef H f) (_N : FGSafetyScopeLaws R S E rho Q)
    (_hr : safetyScopedRoots R Q) (_hb : safetyBound R S Ef E rho)
    (i j : Nat) (x y : V),
    FGBlock.compatible (R.core (V2.D.Run.stateBefore E rho i x)).fg.F
      (R.core (V2.D.Run.stateBefore E rho j y)).fg.F = true) :=
  safety_event_agreement R S Ef H f E rho Good Q

-- safety_fault_count_bound proves the field-6 statement.
example : ∀ [Fintype V]
    (_U : FGSafetyUnitLaws Ef) (linked : P.Label → Prop)
    (_hfg : linked S.fgLabel) (_hL : V2.D.Linked linked rho)
    (_hc : ∀ B, safetyRunBlock R S E rho B →
      safetyCarriage S E rho (chainRows B))
    (_he : ∀ x ∈ rho.honest, safetyNoSlash S E rho x)
    (_hf : (Gen.V2.Duty.faulty rho).card ≤ (n - 1) / 3),
    safetyBound R S Ef E rho := by
  intro _ U linked hfg hL hc he hf
  exact safety_fault_count_bound R S Ef E rho U linked hfg hL hc he hf

-- safety_finalized_monotone proves the field-7 statement.
example : ∀ (_C : FGCoreLaws R) (_O : FGSafetyOrderLaws R S)
    (_hs : rho.events.Pairwise (fun a b => a.key ≤ b.key))
    (_hnr : V2.D.NoRestart rho),
    ∀ x ∈ rho.honest, ∀ t t' : Time, t ≤ t' →
      Block.Preceq (S.finalizedOut (V2.D.Run.readAt E rho t x))
        (S.finalizedOut (V2.D.Run.readAt E rho t' x)) := by
  intro C O hs hnr
  exact safety_finalized_monotone R S E rho C O hs hnr

-- safety_honest_never_slashed has the provisional field type.
example : (∀ (_C : FGCoreLaws R) (_W : FGSafetyWireLaws S)
    (_L : FGSafetyStoreLaws R S H f Good)
    (_J : FGSafetyClientLaws S Ef cfg)
    (linked : P.Label → Prop) (_hfg : linked S.fgLabel)
    (I : Gen.V2.Duty.SlashingInterface (V := V) P)
    (_hi : safetySlashesRead R S E rho I)
    (_hu : V2.D.UnforgeableSignatures E rho) (_hl : V2.D.Linked linked rho),
    Gen.V2.Duty.HonestNeverSlashed I rho) :=
  safety_honest_never_slashed R S Ef H f cfg E rho Good

end AvailableChain.FGCompose
end
