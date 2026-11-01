module
public import AvailableChainFGCompose.Statements.SafetyStore -- shake: keep (re-export)
public import AvailableChainFGCompose.Statements.SafetyClient -- shake: keep (re-export)
public import AvailableChainEngineV2.Conditions.Duty.Committees -- shake: keep (contract types)
public import AvailableChainGeneric.Statements.V2.Duty.Counts -- shake: keep (contract types)

@[expose] public section

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

def SafetyWholeAccountable : Prop :=
  (∀ A B T T' h h',
    safetyRunBlock R S E rho A → safetyRunBlock R S E rho B →
    safetyFinalizedAt f A T h → safetyFinalizedAt f B T' h' →
    HasSlashableWeightBetween Ef (chainRows A) (chainRows B) ∨
      FGBlock.compatible T T' = true) ∧
  (∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ i j : Nat,
    HasSlashableWeightBetween Ef
      (safetyRows R (V2.D.Run.stateBefore E rho i x))
      (safetyRows R (V2.D.Run.stateBefore E rho j y)) ∨
    FGBlock.compatible (R.core (V2.D.Run.stateBefore E rho i x)).fg.F
      (R.core (V2.D.Run.stateBefore E rho j y)).fg.F = true) ∧
  (∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ t t' : Time,
    HasSlashableWeightBetween Ef
      (safetyRows R (V2.D.Run.readAt E rho t x))
      (safetyRows R (V2.D.Run.readAt E rho t' y)) ∨
    FGBlock.compatible (R.core (V2.D.Run.readAt E rho t x)).fg.F
      (R.core (V2.D.Run.readAt E rho t' y)).fg.F = true)

theorem SafetyWholeAccountable_def :
    SafetyWholeAccountable R S Ef f E rho =
      ((∀ A B T T' h h',
    safetyRunBlock R S E rho A → safetyRunBlock R S E rho B →
    safetyFinalizedAt f A T h → safetyFinalizedAt f B T' h' →
    HasSlashableWeightBetween Ef (chainRows A) (chainRows B) ∨
      FGBlock.compatible T T' = true) ∧
  (∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ i j : Nat,
    HasSlashableWeightBetween Ef
      (safetyRows R (V2.D.Run.stateBefore E rho i x))
      (safetyRows R (V2.D.Run.stateBefore E rho j y)) ∨
    FGBlock.compatible (R.core (V2.D.Run.stateBefore E rho i x)).fg.F
      (R.core (V2.D.Run.stateBefore E rho j y)).fg.F = true) ∧
  (∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ t t' : Time,
    HasSlashableWeightBetween Ef
      (safetyRows R (V2.D.Run.readAt E rho t x))
      (safetyRows R (V2.D.Run.readAt E rho t' y)) ∨
    FGBlock.compatible (R.core (V2.D.Run.readAt E rho t x)).fg.F
      (R.core (V2.D.Run.readAt E rho t' y)).fg.F = true)) := rfl

def SafetyWholeAgreement : Prop :=
  (∀ A B T T' h h',
    safetyRunBlock R S E rho A → safetyRunBlock R S E rho B →
    safetyFinalizedAt f A T h → safetyFinalizedAt f B T' h' →
      FGBlock.compatible T T' = true) ∧
  (∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ t t' : Time,
    FGBlock.compatible (R.core (V2.D.Run.readAt E rho t x)).fg.F
      (R.core (V2.D.Run.readAt E rho t' y)).fg.F = true)

theorem SafetyWholeAgreement_def :
    SafetyWholeAgreement R S f E rho =
      ((∀ A B T T' h h',
    safetyRunBlock R S E rho A → safetyRunBlock R S E rho B →
    safetyFinalizedAt f A T h → safetyFinalizedAt f B T' h' →
      FGBlock.compatible T T' = true) ∧
  (∀ x ∈ rho.honest, ∀ y ∈ rho.honest, ∀ t t' : Time,
    FGBlock.compatible (R.core (V2.D.Run.readAt E rho t x)).fg.F
      (R.core (V2.D.Run.readAt E rho t' y)).fg.F = true)) := rfl

def safetySlashesRead (I : Gen.V2.Duty.SlashingInterface (V := V) P) : Prop :=
  ∀ v, I.slashes rho v ↔
    ∃ x y t t' i,
      SlashableBetween (safetyRows R (V2.D.Run.readAt E rho t x))
        (safetyRows R (V2.D.Run.readAt E rho t' y)) i ∧
      safetyHolder S rho i = v

theorem safetySlashesRead_def (I : Gen.V2.Duty.SlashingInterface (V := V) P) :
    safetySlashesRead R S E rho I =
      (∀ v, I.slashes rho v ↔
        ∃ x y t t' i,
          SlashableBetween (safetyRows R (V2.D.Run.readAt E rho t x))
            (safetyRows R (V2.D.Run.readAt E rho t' y)) i ∧
          safetyHolder S rho i = v) := rfl

end AvailableChain.FGCompose
end
