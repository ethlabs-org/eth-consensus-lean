module
public import AvailableChainGeneric.Statements.V2.Duty.Receipt
public import AvailableChainGeneric.Statements.V2.Duty.Reads -- shake: keep (re-export)
public import AvailableChainGeneric.Statements.Pure.Quorum
public import AvailableChainEngineV2.Conditions.Duty.Delivery
public import AvailableChainEngineV2.Conditions.Duty.Interface -- shake: keep (re-export)
public import AvailableChainEngineV2.Conditions.Duty.Schedule -- shake: keep (re-export)
public import Mathlib.Order.Monotone.Basic -- shake: keep (re-export)

@[expose] public section

open AvailableChain AvailableChain.V2 AvailableChain.V2.D AvailableChain.V2.D.Engine
open AvailableChain.Gen.Pure

namespace AvailableChain.Gen.V2.Duty

variable {V : Type} [DecidableEq V] {In : Type} {P : ProtocolSpecD In}

-- DC: Conditions.lean:110,134; INTENTIONAL: One record for both regimes; GLY r3.19 S122.
-- Source: AvailableChainGeneric/Statements/V2/Regimes.lean:26.
def LabelSync (E : Generic.Env V) (rho : D.Run V P) (vt dt : Time) : Prop :=
  ∃ dl cut, DeliveryWithin E rho dl cut ∧ Monotone dl ∧ (∀ t, t < dl t) ∧
    (∀ t, dl t ≤ max t vt + E.Δ) ∧
    vt + E.Δ ≤ dt ∧ dt ≤ cut ∧ dt ≤ rho.horizon

-- Source: AvailableChainGeneric/Statements/V2/Regimes.lean:32.
theorem LabelSync_def (E : Generic.Env V) (rho : D.Run V P) (vt dt : Time) :
    LabelSync E rho vt dt =
      (∃ dl cut, DeliveryWithin E rho dl cut ∧ Monotone dl ∧ (∀ t, t < dl t) ∧
        (∀ t, dl t ≤ max t vt + E.Δ) ∧
        vt + E.Δ ≤ dt ∧ dt ≤ cut ∧ dt ≤ rho.horizon) := rfl

-- DC: Conditions.lean:134,169; INTENTIONAL: Point batch; producer window; GLY r3.19 S123.
-- Source: AvailableChainGeneric/Statements/V2/Regimes.lean:41.
structure LabelFacts (E : Generic.Env V) (rho : D.Run V P) (vt dt : Time) (h m : Nat) : Prop where
  sync  : LabelSync E rho vt dt
  batch : Batch h m

-- DC: Conditions.lean:88; INTENTIONAL: Root freedom is proved; GLY r3.19 S124.
-- Source: AvailableChainGeneric/Statements/V2/Regimes.lean:48.
structure BaseCore (E : Generic.Env V) (rho : D.Run V P) : Prop where
  valid : D.ExecutionValid E rho
  noRestart : D.NoRestart rho

-- DC: Conditions.lean:134; same: Same finite-prefix delivery; GLY r3.19 S125.
-- Source: AvailableChainGeneric/Statements/V2/Regimes.lean:55.
structure HealthyCore (E : Generic.Env V) (rho : D.Run V P) (b₀ : Time) : Prop where
  healthy : D.HealthyPrefixDelivery E rho b₀

-- DC: Regimes.lean:148–149; same: Same healthy and interval fields; GLY r3.19 S126.
-- Source: AvailableChainGeneric/Statements/V2/Regimes.lean:62.
structure CutCore (E : Generic.Env V) (rho : D.Run V P) (b₀ : Time) : Prop
    extends HealthyCore E rho b₀ where
  cut : 0 ≤ b₀ ∧ b₀ ≤ rho.horizon

-- DC: Regimes.lean:149; INTENTIONAL: Adds 0 ≤ T ≤ b₀; GLY r3.19 S127.
-- Source: AvailableChainGeneric/Statements/V2/Regimes.lean:70.
structure OutageCore (rho : D.Run V P) (T b₀ b₁ : Time) : Prop where
  order : 0 ≤ T ∧ T ≤ b₀ ∧ b₀ ≤ b₁ ∧ b₁ ≤ rho.horizon

-- DC: Regimes.lean:59–66; Conditions.lean:110,207; INTENTIONAL: Healing uses G; GLY r3.19 S128.
-- Source: AvailableChainGeneric/Statements/V2/Regimes.lean:76.
structure RecoveryCore {In : Type} (P : ProtocolSpecD In) (I : D.Interface P)
    (E : Generic.Env V) (rho : D.Run V P) (G : Time) : Prop where
  sync : D.PartialSynchrony E rho
  gap  : ∀ t, E.t_GST ≤ t → t + G ≤ rho.horizon →
           ∃ s, t < D.proposalTime I s ∧ D.proposalTime I s ≤ t + G ∧ HonestSlot rho I s

-- DC: additive (no DC counterpart); reason: Duty execution contract.
-- Source: AvailableChainGeneric/Statements/V2/Regimes.lean:91.
def SeedAt (E : Generic.Env V) (rho : D.Run V P) (start : Nat)
    (Q : V → P.State → Prop) : Prop :=
  ∀ v, Q v (D.Run.stateBefore E rho start v)

-- Source: AvailableChainGeneric/Statements/V2/Regimes.lean:95.
theorem SeedAt_def (E : Generic.Env V) (rho : D.Run V P) (start : Nat)
    (Q : V → P.State → Prop) :
    SeedAt E rho start Q = ∀ v, Q v (D.Run.stateBefore E rho start v) := rfl

end AvailableChain.Gen.V2.Duty
