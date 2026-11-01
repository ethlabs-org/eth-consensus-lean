module
public import AvailableChainEngineV2.Conditions.Interface

@[expose] public section

namespace AvailableChain.Gen.V2

open AvailableChain AvailableChain.V2

variable {V : Type} [DecidableEq V] {In : Type}

/-- DC: DecoupledConsensusStatements/Generic/Properties.lean:26 (b241081, 2026-09-28);
same: verbatim mirror over V2 runs.
The V2 output reader is `outputAt` in
`AvailableChainEngineV2/Conditions/Interface.lean:78`; it uses environment `E`. -/
def ConsistentFrom (P : ProtocolSpec In) (E : Generic.Env V)
    (rho : Run V P) (g₁ g₂ : Output P) (t₀ : Time) : Prop :=
  ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t' : Time,
    t₀ ≤ t → t ≤ rho.horizon → t₀ ≤ t' → t' ≤ rho.horizon →
    Block.Compatible (outputAt E rho g₁ u t) (outputAt E rho g₂ v t')

/-- Defining equation.
DC: DecoupledConsensusStatements/Generic/Properties.lean:26 (b241081, 2026-09-28);
same: verbatim mirror over V2 runs. -/
theorem ConsistentFrom_def (P : ProtocolSpec In) (E : Generic.Env V)
    (rho : Run V P) (g₁ g₂ : Output P) (t₀ : Time) :
    ConsistentFrom P E rho g₁ g₂ t₀ =
      (∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t' : Time,
        t₀ ≤ t → t ≤ rho.horizon → t₀ ≤ t' → t' ≤ rho.horizon →
        Block.Compatible (outputAt E rho g₁ u t) (outputAt E rho g₂ v t')) := by rfl

/-- DC: DecoupledConsensusStatements/Generic/Properties.lean:34 (b241081, 2026-09-28);
same: verbatim mirror over V2 runs. -/
def AgreeFrom (P : ProtocolSpec In) (E : Generic.Env V)
    (rho : Run V P) (g : Output P) (t₀ : Time) : Prop :=
  ConsistentFrom P E rho g g t₀

/-- Defining equation.
DC: DecoupledConsensusStatements/Generic/Properties.lean:34 (b241081, 2026-09-28);
same: verbatim mirror over V2 runs. -/
theorem AgreeFrom_def (P : ProtocolSpec In) (E : Generic.Env V)
    (rho : Run V P) (g : Output P) (t₀ : Time) :
    AgreeFrom P E rho g t₀ = ConsistentFrom P E rho g g t₀ := by rfl

/-- DC: DecoupledConsensusStatements/Generic/Properties.lean:40 (b241081, 2026-09-28);
same: verbatim mirror over V2 runs. -/
def MonotoneFrom (P : ProtocolSpec In) (E : Generic.Env V)
    (rho : Run V P) (g : Output P) (t₀ : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ t t' : Time, t₀ ≤ t → t ≤ t' → t' ≤ rho.horizon →
    Block.Preceq (outputAt E rho g v t) (outputAt E rho g v t')

/-- Defining equation.
DC: DecoupledConsensusStatements/Generic/Properties.lean:40 (b241081, 2026-09-28);
same: verbatim mirror over V2 runs. -/
theorem MonotoneFrom_def (P : ProtocolSpec In) (E : Generic.Env V)
    (rho : Run V P) (g : Output P) (t₀ : Time) :
    MonotoneFrom P E rho g t₀ =
      (∀ v ∈ rho.honest, ∀ t t' : Time, t₀ ≤ t → t ≤ t' → t' ≤ rho.horizon →
        Block.Preceq (outputAt E rho g v t) (outputAt E rho g v t')) := by rfl

/-- DC: DecoupledConsensusStatements/Generic/Properties.lean:48 (b241081, 2026-09-28);
same: verbatim mirror over V2 runs. The field order is `agree`, then `monotone`. -/
structure SafeFrom (P : ProtocolSpec In) (E : Generic.Env V)
    (rho : Run V P) (g : Output P) (t₀ : Time) : Prop where
  agree : AgreeFrom P E rho g t₀
  monotone : MonotoneFrom P E rho g t₀

/-- Defining equation for the two fields.
DC: DecoupledConsensusStatements/Generic/Properties.lean:48 (b241081, 2026-09-28);
same: verbatim mirror over V2 runs. -/
theorem SafeFrom_def (P : ProtocolSpec In) (E : Generic.Env V)
    (rho : Run V P) (g : Output P) (t₀ : Time) :
    SafeFrom P E rho g t₀ = (AgreeFrom P E rho g t₀ ∧ MonotoneFrom P E rho g t₀) := by
  apply propext
  exact ⟨fun h => ⟨h.agree, h.monotone⟩, fun h => ⟨h.1, h.2⟩⟩

/-- DC: DecoupledConsensusStatements/Generic/Properties.lean:86 (b241081, 2026-09-28);
same: verbatim mirror over V2 runs. This is the helper used by `PersistsFrom`. -/
def InBy (P : ProtocolSpec In) (E : Generic.Env V)
    (rho : Run V P) (g : Output P) (B : Block) (t : Time) : Prop :=
  ∀ v ∈ rho.honest, Block.Preceq B (outputAt E rho g v t)

/-- Defining equation.
DC: DecoupledConsensusStatements/Generic/Properties.lean:86 (b241081, 2026-09-28);
same: verbatim mirror over V2 runs. -/
theorem InBy_def (P : ProtocolSpec In) (E : Generic.Env V)
    (rho : Run V P) (g : Output P) (B : Block) (t : Time) :
    InBy P E rho g B t =
      (∀ v ∈ rho.honest, Block.Preceq B (outputAt E rho g v t)) := by rfl

/-- DC: DecoupledConsensusStatements/Generic/Properties.lean:124 (b241081, 2026-09-28);
same: verbatim mirror over V2 runs. -/
def PersistsFrom (P : ProtocolSpec In) (E : Generic.Env V)
    (rho : Run V P) (g : Output P) (T b₀ : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ B, Block.Preceq B (outputAt E rho g v T) →
    ∀ t, b₀ ≤ t → t ≤ rho.horizon → InBy P E rho g B t

/-- Defining equation.
DC: DecoupledConsensusStatements/Generic/Properties.lean:124 (b241081, 2026-09-28);
same: verbatim mirror over V2 runs. -/
theorem PersistsFrom_def (P : ProtocolSpec In) (E : Generic.Env V)
    (rho : Run V P) (g : Output P) (T b₀ : Time) :
    PersistsFrom P E rho g T b₀ =
      (∀ v ∈ rho.honest, ∀ B, Block.Preceq B (outputAt E rho g v T) →
        ∀ t, b₀ ≤ t → t ≤ rho.horizon → InBy P E rho g B t) := by rfl

end AvailableChain.Gen.V2
